import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.SatAtBVLogical
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize
import Lean.Elab.Tactic.BVDecide.Frontend.LRAT
import Lean.Meta.Native
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

/-!
# `bv_decidet`: an instrumented `bv_decide`

`bv_decidet "out.csv"` behaves exactly like `bv_decide`, but appends one row per invocation to
`out.csv` giving the wall-clock cost of each internal stage.

The stages, in the order in which `bv_decide` runs them:

* `normalize` -- `Normalize.bvNormalize`: simp set / AC normalization of the Lean goal.
* `reflect`   -- `reflectBV`: Lean goal + hypotheses to `BVLogicalExpr` (incl. `shareCommon`).
* `bitblast`  -- `BVLogicalExpr.bitblast`: build the and-inverter graph.
* `cnf`       -- `relabelNat'` + `AIG.toCNF`: AIG to CNF.
* `dimacs`    -- `CNF.dimacs` serialization and write of the DIMACS file handed to the solver.
* `solve`     -- `External.satQuery`: the external SAT solver process, and nothing else.
* `lrat_read` -- read, parse and trim the LRAT file, then re-serialize it to the certificate.
* `expr_def`  -- `addAndCompile` of the reflected `BVLogicalExpr` constant.
* `cert_def`  -- `addAndCompile` of the LRAT certificate string constant.
* `verify`    -- `nativeEqTrue` on `verifyBVExpr`: compiling and running the LRAT checker.
* `assign`    -- `proveFalse` and `MVarId.assign`: closing the original goal.

Rolled up into the five coarse phases: normalization is `normalize`, AIG is `reflect + bitblast`,
CNF is `cnf + dimacs`, solving is `solve`, and checking is everything from `lrat_read` on.

`total` is the wall-clock time of the whole tactic; it exceeds the sum of the stages by the small
amount of bookkeeping that is deliberately excluded, i.e. computing the AIG/CNF/LRAT sizes that are
reported in the trailing statistics columns.

Times are in milliseconds with microsecond resolution. Every invocation writes exactly one complete
row, including the early-exit paths (goal closed by normalization, or a counterexample found), so
rows can never run into each other.
-/

namespace Lean.Parser
namespace Tactic

@[tactic_alt Lean.Parser.Tactic.bvDecideMacro]
syntax (name := bvDecidet) "bv_decidet" (str)? Lean.Parser.Tactic.optConfig : tactic

end Lean.Parser.Tactic

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Lean.Meta

/-- The timing stages, in the order in which they are recorded. -/
def stageNames : Array String :=
  #["normalize", "reflect", "bitblast", "cnf", "dimacs", "solve", "lrat_read",
    "expr_def", "cert_def", "verify", "assign"]

/--
The trailing size statistics, in the order in which they are recorded.

`lrat_file_bytes` is the size on disk of the LRAT file the solver produced, before parsing and
trimming; `lrat_steps` and `cert_bytes` describe the proof after trimming, which is what actually
gets compiled into the environment and checked.
-/
def statNames : Array String :=
  #["aig_nodes", "cnf_clauses", "lrat_file_bytes", "lrat_steps", "cert_bytes"]

def csvHeader : String :=
  ",".intercalate (["label", "status"] ++ stageNames.toList ++ ["total"] ++ statNames.toList)

/--
A running log of per-stage durations. Durations come from `IO.monoNanosNow` and are recorded as
elapsed times rather than absolute timestamps, so a row cannot be silently misaligned with its
header.
-/
structure StageLog where
  /-- Time at which the current stage started. -/
  last : IO.Ref Nat
  /-- Time at which the tactic started. -/
  start : Nat
  /-- Recorded stage durations, formatted in ms. -/
  times : IO.Ref (Array String)
  /-- Recorded size statistics. -/
  stats : IO.Ref (Array String)

def StageLog.new : IO StageLog := do
  let now ← IO.monoNanosNow
  return { last := ← IO.mkRef now, start := now, times := ← IO.mkRef #[], stats := ← IO.mkRef #[] }

/-- Render a nanosecond count as milliseconds with microsecond resolution. -/
def fmtMs (ns : Nat) : String :=
  let us := ns / 1000
  let frac := toString (us % 1000)
  s!"{us / 1000}.{"".pushn '0' (3 - frac.length) ++ frac}"

/-- Close off the current stage, recording how long it took, and start the next one. -/
def StageLog.tick (log : StageLog) : IO Unit := do
  let now ← IO.monoNanosNow
  let prev ← log.last.get
  log.last.set now
  log.times.modify (·.push (fmtMs (now - prev)))

/--
Restart the clock without recording a stage. Used around instrumentation-only work (computing the
AIG/CNF/LRAT sizes) so that it is not charged to the following stage.
-/
def StageLog.skip (log : StageLog) : IO Unit := do
  log.last.set (← IO.monoNanosNow)

def StageLog.stat (log : StageLog) (value : Nat) : IO Unit :=
  log.stats.modify (·.push (toString value))

/--
Write the accumulated row to `file`, padding any stages that were not reached. Writes the header
first if `file` does not exist yet. The row is emitted with a single write so that concurrently
built modules cannot interleave within a line.
-/
def StageLog.flush (log : StageLog) (file label status : String) : IO Unit := do
  let now ← IO.monoNanosNow
  let pad (a : Array String) (n : Nat) : List String :=
    (a ++ Array.replicate (n - a.size) "").toList
  let times := pad (← log.times.get) stageNames.size
  let stats := pad (← log.stats.get) statNames.size
  let row := ",".intercalate
    ([label, status] ++ times ++ [fmtMs (now - log.start)] ++ stats)
  let hasFile ← System.FilePath.pathExists file
  IO.FS.withFile file IO.FS.Mode.append fun handle => do
    unless hasFile do handle.putStr (csvHeader ++ "\n")
    handle.putStr (row ++ "\n")
    handle.flush

/--
Instrumented copy of `LratCert.toReflectionProof`, split into the three phases that dominate it:
compiling the reflected expression, compiling the certificate string, and actually running the
verified LRAT checker on them.
-/
def toReflectionProoft (cert : LratCert) (ctx : TacticContext) (reflectionResult : ReflectionResult)
    (log : StageLog) : MetaM Expr := do
  mkAuxDecl ctx.exprDef reflectionResult.expr (mkConst ``BVLogicalExpr)
  log.tick -- expr_def

  mkAuxDecl ctx.certDef (toExpr cert) (mkConst ``String)
  log.tick -- cert_def

  let reflectedExpr := mkConst ctx.exprDef
  let certExpr := mkConst ctx.certDef
  let reflectionTerm := mkApp2 (mkConst ``verifyBVExpr) reflectedExpr certExpr
  match (← nativeEqTrue `bv_decide reflectionTerm (axiomDeclRange? := (← getRef))) with
  | .notTrue =>
    throwError m!"Tactic `bv_decidet` failed: The LRAT certificate could not be verified; \
      evaluating the following term returned `false`:{indentExpr reflectionTerm}"
  | .success auxProof =>
    log.tick -- verify
    return mkApp3 (mkConst ``unsat_of_verifyBVExpr_eq_true) reflectedExpr certExpr auxProof
where
  mkAuxDecl (name : Name) (value type : Expr) : CoreM Unit :=
    withOptions (fun opt => opt.set `compiler.extract_closed false) do
      addAndCompile <| .defnDecl {
        name := name,
        levelParams := [],
        type := type,
        value := value,
        hints := .abbrev,
        safety := .safe
      }

/--
Instrumented copy of `lratBitblaster`. `runExternal` is inlined here so that DIMACS serialization,
the solver process itself, and LRAT parsing/trimming can be told apart: in the previous version all
three, plus the whole LRAT check, were lumped into a single trailing measurement.
-/
def lratBitblastert (goal : MVarId) (ctx : TacticContext) (reflectionResult : ReflectionResult)
    (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) (log : StageLog) :
    MetaM (Except CounterExample UnsatProver.Result) := do
  let bvExpr := reflectionResult.bvExpr
  -- lazyPure to prevent compiler lifting
  let entry ← IO.lazyPure (fun _ => bvExpr.bitblast)
  let aigSize := entry.aig.decls.size
  log.tick -- bitblast
  log.stat aigSize
  log.skip

  if ctx.config.graphviz then
    IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry
    log.skip

  -- lazyPure to prevent compiler lifting
  let (cnf, map) ← IO.lazyPure (fun _ =>
    let (entry, map) := entry.relabelNat'
    let cnf := AIG.toCNF entry
    (cnf, map))
  log.tick -- cnf
  log.stat cnf.clauses.size
  log.skip

  let res ← IO.FS.withTempFile fun cnfHandle cnfPath => do
    -- lazyPure to prevent compiler lifting
    cnfHandle.putStr (← IO.lazyPure (fun _ => cnf.dimacs))
    cnfHandle.flush
    log.tick -- dimacs
    let res ←
      External.satQuery ctx.solver cnfPath ctx.lratPath ctx.config.timeout
        ctx.config.binaryProofs ctx.config.solverMode
    log.tick -- solve
    pure res

  match res with
  | .sat assignment =>
    let equations := reconstructCounterExample map assignment aigSize atomsAssignment
    return .error { goal, unusedHypotheses := reflectionResult.unusedHypotheses, equations }
  | .unsat =>
    let lratFileBytes := (← ctx.lratPath.metadata).byteSize.toNat
    log.stat lratFileBytes
    log.skip

    let proof ← LratCert.load ctx.lratPath ctx.config.trimProofs
    let cert := LRAT.lratProofToString proof
    log.tick -- lrat_read
    log.stat proof.size
    log.stat cert.length
    log.skip

    let reflectionProof ← toReflectionProoft cert ctx reflectionResult log
    return .ok ⟨reflectionProof, cert⟩

/--
Instrumented copy of `closeWithBVReflection` composed with `bvUnsat`. Inlining them is what lets
`reflect` be measured on its own; previously it was folded into the AIG measurement.
-/
def bvUnsatt (g : MVarId) (ctx : TacticContext) (log : StageLog) :
    MetaM (Except CounterExample LratCert) := M.run do
  g.withContext do
    let reflectionResult ← reflectBV g
    log.tick -- reflect

    let flipper := (fun (expr, {width, atomNumber, synthetic}) => (atomNumber, (width, expr, synthetic)))
    let atomsPairs := (← getThe State).atoms.toList.map flipper
    let atomsAssignment := Std.HashMap.ofList atomsPairs
    log.skip

    match ← lratBitblastert g ctx reflectionResult atomsAssignment log with
    | .ok ⟨bvExprUnsat, cert⟩ =>
      let proveFalse ← reflectionResult.proveFalse bvExprUnsat
      g.assign proveFalse
      log.tick -- assign
      return .ok cert
    | .error counterExample => return .error counterExample

def bvDecidet' (g : MVarId) (ctx : TacticContext) (log : StageLog) :
    MetaM (Except CounterExample Result) := do
  let g? ← Normalize.bvNormalize g ctx.config
  log.tick -- normalize
  let some g := g? | return .ok ⟨none⟩
  match ← bvUnsatt g ctx log with
  | .ok lratCert => return .ok ⟨some lratCert⟩
  | .error counterExample => return .error counterExample

def bvDecidet (g : MVarId) (ctx : TacticContext) (csv label : String) : MetaM Result := do
  let log ← StageLog.new
  let res ←
    try
      bvDecidet' g ctx log
    catch e =>
      log.flush csv label "error"
      throw e
  match res with
  | .ok result =>
    log.flush csv label (if result.lratCert.isSome then "unsat" else "normalized")
    return result
  | .error counterExample =>
    log.flush csv label "sat"
    counterExample.goal.withContext do
      let error ← explainCounterExampleQuality counterExample
      throwError (← addMessageContextFull error)

declare_config_elab elabBVDecidetConfig Lean.Elab.Tactic.BVDecide.Frontend.BVDecideConfig

@[tactic Lean.Parser.Tactic.bvDecidet]
def evalBvDecidet : Tactic := fun
  | `(tactic| bv_decidet $[$csv?:str]? $cfg:optConfig) => do
    let csv := (csv?.map (·.getString)).getD "bvd_times.csv"
    let label := (← Term.getDeclName?).map toString |>.getD "<anonymous>"
    let cfg ← elabBVDecidetConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← BVDecide.Frontend.TacticContext.new lratFile cfg
      liftMetaFinishingTactic fun g => do
        discard <| bvDecidet g cfg csv label
  | _ => throwUnsupportedSyntax

end Frontend
end Lean.Elab.Tactic.BVDecide
