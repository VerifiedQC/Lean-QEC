
import Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical
import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Tactic.BVDecide.LRAT
import Lean.Meta.Native
import Init.Simproc
import Init.Grind.Tactics
import Init.MetaTypes
import Init.Data.Nat.Bitwise.Basic
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Meta.Tactic.BVDecide.Prover.Bitblast
import Lean.Meta.Tactic.BVDecide.Counterexample
import Lean.Meta.Tactic.Grind.Main
import Lean.Elab.Tactic.BVDecide


namespace Lean.Parser
namespace Tactic

--timed bv_decide tactic: Logs 5 items to a passed csv file:
--start, normalize, aig, cnf, solve, end
--start gives time at beginning of tactic
--normalize gives time after bv_normalize procedure is run: normalizes subexpressions up to associativity and commutativity
--aig converts the formula into an and-inverter-graph
--cnf converts the AIG into cnf form
--solve passes the cnf to the external solver and obtains a .lrat file certifying Sat/UNSAT
--end is the time between obtaining the .lrat and translating its proof into lean form.
@[tactic_alt Lean.Parser.Tactic.bvDecide]
syntax (name := bvDecidet) "bv_decidet" (str)? Lean.Parser.Tactic.optConfig : tactic

end Lean.Parser.Tactic

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Lean.Meta
open Lean.Meta.Tactic.BVDecide


/-- Appends an entry to a local CSV file -/
def logToCSV (fileName : String) (duration : Nat) : IO Unit := do
  -- Open in append mode ("a")
  IO.FS.withFile fileName IO.FS.Mode.append fun handle => do
    -- Format: Step Name, Time (ms)
    handle.putStr s!"{duration},"
    handle.flush


/--  -/
def putline (fileName : String) : IO Unit := do
  -- Open in append mode ("a")
  IO.FS.withFile fileName IO.FS.Mode.append fun handle => do
    -- Format: Step Name, Time (ms)
    handle.putStrLn ""
    handle.flush


/--
Turn an `LratCert` into a proof that some `reflectedExpr` is UNSAT.
(Copy of `Lean.Meta.Tactic.BVDecide.LratCert.toReflectionProof`, which is not exported.)
-/
def LratCert.toReflectionProoft (cert : LratCert) (ctx : TacticContext)
    (reflectionResult : ReflectionResult) : MetaM Expr := do
  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling expr term") do
    mkAuxDecl ctx.exprDef reflectionResult.expr (mkConst ``BVLogicalExpr)

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl ctx.certDef (toExpr cert) (mkConst ``String)

  let reflectedExpr := mkConst ctx.exprDef
  let certExpr := mkConst ctx.certDef
  let reflectionTerm := mkApp2 (mkConst ``verifyBVExpr) reflectedExpr certExpr

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling and evaluating reflection proof term") do
    match (← nativeEqTrue `bv_decide reflectionTerm (axiomDeclRange? := (← getRef))) with
    | .notTrue =>
      throwError m!"Tactic `bv_decidet` failed: The LRAT certificate could not be verified; \
        evaluating the following term returned `false`:{indentExpr reflectionTerm}"
    | .success auxProof =>
      return mkApp3 (mkConst ``unsat_of_verifyBVExpr_eq_true) reflectedExpr certExpr auxProof
where
  /--
  Add an auxiliary declaration. Only used to create constants that appear in our reflection proof.
  -/
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

def lratBitblastert (goal : MVarId) (ctx : TacticContext) (reflectionResult : ReflectionResult)
    (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) (csv : String) :
    MetaM (Except CounterExample (UnsatProver.Result LratCert)) := do
  let bvExpr := reflectionResult.bvExpr
  let entry ←
    withTraceNode `Meta.Tactic.bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => bvExpr.bitblast)
  let aigSize := entry.aig.decls.size
  trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."
  let aigtime ← IO.monoMsNow
  logToCSV csv aigtime
  if ctx.config.graphviz then
    IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry

  let (cnf, map) ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Converting AIG to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ =>
        let (entry, map) := entry.relabelNat'
        let cnf := AIG.toCNF entry
        (cnf, map)
      )
  let cnftime ← IO.monoMsNow
  logToCSV csv cnftime
  let res ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Obtaining external proof certificate") do
      runExternal
        cnf
        ctx.solver
        ctx.lratPath
        ctx.config.trimProofs
        ctx.config.timeout
        ctx.config.binaryProofs
        ctx.config.solverMode

  match res with
  | .ok cert =>
    trace[Meta.Tactic.sat] "SAT solver found a proof."
    let proof ← LratCert.toReflectionProoft cert ctx reflectionResult
    return .ok ⟨proof, cert⟩
  | .error assignment =>
    trace[Meta.Tactic.sat] "SAT solver found a counter example."
    let equations := reconstructCounterExample map assignment aigSize atomsAssignment
    return .error { goal, unusedHypotheses := reflectionResult.unusedHypotheses, equations }

def closeWithBVReflectiont (g : MVarId) (unsatProver : UnsatProver α) :
    M (Except CounterExample α) :=
  g.withContext do
    let reflectionResult ←
      withTraceNode `Meta.Tactic.bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g
    trace[Meta.Tactic.bv] "Reflected bv logical expression: {reflectionResult.bvExpr}"

    let flipper := (fun (expr, {width, atomNumber, synthetic}) => (atomNumber, (width, expr.expr, synthetic)))
    let atomsPairs := (← getThe Meta.Tactic.BVDecide.State).atoms.toList.map flipper
    let atomsAssignment := Std.HashMap.ofList atomsPairs
    match ← unsatProver g reflectionResult atomsAssignment with
    | .ok ⟨bvExprUnsat, cert⟩ =>
      let proveFalse ← reflectionResult.proveFalse bvExprUnsat
      g.assign proveFalse
      return .ok cert
    | .error counterExample => return .error counterExample

def bvUnsatt (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext) (csv : String) :
    Sym.SymM (Except CounterExample LratCert) := M.run (hypotheses := hypotheses) do
  let unsatProver : UnsatProver LratCert := fun g reflectionResult atomsAssignment => do
    withTraceNode `Meta.Tactic.bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblastert g ctx reflectionResult atomsAssignment csv
  let solvetime ← IO.monoMsNow
  logToCSV csv solvetime
  closeWithBVReflection g unsatProver

def bvDecidet' (target : Normalize.Target) (ctx : TacticContext) (csv : String) :
    Grind.GrindM (Except CounterExample Result) := do
  let starttime ← IO.monoMsNow
  logToCSV csv starttime
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    let solved ← Normalize.bvNormalize
    let normalizetime ← IO.monoMsNow
    logToCSV csv normalizetime
    if solved then
      putline csv
      return .ok ⟨none⟩

    match ← bvUnsatt (← Normalize.PreProcessM.getTargetMVarId) (← Normalize.PreProcessM.getHyps) ctx csv with
    | .ok (lratCert) =>
      let endTime ← IO.monoMsNow
      logToCSV csv endTime
      putline csv
      return .ok ⟨some lratCert⟩
    | .error counterExample => return .error counterExample

def bvDecidet (target : Normalize.Target) (ctx : TacticContext) (csv : String) : Grind.GrindM Result := do
  match ← bvDecidet' target ctx csv with
  | .ok result => return result
  | .error counterExample =>
    counterExample.goal.withContext do
      let error ← explainCounterExampleQuality counterExample
      throwError (← addMessageContextFull error)

declare_config_elab elabBVDecidetConfig Lean.Elab.Tactic.BVDecide.BVDecideConfig

#eval (do
  -- 1. Create a dummy configuration block
  let cfg : BVDecideConfig := {}

  -- 2. Construct a mocked tactic context targeting a dummy file
  let ctx ← TacticContext.new "dummy.lrat" cfg

  -- 3. Print out the computed solver FilePath
  IO.println s!"Default solver path: {ctx.solver}"
)

@[tactic Lean.Parser.Tactic.bvDecidet]
def evalBvDecidet : Tactic := fun
  | `(tactic| bv_decidet $csv:str $cfg:optConfig) => do
    logInfo m!"{csv}"
    let cfg ← elabBVDecidetConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg
      liftMetaFinishingTactic fun g => do
        let params ← Grind.mkDefaultParams {}
        discard <| Grind.GrindM.run (params := params) <| bvDecidet (.mvarIdTarget g) cfg csv.getString
  | _ => throwUnsupportedSyntax

end Frontend
end Lean.Elab.Tactic.BVDecide

/-
theorem bitvec_example (x y : BitVec 16)
    (hx : x > 1) (hy : y > 1) :(x.zeroExtend 32) * (y.zeroExtend 32) ≠ 10301 := by
  -- Run your timed version and log to a custom file
  bv_decidet "bvd_times.csv" (timeout := 9999) (maxSteps := 9999999)
-/
