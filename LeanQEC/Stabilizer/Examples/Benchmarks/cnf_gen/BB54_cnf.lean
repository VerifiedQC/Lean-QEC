import LeanQEC.ComputerAlgebra.BitVecSAT
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv

/-!
CNF generation for BB54 (both distance queries).

Cut down from `LeanQEC/Stabilizer/Examples/BB/BB54.lean` to just the two `lt_dist_sat` goals.
Each `sat.solver` wrapper copies the DIMACS file `bv_decide` writes into `bv_decide_queries/` and
exits without reporting a result, so the tactic fails *after* the CNF is written. That is the point:
these modules produce formulas, they do not prove anything, and they are expected to fail to build.

Two rewrites keep the prepared term small, and both are what make the larger codes tractable:
* `hloc` replaces `loc_constraints` by the one-hot `loc_constraints_fast`, turning the
  `n * k = 270` slot comparisons into `k = 5` shifts (`loc_constraints_iff_fast`, which needs
  `n <= 2 ^ nlog`, here `54 <= 64`).
* `hclog` evaluates `Nat.clog 2 54` so `simp` can unfold the `6` steps of `BitVec.xorFold`
  inside `BitVec.dot_product`; plain `simp` cannot evaluate `Nat.clog` itself.
-/

set_option maxRecDepth 9999999
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option exponentiation.threshold 1000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

def BB54_X : BitVec (27 * 54) := 0x9008042800000120100850000002402050800008008040a10000100100854000002002010a800000400402150000008008042a000001001008540000800120000850010002400010a00200048000a10004100100014200082002000a800010400400150000208008002a00004100100054000082002000a802010002000010a402000400002148040008000142100820000002842010400000150040208000002a00804100000054010082000000a80201040000015
def BB54_Z : BitVec (27 * 54) := 0x2a00000082010054000001040200a800000208040150000004100802a00000082010850000001040210a00004000804a100000800100942000010002010054001001040000a800200208000150004004100002a00080082000054001001040010a000200208002140004800100142000090002002840001200040000a840200200000150804004000002a10080080000054201001000000a8402002000021408040040000428100900000028402012000000508040240
def BB54_X_ker : BitVec (31 * 54) := 0x20000019e8a47940000046f3d800800000968a00010000067f3d144200001000de140400002002d028080001948fe5401000047b001ec02000094000500040006523d1e40080011ecde000010002502d0000020019e8fe5100040046f00050000800968000a00010067f29150000201000f67b00004020028140000081948a45100001047b3d850000020940a00a00000467a3d1500000091bcde7b00000125a2d1400000039fcfe7900000016d0000000000036c0000000000000b6800000000001b600000000000005b400000000000db
def BB54_Z_ker : BitVec (31 * 54) := 0x20001008cc288640004023d16d008001008e82a8710004021d049002001008a80e07040040215000000801008b84f03010040217082080201008bc5f4200404003b0e710008100008240200104003a0af14002100098650200044002802d140009000bc7542000140008009040003000fc71c000002023b1df8c000040808041200000823a1d7a80000108984d16000002228145a00000048bc5f57000000a08041200000018fc7fc7000000124004900000002480092000000049001240000000024924000000000492480000000009249

set_option sat.solver "./cnf_loggers/BB54_z.bat" in
lemma BB54_dist_z_cnf : lt_dist_sat BB54_X BB54_Z_ker 5 6 := by
  have hclog : Nat.clog 2 54 = 6 := by norm_num
  have hloc : ∀ (locs : BitVec (5 * 6)) (errs : BitVec 54),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB54_X, BB54_Z_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)

set_option sat.solver "./cnf_loggers/BB54_x.bat" in
lemma BB54_dist_x_cnf : lt_dist_sat BB54_Z BB54_X_ker 5 6 := by
  have hclog : Nat.clog 2 54 = 6 := by norm_num
  have hloc : ∀ (locs : BitVec (5 * 6)) (errs : BitVec 54),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB54_Z, BB54_X_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)
