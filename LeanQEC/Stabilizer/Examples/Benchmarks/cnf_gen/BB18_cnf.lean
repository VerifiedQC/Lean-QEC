import LeanQEC.ComputerAlgebra.BitVecSAT
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv

/-!
CNF generation for BB18 (both distance queries).

Cut down from `LeanQEC/Stabilizer/Examples/BB/BB18.lean` to just the two `lt_dist_sat` goals.
Each `sat.solver` wrapper copies the DIMACS file `bv_decide` writes into `bv_decide_queries/` and
exits without reporting a result, so the tactic fails *after* the CNF is written. That is the point:
these modules produce formulas, they do not prove anything, and they are expected to fail to build.

Two rewrites keep the prepared term small, and both are what make the larger codes tractable:
* `hloc` replaces `loc_constraints` by the one-hot `loc_constraints_fast`, turning the
  `n * k = 54` slot comparisons into `k = 3` shifts (`loc_constraints_iff_fast`, which needs
  `n <= 2 ^ nlog`, here `18 <= 32`).
* `hclog` evaluates `Nat.clog 2 18` so `simp` can unfold the `5` steps of `BitVec.xorFold`
  inside `BitVec.dot_product`; plain `simp` cannot evaluate `Nat.clog` itself.
-/

set_option maxRecDepth 9999999
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option exponentiation.threshold 1000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

def BB18_X : BitVec (9 * 18) := 0x341446860a90c11a4a034b0149620c25418588a0b
def BB18_Z : BitVec (9 * 18) := 0x341446860a90c11a4a034b0149620c25418588a0b
def BB18_X_ker : BitVec (11 * 18) := 0x2003d400f8803b100d0201a040a40875011b40245005cc00ee
def BB18_Z_ker : BitVec (11 * 18) := 0x2003d400f8803b100d0201a040a40875011b40245005cc00ee

set_option sat.solver "./cnf_loggers/BB18_z.bat" in
lemma BB18_dist_z_cnf : lt_dist_sat BB18_X BB18_Z_ker 3 5 := by
  have hclog : Nat.clog 2 18 = 5 := by norm_num
  have hloc : ∀ (locs : BitVec (3 * 5)) (errs : BitVec 18),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB18_X, BB18_Z_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)

set_option sat.solver "./cnf_loggers/BB18_x.bat" in
lemma BB18_dist_x_cnf : lt_dist_sat BB18_Z BB18_X_ker 3 5 := by
  have hclog : Nat.clog 2 18 = 5 := by norm_num
  have hloc : ∀ (locs : BitVec (3 * 5)) (errs : BitVec 18),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB18_Z, BB18_X_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)
