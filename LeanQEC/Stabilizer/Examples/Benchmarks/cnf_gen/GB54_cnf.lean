import LeanQEC.ComputerAlgebra.BitVecSAT
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv

/-!
CNF generation for GB54 (both distance queries).

Cut down from `LeanQEC/Stabilizer/Examples/BB/GB54.lean` to just the two `lt_dist_sat` goals.
Each `sat.solver` wrapper copies the DIMACS file `bv_decide` writes into `bv_decide_queries/` and
exits without reporting a result, so the tactic fails *after* the CNF is written. That is the point:
these modules produce formulas, they do not prove anything, and they are expected to fail to build.

Two rewrites keep the prepared term small, and both are what make the larger codes tractable:
* `hloc` replaces `loc_constraints` by the one-hot `loc_constraints_fast`, turning the
  `n * k = 486` slot comparisons into `k = 9` shifts (`loc_constraints_iff_fast`, which needs
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

def GB54_X : BitVec (27 * 54) := 0x2160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100
def GB54_Z : BitVec (27 * 54) := 0x2160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a100000858000342800010a000068700002140000d0600004280001a2c00008100003458000102000068b00002040000d160000508000182c0000a100003858000142000050b000068400002160000d08000042c0001a100000858000342000010b000068400002160000d08000042c0001a1000
def GB54_X_ker : BitVec (28 * 54) := 0x8000000f6ae87d000000212a2f0200000042545e0400000084a8bc080000010951781000000212a2f0200000fbdaba00400001f7b57400800003ef6ae801000007ded5d0020000f04254400400021f7b570008000bc10950001000178212a00020002f042540004003a1f7b500008008bc10940001002e87ded0000200a2f04240000402ba1f7b0000080a8bc10800001015178210000020d5d0fbc0000042545e0800000084a8bc100000010951782000000212a2f040000007ffffff
def GB54_Z_ker : BitVec (28 * 54) := 0x8000000f6ae87d000000212a2f0200000042545e0400000084a8bc080000010951781000000212a2f0200000fbdaba00400001f7b57400800003ef6ae801000007ded5d0020000f04254400400021f7b570008000bc10950001000178212a00020002f042540004003a1f7b500008008bc10940001002e87ded0000200a2f04240000402ba1f7b0000080a8bc10800001015178210000020d5d0fbc0000042545e0800000084a8bc100000010951782000000212a2f040000007ffffff

set_option sat.solver "./cnf_loggers/GB54_z.bat" in
lemma GB54_dist_z_cnf : lt_dist_sat GB54_X GB54_Z_ker 9 6 := by
  have hclog : Nat.clog 2 54 = 6 := by norm_num
  have hloc : ∀ (locs : BitVec (9 * 6)) (errs : BitVec 54),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [GB54_X, GB54_Z_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)

set_option sat.solver "./cnf_loggers/GB54_x.bat" in
lemma GB54_dist_x_cnf : lt_dist_sat GB54_Z GB54_X_ker 9 6 := by
  have hclog : Nat.clog 2 54 = 6 := by norm_num
  have hloc : ∀ (locs : BitVec (9 * 6)) (errs : BitVec 54),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [GB54_Z, GB54_X_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)
