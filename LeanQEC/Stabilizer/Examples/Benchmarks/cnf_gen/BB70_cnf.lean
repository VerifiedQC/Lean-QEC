import LeanQEC.ComputerAlgebra.BitVecSAT
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
import LeanQEC.timedbv

/-!
CNF generation for BB70 (both distance queries).

Cut down from `LeanQEC/Stabilizer/Examples/BB/BB70.lean` to just the two `lt_dist_sat` goals.
Each `sat.solver` wrapper copies the DIMACS file `bv_decide` writes into `bv_decide_queries/` and
exits without reporting a result, so the tactic fails *after* the CNF is written. That is the point:
these modules produce formulas, they do not prove anything, and they are expected to fail to build.

Two rewrites keep the prepared term small, and both are what make the larger codes tractable:
* `hloc` replaces `loc_constraints` by the one-hot `loc_constraints_fast`, turning the
  `n * k = 560` slot comparisons into `k = 8` shifts (`loc_constraints_iff_fast`, which needs
  `n <= 2 ^ nlog`, here `70 <= 128`).
* `hclog` evaluates `Nat.clog 2 70` so `simp` can unfold the `7` steps of `BitVec.xorFold`
  inside `BitVec.dot_product`; plain `simp` cannot evaluate `Nat.clog` itself.
-/

set_option maxRecDepth 9999999
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option exponentiation.threshold 1000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

def BB70_X : BitVec (35 * 70) := 0x200020080800842008000040101001084010000080240002108020000100480004210040000200900008420804000400010010841100000800020021082200001000800042104400002001000084208800004002000108410080008400200210022000010800400420044000021010000840088000042020001080110000084040002180201000108004004100440000210008008200880000420200010401100000840400020802200001080800041004020042100080002008800084200100004011000108404000008022000210808000010044000421010000020080400842001000040110001084002000080220002108080000100440004210100000200880008420200000401008010840020000802200021080040001004400042101000002008800084202000004011000108404
def BB70_Z : BitVec (35 * 70) := 0x808420002200800001010840004401000002021080008802000080042100011004000100084200402008000010108400044010000020210800088020000040421000110040001000842000220080002001084008040100000202108000880200000404210001100400000808420002200800020010840004401000040021080100802080004042000011004100008084000022008200010108000044010400400210000088020800800420002010061000080840000220042000101080000440084000202100000880108008004200001100210010008400040208420001000800004410840002001000008821080004002000011042100100004000022084200200008000804108400024010000080210800048020000100421000090040000200842002020080000401084004040100010
def BB70_X_ker : BitVec (38 * 70) := 0x800000002b61cc0a9900000000bc2b55014200000002d4358128840000000b06e7911608000000234802908c10000000944c33c3602000000283055caf004000000848861406008000002a28df92d00100000081490a102002000002a609b0774004000008026073a900080000254112520c00100000a0651671900020000214a9084ac00040000846c1ee32000080002a484e9ef800010000818828087000020002508c94c1000004000a1095852a000008002e40db5d340000100088690450100000200244b12c09c000004009d81136bb00000080290a10202800000100b8e811299000000202258d0982c0000004091a9681a200000008277301462400000010a40148463000000022539d342a000000004a16b1051300000000a16b5040b800000001a9ce6a6af000000001f0001f07c0000000003e007fff000000000007c1ff80000000000000f83ff
def BB70_Z_ker : BitVec (38 * 70) := 0x80000000022244185500000000044b0bee5200000000f0a9e8dc84000000021e5befb608000000044349df50100000002844b0bcf0200000005089617dc0400000035e1abee4008000000943f57208010000002c8891041002000000f508961780040000020a1eafd000080000046bc357dc0010000009287eae40002000001591122080004000005eae913d000080000f417dda0400010000208d8055000002000041250fd5c00004000082b2224400000800020bebddd80000100005e82fbb4000002000f41250f54000004002082b220500000080041056444800000100244185444000000200b0bee50880000004029e8dc9e1000000080541056440000000103482f2f77000000020448830a880000000409617dca1000000008153d1b93c000000013ca8d89370000000028693bea10000000007c00f83ff0000000000f83fff8000000000001f07fff

set_option sat.solver "./cnf_loggers/BB70_z.bat" in
lemma BB70_dist_z_cnf : lt_dist_sat BB70_X BB70_Z_ker 8 7 := by
  have hclog : Nat.clog 2 70 = 7 := by norm_num
  have hloc : ∀ (locs : BitVec (8 * 7)) (errs : BitVec 70),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB70_X, BB70_Z_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)

set_option sat.solver "./cnf_loggers/BB70_x.bat" in
lemma BB70_dist_x_cnf : lt_dist_sat BB70_Z BB70_X_ker 8 7 := by
  have hclog : Nat.clog 2 70 = 7 := by norm_num
  have hloc : ∀ (locs : BitVec (8 * 7)) (errs : BitVec 70),
      loc_constraints locs errs ↔ loc_constraints_fast locs errs :=
    fun locs errs => loc_constraints_iff_fast (by norm_num) (by norm_num) (by norm_num) locs errs
  rw [BB70_Z, BB70_X_ker]
  simp (maxSteps := 99999999) only [lt_dist_sat, hloc, loc_constraints_fast, loc_union_aux, loc_slot, Nat.reduceMul,
  symmetry_constraints, symmetry_constraints_aux, Nat.add_one_sub_one,
  one_mul, BitVec.ofNat_eq_ofNat, zero_mul, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, hclog, BitVec.xorFold, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decidet "cnf_gen_times.csv" (timeout := 99999) (maxSteps := 99999999)
