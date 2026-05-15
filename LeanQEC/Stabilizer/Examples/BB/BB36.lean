import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.BitVecSATToDist
set_option maxRecDepth 9999999
def BB36_A :=
  let l := 6
  let m := 3
  BB3_matrix l m (true, 0) (false, 1) (false, 2)
def BB36_B :=
  let l := 6
  let m := 3
  BB3_matrix l m (true, 0) (true, 1) (false, 1)
def BB36_X_mat := BB36_A.hstack_fin BB36_B
def BB36_Z_mat := BB36_B.transpose.hstack_fin BB36_A.transpose
def BB36_X : BitVec (18 * 36) := 0xa00138000c000b80006000780009400070005800070002c0007000128000e000b0000e00058000e000250001c00160001c000b0001c0004a00038002c000380016000380009400070005800070002c0007
def BB36_Z : BitVec (18 * 36) := 0xe00034000e0001a000e000290001c00068001c00034001c0005200038000d00038000680038000a400070001a00070000d0007000148000e00034000e0001a000e000290001e00060001d00030001c8005
def BB36_X_ker : BitVec (20 * 36) := 0x88b44924145a2c12092d16890481c0000200038000040007000008000e000010001c8000000028000000018000000005000000003000000000a000000006000000001400000000c0000000028000000018000000005000000003
def BB36_Z_ker : BitVec (20 * 36) := 0x800007000400007000200007000100000e00080000e00040000e000200001c00100001c00080001c000400003800200003800100003800080000700040000700020000700010bb9d00008bb9d00004bb9d00002e77300001dcee
def indrowsx : Fin 16 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
lemma StrictMono_indrowsx : StrictMono indrowsx := by decide
def indrowsz : Fin 16 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
lemma StrictMono_indrowsz : StrictMono indrowsz := by decide
def BB36_X_submat : BitVec (16 * 36) := 0x6000780009400070005800070002c0007000128000e000b0000e00058000e000250001c00160001c000b0001c0004a00038002c000380016000380009400070005800070002c0007
lemma BB36_X_submat_correct : BB36_X_submat = flatten_matrix (BB36_X_mat.submatrix indrowsx id) := by decide
def BB36_Z_submat : BitVec (16 * 36) := 0xe000290001c00068001c00034001c0005200038000d00038000680038000a400070001a00070000d0007000148000e00034000e0001a000e000290001e00060001d00030001c8005
lemma BB36_Z_submat_correct : BB36_Z_submat = flatten_matrix (BB36_Z_mat.submatrix indrowsz id) := by decide
def BB36_X_ker_mat := BitVecMatrix BB36_X_ker
def BB36_Z_ker_mat := BitVecMatrix BB36_Z_ker
lemma BB36_X_ker_mat_correct : flatten_matrix BB36_X_ker_mat = BB36_X_ker := flatten_BitVecMatrix_id _
lemma BB36_Z_ker_mat_correct : flatten_matrix BB36_Z_ker_mat = BB36_Z_ker := flatten_BitVecMatrix_id _
set_option exponentiation.threshold 10000 in
lemma BB36_X_correct : BB36_X = flatten_matrix BB36_X_mat := by decide
set_option exponentiation.threshold 10000 in
lemma BB36_Z_correct : BB36_Z = flatten_matrix BB36_Z_mat := by decide
set_option maxHeartbeats 0 in
lemma BB36_X_rank : 16 ≤ BB36_X_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ indrowsx StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB36_X_submat_correct, BB36_X_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide
set_option maxHeartbeats 0 in
lemma BB36_Z_rank : 16 ≤ BB36_Z_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ indrowsz StrictMono_indrowsx
  rw [linear_indep_SAT_correct,  ←BB36_Z_submat_correct, BB36_Z_submat]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide
set_option maxHeartbeats 0 in
lemma BB36_X_ker_rank : 20 ≤ BB36_X_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB36_X_ker_mat_correct, BB36_X_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide
set_option maxHeartbeats 0 in
lemma BB36_Z_ker_rank : 20 ≤ BB36_Z_ker_mat.rank := by
  apply Matrix.rank_le_of_submatrix_independent _ id (strictMono_id)
  rw [Matrix.submatrix_id_id]
  rw [linear_indep_SAT_correct, BB36_Z_ker_mat_correct, BB36_Z_ker]
  simp only [linear_indep_SAT, nonzero, nonzero_aux, Nat.add_one_sub_one, Nat.lt_add_one,
      getElem!_pos, Nat.one_lt_ofNat, Nat.ofNat_pos, Bool.decide_or, Bool.decide_eq_true,
      Bool.or_eq_true, all_dot_zero, all_dot_zero_aux, dot_col_zero, dot_col_aux, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_true, one_mul,
      Nat.reduceLT, zero_mul, zero_add, Bool.and_false, Bool.false_bne, Bool.bne_false,
      bne_self_eq_false, add_zero, Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq]
  bv_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB36_XZ_orth : BB36_X_mat.mutually_orth_rows BB36_Z_mat := by
  rw [←mutually_orth_nat_correct, ←BB36_X_correct, ←BB36_Z_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB36_X_ker_orth : BB36_X_mat.mutually_orth_rows BB36_X_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB36_X_correct, BB36_X_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option exponentiation.threshold 10000
set_option maxHeartbeats 0
lemma BB36_Z_ker_orth : BB36_Z_mat.mutually_orth_rows BB36_Z_ker_mat := by
  rw [←mutually_orth_nat_correct, ←BB36_Z_correct, BB36_Z_ker_mat_correct]
  unfold bitvec_mutually_orth_nat
  native_decide
set_option maxHeartbeats 0 in
lemma BB36_dist_z : lt_dist_sat BB36_X BB36_Z_ker 3 6 := by
  rw [BB36_X, BB36_Z_ker]
  simp only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 999) (maxSteps := 9999999)
set_option maxHeartbeats 0 in
lemma BB36_dist_x : lt_dist_sat BB36_Z BB36_X_ker 3 6 := by
  rw [BB36_Z, BB36_X_ker]
  simp only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
  Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
  loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
  Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
  parity_constraints_aux, BitVec.dot_product, dot_product_aux, BitVec.row,
  Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
  rowspace_constraints_aux, not_and, and_imp]
  bv_decide (timeout := 999) (maxSteps := 9999999)
lemma BB36_X_ker_is_ker : BB36_X_ker_mat.is_ker_for BB36_X_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB36_X_rank BB36_X_ker_rank (by norm_num) BB36_X_ker_orth
lemma BB36_Z_ker_is_ker : BB36_Z_ker_mat.is_ker_for BB36_Z_mat := by
  apply Matrix.is_ker_for_of_rank_sum_mutually_orth _ _ BB36_Z_rank BB36_Z_ker_rank (by norm_num) BB36_Z_ker_orth
def BB36_css : CSS_pair 36 18 18 :=
  CSS_pair.of_matrices BB36_X_mat BB36_Z_mat BB36_XZ_orth
theorem BB36_dist_4 : 4 ≤ BB36_css.toBSM.distance (by norm_num) := by
  apply bitvec_sat_translation_correct BB36_css
      BB36_Z_ker_mat BB36_Z_ker_is_ker
      BB36_X_ker_mat BB36_X_ker_is_ker (by norm_num) _ _
  · rw [BB36_css, CSS_pair.of_matrices, ←BB36_X_correct, BB36_Z_ker_mat_correct]
    exact BB36_dist_z
  rw [BB36_css, CSS_pair.of_matrices, ←BB36_Z_correct, BB36_X_ker_mat_correct]
  exact BB36_dist_x
