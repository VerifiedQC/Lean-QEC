import LeanQEC.Stabilizer.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

set_option maxRecDepth 9999999

def steane_mat : BitVec (3 * 7) :=
  0x1ee711

def steane_ker : BitVec (4 * 7) :=
  0x8421ebd

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma steane_dist : lt_dist_sat steane_mat steane_ker 2 3
  := by
  simp (maxSteps := 9999999) only [lt_dist_sat, loc_constraints, loc_constraints_aux,
    loc_constraints_ith, Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    eq_iff_iff, Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, row_parity_constraint, row_parity_constraint_aux, Nat.reduceMul,
    Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true, mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add, rowspace_constraints, rowspace_constraints_aux, row_rowspace_constraint,
    row_rowspace_constraint_aux, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_or, Bool.or_eq_true, not_and, not_or, and_imp,
    loc_constraints_ith_jth, loc_constraints_ith_jth_aux, BitVec.extractLsb', Nat.add_one_sub_one, Nat.reduceMul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    Nat.shiftRight_zero, BitVec.ofNat_toNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false,
    Nat.reduceLT, getElem!_pos, Bool.and_true, bne_self_eq_false, Bool.bne_false, Bool.false_bne,
    bne_eq_false_iff_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq,
    and_imp, steane_mat, steane_ker]
  bv_check "Steane.lean-steane_dist-31-2.lrat"
