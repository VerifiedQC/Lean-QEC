import LeanQEC.Stabilizer.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

set_option maxRecDepth 9999999

def golay_mat : BitVec (11 * 23) :=
  0x40100401004010040100401004008eb27ea5ee3366d9b661ed7b5ed18ee3a

def golay_ker : BitVec (12 * 23) :=
  0x800400200100080040020010008004002001f927c9c7663bc8f9d5b785bc2de16ff25

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma steane_dist : lt_dist_sat golay_mat golay_ker 6 5
  := by
  simp (maxSteps := 9999999) only [lt_dist_sat, loc_constraints, loc_constraints_aux,
    loc_constraints_ith, Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    eq_iff_iff, Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, row_parity_constraint, row_parity_constraint_aux, Nat.reduceMul,
    Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true, mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add, stabilizer_constraints, stabilizer_constraints_aux, row_stabilizer_constraint,
    row_stabilizer_constraint_aux, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_or, Bool.or_eq_true, not_and, not_or, and_imp,
    loc_constraints_ith_jth, loc_constraints_ith_jth_aux, BitVec.extractLsb', Nat.add_one_sub_one, Nat.reduceMul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    Nat.shiftRight_zero, BitVec.ofNat_toNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false,
    Nat.reduceLT, getElem!_pos, Bool.and_true, bne_self_eq_false, Bool.bne_false, Bool.false_bne,
    bne_eq_false_iff_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq,
    and_imp, golay_mat, golay_ker]
  bv_check "Golay.lean-steane_dist-31-2.lrat"
