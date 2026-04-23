import LeanQEC.Stabilizer.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

set_option maxRecDepth 9999999

def HX : BitVec (36 * 72) :=
  0x1208000000904000000482000008041000004020800002010400000048200000024100000012080000201040000100820000080410000001208000000904000000482000008041000004020800002010400000048200000024100000012080000201040000100820000080418000001204000000902000000481000008040800004020400002018200000044100000022080000011040000200820000100410000086000200003000100001800080000c0004000840002000c0000100001800080000c0004000060002000030001000210000800300000400006000200003000100001800080000c0004000840002000c0000180001800040000c0002000060001000030000800210000400300000200006000100003000080001800040000c0002000840001000c0000080001800040000c000200006000100003000080021000040030

def Z_ker : BitVec (42 * 72) :=
  0xd00afd97707000000241060000004820c000020104b0060880413c033d594260d048bf65dc301a2bc977060abc9e6640c157b34ec0b0516ed3b03c1993ff9a00d46ff7d2003119fcf080068bc9e74000d17b3cc800b45fefb2003d1ffffc8a00608c0619402bf615e18000000000100000000002000000000040000000000a0d16ec3b8143dc84d7508000000000100000000002000000000040000000000acdfefb600173804118008000000000100000000002000000000040000000000bf9e5488001a2bc9e7000abc9e74400157b3ce800080000000001000000000037602dd8000bb406ed000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000000000080000000001

def HZ : BitVec (36 * 72) :=
  0xc0020000840010000c0000800060000400030000200018000100000300080002100040003000020001800010000c0000800060000400000c0020000840010000c0000800060000400030000200018000180000300040002100020003000010001800008000c0000400060000200000c0010000840008000c0000400060000200030000100018000080000300040002100020003000010001800008000c000040006100000820080000410040000208800000104400000082200000041804000020402000010201000008120000004090000002048000001820100000410080000208040000104800000082400000041200000020804000010402000008201000004120000002090000001048000000820100000410080000208040000104800000082400000041200000020804000010402000008201000004120000002090000001048

def X_ker : BitVec (42 * 72) :=
  0x800000000010000000000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000b7602dd0001bb406ec000000000080000000001000173cdea80022e793d5000e793d45800112a79fd000000000020000000000400000000008000000000100188201ce8006df7fb3500000000002000000000040000000000800000000010aeb213bc281dc3768b05000000000020000000000400000000008000000000187a86fd4029860310600513ffff8bc004df7fa2d00133cde8b0002e793d160010f3f988c004beff62b0059ffc9983c0dcb768a0d0372cdea830266793d5060ee93d4580c3ba6fd120b06429abcc03c820110600d2080400003041200000060824000000e0ee9bf500b

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma bb72_test_z : all_dist_constraints HX Z_ker 5 7
  := by
  simp (maxSteps := 9999999) only [all_dist_constraints, loc_constraints, loc_constraints_aux,
    loc_constraints_ith, Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    eq_iff_iff, Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, row_parity_constraint, row_parity_constraint_aux, Nat.reduceMul, HX,
    Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true, mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add, stabilizer_constraints, stabilizer_constraints_aux, row_stabilizer_constraint,
    row_stabilizer_constraint_aux, Z_ker, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_or, Bool.or_eq_true, not_and, not_or, and_imp,
    loc_constraints_ith_jth, loc_constraints_ith_jth_aux, BitVec.extractLsb', Nat.add_one_sub_one, Nat.reduceMul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    Nat.shiftRight_zero, BitVec.ofNat_toNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false,
    Nat.reduceLT, getElem!_pos, Bool.and_true, bne_self_eq_false, Bool.bne_false, Bool.false_bne,
    bne_eq_false_iff_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq,
    and_imp]
  bv_check (timeout := 999)
    --bv_check (timeout := 99) "bb72.lrat"
    "BB72.lean-bb72_test-35-2.lrat"
  --bv_check (timeout := 99) "bb72.lrat"

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma bb72_test_x : all_dist_constraints HZ X_ker 5 7
  := by
  simp (maxSteps := 9999999) only [all_dist_constraints, loc_constraints, loc_constraints_aux,
    loc_constraints_ith, Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    eq_iff_iff, Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, row_parity_constraint, row_parity_constraint_aux, Nat.reduceMul, HZ,
    Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true, mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add, stabilizer_constraints, stabilizer_constraints_aux, row_stabilizer_constraint,
    row_stabilizer_constraint_aux, X_ker, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_or, Bool.or_eq_true, not_and, not_or, and_imp,
    loc_constraints_ith_jth, loc_constraints_ith_jth_aux, BitVec.extractLsb', Nat.add_one_sub_one, Nat.reduceMul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat,
    Nat.shiftRight_zero, BitVec.ofNat_toNat, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false,
    Nat.reduceLT, getElem!_pos, Bool.and_true, bne_self_eq_false, Bool.bne_false, Bool.false_bne,
    bne_eq_false_iff_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq,
    and_imp]
  bv_check (timeout := 999)"BB72.lean-bb72_test_x-60-2.lrat"



#print axioms bb72_test_z
