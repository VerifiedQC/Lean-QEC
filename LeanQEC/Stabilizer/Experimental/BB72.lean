import Mathlib.Data.BitVec
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide

set_option maxRecDepth 9999999

def HX : BitVec (36 * 72) :=
  0x1208000000904000000482000008041000004020800002010400000048200000024100000012080000201040000100820000080410000001208000000904000000482000008041000004020800002010400000048200000024100000012080000201040000100820000080418000001204000000902000000481000008040800004020400002018200000044100000022080000011040000200820000100410000086000200003000100001800080000c0004000840002000c0000100001800080000c0004000060002000030001000210000800300000400006000200003000100001800080000c0004000840002000c0000180001800040000c0002000060001000030000800210000400300000200006000100003000080001800040000c0002000840001000c0000080001800040000c000200006000100003000080021000040030

def N : BitVec (42 * 72) :=
  0xd00afd97707000000241060000004820c000020104b0060880413c033d594260d048bf65dc301a2bc977060abc9e6640c157b34ec0b0516ed3b03c1993ff9a00d46ff7d2003119fcf080068bc9e74000d17b3cc800b45fefb2003d1ffffc8a00608c0619402bf615e18000000000100000000002000000000040000000000a0d16ec3b8143dc84d7508000000000100000000002000000000040000000000acdfefb600173804118008000000000100000000002000000000040000000000bf9e5488001a2bc9e7000abc9e74400157b3ce800080000000001000000000037602dd8000bb406ed000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000000000080000000001000000000020000000000400000000008000000000100000000002000000000040000000000800000000010000000000200000000004000000000080000000001

def loc_constraints_ith
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72)
  (i : ℕ) :=
  errs[i]! = (loc0 = i ∨ loc1 = i ∨ loc2 = i ∨ loc3 = i ∨ loc4 = i)

def loc_constraints_aux
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72)
  (c : ℕ) :=
  match c with
  | 0 => loc_constraints_ith loc0 loc1 loc2 loc3 loc4 errs 0
  | c' + 1 =>
    loc_constraints_ith loc0 loc1 loc2 loc3 loc4 errs c ∧
    loc_constraints_aux loc0 loc1 loc2 loc3 loc4 errs c'

def loc_constraints
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72) :=
  loc_constraints_aux loc0 loc1 loc2 loc3 loc4 errs 71

def row_parity_constraint_aux
  (errs : BitVec 72) (r : ℕ) (c : ℕ) :=
  let k := r + 36 * c
  match c with
  | 0 => errs[c]! && HX[k]!
  | c' + 1 => (errs[c]! && HX[k]!) ^^ row_parity_constraint_aux errs r c'

def row_parity_constraint (errs : BitVec 72) (r : ℕ) :=
  ¬(row_parity_constraint_aux errs r 71)

def parity_constraints_aux (errs : BitVec 72) (r : ℕ) :=
  match r with
  | 0 => row_parity_constraint errs 0
  | r' + 1 => row_parity_constraint errs r ∧ parity_constraints_aux errs r'

def parity_constraints (errs : BitVec 72) :=
  parity_constraints_aux errs 35

def row_stabilizer_constraint_aux
  (errs : BitVec 72) (r : ℕ) (c : ℕ) :=
  let k := r + 36 * c
  match c with
  | 0 => (errs[c]! && N[k]!)
  | c' + 1 => (errs[c]! && N[k]!) ^^ row_stabilizer_constraint_aux errs r c'

def row_stabilizer_constraint (errs : BitVec 72) (r : ℕ) :=
  row_stabilizer_constraint_aux errs r 71

def stabilizer_constraints_aux
  (errs : BitVec 72) (r : ℕ) :=
  match r with
  | 0 => row_stabilizer_constraint errs 0
  | r' + 1 => row_stabilizer_constraint errs r' ∨
      stabilizer_constraints_aux errs r'

def stabilizer_constraints
  (errs : BitVec 72) :=
  stabilizer_constraints_aux errs 41

set_option maxHeartbeats 0 in
-- heavy unfolding
lemma bb72_test
  (loc0 loc1 loc2 loc3 loc4 : BitVec 7)
  (errs : BitVec 72) :
  ¬ (
    loc_constraints loc0 loc1 loc2 loc3 loc4 errs /\
    parity_constraints errs /\
    stabilizer_constraints errs)
  := by
  simp (maxSteps := 9999999) only [loc_constraints, loc_constraints_aux, loc_constraints_ith,
    Nat.lt_add_one, getElem!_pos, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, eq_iff_iff,
    Nat.reduceLT, Nat.cast_one, Nat.zero_lt_succ,
    Nat.cast_zero, parity_constraints, parity_constraints_aux, row_parity_constraint,
    row_parity_constraint_aux,
    Nat.reduceMul, HX, Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_true,
    mul_one, mul_zero, add_zero,
    bne_self_eq_false, Bool.bne_false, Bool.false_bne, bne_iff_ne, ne_eq, Decidable.not_not,
    zero_add,
    stabilizer_constraints, stabilizer_constraints_aux, row_stabilizer_constraint,
    row_stabilizer_constraint_aux, N,
    or_self, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.decide_or, Bool.or_eq_true,
    not_and, not_or, and_imp]
  bv_check (timeout := 99) "bb72.lrat"

#print axioms bb72_test
