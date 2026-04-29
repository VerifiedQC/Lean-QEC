import LeanQEC.ComputerAlgebra.BitVecSAT
import Lean.Elab.Tactic.BVDecide
import Std.Tactic.BVDecide
import LeanQEC.ComputerAlgebra.BitVecCorrectness

set_option maxRecDepth 9999999

def steane_mat : BitVec (3 * 7) :=
  1234583#21

def steane_ker : BitVec (4 * 7) :=
  0x8421ebd

def steane_mat' : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 1, 1;
    0, 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 1, 1, 1]

def steane_ker' : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
 !![1, 1, 0, 1, 0, 0, 0;
 0, 1, 1, 0, 1, 0, 0;
 1, 0, 1, 0, 0, 1, 0;
 1, 1, 1, 0, 0, 0, 1;]


#eval flatten_matrix steane_ker'
#eval flatten_matrix steane_mat'
def T : Matrix (Fin 1) (Fin 7) (ZMod 2) := !![1, 0, 0, 1, 0, 1, 1;]
#eval! flatten_matrix T -- evaluates to 105: should be 75
#eval T.toBitVecs 0
def v : Fin 7 → Fin 2 := ![1, 0, 0, 1, 0, 1, 1]
#eval! vec_to_BitVec v

--#eval! (flatten_matrix T)[1]

#eval flatten_matrix steane_mat'

def steane_ker'' : BitVec (4 * 7) := 149506827#28

def steane_mat'' : BitVec (3 * 7) := 1912169#21

def errs : BitVec 7 := 9#7
def locs : BitVec (2 * 3) := 3#6

#eval! BitVec_to_vec errs

#eval BitVec_to_vec (BitVec.extractLsb' 7 7 steane_mat'')

#eval row_inner_product steane_mat'' errs 1
#eval! BitVec_to_vec locs






set_option maxHeartbeats 0 in
-- heavy unfolding
lemma steane_dist : lt_dist_sat steane_mat'' steane_ker'' 2 3
  := by
  simp only [lt_dist_sat, Nat.reduceMul, loc_constraints, loc_constraints_aux, loc_constraints_ith,
    Nat.add_one_sub_one, Nat.lt_add_one, getElem!_pos, loc_constraints_ith_jth_aux,
    loc_constraints_ith_jth, one_mul, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, zero_mul, eq_iff_iff,
    Nat.reduceLT, Nat.one_lt_ofNat, Nat.cast_one, Nat.ofNat_pos, Nat.cast_zero, parity_constraints,
    parity_constraints_aux, row_inner_product, row_inner_product_aux, steane_mat'',
    BitVec.reduceGetElem, Bool.and_true, add_zero, Bool.not_eq_eq_eq_not, Bool.not_true,
    bne_eq_false_iff_eq, decide_eq_true_eq, rowspace_constraints,
    rowspace_constraints_aux, steane_ker'', Bool.and_false, bne_self_eq_false, Bool.false_eq_true,
    Bool.false_bne, false_or, Bool.decide_eq_true, or_self, not_and, Bool.not_eq_true, and_imp]
  bv_decide (timeout := 999)
