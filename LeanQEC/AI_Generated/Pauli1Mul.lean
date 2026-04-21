/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: acb3644d-807e-441c-b252-3cbc4592134a

The following was proved by Aristotle:

- lemma mul_Pauli1_correct (P Q : Pauli) :
  let PQ
-/

import LeanQEC.Unitary.Basic
import LeanQEC.States.Phase
import LeanQEC.Unitary.Paulis.Pauli1
import LeanQEC.Unitary.Paulis.PauliFolding

set_option maxHeartbeats 0

noncomputable section

@[simp]
def phase_i : phase where
  z := Complex.I
  z_norm := by simp

@[simp]
def phase_ni : phase where
  z := -Complex.I
  z_norm := by simp

def pgphase_i : pgroup_phases := ⟨phase_i, by simp [pgroup_phases]⟩

def pgphase_ni : pgroup_phases := ⟨phase_ni, by simp [pgroup_phases]⟩

-- this is obviously terrible
def mul_Pauli1 (P : Pauli) (Q : Pauli) : pgroup_phases × Pauli :=
  if P = Pauli_I then
    (1, Q)
  else if P = Pauli_X then
    if Q = Pauli_I then
      (1, Pauli_X)
    else if Q = Pauli_X then
      (1, Pauli_I)
    else if Q = Pauli_Y then
      (pgphase_i, Pauli_Z)
    else -- Q = Z
      (pgphase_ni, Pauli_Y)
  else if P = Pauli_Y then
    if Q = Pauli_I then
      (1, Pauli_Y)
    else if Q = Pauli_X then
      (pgphase_ni, Pauli_Z)
    else if Q = Pauli_Y then
      (1, Pauli_I)
    else -- Q = Z
      (pgphase_i, Pauli_X)
  else -- P = Z
    if Q = Pauli_I then
      (1, Pauli_Z)
    else if Q = Pauli_X then
      (pgphase_i, Pauli_Y)
    else if Q = Pauli_Y then
      (pgphase_ni, Pauli_X)
    else -- Q = Z
      (1, Pauli_I)

def getmat (P : Pauli) : 𝐔ₙ[1] := P

noncomputable section AristotleLemmas

open Qubit

lemma pX_sq : pX * pX = 1 := by
  unfold pX;
  unfold unitary_fin_equiv;
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Qubit.X ];
  · rfl;
  · rfl;
  · rfl;
  · rfl
lemma pY_sq : pY * pY = 1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> simp ( config := { decide := Bool.true } ) [ pY ];
  · simp ( config := { decide := Bool.true } ) [ unitary_fin_equiv, Qubit.Y ];
    rfl;
  · unfold unitary_fin_equiv; norm_num;
    norm_num [ Matrix.mul_apply, Qubit.Y ];
    norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail, beq ];
  · unfold unitary_fin_equiv; aesop;
    norm_num [ Qubit.Y, Matrix.mul_apply ];
    norm_num [ beq ];
  · unfold Qubit.Y ;
    unfold unitary_fin_equiv; norm_num;
    rfl
lemma pZ_sq : pZ * pZ = 1 := by
  unfold pZ;
  -- By definition of matrix multiplication, we can compute each entry of the product.
  have hZ_sq : (Qubit.Z : Matrix (Fin 2) (Fin 2) ℂ) * (Qubit.Z : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Qubit.Z ];
  unfold unitary_fin_equiv; aesop;
lemma pX_mul_pY : pX * pY = U_phase pZ phase_i := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num;
  · simp +decide [ U_phase, pX, pY, pZ ];
    simp +decide [ unitary_fin_equiv ];
    unfold Qubit.X Qubit.Y Qubit.Z; norm_num;
    simp +decide [ beq ];
  · simp ( config := { decide := Bool.true } ) [ pX, pY, pZ, U_phase, Matrix.mul_apply ];
    unfold unitary_fin_equiv;
    unfold Qubit.X Qubit.Y Qubit.Z; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ; ring; norm_num;
    repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
    exact Or.inl rfl;
  · simp +decide [ pX, pY, pZ, U_phase ];
    unfold unitary_fin_equiv; simp +decide [ Qubit.X, Qubit.Y, Qubit.Z ];
    simp +decide [ beq ];
  · norm_num [ Matrix.mul_apply, pX, pY, pZ, U_phase ];
    norm_num [ unitary_fin_equiv ];
    simp +zetaDelta at *;
    erw [ show ( beq.symm 0#1 : Fin 2 ) = 0 from rfl, show ( beq.symm 1#1 : Fin 2 ) = 1 from rfl ] ; norm_num [ Qubit.X, Qubit.Y, Qubit.Z ]
lemma pY_mul_pZ : pY * pZ = U_phase pX phase_i := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Complex.ext_iff, Fin.sum_univ_succ ] <;> ring_nf <;> norm_num;
  · unfold U_phase pX pY pZ; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, Complex.ext_iff, Fin.sum_univ_succ ] ;
    unfold unitary_fin_equiv Qubit.X Qubit.Y Qubit.Z; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, Complex.ext_iff ] ;
    repeat erw [ Matrix.cons_val_zero ] ; norm_num;
  · unfold U_phase; norm_num [ Complex.ext_iff, Matrix.mul_apply ] ;
    erw [ show ( pY : Matrix ( BitVec 1 ) ( BitVec 1 ) ℂ ) = Matrix.of ( fun i j => if i = 0 ∧ j = 0 then 0 else if i = 0 ∧ j = 1 then -Complex.I else if i = 1 ∧ j = 0 then Complex.I else 0 ) from ?_, show ( pZ : Matrix ( BitVec 1 ) ( BitVec 1 ) ℂ ) = Matrix.of ( fun i j => if i = 0 ∧ j = 0 then 1 else if i = 0 ∧ j = 1 then 0 else if i = 1 ∧ j = 0 then 0 else -1 ) from ?_, show ( pX : Matrix ( BitVec 1 ) ( BitVec 1 ) ℂ ) = Matrix.of ( fun i j => if i = 0 ∧ j = 0 then 0 else if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then 1 else 0 ) from ?_ ] ; norm_num [ Complex.ext_iff, Fin.sum_univ_succ, Matrix.mul_apply ];
    · simp ( config := { decide := Bool.true } ) [ BitVec.equivFin ];
    · ext i j ; fin_cases i ; fin_cases j ; rfl;
      · rfl;
      · fin_cases j <;> rfl;
    · ext i j; fin_cases i; fin_cases j; rfl;
      · rfl;
      · fin_cases j <;> rfl;
    · exact Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl;
  · unfold U_phase pX pY pZ; norm_num [ Fin.sum_univ_succ ] ; ring_nf ; norm_num [ Complex.ext_iff, Fin.ext_iff, Fin.forall_fin_succ ] ;
    unfold unitary_fin_equiv; norm_num [ Qubit.X, Qubit.Y, Qubit.Z ] ;
    repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
    repeat erw [ Matrix.cons_val_zero ] ; norm_num;
    rfl;
  · unfold U_phase; norm_num [ Complex.ext_iff, Matrix.mul_apply ] ;
    unfold pX pY pZ; norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ] ; ring_nf ; norm_num;
    unfold unitary_fin_equiv; norm_num [ Qubit.X, Qubit.Y, Qubit.Z, Fin.sum_univ_succ ] ; ring_nf ; norm_num;
    repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
    exact Or.inr rfl
lemma pZ_mul_pX : pZ * pX = U_phase pY phase_i := by
  unfold pZ pX U_phase phase_i;
  unfold unitary_fin_equiv pY; aesop;
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Qubit.X, Qubit.Y, Qubit.Z ];
  · unfold unitary_fin_equiv; aesop;
    simp ( config := { decide := Bool.true } ) [ beq ];
  · simp +decide [ unitary_fin_equiv ] ; ring_nf;
    simp +decide [ beq ];
  · simp +decide [ unitary_fin_equiv ];
    simp +decide [ beq ];
  · unfold unitary_fin_equiv; norm_num [ Matrix.vecHead, Matrix.vecTail ] ;
    simp ( config := { decide := Bool.true } ) [ beq ]
lemma pY_mul_pX : pY * pX = U_phase pZ phase_ni := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, U_phase ] <;> norm_cast;
  · simp +decide [ pY, pX, pZ ];
    simp +decide [ unitary_fin_equiv ];
    simp +decide [ Qubit.Y, Qubit.X, Qubit.Z, beq ];
    simp +decide [ BitVec.equivFin ];
    exact Or.inl rfl;
  · unfold pX pY pZ; norm_num [ Complex.ext_iff ];
    unfold unitary_fin_equiv; norm_num [ Matrix.mul_apply, Qubit.X, Qubit.Y, Qubit.Z ] ;
    repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
    tauto;
  · simp ( config := { decide := Bool.true } ) [ pY, pX, pZ ];
    simp ( config := { decide := Bool.true } ) [ unitary_fin_equiv, Qubit.X, Qubit.Y, Qubit.Z ];
    simp ( config := { decide := Bool.true } ) [ beq ];
    simp ( config := { decide := Bool.true } ) [ BitVec.equivFin ];
    exact Or.inr rfl;
  · norm_num [ Matrix.mul_apply, pX, pY, pZ ];
    unfold unitary_fin_equiv; norm_num [ beq ] ;
    simp ( config := { decide := Bool.true } ) [ Qubit.X, Qubit.Y, Qubit.Z ]
lemma pZ_mul_pY : pZ * pY = U_phase pX phase_ni := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Phase.phase_star, pX, pY, pZ, U_phase ] <;> norm_cast;
  · unfold unitary_fin_equiv; norm_num [ Matrix.mul_apply ] ;
    simp +decide [ Qubit.Z, Qubit.Y, Qubit.X, beq ];
  · norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, Qubit.Z, Qubit.Y, Qubit.X, unitary_fin_equiv ];
    simp ( config := { decide := Bool.true } ) [ beq ];
  · unfold unitary_fin_equiv; norm_num [ Matrix.mul_apply, Qubit.X, Qubit.Y, Qubit.Z ] ;
    simp ( config := { decide := Bool.true } ) [ beq ];
  · unfold unitary_fin_equiv; simp +decide [ Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply ] ; ring;
    simp +decide [ beq ]
lemma pX_mul_pZ : pX * pZ = U_phase pY phase_ni := by
  unfold pX pZ pY;
  -- Let's calculate the product of the X and Z matrices and show it equals the Y matrix with the phase -i.
  have h_prod : (Qubit.X * Qubit.Z : Matrix (Fin 2) (Fin 2) ℂ) = (-Complex.I : ℂ) • Qubit.Y := by
    ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Qubit.X, Qubit.Y, Qubit.Z ];
  refine' Subtype.ext _;
  unfold unitary_fin_equiv U_phase; aesop;

end AristotleLemmas

--completely inscrutable aristotle proof
lemma mul_Pauli1_correct (P Q : Pauli) :
  let PQ := mul_Pauli1 P Q
  P.val * Q.val = U_phase PQ.2 PQ.1 := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl
  all_goals rcases Pauli_cases Q with rfl | rfl | rfl | rfl
  · simp [mul_Pauli1]
    change Pauli_X.val * Pauli_X.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa using pX_sq
  · simpa [mul_Pauli1] using pX_mul_pY
  · simpa [mul_Pauli1] using pX_mul_pZ
  · simp [mul_Pauli1]
    change Pauli_X.val * Pauli_I.val = U_phase Pauli_X.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simpa [mul_Pauli1] using pY_mul_pX
  · simp [mul_Pauli1]
    change Pauli_Y.val * Pauli_Y.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa using pY_sq
  · simpa [mul_Pauli1] using pY_mul_pZ
  · simp [mul_Pauli1]
    change Pauli_Y.val * Pauli_I.val = U_phase Pauli_Y.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simpa [mul_Pauli1] using pZ_mul_pX
  · simpa [mul_Pauli1] using pZ_mul_pY
  · simp [mul_Pauli1]
    change Pauli_Z.val * Pauli_Z.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa using pZ_sq
  · simp [mul_Pauli1]
    change Pauli_Z.val * Pauli_I.val = U_phase Pauli_Z.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_X.val = U_phase Pauli_X.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_Y.val = U_phase Pauli_Y.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_Z.val = U_phase Pauli_Z.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_I.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa [Pauli_I]
