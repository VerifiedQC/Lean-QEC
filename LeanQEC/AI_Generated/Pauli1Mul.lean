/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: acb3644d-807e-441c-b252-3cbc4592134a

The following was proved by Aristotle:

- lemma mul_Pauli1_correct (P Q : Pauli) :
  let PQ
-/

import Mathlib
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
  apply Subtype.ext
  simp only [pX, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, beq, BitVec.equivFin, Matrix.mul_apply] <;> rfl

lemma pY_sq : pY * pY = 1 := by
  apply Subtype.ext
  simp only [pY, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.Y, beq, BitVec.equivFin, Matrix.mul_apply] <;> rfl

lemma pZ_sq : pZ * pZ = 1 := by
  apply Subtype.ext
  simp only [pZ, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.Z, beq, BitVec.equivFin, Matrix.mul_apply] <;> rfl

lemma pX_mul_pY : pX * pY = U_phase pZ phase_i := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

lemma pY_mul_pZ : pY * pZ = U_phase pX phase_i := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

lemma pZ_mul_pX : pZ * pX = U_phase pY phase_i := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

lemma pY_mul_pX : pY * pX = U_phase pZ phase_ni := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

lemma pZ_mul_pY : pZ * pY = U_phase pX phase_ni := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

lemma pX_mul_pZ : pX * pZ = U_phase pY phase_ni := by
  have hb0 : beq.symm 0#1 = 0 := rfl
  have hb1 : beq.symm 1#1 = 1 := rfl
  apply Subtype.ext
  simp only [pX, pY, pZ, U_phase, unitary_fin_equiv]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Qubit.X, Qubit.Y, Qubit.Z, Matrix.mul_apply, hb0, hb1]

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
    simpa using! pX_sq
  · simpa [mul_Pauli1] using! pX_mul_pY
  · simpa [mul_Pauli1] using! pX_mul_pZ
  · simp [mul_Pauli1]
    change Pauli_X.val * Pauli_I.val = U_phase Pauli_X.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simpa [mul_Pauli1] using! pY_mul_pX
  · simp [mul_Pauli1]
    change Pauli_Y.val * Pauli_Y.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa using! pY_sq
  · simpa [mul_Pauli1] using! pY_mul_pZ
  · simp [mul_Pauli1]
    change Pauli_Y.val * Pauli_I.val = U_phase Pauli_Y.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simpa [mul_Pauli1] using! pZ_mul_pX
  · simpa [mul_Pauli1] using! pZ_mul_pY
  · simp [mul_Pauli1]
    change Pauli_Z.val * Pauli_Z.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simpa using! pZ_sq
  · simp [mul_Pauli1]
    change Pauli_Z.val * Pauli_I.val = U_phase Pauli_Z.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_X.val = U_phase Pauli_X.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_Y.val = U_phase Pauli_Y.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_Z.val = U_phase Pauli_Z.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]
  · simp [mul_Pauli1]
    change Pauli_I.val * Pauli_I.val = U_phase Pauli_I.val phase_id
    rw [U_phase_id]
    simp [Pauli_I]