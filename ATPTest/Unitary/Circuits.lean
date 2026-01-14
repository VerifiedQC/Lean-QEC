import ATPTest.Unitary.Paulis.Pauli1
import ATPTest.States.Basic
import ATPTest.Unitary.Paulis.Pauli
import ATPTest.Braket

open Qubit
open Function

noncomputable section

def rawH : Matrix (Fin 2) (Fin 2) ℂ := (1 / Real.sqrt 2) • !![1, 1; 1, -1]

lemma hadamard_is_unitary : rawH ∈ 𝐔[Qubit] := by
  simp [rawH]
  constructor <;> matrix_expand

def H : 𝐔[Qubit] := ⟨rawH, hadamard_is_unitary⟩

def Hgate := (unitary_fin_equiv beq) H

def rawP := !![1, 0; 0, Complex.I]

lemma P_is_unitary : rawP ∈ 𝐔[Qubit] := by
  simp [rawP]
  constructor <;> matrix_expand

def P : 𝐔[Qubit] := ⟨rawP, P_is_unitary⟩

def Pgate := (unitary_fin_equiv beq) P

def raw_CNOT : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

lemma CNOT_is_unitary : raw_CNOT ∈ 𝐔[Fin 4] := by
  simp [raw_CNOT]
  sorry

def CNOT : 𝐔[Fin 4] := ⟨raw_CNOT, CNOT_is_unitary⟩

def beq2 : Fin 4 ≃ BitVec 2 := (@BitVec.equivFin 2).symm
def CNOTgate : 𝐔ₙ[2] := (unitary_fin_equiv beq2) CNOT

/- Gates on certain wires -/

-- TODO Some kind of tricky re-indexing...

def CNOTᵢⱼ{n : Nat} (i j : Fin n) : 𝐔ₙ[n] := sorry

def Xᵢ {n : Nat} (i : Fin n) : 𝐔ₙ[n] := sorry

def Hᵢ {n : Nat} (i : Fin n) : 𝐔ₙ[n] := sorry

def Zᵢ {n : Nat} (i : Fin n) : 𝐔ₙ[n] := sorry

def Pᵢ {n : Nat} (i : Fin n) : 𝐔ₙ[n] := sorry

/- Measurements as observables -/

def meas_is_zero {n} (i : Fin n) (k : PState n) :=
  Module.End.HasEigenvector (Zᵢ i).1.toLin' 1 k

def meas_is_one {n} (i : Fin n) (k : PState n) :=
  Module.End.HasEigenvector (Zᵢ i).1.toLin' (-1) k

/- Syndrome measurements -/

-- Eigenvalue recording

def Crecᵢ {n} (i : Fin n) (Qᵢ : Pauli) : 𝐔ₙ[n + 1] :=
  let i' := Fin.castSucc i
  if Qᵢ == Pauli_I then
    1
  else if Qᵢ == Pauli_X then
    (Hᵢ i') * (CNOTᵢⱼ i' (Fin.last n)) * (Hᵢ i')
  else if Qᵢ == Pauli_Z then
    (CNOTᵢⱼ i' (Fin.last n))
  else
    (Pᵢ i') * (Hᵢ i')

-- Doesn't let me use BigOperators
-- Unitary matrix multiplications aren't commutative in general
def Crec {n} (P : PauliGroup n) : 𝐔ₙ[n + 1] :=
  List.prod (List.ofFn (fun i => Crecᵢ i (PauliGroup.map P i)))

lemma Crec_correct {n} (γ : ({phase_id, phase_n1} : Finset phase))
  (P : PauliGroup n)
  (v : PState n)
  (is_eigen : v.apply P = v.phase_mul γ) :
  (v.kron qub_zero).apply (Crec P) =
  (v.kron (if γ == phase_id then qub_zero else qub_one))
  := by
  sorry
