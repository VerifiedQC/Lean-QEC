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

-- Permute qubits
-- TODO Some kind of tricky re-indexing...
#check reindex_unitary

def permute_qubits {n} (π : Fin n -> Fin n)
  (is_bij: Function.Bijective π)
  (U : 𝐔ₙ[n]) : 𝐔ₙ[n] := sorry

def swapᵢⱼ {n} (i j : Fin n) (x : Fin n) : Fin n :=
  if x == i then j else
  if x == j then i else
  x

def is_bijective_swap {n} (i j : Fin n) :
  Function.Bijective (swapᵢⱼ i j) := by
  sorry

def swap_unitary_qubits {n} (i j : Fin n) :=
  permute_qubits (swapᵢⱼ i j) (is_bijective_swap i j)

def CNOTᵢⱼ{n : Nat} (i j : Fin n) : 𝐔ₙ[n] := sorry

lemma pad_aux {n : Nat} (i : Nat) (len_i : i ≤ n) :
  i + (n - i) = n := by sorry

def pad_unitary {n} {i : Nat} (len_i : i ≤ n) (U : 𝐔ₙ[i]) : 𝐔ₙ[n] :=
  cast (by rw [pad_aux]; assumption) (U ⊗ₙ (1 : 𝐔ₙ[n - i]))

def Uᵢ {n : Nat} [NeZero n] (U : 𝐔ₙ[1]) (i : Fin n) : 𝐔ₙ[n] :=
  (swap_unitary_qubits 0 i (pad_unitary (by simp [NeZero.one_le]) U))

def Xᵢ {n : Nat} [NeZero n] (i : Fin n) : 𝐔ₙ[n] :=
  Uᵢ pX i

def Hᵢ {n : Nat} [NeZero n] (i : Fin n) : 𝐔ₙ[n] :=
  Uᵢ Hgate i

def Zᵢ {n : Nat} [NeZero n] (i : Fin n) : 𝐔ₙ[n] :=
  Uᵢ pZ i

def Pᵢ {n : Nat} [NeZero n] (i : Fin n) : 𝐔ₙ[n] :=
  Uᵢ Pgate i

/- Measurements as observables -/

def meas_is_zero {n} [NeZero n] (i : Fin n) (k : PState n) :=
  Module.End.HasEigenvector (Zᵢ i).1.toLin' 1 k

def meas_is_one {n} [NeZero n] (i : Fin n) (k : PState n) :=
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
  else -- Pauli Y
    (Pᵢ i') * (Hᵢ i')

-- Doesn't let me use BigOperators
-- Matrix multiplications aren't commutative
def record_syndrome {n} (P : PauliGroup n) : 𝐔ₙ[n + 1] :=
  List.prod (List.ofFn (fun i => Crecᵢ i (PauliGroup.map P i)))

lemma record_syndrome_correct {n}
  (γ : ({phase_id, phase_n1} : Finset phase))
  (P : PauliGroup n)
  (v : PState n)
  (is_eigen : v.apply P = v.phase_mul γ) :
  (v.kron qub_zero).apply (record_syndrome P) =
  (v.kron (if γ == phase_id then qub_zero else qub_one))
  := by
  sorry

def record_all_syndromes {n s}
  [NeZero s]
  (stabilizer_generators : Fin s -> PauliGroup n) : 𝐔ₙ[n + s] :=
  let Cᵢ i : 𝐔ₙ[n + s] := pad_unitary (by simp[NeZero.one_le]) (record_syndrome (stabilizer_generators i))
  let Cᵢ' (i : Fin s) : 𝐔ₙ[n + s] :=
    let n' := Fin.ofNat (n + s) n
    let j := Fin.ofNat (n + s) (n + i)
    swap_unitary_qubits n' j (Cᵢ i)
  List.prod (List.ofFn (fun i => Cᵢ' i))

def qub_zero_n {n} : PState n := pstate_n_kron (fun _ => qub_zero)

lemma record_all_syndromes_correct {n s}
  (ne0_s: NeZero s)
  (γ : Fin s -> ({phase_id, phase_n1} : Finset phase))
  (P : Fin s -> PauliGroup n)
  (v : PState n)
  (is_eigen : forall s, v.apply (P s) = v.phase_mul (γ s)) :
  (v.kron qub_zero_n).apply (record_all_syndromes P) =
  v.kron (pstate_n_kron (fun i =>
    if γ i == phase_id then qub_zero else qub_one)) := by
  sorry
