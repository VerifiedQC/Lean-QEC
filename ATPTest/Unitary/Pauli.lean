import ATPTest.Unitary.Basic

open Qubit

def pX := (unitary_fin_equiv beq) X
def pY := (unitary_fin_equiv beq) Y
def pZ := (unitary_fin_equiv beq) Z

noncomputable def Pauli : Finset (𝐔ₙ[1]):= {1, pX, pY, pZ}

lemma pauli_herm {p : Pauli} : Matrix.IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl) <;> matrix_expand [X, Y, Z]

variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

def pauli_tensor : 𝐔ₙ[n] :=
  unitary_n_nkron hn (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor hn m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]
