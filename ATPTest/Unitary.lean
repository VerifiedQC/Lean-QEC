import QuantumInfo
import ClassicalInfo
import ClassicalInfo.Capacity
import ATPTest.Tensors

open Qubit

def I : 𝐔[Qubit] :=
  ⟨!![Complex.I, 0; 0, Complex.I], by constructor <;> matrix_expand⟩

open Matrix

def unitary_fin_equiv {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (h: a ≃ b) :(𝐔[a] ≃ 𝐔[b]) where
  toFun U := ⟨(reindex h h) U.1, by
    have h_mem := U.2
    rw [mem_unitaryGroup_iff] at h_mem ⊢
    simp
    rw [star_eq_conjTranspose, conjTranspose_submatrix]
    simp [←star_eq_conjTranspose, h_mem]
    ⟩
  invFun U := ⟨(Matrix.reindex h.symm h.symm) U.1, by
    have h_mem := U.2
    rw [mem_unitaryGroup_iff] at h_mem ⊢
    simp [star_eq_conjTranspose]
    simp [←star_eq_conjTranspose, h_mem]
    ⟩
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    simp

def fin_pow_succ_equiv {n : ℕ} : (Fin 2 × Fin (2^n)) ≃ Fin (2^(n+1)) := by
  rewrite [Nat.pow_succ']
  exact finProdFinEquiv

def qubit_tensor {n : ℕ} (m : Fin n → 𝐔[Qubit]) : 𝐔[Fin (2^n)] :=
match n with
| 0 => 1
| n0+1 => (unitary_fin_equiv fin_pow_succ_equiv).toFun ((m 0) ⊗ᵤ (qubit_tensor (λ (x : Fin n0) => m ⟨x.val + 1, by simp [x.isLt]⟩)))

def herm_of_qubit_tensor_herm {n : ℕ} (m : Fin n → 𝐔[Qubit]) (Hm : ∀ x, Matrix.IsHermitian (m x).1) :
  Matrix.IsHermitian (qubit_tensor m).1 := by
  induction n with
  | zero => simp [qubit_tensor]
  | succ n ih => simp only [qubit_tensor, unitary_fin_equiv, reindex_apply, Equiv.symm_symm,
    unitary_kron, Equiv.toFun_as_coe, Equiv.coe_fn_mk, isHermitian_submatrix_equiv]
                 refine is_herm_of_kron_herm (Hm 0) ?_
                 refine ih ?_ (fun x => ?_)
                 apply Hm

noncomputable def Pauli : Finset (𝐔[Qubit]):= {1, X, Y, Z}

lemma pauli_herm {p : Pauli} : IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl) <;> matrix_expand [X, Y, Z]

variable {n : ℕ} (m : Fin n → Pauli)

def pauli_tensor : 𝐔[Fin (2^n)] :=
  qubit_tensor (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]


def pauli_tensor_herm : HermitianMat (Fin (2^n)) ℂ :=
  ⟨(pauli_tensor m).1, pauli_tensor_hermitian m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)

--define negative and imaginary phase factors on unitary matrices

variable {k : Type*} [Fintype k] [DecidableEq k]

noncomputable def U_phase (U : 𝐔[k]) (z : ℂ) (hp: ‖z‖ = 1) : 𝐔[k] := ⟨z • U.val, by
  simp [unitary.mem_iff, smul_smul, mul_comm]
  rw [mul_comm, ←Complex.normSq_eq_conj_mul_self, Complex.coe_smul, Complex.normSq_eq_norm_sq, hp]
  simp
⟩

noncomputable def u_neg (U : 𝐔[k]) : 𝐔[k] := (U_phase U (-1) (by norm_num))

noncomputable def u_im (U : 𝐔[k]) : 𝐔[k] := (U_phase U Complex.I (by norm_num))
