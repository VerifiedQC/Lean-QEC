import QuantumInfo
import ClassicalInfo
import ClassicalInfo.Capacity


#check Code

#check Qubit

open Qubit

def I : 𝐔[Qubit] :=
  ⟨!![Complex.I, 0; 0, Complex.I], by constructor <;> matrix_expand⟩


@[simp]
theorem X_Y_flip: X * Y = I * Z := by {
  matrix_expand [I, Z, X, Y]
}



variable {k : Type*} [Fintype k] [DecidableEq k]

variable (f g : 𝐔[k])

open Matrix

variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α]

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

variable (A : 𝐔[α])

variable (B : 𝐔[β])


lemma X_conj : (↑X)ᴴ = (↑X : Matrix Qubit Qubit ℂ) := by
  matrix_expand [X]

lemma Y_conj : (↑Y)ᴴ = (↑Y : Matrix Qubit Qubit ℂ) := by
  matrix_expand [Y]

lemma Z_conj : (↑Z)ᴴ = (↑Z : Matrix Qubit Qubit ℂ) := by
  matrix_expand [Z]

@[simp]
lemma X_one_zero : X.val *ᵥ ![1, 0] = ![0, 1] := by
  unfold X
  funext i
  fin_cases i <;> simp

@[simp]
lemma X_zero_one : X.val *ᵥ ![0, 1] = ![1, 0] := by
  unfold X
  funext i
  fin_cases i <;> simp

def qub_zero : Ket Qubit := {
  vec := ![1, 0]
  normalized' := (by simp
  )
}

def qub_one : Ket Qubit := {
  vec := ![0, 1]
  normalized' := (by simp
  )
}

variable (d : Type*) [Fintype d]


-- proving this is surprisingly difficult and probably
-- requires v to live in EuclideanSpace


def unitary_norm_preserve (U : 𝐔[k]) (v: k → ℂ) :
  ∑ x, ‖(U.1.toLin' v) x‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  sorry


def Ket.uapply (psi : Ket k) (U : 𝐔[k]) : Ket k where
  vec := U.1.toLin' psi.vec
  normalized' := by
    rewrite [unitary_norm_preserve]
    exact psi.normalized'

example : qub_one.uapply X = qub_zero := by
  ext x
  unfold Ket.uapply qub_one qub_zero
  fin_cases x <;> simp


--A PVM is a POVM bundled with the assumption that its matrices are projectors.
structure PVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  POVM : POVM X d
  H_proj: ∀ x, (POVM.mats x).toMat * (POVM.mats x).toMat = (POVM.mats x).toMat

#check finProdFinEquiv

def unitary_fin_equiv {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (h: a ≃ b) :(𝐔[a] ≃ 𝐔[b]) where
  toFun U := ⟨(Matrix.reindex h h) U.1, by
    have h_mem := U.2
    rw [Matrix.mem_unitaryGroup_iff] at h_mem ⊢
    simp
    rw [star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
    simp [←star_eq_conjTranspose, h_mem]
    ⟩
  invFun U := ⟨(Matrix.reindex h.symm h.symm) U.1, by
    have h_mem := U.2
    rw [Matrix.mem_unitaryGroup_iff] at h_mem ⊢
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


def unitary_tensor {n : ℕ} (m : Fin n → 𝐔[Fin 2]) : 𝐔[Fin (2^n)] :=
match n with
| 0 => 1
| n0+1 => (unitary_fin_equiv fin_pow_succ_equiv).toFun ((m 0) ⊗ᵤ (unitary_tensor (λ (x : Fin n0) => m ⟨x.val + 1, by simp [x.isLt]⟩)))

noncomputable def Pauli : Finset (𝐔[Qubit]):= {I, X, Y, Z}

variable {n : ℕ} (m : Fin n → Pauli)

def pauli_tensor : 𝐔[Fin (2^n)] :=
  unitary_tensor (λ x => (m x))

lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor m).1 := sorry

def pauli_tensor_herm : HermitianMat (Fin (2^n)) ℂ :=
  ⟨(pauli_tensor m).1, pauli_tensor_hermitian m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1) := sorry

--@[simp]
lemma unitary_coe_mul (f g : 𝐔[k]) : (f : Matrix k k ℂ) * (g: Matrix k k ℂ) = ↑(f * g):= by
  rfl

@[simp]
theorem unitary_kron_one_one : (1 : 𝐔[α]) ⊗ᵤ (1 : 𝐔[β]) = (1 : 𝐔[α × β]) := by
  simp only [unitary_kron, OneMemClass.coe_one, zero_mul, implies_true, mul_zero, mul_one,
    kroneckerMap_one_one, Submonoid.mk_eq_one]

open scoped Matrix in

theorem tensor_kron_A_B: (A ⊗ᵤ B) * (A' ⊗ᵤ B') = ((A * A') ⊗ᵤ (B * B')) := by {
  apply Subtype.ext
  simp [unitary_kron, ←Matrix.mul_kronecker_mul]
}

lemma X_Z_anticomm : (X * Z) = - (Z * X) := by{
  simp [Z_X_anticomm]
}

lemma X_X_Z_Z_commute : (X ⊗ᵤ X) * (Z ⊗ᵤ Z) = (Z ⊗ᵤ Z) * (X ⊗ᵤ X) := by {
  simp only [tensor_kron_A_B, X_Z_anticomm]
  apply Subtype.ext
  ext i j
  simp [unitary_kron]
}

lemma X_X_Y_Y_commute : (X ⊗ᵤ X) * (Y ⊗ᵤ Y) = (Y ⊗ᵤ Y) * (X ⊗ᵤ X) := by {
  simp only [tensor_kron_A_B, X_Y_anticomm]
  apply Subtype.ext
  ext i j
  simp [unitary_kron]
}

-- TODO: define big tensor prod, prove commutation
-- for collections of even numbers of Pauli operators
