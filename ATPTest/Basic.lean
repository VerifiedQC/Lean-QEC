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

@[simp]
lemma X_conj : (↑X)ᴴ = (↑X : Matrix Qubit Qubit ℂ) := by
  matrix_expand [X]

@[simp] lemma Y_conj : (↑Y)ᴴ = (↑Y : Matrix Qubit Qubit ℂ) := by
  matrix_expand [Y]

@[simp] lemma Z_conj : (↑Z)ᴴ = (↑Z : Matrix Qubit Qubit ℂ) := by
  matrix_expand [Z]

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

-- Define multi-qubit pauli channels to model errors

-- First define single-qubit bit-flip channel

noncomputable def kraus_bit_flip (p : ℝ) (i : Qubit): Matrix Qubit Qubit ℂ :=
  match i with
  | 0 => √(1 - p) • (1 : Matrix Qubit Qubit ℂ)
  | 1 => √p • X

@[simp] lemma kraus_bit_flip_0 : kraus_bit_flip p 0 = √(1 - p) • 1 := by
  rfl

@[simp] lemma kraus_bit_flip_1 : kraus_bit_flip p 1 = √p • X := by
  rfl

noncomputable def bit_flip_channel (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) : CPTPMap Qubit Qubit ℂ where
  toLinearMap := MatrixMap.of_kraus (kraus_bit_flip p) (kraus_bit_flip p)
  cp := MatrixMap.IsCompletelyPositive.of_kraus_isCompletelyPositive (kraus_bit_flip p)
  TP := by
    apply MatrixMap.IsTracePreserving.of_kraus_isTracePreserving (kraus_bit_flip p) (kraus_bit_flip p)
    simp
    rewrite [smul_smul, Real.mul_self_sqrt hp2, smul_smul, Real.mul_self_sqrt hp1]
    rewrite [unitary_coe_mul, X_sq, OneMemClass.coe_one]
    rewrite [←add_smul, sub_add_cancel, one_smul]
    rfl




def of_kraus_prob_unitary {n : ℕ} (pfun : Fin n → ℝ) (hpfun1 : ∀ i, 0 ≤ pfun i) (hpfun2 : ∀ i, 0 ≤ 1 - pfun i)
: CPTPMap Qubit Qubit ℂ := sorry
