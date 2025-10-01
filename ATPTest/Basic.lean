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
