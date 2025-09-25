import QuantumInfo
import ClassicalInfo
import LeanCopilot
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

@[simp]
theorem unitary_kron_one_one : (1 : 𝐔[α]) ⊗ᵤ (1 : 𝐔[β]) = (1 : 𝐔[α × β]) := by
  simp only [unitary_kron, OneMemClass.coe_one, zero_mul, implies_true, mul_zero, mul_one,
    kroneckerMap_one_one, Submonoid.mk_eq_one]

open scoped Matrix in
theorem tensor_kron_f_g: (f ⊗ᵤ 1) * (1 ⊗ᵤ g) =  (f ⊗ᵤ g):= by {
  sorry
}
