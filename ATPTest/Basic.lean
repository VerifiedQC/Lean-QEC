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
