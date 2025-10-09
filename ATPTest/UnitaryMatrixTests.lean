import ATPTest.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

-- Test Cases for Unitary Matrices

open Qubit
open Matrix


section BasicUnitaryTests


-- Conjugate transpose of unitary matrix is unitary
example (U : 𝐔[Qubit]) :
  (U : Matrix Qubit Qubit ℂ)ᴴ ∈ unitaryGroup Qubit ℂ := by
  rw [←Matrix.star_eq_conjTranspose]
  exact unitary.star_mem U.2

end BasicUnitaryTests

section PauliMatrixTests


-- Pauli matrices are self-adjoint
example : (X : Matrix Qubit Qubit ℂ)ᴴ = X := by
  exact X_conj

example : (Y : Matrix Qubit Qubit ℂ)ᴴ = Y := by
  exact Y_conj

example : (Z : Matrix Qubit Qubit ℂ)ᴴ = Z := by
  exact Z_conj


-- Test case 10: Pauli matrix multiplication properties
example : X * Y = I * Z := by
  exact X_Y_flip

example : X * Z = -(Z * X) := by
  exact X_Z_anticomm



-- Commutation properties of tensor products of Pauli matrices
example : (X ⊗ᵤ X) * (Z ⊗ᵤ Z) = (Z ⊗ᵤ Z) * (X ⊗ᵤ X) := by
  exact X_X_Z_Z_commute

example : (X ⊗ᵤ X) * (Y ⊗ᵤ Y) = (Y ⊗ᵤ Y) * (X ⊗ᵤ X) := by
  exact X_X_Y_Y_commute
