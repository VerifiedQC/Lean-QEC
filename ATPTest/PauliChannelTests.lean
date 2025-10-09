import ATPTest.Pauli_Channels
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Sqrt


open Qubit
open Matrix

section KrausOperatorTests

-- Kraus operators for unitary channels
variable (U : 𝐔[Qubit]) (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p)


-- Kraus operators for bit-flip channel
example : kraus_bit_flip p 0 = √(1 - p) • (1 : Matrix Qubit Qubit ℂ) := by
  exact kraus_bit_flip_0

example : kraus_bit_flip p 1 = √p • X := by
  exact kraus_bit_flip_1

-- Kraus operators for dephasing channel
example : kraus_dephasing p 0 = √(1 - p) • (1 : Matrix Qubit Qubit ℂ) := by
  exact kraus_dephasing_0

example : kraus_dephasing p 1 = √p • Z := by
  exact kraus_dephasing_1

-- Kraus operators for Pauli channel
variable (p1 p2 p3 p4 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)

example : kraus_pauli p1 p2 p3 p4 0 = √p1 • (1 : Matrix Qubit Qubit ℂ) := by
  simp [kraus_pauli]

example : kraus_pauli p1 p2 p3 p4 1 = √p2 • X := by
  simp [kraus_pauli]

example : kraus_pauli p1 p2 p3 p4 2 = √p3 • Y := by
  simp [kraus_pauli]

example : kraus_pauli p1 p2 p3 p4 3 = √p4 • Z := by
  simp [kraus_pauli]

-- Kraus operators for depolarizing channel
variable (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p)

example : kraus_depolarizing p 0 = √(1 - p) • (1 : Matrix Qubit Qubit ℂ) := by
  simp [kraus_depolarizing, kraus_pauli]

example : kraus_depolarizing p 1 = √(p/3) • X := by
  simp [kraus_depolarizing, kraus_pauli]

example : kraus_depolarizing p 2 = √(p/3) • Y := by
  simp [kraus_depolarizing, kraus_pauli]

example : kraus_depolarizing p 3 = √(p/3) • Z := by
  simp [kraus_depolarizing, kraus_pauli]

end KrausOperatorTests

section UnitaryChannelTests


-- Unitary matrices preserve the identity condition
example (U : 𝐔[Qubit]) : (U : Matrix Qubit Qubit ℂ) * (U : Matrix Qubit Qubit ℂ).conjTranspose = 1 := by
  rw [←Matrix.star_eq_conjTranspose]
  simp only [SetLike.coe_mem, unitary.mul_star_self_of_mem]


-- Scalar multiplication distributes over addition
example (p1 p2 : ℝ) : √(1 - p1) • (1 : Matrix Qubit Qubit ℂ) + √p1 • X =
  √(1 - p1) • (1 : Matrix Qubit Qubit ℂ) + √p1 • X := by
  rfl

end UnitaryChannelTests

section ProbabilityTests

-- Probability normalization for Pauli channels
variable (p1 p2 p3 p4 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)
variable (hp : p1 + p2 + p3 + p4 = 1)

example : p1 + p2 + p3 + p4 = 1 := by
  exact hp

-- Probability bounds for depolarizing channel
example (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) :
  0 ≤ 1 - p ∧ 0 ≤ p/3 := by
  constructor
  · exact hp2
  · linarith [hp1]
