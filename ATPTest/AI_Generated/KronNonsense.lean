import Mathlib

lemma kron_injective_up_to_scalar {T₁ U₁ T₂ U₂}
  [Fintype T₁] [Fintype T₂]
  [Fintype U₁] [Fintype U₂]
  {M₁ M₁' : Matrix T₁ U₁ ℂ}
  {M₂ M₂' : Matrix T₂ U₂ ℂ}
  (eq_krons: M₁.kronecker M₂ = M₁'.kronecker M₂')
  (ne0_M1: M₁ ≠ 0) (ne0_M2: M₂ ≠ 0) :
  exists (z : ℂˣ), (M₁ = z • M₁' /\ M₂ = z⁻¹ • M₂') := by sorry
