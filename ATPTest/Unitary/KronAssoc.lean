import ATPTest.Unitary.Basic
import ATPTest.States.Phase

-- ??????
-- don't ask...
lemma kron_assoc {n₁ n₂ n₃} (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) (U₃ : 𝐔ₙ[n₃]) :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ ≍ (U₁ ⊗ₙ (U₂ ⊗ₙ U₃)) := by
  apply heq_of_eq_cast
  swap
  · suffices: n₁ + (n₂ + n₃) = n₁ + n₂ + n₃
    · rw [this]
    group

  sorry
