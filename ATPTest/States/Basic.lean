import ATPTest.States.PState

def qub_zero : PState 1 := {
  vec := (Equiv.arrowCongr beq (Equiv.refl _)) ![(1 : ℂ), 0]
  normalized' := by
    have h: ∑ x, ‖![(1 : ℂ), 0] x‖ ^ 2 = 1 := by simp
    rw [Fintype.sum_equiv beq.symm]
    exact h
    simp
}

def qub_one : PState 1 := {
  vec := (Equiv.arrowCongr beq (Equiv.refl _)) ![(0 : ℂ), 1]
  normalized' := by
    have h: ∑ x, ‖![(0 : ℂ), 1] x‖ ^ 2 = 1 := by simp
    rw [Fintype.sum_equiv beq.symm]
    exact h
    simp
}

@[simp] lemma qub_zero_zero : qub_zero 0#1 = 1 := sorry

@[simp] lemma qub_zero_one : qub_zero 1#1 = 0 := sorry

@[simp] lemma qub_one_zero : qub_one 0#1 = 0 := sorry

@[simp] lemma qub_one_one : qub_one 1#1 = 1 := sorry



variable (ψ : PState 1)

lemma single_qub_normalized : ‖(ψ 0)‖^2+‖(ψ 1)‖^2 = 1 := by
  convert ψ.normalized
  simp [Complex.normSq_eq_norm_sq]



lemma zero_one_orth : qub_zero.orth qub_one := by
  unfold PState.orth PState.dot
  simp

lemma one_qub_decomp : ψ = qub_zero.sum qub_one (ψ.vec 0) (ψ.vec 1) (single_qub_normalized ψ) (zero_one_orth) := sorry

lemma prod_orth {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho₁ : ψ₁.orth φ₁) (ho₂ : ψ₂.orth φ₂)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂):= sorry
