import ATPTest.States.PState

--what's a better way to do this...
def beq : Fin 2 ≃ BitVec 1 := (@BitVec.equivFin 1).symm

def qub_zero : PState 1 := {
  vec := (Equiv.arrowCongr beq (Equiv.refl _)) ![(1 : ℂ), 0]
  normalized := by
    have h: ∑ x, ‖![(1 : ℂ), 0] x‖ ^ 2 = 1 := by simp
    rw [Fintype.sum_equiv beq.symm]
    exact h
    simp
}

def qub_one : PState 1 := {
  vec := (Equiv.arrowCongr beq (Equiv.refl _)) ![(0 : ℂ), 1]
  normalized := by
    have h: ∑ x, ‖![(0 : ℂ), 1] x‖ ^ 2 = 1 := by simp
    rw [Fintype.sum_equiv beq.symm]
    exact h
    simp
}
