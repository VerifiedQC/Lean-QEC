import QuantumInfo.Finite.Braket

variable {k : Type*} [Fintype k] [DecidableEq k]

--phase_mul
def Ket.phase (ψ : Ket k) (z : ℂ) (hp: ‖z‖ = 1) : Ket k where
  vec := z • ψ.vec
  normalized' := sorry
