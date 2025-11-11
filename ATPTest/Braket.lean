import QuantumInfo.Finite.Braket

variable {k : Type*} [Fintype k]
--to deal with rewrites
lemma Ket.normalized'' (ψ : Ket k) : ∑ x, ‖ψ x‖^2 = 1 := ψ.normalized'
--phase_mul
def Ket.phase (ψ : Ket k) (z : ℂ) (hp: ‖z‖ = 1) : Ket k where
  vec := z • ψ.vec
  normalized' := sorry
