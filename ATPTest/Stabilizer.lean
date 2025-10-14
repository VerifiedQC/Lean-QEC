import ATPTest.Unitary

variable {k : Type*} [Fintype k] [DecidableEq k]

def stabilizes (U : 𝐔[k]) (psi : Ket k) := psi.uapply U = psi

--prove:
-- X stabilizes +
-- Z stabilizes 0
-- a product of stabilizers stabilizes

open Qubit

theorem X_stab_plus : stabilizes X qub_plus := by
  unfold stabilizes Ket.uapply qub_plus
  rw [Ket.mk.injEq, Matrix.toLin'_apply]
  funext i
  fin_cases i <;> simp [X]

theorem Z_stab_zero : stabilizes Z qub_zero := by
  unfold stabilizes Ket.uapply qub_zero
  rw [Ket.mk.injEq, Matrix.toLin'_apply]
  funext i
  fin_cases i <;> simp [Z]

variable {k₁ k₂ : Type*} [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]

theorem stab_prod {U₁ : 𝐔[k₁]} {U₂ : 𝐔[k₂]} {ψ₁ : Ket k₁} {ψ₂ : Ket k₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs2 : stabilizes U₂ ψ₂) :
  stabilizes (Matrix.unitary_kron U₁ U₂) (ψ₁ ⊗ ψ₂) := sorry
