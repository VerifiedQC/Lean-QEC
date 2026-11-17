import LeanQEC.States.PState

open Matrix

noncomputable section

variable {n₁ n₂ : ℕ}

lemma ket_basis_zero_one_orth :
    (Ket.basis (0 : Qubit)).vec ⬝ᵥ star (Ket.basis (1 : Qubit)).vec = 0 := by
  simp [Ket.basis, dotProduct]

lemma one_qub_decomp (ψ : Qubit → ℂ) :
    ψ = (ψ 0) • (Ket.basis (0 : Qubit)).vec + (ψ 1) • (Ket.basis (1 : Qubit)).vec := by
  ext i
  fin_cases i <;> simp [Ket.basis]

lemma Ket.prod_vec_eq_kron (ψ₁ : Ket (Qubits n₁)) (ψ₂ : Ket (Qubits n₂)) :
    (ψ₁.vec ⊗ₚ ψ₂.vec) = fun s => (ψ₁ ⊗ᵠ ψ₂).vec ((qubitsAppend n₁ n₂).symm s) := by
  ext s
  rfl

lemma dot_kron (ψ₁ φ₁ : PState n₁) (ψ₂ φ₂ : PState n₂) :
    (ψ₁ ⊗ₚ ψ₂) ⬝ᵥ (φ₁ ⊗ₚ φ₂) = (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := by
  simp only [dotProduct, PState.kron_val]
  rw [← (qubitsAppend n₁ n₂).sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply]
  ring

lemma PState.star_prod (ψ₁ : PState n₁) (ψ₂ : PState n₂) :
    starRingEnd (Qubits (n₁ + n₂) → ℂ) (ψ₁ ⊗ₚ ψ₂)
      = (starRingEnd (Qubits n₁ → ℂ) ψ₁) ⊗ₚ (starRingEnd (Qubits n₂ → ℂ) ψ₂) := by
  ext x
  simp [Pi.conj_apply, PState.kron_val]

lemma PState.prod_dot_prod' {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
    (ψ₁ ⊗ₚ ψ₂) ⬝ᵥ (φ₁ ⊗ₚ φ₂) = (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := dot_kron _ _ _ _

lemma PState.prod_dot_prod {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
    (ψ₁ ⊗ₚ ψ₂).dot (φ₁ ⊗ₚ φ₂) = (ψ₁.dot φ₁) * (ψ₂.dot φ₂) := by
  unfold PState.dot
  rw [PState.star_prod]
  exact PState.prod_dot_prod'

lemma prod_orth_left {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₁.orth φ₁) :
    (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold PState.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, zero_mul]

lemma prod_orth_right {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₂.orth φ₂) :
    (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold PState.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, mul_zero]

lemma PState.smul_kron_smul (ψ₁ : PState n₁) (ψ₂ : PState n₂) (a b : ℂ) :
    (a • ψ₁) ⊗ₚ (b • ψ₂) = (a * b) • (ψ₁ ⊗ₚ ψ₂) := by
  ext x
  simp only [PState.kron_val, Pi.smul_apply, smul_eq_mul]
  ring

end
