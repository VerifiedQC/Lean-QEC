import LeanQEC.States.PState

noncomputable section

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

@[simp] lemma qub_zero_zero : qub_zero 0#1 = 1 := by
  simp [qub_zero, Ket.apply, beq]
  simp [BitVec.equivFin]
  rfl

lemma qub_zero_vec_zero : qub_zero.vec 0#1 = 1 := by
  rw [<- Ket.apply, qub_zero_zero]

@[simp] lemma qub_zero_one : qub_zero 1#1 = 0 := by
  simp [qub_zero, Ket.apply, beq]
  simp [BitVec.equivFin]

lemma qub_zero_vec_one : qub_zero.vec 1#1 = 0 := by
  rw [<- Ket.apply, qub_zero_one]

@[simp] lemma qub_one_zero : qub_one 0#1 = 0 := by
  simp [qub_one, Ket.apply, beq]
  simp [BitVec.equivFin]
  rfl

lemma qub_one_vec_zero : qub_one.vec 0#1 = 0 := by
  rw [<- Ket.apply, qub_one_zero]

@[simp] lemma qub_one_one : qub_one 1#1 = 1 := by
  simp [qub_one, Ket.apply, beq]
  simp [BitVec.equivFin]

lemma qub_one_vec_one : qub_one.vec 1#1 = 1 := by
  rw [<- Ket.apply, qub_one_one]


def Ket.star {k : Type*} [Fintype k] (ψ : Ket k) : Ket k where
  vec := starRingEnd (k → ℂ) ψ
  normalized' := by
    simp only [Pi.conj_apply, RCLike.norm_conj]
    simp [DFunLike.coe, ψ.normalized']

variable (ψ : PState 1)

lemma single_qub_normalized : ‖(ψ 0)‖^2+‖(ψ 1)‖^2 = 1 := by
  convert ψ.normalized''
  simp



lemma zero_one_orth : qub_zero.orth qub_one := by
  unfold Ket.orth Ket.dot
  simp [dotProduct, BitVec.sum_univ_one]

lemma one_qub_decomp : ψ = qub_zero.sum qub_one (ψ.vec 0) (ψ.vec 1) (single_qub_normalized ψ) (zero_one_orth) := by
  rw [PState.sum]
  rw [Ket.mk.injEq]; simp
  ext i
  rcases (BitVec1_cases i) with H0 | H1
  · simp
    rw [H0]
    simp
  · simp
    rw [H1]
    simp

-- less painful than expected
lemma ket_prodE {n₁ n₂} (ψ₁ : BitVec n₁ → ℂ) (ψ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ =
  λ(s : BitVec (n₁ + n₂)) =>
    let (s₁, s₂) := bits_cat.symm s
    ψ₁ s₁ * ψ₂ s₂ := by
  ext s; simp
  simp [ket_prod, toMat, normalized_kron, normalize_mat]

lemma sum_prod_bitvecs {n₁ n₂} (f : _ → ℂ) :
  ∑ (s : BitVec n₁ × BitVec n₂), f s =
  ∑ (s₁ : BitVec n₁), ∑ (s₂ : BitVec n₂), f (s₁, s₂) := by
  simp [<- Finset.sum_product]

lemma dot_kron {n₁ n₂} (ψ₁ φ₁ : BitVec n₁ → ℂ) (ψ₂ φ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ ⬝ᵥ (ket_prod φ₁ φ₂) =
  (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := by
  simp [ket_prodE]
  simp [dotProduct]
  rw [Fintype.sum_equiv bits_cat.symm _ (
    λ(x' : BitVec n₁ × BitVec n₂) =>
    let (x₁, x₂) := x'
    (ψ₁ x₁ * φ₁ x₁) * (ψ₂ x₂ * φ₂ x₂)
  )]
  · simp [Finset.sum_mul_sum, sum_prod_bitvecs]
  · -- what is this nonsense?
    simp; group; simp


lemma PState.star_prod {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) :
  starRingEnd (BitVec (n₁ + n₂) → ℂ) (ψ₁ ⊗ₚ ψ₂) = (ψ₁.star ⊗ₚ ψ₂.star) := by
  unfold PState.kron Ket.star
  nth_rw 2 [DFunLike.coe]
  unfold Braket.instFunLikeKet
  ext x
  simp [Pi.conj_apply, ket_prodE]

lemma PState.prod_dot_prod' {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
  (ψ₁ ⊗ₚ ψ₂) ⬝ᵥ (φ₁ ⊗ₚ φ₂) = (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := by apply dot_kron

lemma PState.prod_dot_prod {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
  (ψ₁ ⊗ₚ ψ₂).dot (φ₁ ⊗ₚ φ₂) = (ψ₁.dot φ₁) * (ψ₂.dot φ₂) := by
  unfold Ket.dot
  rw [PState.star_prod]
  rw [PState.prod_dot_prod', Ket.star]
  rfl

lemma prod_orth_left {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₁.orth φ₁)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold Ket.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, zero_mul]

lemma prod_orth_right {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₂.orth φ₂)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold Ket.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, mul_zero]

lemma PState.phase_prod_phase {n₁ n₂} (ψ₁ : PState n₁) (ψ₂ : PState n₂) {p₁ p₂ : phase} :
  (ψ₁.phase_mul p₁) ⊗ₚ (ψ₂.phase_mul p₂) = (ψ₁ ⊗ₚ ψ₂).phase_mul (p₁ * p₂) := by
  unfold PState.kron Ket.phase_mul
  ext x
  simp_rw [ket_prodE, DFunLike.coe, Pi.smul_apply, smul_mul_smul]
  congr
