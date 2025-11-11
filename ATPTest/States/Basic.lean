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

local instance : NatCast (Fin 2) := Fin.NatCast.instNatCast 2

@[simp] lemma qub_zero_zero : qub_zero 0#1 = 1 := by
  simp [qub_zero, Ket.apply, beq]
  simp [BitVec.equivFin]
  have: (Nat.cast (0 : ℕ)) = (0 : Fin 2) := by rfl
  rw [this, Matrix.cons_val_zero]

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
  have: (Nat.cast (0 : ℕ)) = (0 : Fin 2) := by rfl
  rw [this, Matrix.cons_val_zero]

lemma qub_one_vec_zero : qub_one.vec 0#1 = 0 := by
  rw [<- Ket.apply, qub_one_zero]

@[simp] lemma qub_one_one : qub_one 1#1 = 1 := by
  simp [qub_one, Ket.apply, beq]
  simp [BitVec.equivFin]

lemma qub_one_vec_one : qub_one.vec 1#1 = 1 := by
  rw [<- Ket.apply, qub_one_one]

variable (ψ : PState 1)

lemma single_qub_normalized : ‖(ψ 0)‖^2+‖(ψ 1)‖^2 = 1 := by
  convert ψ.normalized
  simp [Complex.normSq_eq_norm_sq]



lemma zero_one_orth : qub_zero.orth qub_one := by
  unfold PState.orth PState.dot
  simp

lemma one_qub_decomp : ψ = qub_zero.sum qub_one (ψ.vec 0) (ψ.vec 1) (single_qub_normalized ψ) (zero_one_orth) := by
  rw [PState.sum]
  rw [Ket.mk.injEq]; simp
  ext i
  rcases (BitVec1_cases i) with H0 | H1
  · simp
    rw [H0]
    simp [qub_zero_vec_zero, qub_one_vec_zero]
  · simp
    rw [H1]
    simp [qub_zero_vec_one, qub_one_vec_one]

-- less painful than expected
lemma ket_prodE {n₁ n₂} (ψ₁ : BitVec n₁ → ℂ) (ψ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ =
  λ(s : BitVec (n₁ + n₂)) =>
    let (s₁, s₂) := bits_cat.symm s
    ψ₁ s₁ * ψ₂ s₂ := by
  ext s; simp
  simp [ket_prod, toMat, normalized_kron, normalize_mat]

lemma sum_prod_bitvecs {n₁ n₂} (f : _ -> ℂ) :
  ∑ (s : BitVec n₁ × BitVec n₂), f s =
  ∑ (s₁ : BitVec n₁), ∑ (s₂ : BitVec n₂), f (s₁, s₂) := by
  simp [<- Finset.sum_product]

lemma dot_kron {n₁ n₂} (ψ₁ φ₁ : BitVec n₁ → ℂ) (ψ₂ φ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ ⬝ᵥ ket_prod φ₁ φ₂ =
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

def orth_base {n} (ψ φ : BitVec n → ℂ) := ψ ⬝ᵥ φ = 0

lemma prod_orth_base {n₁ n₂} {ψ₁ φ₁ : BitVec n₁ → ℂ} {ψ₂ φ₂ : BitVec n₂ → ℂ}
  (h : orth_base ψ₁ φ₁ ∨ orth_base ψ₂ φ₂)
  : orth_base (ket_prod ψ₁ ψ₂) (ket_prod φ₁ φ₂) := by
  rw [orth_base] at ⊢ h h
  rw [dot_kron]
  rcases h with h1 | h2
  · simp [h1]
  · simp [h2]

lemma orthE {n} (ψ φ : PState n) :
  ψ.orth φ = orth_base ψ.1 φ.1 := by rfl

lemma prod_orth' {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (h : ψ₁.orth φ₁ ∨ ψ₂.orth φ₂)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  rw [orthE] at h h ⊢
  apply prod_orth_base
  tauto

-- You actually only need ho₁ OR ho₂; stronger version above
lemma prod_orth {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho₁ : ψ₁.orth φ₁) (ho₂ : ψ₂.orth φ₂)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  apply prod_orth'
  tauto
