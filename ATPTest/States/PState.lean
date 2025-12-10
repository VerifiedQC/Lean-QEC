import ATPTest.States.BitVec
import ATPTest.Unitary.Basic
import ATPTest.Braket

section pstate

abbrev PState (n : ℕ) := Ket (BitVec n)
/-
structure PState (n : ℕ) where
  vec : (BitVec n) → ℂ
  normalized : ∑ x, ‖vec x‖^2 = 1
-/
variable {n : ℕ}

theorem unitary_inner_preserve {k : Type*} [Fintype k] [DecidableEq k] (v₁ v₂ : k → ℂ) (U : 𝐔[k]) :
  ∑ x : k, (U.val.mulVec v₁) x * starRingEnd ℂ ((U.val.mulVec v₂) x) = ∑ x : k, v₁ x * starRingEnd ℂ (v₂ x) := by
  have h_unitary : U.val.conjTranspose * U.val = 1 := by
    rw [←Matrix.star_eq_conjTranspose, ←Matrix.mem_unitaryGroup_iff']
    simp_all only [SetLike.coe_mem]
  have h_inner : ∑ x : k, (U.val.mulVec v₁) x * starRingEnd ℂ ((U.val.mulVec v₂) x) = ∑ x : k, ∑ y : k, v₁ y * starRingEnd ℂ (v₂ x) * (U.val.conjTranspose * U.val) x y := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
  rw [h_inner]
  simp_all [Matrix.one_apply]




--thanks aristotle
theorem unitary_norm_preserve {k : Type*} [Fintype k] [DecidableEq k] (U : 𝐔[k]) (v: k → ℂ) :
  ∑ x, ‖(U.1.toLin' v) x‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  have h_norm : ∀ (v : k → ℂ), (∑ x : k, ‖(Matrix.toLin' U.val v) x‖ ^ 2) = (∑ x : k, ‖v x‖ ^ 2) := by
    -- Since $U$ is unitary, we have $\langle Uv, Uv \rangle = \langle v, v \rangle$.
    have h_inner : ∀ (v : k → ℂ), ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, v x * starRingEnd ℂ (v x) := by
      intro v
      have h_unitary : U.val.conjTranspose * U.val = 1 := by
        aesop;
        cases property ; aesop
      have h_unitary : ∀ (v : k → ℂ), ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, v x * starRingEnd ℂ (v x) := by
        intro v
        have h_inner : ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, ∑ y : k, v y * starRingEnd ℂ (v x) * (U.val.conjTranspose * U.val) x y := by
          simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
          simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
        simp_all +decide [ Matrix.one_apply];
      exact h_unitary v;
    -- Since the norm squared of a complex number z is z * conjugate(z), we can rewrite the sums in terms of the inner product.
    have h_norm_sq : ∀ (v : k → ℂ), ∑ x : k, ‖(Matrix.toLin' U.val v) x‖ ^ 2 = ∑ x : k, (Matrix.toLin' U.val v) x * starRingEnd ℂ ((Matrix.toLin' U.val v) x) := by
      simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    intro v; specialize h_norm_sq v; specialize h_inner v; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;
    exact_mod_cast h_inner;
  -- Apply the hypothesis `h_norm` to the vector `v`.
  apply h_norm

@[simp]
def PState.apply (ψ : PState n) (U : 𝐔ₙ[n]) : PState n where
  vec := U.1.toLin' ψ.vec
  normalized' := by
    rewrite [unitary_norm_preserve]
    exact ψ.normalized'

def PState.kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) : PState (n₁ + n₂) where
  vec := ket_prod ψ₁.vec ψ₂.vec
  normalized' := by
    simp [ket_prod, normalized_kron, toMat]
    have h : ∑ (x : BitVec n₁ × BitVec n₂), (‖ψ₁.vec x.1‖ * ‖ψ₂.vec x.2‖) ^ 2 = 1 := by
      rw [Fintype.sum_prod_type]
      simp_rw [mul_pow, ←Finset.mul_sum, ψ₂.normalized', mul_one, ψ₁.normalized']
    rw [Fintype.sum_equiv bits_cat.symm]
    exact h
    simp

notation a:60 " ⊗ₚ " b:60 => PState.kron a b

open scoped unitary

variable {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂])

-- #check (ψ₁.apply U₁) ⊗ₚ (ψ₁.apply U₁)

theorem kron_mul_kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) :
  (ψ₁ ⊗ₚ ψ₂).apply (U₁ ⊗ₙ U₂) = (ψ₁.apply U₁) ⊗ₚ (ψ₂.apply U₂) := by
  rw [Ket.mk.injEq]
  simp [PState.kron, unitary_nkron, kron_prod]

/-
The trivial pure state, on 0 qubits, or a vector space with dimension 1.
Notably, this is not a singleton type due to global phase.
-/
def PState.trivial : PState 0 where
  vec := fun _ => 1
  normalized' := by
    rw [Fintype.sum_subsingleton _ BitVec.nil]
    norm_num

noncomputable def pstate_n_kron {n : ℕ} (m : Fin n → PState 1) : PState n :=
match n with
| 0 => PState.trivial
| n₀+1 => ((pstate_n_kron (λ (x : Fin n₀) => m ⟨x.val + 1, by simp [x.isLt]⟩)).kron (m 0))


lemma PState.kron_val (n₁ n₂) {ψ₁ : PState n₁} {ψ₂ : PState n₂} {x : BitVec (n₁ + n₂)} :
  (ψ₁ ⊗ₚ ψ₂) x = (ψ₁ (bits_cat.symm x).1) * (ψ₂ (bits_cat.symm x).2) := by
  simp [PState.kron, ket_prod, toMat, normalized_kron]
  rfl

lemma PState.kron_assoc {ψ₁ ψ₂ ψ₃ : PState 1} : (ψ₁ ⊗ₚ ψ₂) ⊗ₚ ψ₃ = ψ₁ ⊗ₚ (ψ₂ ⊗ₚ ψ₃) := by
  ext x
  rw [@PState.kron_val 2 1, PState.kron_val]
  rw [@PState.kron_val 1 2, PState.kron_val]
  rw [mul_assoc]
  fin_cases x <;> rfl

noncomputable section
open ComplexConjugate

lemma Complex.normSq_eq_mul_self_conj_re {z : ℂ} : (normSq z : ℝ) = (z * (starRingEnd ℂ z)).re := by
  simp [Complex.normSq]

@[simp]
def Ket.dot {k : Type*} [Fintype k] (ψ₁ ψ₂ : Ket k) : ℂ := ψ₁ ⬝ᵥ (conj ψ₂)

lemma Ket.dot_star_symm {k : Type*} [Fintype k] (ψ₁ ψ₂ : Ket k) : ψ₁.dot ψ₂ = conj (ψ₂.dot ψ₁) := by
  unfold Ket.dot dotProduct
  simp_rw [starRingEnd_apply, star_sum, star_mul]
  simp

lemma dot_self_real {k : Type*} [Fintype k] (ψ₁ : Ket k) : (ψ₁.dot ψ₁).im = 0 := by
  unfold Ket.dot dotProduct
  show (∑ i, ψ₁ i * (starRingEnd (ℂ) (⇑ψ₁ i))).im = 0
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero (fun x  hx => ?_)
  rw [Complex.im_eq_zero_iff_isSelfAdjoint]
  unfold IsSelfAdjoint
  simp [mul_comm]



lemma Ket.dot_self {k : Type*} [Fintype k] (ψ₁ : Ket k) : ψ₁.dot ψ₁ = 1 := by
  have:= ψ₁.normalized'
  simp_rw [Complex.sq_norm, Complex.normSq_eq_mul_self_conj_re, ←Complex.re_sum] at this
  apply Complex.ext
  · rw [Complex.one_re]
    exact this
  rw [Complex.one_im]
  exact (dot_self_real ψ₁)

@[simp]
lemma Ket.dot_self' {k : Type*} [Fintype k] (ψ₁ : Ket k) : ψ₁ ⬝ᵥ starRingEnd (k → ℂ) ψ₁ = 1 := Ket.dot_self ψ₁

@[simp]
lemma starRingEnd_smul {R : Type u} [CommSemiring R] [StarRing R]
  {A : Type v} [CommSemiring A] [StarRing A] [SMul R A] [StarModule R A] (x : R) (y : A)
   : (starRingEnd A) (x • y) = ((starRingEnd R) x) • ((starRingEnd A) y) := by
  rw [starRingEnd_apply, star_smul, ←starRingEnd_apply, ←starRingEnd_apply]

@[simp]
def Ket.orth {k : Type*} [Fintype k] (ψ₁ ψ₂ : Ket k) : Prop := ψ₁.dot ψ₂ = 0

lemma Ket.orth_symm {k : Type*} [Fintype k] {ψ₁ ψ₂ : Ket k} :
  ψ₁.orth ψ₂ ↔ ψ₂.orth ψ₁ := by
  unfold Ket.orth
  rw [Ket.dot_star_symm]
  simp


@[simp]
lemma Ket.dot_orth1 {k : Type*} [Fintype k] {ψ₁ ψ₂ : Ket k} (h_orth : ψ₁.orth ψ₂) :
  ψ₁ ⬝ᵥ starRingEnd (k → ℂ) ψ₂ = 0 := h_orth

@[simp]
lemma Ket.dot_orth2 {k : Type*} [Fintype k] {ψ₁ ψ₂ : Ket k} (h_orth : ψ₁.orth ψ₂) :
  ψ₂ ⬝ᵥ starRingEnd (k → ℂ) ψ₁ = 0 := Ket.orth_symm.1 h_orth


def PState.sum {n : ℕ} (ψ₁ ψ₂ : PState n) (a b : ℂ) (hab: ‖a‖^2+‖b‖^2 = 1) (h_orth : ψ₁.orth ψ₂) : PState n where
  vec := a • ψ₁ + b • ψ₂
  normalized' := by
    simp_rw [Complex.sq_norm, Complex.normSq_eq_mul_self_conj_re, ←Complex.re_sum]
    change ((a • ⇑ψ₁ + b • ⇑ψ₂) ⬝ᵥ (conj (a • ⇑ψ₁ + b • ⇑ψ₂))).re = 1
    simp only [map_add, dotProduct_add, add_dotProduct,
    smul_dotProduct, starRingEnd_smul, dotProduct_smul, Ket.dot_self',
    Ket.dot_orth1 h_orth, Ket.dot_orth2 h_orth]
    simp [ -Complex.add_re, -Complex.mul_re, ←Complex.normSq_eq_conj_mul_self, ←Complex.sq_norm, sq,
    -Complex.ofReal_mul, ←Complex.ofReal_add]
    simp [←sq, hab]

lemma PState.apply_eq {n : ℕ} {ψ : PState n} {U : 𝐔ₙ[n]} {i : BitVec n} : (ψ.apply U) i = (U.val.mulVec ψ) i := by rfl


lemma PState.apply_orth {n : ℕ} {ψ φ : PState n} (h_orth : ψ.orth φ) {U : 𝐔ₙ[n]} :
  (ψ.apply U).orth (φ.apply U) := by
  unfold Ket.orth
  have h_dot : Ket.dot (ψ.apply U) (φ.apply U) = Ket.dot ψ φ := by
    unfold Ket.dot dotProduct
    simp_rw [Pi.conj_apply, PState.apply_eq]
    refine (unitary_inner_preserve _ _ _)
  rw [h_dot]
  exact h_orth


lemma PState.sum_coe {n : ℕ} {ψ φ : PState n} {a b : ℂ} (hab : ‖a‖^2 + ‖b‖^2 = 1) (h_orth : ψ.orth φ) :
  ((PState.sum ψ φ a b hab h_orth) : (BitVec n → ℂ)) = a • ψ + b • φ := by rfl

lemma PState.sum_apply {n : ℕ} {ψ φ : PState n} {a b : ℂ} (hab : ‖a‖^2 + ‖b‖^2 = 1) (h_orth : ψ.orth φ) (U : 𝐔ₙ[n]) :
  (PState.sum ψ φ a b hab h_orth).apply U = PState.sum (ψ.apply U) (φ.apply U) a b hab (PState.apply_orth h_orth) := by
  ext i
  rw [PState.apply_eq, PState.sum_coe, Matrix.mulVec_add, PState.sum_coe,
  Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

@[simp]
lemma PState.apply_id {n : ℕ} {ψ : PState n} : ψ.apply 1 = ψ := by simp
