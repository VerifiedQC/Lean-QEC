import ATPTest.States.BitVec
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import ATPTest.Unitary.Basic

section pstate

structure PState (n : ℕ) where
  vec : (BitVec n) → ℂ
  normalized : ∑ x, ‖vec x‖^2 = 1

variable {n : ℕ}

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
  normalized := by
    rewrite [unitary_norm_preserve]
    exact ψ.normalized

def PState.kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) : PState (n₁ + n₂) where
  vec := ket_prod ψ₁.vec ψ₂.vec
  normalized := by
    simp [ket_prod, normalized_kron, toMat]
    have h : ∑ (x : BitVec n₁ × BitVec n₂), (‖ψ₁.vec x.1‖ * ‖ψ₂.vec x.2‖) ^ 2 = 1
    · rw [Fintype.sum_prod_type]
      simp_rw [mul_pow, ←Finset.mul_sum, ψ₂.normalized, mul_one, ψ₁.normalized]
    rw [Fintype.sum_equiv bits_cat.symm]
    exact h
    simp

notation a:60 " ⊗ₖ " b:60 => PState.kron a b

open scoped unitary

theorem kron_mul_kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) :
  (ψ₁ ⊗ₖ ψ₂).apply (U₁ ⊗ₙ U₂) = (ψ₁.apply U₁) ⊗ₖ (ψ₂.apply U₂) := by
  rw [PState.mk.injEq]
  simp [PState.kron, unitary_nkron, kron_prod]

def pstate_n_kron {n : ℕ} (hn : 0 < n) (m : Fin n → PState 1) : PState n :=
match n with
| 0 => (by contradiction)
| 1 => (m 0)
| n₀+2 => ((pstate_n_kron (by norm_num) (λ (x : Fin (n₀+1)) => m ⟨x.val + 1, by simp [x.isLt]⟩)).kron (m 0))

instance instFunLikeKet : FunLike (PState n) (BitVec n) ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [PState.mk.injEq]

noncomputable section

def PState.dot (ψ₁ ψ₂ : PState n) : ℂ := ∑ x, (ψ₁ x) * (ψ₂ x)

def PState.orth (ψ₁ ψ₂ : PState n) : Prop := ψ₁.dot ψ₂ = 0

def PState.sum {n : ℕ} (ψ₁ ψ₂ : PState n) (a b : ℂ) (hab: ‖a‖^2+‖b‖^2 = 1) (h_orth : ψ₁.orth ψ₂) : PState n where
  vec := a • ψ₁.vec + b • ψ₂.vec
  normalized := sorry
