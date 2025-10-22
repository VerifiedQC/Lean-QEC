import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

abbrev Qubit := Fin 2

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

structure State (n : ℕ) where
  vec : (Fin n → Qubit) → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1

def qub_zero : State 1 := {
  vec := fun f => if f 0 = 0 then 1 else 0
  normalized' := (by
    norm_cast
  )
}

def qub_one : State 1 := {
  vec := fun f => if f 0 = 1 then 1 else 0
  normalized' := (by
    norm_cast
  )
}

def State.prod {n₁ n₂ : ℕ} (ψ₁ : State n₁) (ψ₂ : State n₂) : State (n₁ + n₂) where
  vec := fun x =>
    let x₁ : Fin n₁ → Qubit := fun i => x (Fin.castAdd n₂ i)
    let x₂ : Fin n₂ → Qubit := fun i => x (Fin.natAdd n₁ i)
    ψ₁.vec x₁ * ψ₂.vec x₂
  normalized' := by --proof by aristotle
    have h₁ := ψ₁.normalized'
    have h₂ := ψ₂.normalized'
    have h_fubini : ∑ x : Fin (n₁ + n₂) → Qubit, ‖ψ₁.vec (fun i => x (Fin.castAdd n₂ i)) * ψ₂.vec (fun i => x (Fin.natAdd n₁ i))‖ ^ 2 = (∑ x₁ : Fin n₁ → Qubit, ‖ψ₁.vec x₁‖ ^ 2) * (∑ x₂ : Fin n₂ → Qubit, ‖ψ₂.vec x₂‖ ^ 2) := by
      simp +decide only [Finset.sum_mul];
      simp +decide only [Finset.mul_sum _ _ _];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( fun i => x ( Fin.castAdd n₂ i ), fun i => x ( Fin.natAdd n₁ i ) ) ) _ _ _ _ <;> aesop;
      · ext i; cases i using Fin.addCases
        · simp [funext_iff.1 left]
        · simp [funext_iff.1 right]
      · refine' ⟨ Fin.addCases fst snd, _, _ ⟩ <;> aesop;
      · ring;
    rw [h₁, h₂, one_mul] at h_fubini
    exact h_fubini

def n_qubit_unitary (n : ℕ) := 𝐔[Fin n → Qubit]

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

def State.apply {n : ℕ} (ψ : State n) (U : n_qubit_unitary n) : State n where
  vec := U.1.toLin' ψ.vec
  normalized' := by
    rewrite [unitary_norm_preserve]
    exact ψ.normalized'
