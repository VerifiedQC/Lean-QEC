import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import ATPTest.Braket

/-
an attempt to redefine Ket and Unitary matrices so they are exactly
specified to our situation: they have a number of qubits, and the fintype
behind them is exactly Fin n → Qubit (where Abbrev Qubit := Fin 2). This
represents bitstrings of length n, and ideally gives us a convenient
representation for tensor products in this form. If State n is a pure
state on n qubits, then (ψ₁ : State n₁) ⊗ (ψ₂ : State n₂) is a pure state
on n₁+n₂ qubits, with a (vec : (Fin (n₁ + n₂) → Qubit) → ℂ). Previously,
our definition of tensor products for kets and unitaries output products
of the input types, but we want to conveniently redefine them so they just
output a bitstring of the desired length. The reason for this is that
if you abstractly have n single-qubit kets, there isn't a good
lean-theoretic statement for the product of (Fin 2), n times. If there was,
it would be isomorphic to Fin (2^n), which is how we were writing it when
we had a specified n for the the number of tensors.

-/
structure State (n : ℕ) where
  vec : (Fin n → Qubit) → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1

instance instFunLikeKet (n : ℕ): FunLike (State n) (Fin n → Qubit) ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [State.mk.injEq]

def state_zero : State 1 := {
  vec := fun f => if f 0 = 0 then 1 else 0
  normalized' := (by
    norm_cast
  )
}

def state_one : State 1 := {
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

def State.apply {n : ℕ} (ψ : State n) (U : n_qubit_unitary n) : State n where
  vec := U.1.toLin' ψ.vec
  normalized' := by
    rewrite [unitary_norm_preserve]
    exact ψ.normalized'

def bitstring_prod_equiv {n₁ n₂ : ℕ} :
((Fin n₁ → Qubit) × (Fin n₂ → Qubit) ≃ (Fin (n₁ + n₂) → Qubit)) where
  toFun := fun (p : (Fin n₁ → Qubit) × (Fin n₂ → Qubit)) =>
    fun (i : Fin (n₁ + n₂)) =>
      if h : i.val < n₁ then
        p.1 ⟨i.val, h⟩
      else
        p.2 ⟨i.val-n₁, by
          push_neg at h
          have hi : i - n₁ < (n₁ + n₂) - n₁ := by
            apply Nat.sub_lt_sub_right h i.2
          convert hi
          simp
        ⟩
  invFun := fun (p : Fin (n₁ + n₂) → Qubit) =>
    ⟨fun (i : Fin n₁) => p ⟨i, lt_of_lt_of_le i.2 (self_le_add_right _ _)⟩,
    fun (i : Fin n₂) => p ⟨n₁+i, Nat.add_lt_add_left i.2 _⟩⟩
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    ext i
    by_cases h: i < n₁
    · simp [h]
    simp [h, Nat.add_sub_cancel' (le_of_not_gt h)]

def bitstring_vec_prod_equiv {n₁ n₂ : ℕ} :
(((Fin n₁ → Qubit) × (Fin n₂ → Qubit)) → ℂ) ≃ ((Fin (n₁ + n₂) → Qubit) → ℂ) where
  toFun := fun P => fun x =>
    P (bitstring_prod_equiv.invFun x)
  invFun := fun P => fun x =>
    P (bitstring_prod_equiv.toFun x)
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    simp


def n_qubit_unitary.prod {n₁ n₂ : ℕ} (U₁ : n_qubit_unitary n₁) (U₂ : n_qubit_unitary n₂) :
  n_qubit_unitary (n₁ + n₂) :=
  unitary_fin_equiv bitstring_prod_equiv (Matrix.unitary_kron U₁ U₂)

open Matrix


lemma State.prod_mul_kron {n₁ n₂ : ℕ} (M₁ : Matrix (Fin n₁ → Qubit) (Fin n₁ → Qubit) ℂ) (M₂ : Matrix (Fin n₂ → Qubit) (Fin n₂ → Qubit) ℂ) (ψ₁ : State n₁) (ψ₂ : State n₂):
  (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M₁ M₂) *ᵥ (bitstring_vec_prod_equiv.invFun (ψ₁.prod ψ₂).vec) = fun (i, j) ↦ ((M₁ *ᵥ ψ₁) i) * ((M₂ *ᵥ ψ₂) j) := by
  ext ⟨i₁, i₂⟩
  simp only [mulVec, kroneckerMap_apply, DFunLike.coe, prod, bitstring_vec_prod_equiv, bitstring_prod_equiv]
  sorry


theorem State.prod_apply {n₁ n₂ : ℕ} (ψ₁ : State n₁) (ψ₂ : State n₂) (U₁ : n_qubit_unitary n₁)
  (U₂ : n_qubit_unitary n₂) : (ψ₁.prod ψ₂).apply (n_qubit_unitary.prod U₁ U₂) =
  (ψ₁.apply U₁).prod (ψ₂.apply U₂) := by
  unfold State.apply n_qubit_unitary.prod State.prod
  rw [State.mk.injEq, Matrix.toLin'_apply]
  simp
