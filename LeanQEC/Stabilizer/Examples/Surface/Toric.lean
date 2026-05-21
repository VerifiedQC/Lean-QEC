import Mathlib
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import LeanQEC.Stabilizer.Basic
import LeanQEC.Classical_EC.Basic
import LeanQEC.Stabilizer.CSS

-- Edges are encoded as triples (d, a, b), where the edge starts at vertex (a, b) and faces right (d=0) or down (d=1). Vertexes and faces are encoded as (i, j) where i is the row and j is the column. Vertex (i, j) is the top-left vertex of face (i, j)

@[reducible]
def toricH₁_conn {L : ℕ} [NeZero L] (i j : Fin L) (d : Fin 2) (a b : Fin L) : Prop :=
  (d = 0 ∧ a = i ∧ b+1 = j) ∨
  (d = 0 ∧ a = i ∧ b = j) ∨
  (d = 1 ∧ a+1 = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b = j)

def toricH₁ (L : ℕ) [NeZero L] : Matrix (Fin L × Fin L) (Fin 2 × Fin L × Fin L) (ZMod 2) :=
  fun (i, j) (d, a, b) =>
    if toricH₁_conn i j d a b then
      1
    else
      0

@[reducible]
def toricH₂_conn {L : ℕ} [NeZero L] (i j : Fin L) (d : Fin 2) (a b : Fin L) : Prop :=
  (d = 0 ∧ a = i ∧ b = j) ∨
  (d = 0 ∧ a-1 = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b-1 = j)

def toricH₂ (L : ℕ) [NeZero L] : Matrix (Fin L × Fin L) (Fin 2 × Fin L × Fin L) (ZMod 2) :=
  fun (i, j) (d, a, b) =>
    if toricH₂_conn i j d a b then
      1
    else
      0

def coe1 (L : ℕ) : Fin L × Fin L ≃ Fin (L^2) := by
  rw [pow_two]
  apply finProdFinEquiv

def coe2 (L : ℕ) : Fin 2 × Fin L × Fin L ≃ Fin (2 * L ^ 2) := by
  rw [pow_two]
  exact ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def toricH₁' (L : ℕ) [NeZero L] : Matrix (Fin (L^2)) (Fin (2 * L^2)) (ZMod 2) :=
  Matrix.reindex (coe1 L) (coe2 L) (toricH₁ L)

def toricH₂' (L : ℕ) [NeZero L] : Matrix (Fin (L^2)) (Fin (2 * L^2)) (ZMod 2) :=
  Matrix.reindex (coe1 L) (coe2 L) (toricH₂ L)

@[reducible]
def vert_on_face {L : ℕ} [NeZero L] (i1 j1 i2 j2 : Fin L) : Prop :=
  (i1 = i2 ∧ j1 = j2) ∨
  (i1-1 = i2 ∧ j1 = j2) ∨
  (i1 = i2 ∧ j1-1 = j2) ∨
  (i1-1 = i2 ∧ j1-1 = j2)

lemma toricH₁_mul_toricH₂_eq_zero {L : ℕ} [NeZero L] (i1 j1 i2 j2 : Fin L) :
    ∀ d,
    ¬vert_on_face i1 j1 i2 j2 →
    toricH₁ L (i1, j1) d * toricH₂ L (i2, j2) d = 0 := by
  intro (d, a, b)
  simp only [toricH₁, toricH₂]
  intro H
  split
  case isTrue H1 =>
    split
    case isTrue H2 =>
      exfalso
      simp only [toricH₁_conn, toricH₂_conn, vert_on_face] at *
      simp only [not_or] at H
      rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
      rcases H2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
      obtain ⟨_, _, _, _⟩ := H <;>
      simp_all <;> subst_vars <;> simp_all
    case isFalse =>
      simp
  case isFalse =>
    simp

lemma toricH₁_mul_toricH₂_eq_one {L : ℕ} [NeZero L] {i1 j1 i2 j2 : Fin L} {d} :
    vert_on_face i1 j1 i2 j2 →
    ∑ s, toricH₁ L (i1, j1) (d, s) * toricH₂ L (i2, j2) (d, s) = 1 := by
  intro H
  simp_rw [toricH₁, toricH₂, ite_mul, mul_ite, one_mul, mul_one, zero_mul, ite_self, ← ite_and]
  rcases H with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars
  -- Top left vertex
  case inl =>
    rw [Finset.sum_eq_single_of_mem (i2, j1)]
    case h => simp
    case h₀ =>
      intro (i', j') _ H
      apply if_neg; dsimp
      rw [not_and]
      simp only [toricH₁_conn, toricH₂_conn]
      intro H1
      rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
    dsimp; apply if_pos
    simp only [toricH₁_conn, toricH₂_conn]
    fin_cases d <;> simp
  -- Bottom left vertex
  case inr.inl =>
    fin_cases d; simp
    · rw [Finset.sum_eq_single_of_mem (i1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i1-1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp
  -- Top right vertex
  case inr.inr.inl =>
    fin_cases d; simp
    · rw [Finset.sum_eq_single_of_mem (i2, j1-1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i2, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp
  -- Bottom right vertex
  case inr.inr.inr =>
    fin_cases d; dsimp
    · rw [Finset.sum_eq_single_of_mem (i1, j1-1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i1-1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp


lemma toric_orth (L : ℕ) [NeZero L] :
    (toricH₁ L).mutually_orth_rows (toricH₂ L) := by
  intro (i1, j1) (i2, j2)
  simp only [dotProduct]
  -- There are two cases, either:
  -- 1. The vertex is a part of the face, in which case there will be only 2 shared edges, i.e two of the terms are 1 and the rest are 0
  -- 2. The vertex is not a part of the face, in which case there are 0 shared edges, i.e all terms are 0
  cases (Classical.em (vert_on_face i1 j1 i2 j2))
  case inl H =>
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
    simp_rw [toricH₁_mul_toricH₂_eq_one H]
    decide
  case inr H =>
    apply Finset.sum_eq_zero
    intro x H
    apply toricH₁_mul_toricH₂_eq_zero
    assumption


lemma toric_orth' (L : ℕ) [NeZero L] :
    (toricH₁' L).mutually_orth_rows (toricH₂' L) := by
  intro f v
  simp only [dotProduct, toricH₁', toricH₂', Matrix.reindex_apply]
  rw [← Equiv.sum_comp (coe2 L)]
  simp only [Matrix.submatrix, Matrix.of_apply, Equiv.symm_apply_apply]
  apply toric_orth


def toricCode (L : ℕ) [NeZero L] :
    CSS_pair (2 * L^2) (L^2) (L^2) :=
  CSS_pair.of_matrices
    (toricH₁' L)
    (toricH₂' L)
    (toric_orth' L)

lemma toricCode_dist_lb_X {L : ℕ} [NeZero L] :
    L ≤ (toricCode L).dX
  := by
  simp only [toricCode, CSS_pair.dX, min_weight_ker_not_mem_rowspace]
  sorry


lemma toricCode_dist_lb_Z {L : ℕ} [NeZero L] :
    L ≤ (toricCode L).dZ
  := by
  sorry

theorem toricCode_dist_lb (L : ℕ) [NeZero L] :
    L ≤ (toricCode L).toBSM.distance (Nat.add_pos_left (toricCode L).nt₁ _) := by
  rw [CSS.toBSM_dist_eq]
  apply le_min
  · apply toricCode_dist_lb_X
  · apply toricCode_dist_lb_Z
