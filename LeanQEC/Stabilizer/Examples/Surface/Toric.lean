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

def coe1 (L : ℕ) : Fin L × Fin L ≃ Fin (L^2) :=
  pow_two L ▸ finProdFinEquiv

def coe2 (L : ℕ) : Fin 2 × Fin L × Fin L ≃ Fin (2 * L ^ 2) :=
  pow_two L ▸ ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

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

lemma toricH₁_mul_toricH₂_eq_one {L : ℕ} [NeZero L] {i1 j1 i2 j2 : Fin L} :
    ∀ d,
    vert_on_face i1 j1 i2 j2 →
    ∑ s, toricH₁ L (i1, j1) (d, s) * toricH₂ L (i2, j2) (d, s) = 1 := by
  intro d H
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
    simp_rw [toricH₁_mul_toricH₂_eq_one _ H]
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

-- Distance lower bound proof
-- TODO: Tons of duplication, see if that can be cleaned up?
-- TODO: See if `helpZ` can be derived from `helpX` instead of proving it separately?
-- TODO: See if it's worth it to define the torus in terms of `ShortComplex` instead. I think it would only be worth it if mathlib has some results about them that would simplify/beautify these proofs, otherwise I'm not sure. As in, CSS codes are in such tight correspondance with `ShortComplex`es already that the "new" proofs might just end up looking like these current proofs, modulo whatever cleanup I do before then
-- TODO: Finish the proofs by proving the contra cases, have to construct a boundary for `helpX` and a coboundary for `helpZ`

lemma helpX {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v ∈ (Matrix.toLin' (toricH₁' L)).ker, v ∉ (toricH₂' L).rowSpace →
    L ≤ hammingNorm v := by
  intro v Hker Hrow
  simp only [Matrix.rowSpace, Submodule.span, sInf, Set.range] at Hrow
  simp_all
  obtain ⟨s, Hsub, Hnin⟩ := Hrow
  have Hver : ∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0 := by
    intro i j
    have H := congr_fun Hker (coe1 L (i, j))
    simp only [toricH₁', Matrix.mulVec, Matrix.reindex_apply, dotProduct, Matrix.submatrix, coe1, coe2] at H
    simp at H
    rw [← Equiv.sum_comp (coe2 L)] at H
    simp only [Equiv.symm_apply_apply, coe2] at H
    have Hcoe : ∀ x : Fin 2 × Fin L × Fin L,
    (pow_two L ▸ ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv) x = coe2 L x :=
      fun x => rfl
    simp_rw [Hcoe] at H; clear Hcoe
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two] at H
    have H0 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
    v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j - 1), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
          ∑ y, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    have H1 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
    v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i - 1, j), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
          ∑ y, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    rw [H0, H1, ← add_assoc] at H
    assumption
  let col_wind j := ∑ i, v (coe2 L (0, i, j))
  have Hcol_const : ∃ c, ∀ j, col_wind j = c := by
    suffices Hsuf : ∀ j, col_wind j = col_wind (j - 1)
    · exists (col_wind 0)
      intro j
      obtain ⟨j, Hj⟩ := j
      induction j
      case zero => simp
      case succ n Hn =>
        rw [← Hn (by omega)]
        specialize Hsuf ⟨n+1, by omega⟩
        rw [Hsuf]
        congr 1; ext
        simp [Fin.val_sub]
        have H : n < L := by omega
        rcases L with _ | _ | L
        · omega
        · have : n = 0 := by omega
          subst this; omega
        · have Hmod : 1 % (L + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          have Hsum : L + 2 - 1 % (L + 2) + (n + 1) = n + (L + 2) := by rw [Hmod]; omega
          rw [Hsum, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt H, add_zero, Nat.mod_eq_of_lt H]
    intro j; clear Hnin Hsub
    replace Hver := fun i => Hver i j
    replace Hver :=
      Finset.sum_eq_zero (s := Finset.univ)
        (f := fun i =>
          v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) +
          v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)))
        (fun i _ => Hver i)
    simp_rw [Finset.sum_add_distrib] at Hver
    rw [show ∑ i, v (coe2 L (0, i, j)) = col_wind j from rfl] at Hver
    rw [show ∑ i, v (coe2 L (0, i, j-1)) = col_wind (j-1) from rfl] at Hver
    have Heq : ∑ x, v ((coe2 L) (1, x - 1, j)) = ∑ x, v ((coe2 L) (1, x, j)) := by
      rw [Fintype.sum_equiv (finRotate L).symm]
      simp
    rw [Heq] at Hver; clear Heq
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at Hver
    set x := col_wind (j-1); set y := col_wind j;
    clear_value x y
    fin_cases x <;> fin_cases y
    · simp_all
    · exact absurd Hver (by decide)
    · exact absurd Hver (by decide)
    · simp_all
  let row_wind i := ∑ j, v (coe2 L (1, i, j))
  have Hrow_const : ∃ c, ∀ i, row_wind i = c := by
    suffices Hsuf : ∀ i, row_wind i = row_wind (i - 1)
    · exists (row_wind 0)
      intro j
      obtain ⟨j, Hj⟩ := j
      induction j
      case zero => simp
      case succ n Hn =>
        rw [← Hn (by omega)]
        specialize Hsuf ⟨n+1, by omega⟩
        rw [Hsuf]
        congr 1; ext
        simp [Fin.val_sub]
        have H : n < L := by omega
        rcases L with _ | _ | L
        · omega
        · have : n = 0 := by omega
          subst this; omega
        · have Hmod : 1 % (L + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          have Hsum : L + 2 - 1 % (L + 2) + (n + 1) = n + (L + 2) := by rw [Hmod]; omega
          rw [Hsum, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt H, add_zero, Nat.mod_eq_of_lt H]
    intro i; clear Hnin Hsub
    replace Hver := fun j => Hver i j
    replace Hver :=
      Finset.sum_eq_zero (s := Finset.univ)
        (f := fun j =>
          v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) +
          v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)))
        (fun i _ => Hver i)
    simp_rw [Finset.sum_add_distrib] at Hver
    rw [show ∑ j, v (coe2 L (1, i, j)) = row_wind i from rfl] at Hver
    rw [show ∑ j, v (coe2 L (1, i-1, j)) = row_wind (i-1) from rfl] at Hver
    have Heq : ∑ x, v ((coe2 L) (0, i, x - 1)) = ∑ x, v ((coe2 L) (0, i, x)) := by
      rw [Fintype.sum_equiv (finRotate L).symm]
      simp
    rw [Heq] at Hver; clear Heq
    rw [add_assoc, CharTwo.add_self_eq_zero, add_comm, add_assoc, add_zero] at Hver
    set x := row_wind (i-1); set y := row_wind i;
    clear_value x y
    fin_cases x <;> fin_cases y
    · simp_all
    · exact absurd Hver (by decide)
    · exact absurd Hver (by decide)
    · simp_all
  obtain ⟨cc, Hcol_const⟩ := Hcol_const
  obtain ⟨cr, Hrow_const⟩ := Hrow_const
  fin_cases cc <;> simp at Hcol_const
  · fin_cases cr <;> simp at Hrow_const
    · suffices Hin : ∃ w, toricH₂' L w = v
      · exfalso
        apply Hnin
        apply Hsub
        assumption
      -- TODO: Exhibit a cycle that is a boundary
      sorry
    · have Hex : ∀ i : Fin L, ∃ j : Fin L, v (coe2 L (1, i, j)) ≠ 0 := by
        intro i
        by_contra H
        push Not at H
        have : row_wind i = 0 := by
          simp [row_wind, Finset.sum_eq_zero (fun j _ => H j)]
        rw [Hrow_const] at this
        exact one_ne_zero this
      choose wit Hwit using Hex
      have Hinj : Function.Injective (fun i => (⟨coe2 L (1, i, wit i), Hwit i⟩ : {e // v e ≠ 0})) := by
        intro i1 i2 H
        simp only [Subtype.mk.injEq] at H
        have := (coe2 L).injective H
        simp only [Prod.mk.injEq] at this
        exact this.2.1
      calc L = Fintype.card (Fin L) := by simp
          _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
          _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]
  · have Hex : ∀ j : Fin L, ∃ i : Fin L, v (coe2 L (0, i, j)) ≠ 0 := by
      intro j
      by_contra H
      push Not at H
      have : col_wind j = 0 := by
        simp [col_wind, Finset.sum_eq_zero (fun i _ => H i)]
      rw [Hcol_const] at this
      exact one_ne_zero this
    choose wit Hwit using Hex
    have Hinj : Function.Injective (fun j => (⟨coe2 L (0, wit j, j), Hwit j⟩ : {e // v e ≠ 0})) := by
      intro j1 j2 H
      simp only [Subtype.mk.injEq] at H
      have := (coe2 L).injective H
      simp only [Prod.mk.injEq] at this
      exact this.2.2
    calc L = Fintype.card (Fin L) := by simp
        _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
        _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]

lemma helpZ {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v ∈ (Matrix.toLin' (toricH₂' L)).ker, v ∉ (toricH₁' L).rowSpace →
    L ≤ hammingNorm v := by
  intro v Hker Hrow
  simp only [Matrix.rowSpace, Submodule.span, sInf, Set.range] at Hrow
  simp_all
  obtain ⟨s, Hsub, Hnin⟩ := Hrow
  have Hver : ∀ i j, v (coe2 L (0, i, j)) + v (coe2 L (0, i + 1, j)) + v (coe2 L (1, i, j)) + v (coe2 L (1, i, j + 1)) = 0 := by
    intro i j
    have H := congr_fun Hker (coe1 L (i, j))
    simp only [toricH₂', Matrix.mulVec, Matrix.reindex_apply, dotProduct, Matrix.submatrix, coe1, coe2] at H
    simp at H
    rw [← Equiv.sum_comp (coe2 L)] at H
    simp only [Equiv.symm_apply_apply, coe2] at H
    have Hcoe : ∀ x : Fin 2 × Fin L × Fin L,
      (pow_two L ▸ ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv) x = coe2 L x :=
      fun x => rfl
    simp_rw [Hcoe] at H; clear Hcoe
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two] at H
    have H0 : ∑ y : Fin L × Fin L, toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) =
        v (coe2 L (0, i, j)) + v (coe2 L (0, i + 1, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j), (i + 1, j)} : Finset (Fin L × Fin L)),
              toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) =
          ∑ y, toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst; simp at inst
      · simp at Hne_one
      · rw [Finset.sum_pair]
        · simp only [toricH₂, toricH₂_conn]
          split <;> simp_all
        · simp [Prod.mk.injEq]
    have H1 : ∑ y : Fin L × Fin L, toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) =
        v (coe2 L (1, i, j)) + v (coe2 L (1, i, j + 1)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j), (i, j + 1)} : Finset (Fin L × Fin L)),
              toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) =
          ∑ y, toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst; simp at inst
      · simp at Hne_one
      · rw [Finset.sum_pair]
        · simp only [toricH₂, toricH₂_conn]
          split <;> simp_all
        · simp [Prod.mk.injEq]
    rw [H0, H1, ← add_assoc] at H
    assumption
  let col_wind j := ∑ i, v (coe2 L (1, i, j))
  have Hcol_const : ∃ c, ∀ j, col_wind j = c := by
    suffices Hsuf : ∀ j, col_wind j = col_wind (j + 1)
    · exists (col_wind 0)
      intro j
      obtain ⟨j, Hj⟩ := j
      induction j
      case zero => simp
      case succ n Hn =>
        have hstep : (⟨n, by omega⟩ : Fin L) + 1 = ⟨n + 1, Hj⟩ := by
          ext; simp [Fin.val_add, Nat.mod_eq_of_lt Hj]
        rw [← hstep, ← Hsuf ⟨n, by omega⟩]
        exact Hn (by omega)
    intro j; clear Hnin Hsub
    replace Hver := fun i => Hver i j
    replace Hver :=
      Finset.sum_eq_zero (s := Finset.univ)
        (f := fun i =>
          v (coe2 L (0, i, j)) + v (coe2 L (0, i + 1, j)) +
          v (coe2 L (1, i, j)) + v (coe2 L (1, i, j + 1)))
        (fun i _ => Hver i)
    simp_rw [Finset.sum_add_distrib] at Hver
    rw [show ∑ i, v (coe2 L (1, i, j)) = col_wind j from rfl] at Hver
    rw [show ∑ i, v (coe2 L (1, i, j + 1)) = col_wind (j + 1) from rfl] at Hver
    have Heq : ∑ x : Fin L, v ((coe2 L) (0, x + 1, j)) = ∑ x : Fin L, v ((coe2 L) (0, x, j)) := by
      rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin L))]
      simp
    rw [Heq] at Hver; clear Heq
    rw [CharTwo.add_self_eq_zero, zero_add] at Hver
    set x := col_wind j; set y := col_wind (j + 1)
    clear_value x y
    fin_cases x <;> fin_cases y
    · simp_all
    · exact absurd Hver (by decide)
    · exact absurd Hver (by decide)
    · simp_all
  let row_wind i := ∑ j, v (coe2 L (0, i, j))
  have Hrow_const : ∃ c, ∀ i, row_wind i = c := by
    suffices Hsuf : ∀ i, row_wind i = row_wind (i + 1)
    · exists (row_wind 0)
      intro i
      obtain ⟨i, Hi⟩ := i
      induction i
      case zero => simp
      case succ n Hn =>
        have hstep : (⟨n, by omega⟩ : Fin L) + 1 = ⟨n + 1, Hi⟩ := by
          ext; simp [Fin.val_add, Nat.mod_eq_of_lt Hi]
        rw [← hstep, ← Hsuf ⟨n, by omega⟩]
        exact Hn (by omega)
    intro i; clear Hnin Hsub
    replace Hver := fun j => Hver i j
    replace Hver :=
      Finset.sum_eq_zero (s := Finset.univ)
        (f := fun j =>
          v (coe2 L (0, i, j)) + v (coe2 L (0, i + 1, j)) +
          v (coe2 L (1, i, j)) + v (coe2 L (1, i, j + 1)))
        (fun j _ => Hver j)
    simp_rw [Finset.sum_add_distrib] at Hver
    rw [show ∑ j, v (coe2 L (0, i, j)) = row_wind i from rfl] at Hver
    rw [show ∑ j, v (coe2 L (0, i + 1, j)) = row_wind (i + 1) from rfl] at Hver
    have Heq : ∑ x : Fin L, v ((coe2 L) (1, i, x + 1)) = ∑ x : Fin L, v ((coe2 L) (1, i, x)) := by
      rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin L))]
      simp
    rw [Heq] at Hver; clear Heq
    rw [show row_wind i + row_wind (i + 1) + ∑ x, v ((coe2 L) (1, i, x)) + ∑ x, v ((coe2 L) (1, i, x)) =
    row_wind i + row_wind (i + 1) + (∑ x, v ((coe2 L) (1, i, x)) + ∑ x, v ((coe2 L) (1, i, x)) ) from by ring] at Hver
    rw [CharTwo.add_self_eq_zero, add_zero] at Hver
    set x := row_wind i; set y := row_wind (i + 1)
    clear_value x y
    fin_cases x <;> fin_cases y
    · simp_all
    · exact absurd Hver (by decide)
    · exact absurd Hver (by decide)
    · simp_all
  obtain ⟨cc, Hcol_const⟩ := Hcol_const
  obtain ⟨cr, Hrow_const⟩ := Hrow_const
  fin_cases cc <;> simp at Hcol_const
  · fin_cases cr <;> simp at Hrow_const
    · suffices Hin : ∃ w, toricH₁' L w = v
      · exfalso
        apply Hnin
        apply Hsub
        assumption
      -- TODO: Exhibit a cocycle that is a coboundary
      sorry
    · have Hex : ∀ i : Fin L, ∃ j : Fin L, v (coe2 L (0, i, j)) ≠ 0 := by
        intro i
        by_contra H
        push Not at H
        have : row_wind i = 0 := by
          simp [row_wind, Finset.sum_eq_zero (fun j _ => H j)]
        rw [Hrow_const] at this
        exact one_ne_zero this
      choose wit Hwit using Hex
      have Hinj : Function.Injective (fun i => (⟨coe2 L (0, i, wit i), Hwit i⟩ : {e // v e ≠ 0})) := by
        intro i1 i2 H
        simp only [Subtype.mk.injEq] at H
        have := (coe2 L).injective H
        simp only [Prod.mk.injEq] at this
        exact this.2.1
      calc L = Fintype.card (Fin L) := by simp
           _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
           _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]
  · have Hex : ∀ j : Fin L, ∃ i : Fin L, v (coe2 L (1, i, j)) ≠ 0 := by
      intro j
      by_contra H
      push Not at H
      have : col_wind j = 0 := by
        simp [col_wind, Finset.sum_eq_zero (fun i _ => H i)]
      rw [Hcol_const] at this
      exact one_ne_zero this
    choose wit Hwit using Hex
    have Hinj : Function.Injective (fun j => (⟨coe2 L (1, wit j, j), Hwit j⟩ : {e // v e ≠ 0})) := by
      intro j1 j2 H
      simp only [Subtype.mk.injEq] at H
      have := (coe2 L).injective H
      simp only [Prod.mk.injEq] at this
      exact this.2.2
    calc L = Fintype.card (Fin L) := by simp
         _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
         _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]

theorem toricCode_dist_lb (L : ℕ) [NeZero L] :
    L ≤ (toricCode L).toBSM.distance (Nat.add_pos_left (toricCode L).nt₁ _) := by
  rw [CSS.toBSM_dist_eq]
  apply le_min
  · rcases L with _ | _ | L
    · simp
    · simp only [toricCode, CSS_pair.dX, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₂' 1).toLin' →
                  v ∉ (toricH₁' 1).rowSpace → 1 ≤ hammingNorm v by
        simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      intro v _ Hrow
      have Hne : v ≠ 0 := fun h => Hrow (by simp [h, Matrix.rowSpace])
      exact hammingNorm_pos_iff.mpr Hne
    · simp only [toricCode, CSS_pair.dX, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₂' (L+1+1)).toLin' → v ∉ (toricH₁' (L+1+1)).rowSpace → (L+1+1) ≤ hammingNorm v
      · simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      apply helpZ (by simp)
  · rcases L with _ | _ | L
    · simp
    · simp only [toricCode, CSS_pair.dZ, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₁' 1).toLin' →
                  v ∉ (toricH₂' 1).rowSpace → 1 ≤ hammingNorm v by
        simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      intro v _ Hrow
      have Hne : v ≠ 0 := fun h => Hrow (by simp [h, Matrix.rowSpace])
      exact hammingNorm_pos_iff.mpr Hne
    · simp only [toricCode, CSS_pair.dZ, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₁' (L+1+1)).toLin' → v ∉ (toricH₂' (L+1+1)).rowSpace → (L+1+1) ≤ hammingNorm v
      · simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      apply helpX (by simp)
