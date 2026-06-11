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

lemma tr_help {m n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin m) (Fin n) R) :
    M.rowSpace = LinearMap.range M.transpose.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by
      ext j
      simp⟩
  · rintro _ ⟨v, rfl⟩
    have key : M.transpose.mulVec v = ∑ i, v i • M i := by
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    rw [Matrix.mulVecLin_apply, key]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def face1 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (d, a, b) =>
    if d = 0 then
      (a-1, b)
    else
      (a, b-1)

def face2 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (_, a, b) => (a, b)

def face1' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ face1 ∘ (coe2 L).symm

def face2' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ face2 ∘ (coe2 L).symm

lemma help_face1_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₂ L (face1 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₂, face1]
  apply if_pos
  fin_cases d <;> simp [toricH₂_conn]

lemma help_face2_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₂ L (face2 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₂, face2]
  apply if_pos
  fin_cases d <;> simp [toricH₂_conn]

lemma help_face1_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₂' L (face1' x) x = 1 := by
  intro x
  simp only [toricH₂', face1', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_face1_one_raw ((coe2 L).symm x)

lemma help_face2_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₂' L (face2' x) x = 1 := by
  intro x
  simp only [toricH₂', face2', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_face2_one_raw ((coe2 L).symm x)

lemma help_face_zero_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L) (f : Fin L × Fin L),
      f ≠ face1 e → f ≠ face2 e → toricH₂ L f e = 0 := by
  intro ⟨d, a, b⟩ ⟨i, j⟩ H1 H2
  simp only [toricH₂, face1, face2] at *
  apply if_neg
  simp only [toricH₂_conn]
  fin_cases d <;> simp_all [Prod.ext_iff, eq_comm]

lemma help_face_zero {L : ℕ} [NeZero L] :
    ∀ x y, y ≠ face1' x → y ≠ face2' x → toricH₂' L y x = 0 := by
  intro x y H1 H2
  have H1' : (coe1 L).symm y ≠ face1 ((coe2 L).symm x) := fun h =>
    H1 (by simp only [face1', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  have H2' : (coe1 L).symm y ≠ face2 ((coe2 L).symm x) := fun h =>
    H2 (by simp only [face2', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  simp only [toricH₂', Matrix.reindex_apply, Matrix.submatrix_apply]
  exact help_face_zero_raw _ _ H1' H2'

lemma help1 {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
  ∀ (v : Fin (2 * L ^ 2) → ZMod 2) (w : Fin (L^2) → ZMod 2),
    v = (fun e => w (face1' e) + w (face2' e)) →
    (Matrix.transpose (toricH₂' L)).mulVec w = v
  := by
  intro v w H
  subst_vars
  ext x
  simp only [Matrix.transpose, Matrix.mulVec, dotProduct]
  simp
  rw [← Finset.sum_subset (s₁:= {face1' x, face2' x})]
  · rw [Finset.sum_pair]
    · rw [help_face1_one, help_face2_one]
      simp
    · simp only [face1', face2']
      simp
      rcases ((coe2 L).symm x) with ⟨d, a, b⟩
      simp only [face1, face2]
      split
      · intro Heq
        have H : a - 1 = a := (Prod.mk.inj Heq).1
        apply Hne_one
        have Hneg : (-1 : Fin L) = 0 :=
          add_left_cancel (a := a)
            (by rw [← sub_eq_add_neg, add_zero]; exact H)
        have Hval := congr_arg Fin.val Hneg
        simp only [Fin.val_neg, Fin.val_zero] at Hval
        have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        rw [if_neg] at Hval
        · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
        · haveI : Nontrivial (Fin L) := Fin.nontrivial_iff_two_le.mpr (by omega)
          apply Fin.ne_of_val_ne
          simp only [Fin.val_zero]
          norm_num
          assumption
      · intro Heq
        have H : b - 1 = b := (Prod.mk.inj Heq).2
        apply Hne_one
        have Hneg : (-1 : Fin L) = 0 :=
          add_left_cancel (a := b)
            (by rw [← sub_eq_add_neg, add_zero]; exact H)
        have Hval := congr_arg Fin.val Hneg
        simp only [Fin.val_neg, Fin.val_zero] at Hval
        have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        rw [if_neg] at Hval
        · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
        · apply Fin.ne_of_val_ne
          simp only [Fin.val_zero]
          norm_num
          assumption
  · simp
  · simp
    intro y H1 H2
    left
    rw [help_face_zero]
    <;> assumption

def fill_torus {L : ℕ} [NeZero L] (v : Fin (2*L^2) → ZMod 2) : Fin L × Fin L → ZMod 2 :=
  fun (i, j) => v (coe2 L (0, i, 0)) + ∑ k : Fin (j + 1), v (coe2 L (1, i, ⟨k, by omega⟩))

lemma comm_zmod_cancel (a b c : ZMod 2) : a + b + a + c = b + c := by
  have h : a + a = 0 := by fin_cases a <;> rfl
  calc a + b + a + c
      = a + a + b + c := by ring
    _ = 0 + b + c := by rw [h]
    _ = b + c := by simp

lemma helpX {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v,
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      v ∉ (toricH₂' L).rowSpace →
      L ≤ hammingNorm v := by
  suffices H :
      ∀ v,
        v ∈ (Matrix.toLin' (toricH₁' L)).ker →
        hammingNorm v < L →
        v ∈ (toricH₂' L).rowSpace by
    intro v H1 H2
    by_contra H3
    apply H2
    simp at H3
    apply H <;> assumption
  intro v Hker Hlen
  have Hver : ∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0 := by
    intro i j
    have H := congr_fun Hker (coe1 L (i, j))
    simp only [Matrix.toLin', LinearMap.toMatrix'] at H
    simp at H
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
    intro i
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
  suffices H : ∃ w, (Matrix.transpose (toricH₂' L)).mulVec w = v by
    rw [tr_help]
    simp
    obtain ⟨w, H⟩ := H
    exists w
    rw [← H]
    exact (Matrix.mulVec_transpose (toricH₂' L) w).symm
  suffices H : ∃ (w : Fin (L^2) → ZMod 2), v = (fun e => w (face1' e) + w (face2' e)) by
    obtain ⟨w, H⟩ := H
    exists w
    apply help1
    <;> assumption
  suffices H : ∃ (w : Fin (L^2) → ZMod 2), ∀ e, v (coe2 L e) = w (face1' (coe2 L e)) + w (face2' (coe2 L e)) by
    obtain ⟨w, H⟩ := H
    exists w
    ext e
    specialize (H ((coe2 L).symm e))
    rw [Equiv.apply_symm_apply] at H
    assumption
  have Hvedges : ∀ i j, v ((coe2 L) (1, i, j)) = fill_torus v (i, j - 1) + fill_torus v (i, j) := by
    intro i j
    simp only [fill_torus]
    rw [add_comm (v ((coe2 L) (0, i, 0))), add_assoc, ← add_assoc (v ((coe2 L) (0, i, 0))), ZModModule.add_self]
    simp
    cases (Classical.em (j = 0)) <;>
    rename_i h Hj
    -- Seam
    · subst_vars
      simp
      suffices H : ∀ n : ℕ, ∀ Hn : n = L, ∑ k : Fin n, v ((coe2 L) (1, i, ⟨↑k, by omega⟩)) = 0 by
        apply H
        have hL : 0 < L := NeZero.pos L
        rw [zero_sub]
        suffices H : ∀ n, n = L-1+1 → [NeZero n] → ↑((-1) : Fin n) + 1 = L by
          apply H
          omega
        intro n Hn inst
        subst_vars
        rw [Fin.coe_neg_one]
        omega
      intro L Hn
      subst_vars
      obtain ⟨c, Hrow_const⟩ := Hrow_const
      fin_cases c <;> (simp; simp at Hrow_const)
      · specialize (Hrow_const i)
        assumption
      · have Hcontra : hammingNorm v ≥ L := by
          have Hex : ∀ i : Fin L, ∃ j : Fin L, v (coe2 L (1, i, j)) ≠ 0 := by
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
        omega
    -- Not a seam
    · suffices H : ∀ n : ℕ, ∀ Hn : n = j, v ((coe2 L) (1, i, j)) = (∑ k : Fin n, v ((coe2 L) (1, i, ⟨k.val, by have := k.isLt; have := j.isLt; omega⟩))) + (∑ k : Fin (j+1), v ((coe2 L) (1, i, ⟨↑k, by omega⟩)))
      · apply H
        have Hj_val : 0 < j.val := by
          simp only [Fin.ext_iff, Fin.val_zero] at Hj
          omega
        have Hval : (j - 1 : Fin L).val = j.val - 1 := by
          simp only [Fin.sub_def]
          have Heq : L - 1 + j.val = j.val - 1 + L := by omega
          simp
          have H1modL : 1 % L = 1 := by
            apply Nat.mod_eq_of_lt
            omega
          rw [H1modL, Heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      intro n Hn
      subst_vars
      rw [Fin.sum_univ_add]
      simp
      rw [← add_assoc, ZModModule.add_self]
      simp
  exists (fill_torus v ∘ (coe1 L).symm)
  intro (d, i, j)
  simp only [face1', face2', Function.comp]
  simp [Equiv.symm_apply_apply, face1, face2]
  fin_cases d <;> simp
  -- Horizontal edges
  · clear Hrow_const row_wind Hlen Hker
    have this : ∃ L', L = L' + 1:= by
      exists (L - 1)
      have h := NeZero.pos L
      omega
    obtain ⟨L', this⟩ := this
    subst_vars
    induction j using Fin.induction
    case zero =>
      sorry
    case succ j Hj =>
      sorry
  -- Vertical edges
  · apply Hvedges



lemma helpZ {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v,
    v ∈ (Matrix.toLin' (toricH₂' L)).ker →
    v ∉ (toricH₁' L).rowSpace →
    L ≤ hammingNorm v := by
  intro v Hker Hrow
  apply helpX Hne_one
  ·
  ·
    sorry

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
