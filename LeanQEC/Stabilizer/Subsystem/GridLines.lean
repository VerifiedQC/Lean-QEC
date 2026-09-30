import Mathlib

/-!
# Lines, boxes and cubes on a finite grid

Combinatorics underlying the distance of the RLG subsystem code. Points of the grid are
dependent tuples `x : (i : Fin l) → α i`. We study `ZMod 2`-valued functions on the grid.

* `Grid.lineSpan` is the span of the indicator vectors of coordinate lines (the gauge group).
* `Grid.Cent z` says `z` has even overlap with every non-degenerate box of parallel lines
  (commutation with the stabilizers).
* `Grid.cubeSum z a b` is the sum of `z` over the `2^l` corners of the cube spanned by `a, b`.

The two main results are proved by induction on `l`, slicing along the first coordinate:

* `Grid.mem_lineSpan_of_cubeSum`: a function with vanishing sum on every non-degenerate cube
  lies in the span of the lines.
* `Grid.two_pow_le_hammingNorm`: when every side has even size at least `4`, a function
  commuting with the stabilizers but outside the gauge span has weight at least `2^l`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Finset

namespace Grid

universe u

variable {l : ℕ} {α : Fin l → Type u} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- Points of the grid. -/
abbrev Pt (α : Fin l → Type u) := (i : Fin l) → α i

/-- Binary vectors supported on the grid. -/
abbrev Vec (α : Fin l → Type u) := Pt α → ZMod 2

/-- Indicator of the coordinate line through `c` in direction `i`. -/
def line (i : Fin l) (c : Pt α) : Vec α :=
  fun x => if ∀ j, j ≠ i → x j = c j then 1 else 0

/-- The span of all coordinate lines. -/
def lineSpan (α : Fin l → Type u) [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] :
    Submodule (ZMod 2) (Vec α) :=
  Submodule.span (ZMod 2) (Set.range fun p : Fin l × Pt α => line p.1 p.2)

lemma line_mem_lineSpan (i : Fin l) (c : Pt α) : line i c ∈ lineSpan α :=
  Submodule.subset_span ⟨(i, c), rfl⟩

/-- Sum of `z` over the box of lines in direction `i` with transverse values `a j` or `b j`. -/
def boxSum (z : Vec α) (i : Fin l) (a b : Pt α) : ZMod 2 :=
  ∑ x, if (∀ j, j ≠ i → x j = a j ∨ x j = b j) then z x else 0

/-- The box is non-degenerate: `a` and `b` differ in every transverse coordinate. -/
def Nondeg (i : Fin l) (a b : Pt α) : Prop := ∀ j, j ≠ i → a j ≠ b j

/-- `z` commutes with every box stabilizer. -/
def Cent (z : Vec α) : Prop := ∀ i a b, Nondeg i a b → boxSum z i a b = 0

/-- Sum of `z` over the `2^l` corners of the cube spanned by `a` and `b`. -/
def cubeSum (z : Vec α) (a b : Pt α) : ZMod 2 :=
  ∑ x, if (∀ j, x j = a j ∨ x j = b j) then z x else 0

/-- The cube is non-degenerate: `a` and `b` differ in every coordinate. -/
def CubeNondeg (a b : Pt α) : Prop := ∀ j, a j ≠ b j

/-! ### `ZMod 2` bookkeeping -/

lemma vec_add_self {β : Fin l → Type u} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (w : Vec β) : w + w = 0 := by
  funext x; exact CharTwo.add_self_eq_zero _

lemma vec_add_add_cancel {β : Fin l → Type u} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (v w : Vec β) : v + w + w = v := by
  rw [add_assoc, vec_add_self, add_zero]

lemma vec_add_add_add_cancel_mid {β : Fin l → Type u} [∀ i, Fintype (β i)]
    [∀ i, DecidableEq (β i)] (a b c : Vec β) : a + b + (b + c) = a + c := by
  rw [add_assoc, ← add_assoc b b c, vec_add_self, zero_add]

lemma vec_add_add_add_cancel_right {β : Fin l → Type u} [∀ i, Fintype (β i)]
    [∀ i, DecidableEq (β i)] (a b c : Vec β) : a + b + (c + b) = a + c := by
  rw [add_add_add_comm, vec_add_self, add_zero]

lemma odd_nsmul_vec {β : Fin l → Type u} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    {m : ℕ} (hm : Odd m) (w : Vec β) : m • w = w := by
  obtain ⟨k, rfl⟩ := hm
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, vec_add_self, nsmul_zero, zero_add]

lemma hammingNorm_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ZMod 2) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  unfold hammingNorm
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro i
  simp only [mem_filter, mem_univ, true_and, mem_union, Pi.add_apply]
  intro h
  by_contra hc
  push Not at hc
  exact h (by rw [hc.1, hc.2, add_zero])

lemma sum_ite_or {U : Type*} [Fintype U] [DecidableEq U] {M : Type*} [AddCommMonoid M]
    {u u' : U} (h : u ≠ u') (g : U → M) :
    ∑ w, (if w = u ∨ w = u' then g w else 0) = g u + g u' := by
  rw [← Finset.sum_filter]
  have : univ.filter (fun w => w = u ∨ w = u') = {u, u'} := by ext; simp
  rw [this, Finset.sum_pair h]

lemma sum_four_le {U : Type*} [Fintype U] [DecidableEq U] (m : U → ℕ) {a b a' b' : U}
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (ha'b' : a' ≠ b') :
    m a + m b + m a' + m b' ≤ ∑ u, m u := by
  have hsub : ∑ u ∈ ({a, b, a', b'} : Finset U), m u ≤ ∑ u, m u :=
    Finset.sum_le_sum_of_subset (subset_univ _)
  rw [Finset.sum_insert (by simp [hab, haa', hab']), Finset.sum_insert (by simp [hba', hbb']),
    Finset.sum_insert (by simp [ha'b']), Finset.sum_singleton] at hsub
  omega

/-! ### Base case: the zero-dimensional grid -/

section zero

variable {α₀ : Fin 0 → Type u} [∀ i, Fintype (α₀ i)] [∀ i, DecidableEq (α₀ i)]

lemma cubeSum_zero_dim (z : Vec α₀) (a b : Pt α₀) : cubeSum z a b = z a := by
  unfold cubeSum
  rw [Fintype.sum_unique]
  simp only [IsEmpty.forall_iff, if_true]
  congr 1
  exact Subsingleton.elim _ _

lemma mem_lineSpan_zero_dim (z : Vec α₀) (hz : ∀ a b, CubeNondeg a b → cubeSum z a b = 0) :
    z ∈ lineSpan α₀ := by
  have : z = 0 := by
    funext x
    have h := hz x x (fun j => j.elim0)
    rwa [cubeSum_zero_dim] at h
  rw [this]; exact zero_mem _

end zero

/-! ### Slicing along the first coordinate -/

section slice

variable {α : Fin (l + 1) → Type u} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- The slice of `z` at first coordinate `v`. -/
def slice (z : Vec α) (v : α 0) : Vec (fun i => α i.succ) := fun y => z (Fin.cons v y)

/-- `w ⊗ δ_v`: `w` placed in the slice `v`, zero elsewhere. -/
def extend (v : α 0) (w : Vec (fun i => α i.succ)) : Vec α :=
  fun x => if x 0 = v then w (Fin.tail x) else 0

/-- `w ⊗ 1`: `w` repeated in every slice. -/
def const (w : Vec (fun i => α i.succ)) : Vec α := fun x => w (Fin.tail x)

@[simp] lemma slice_apply (z : Vec α) (v : α 0) (y) : slice z v y = z (Fin.cons v y) := rfl

@[simp] lemma extend_cons (v u : α 0) (w : Vec (fun i => α i.succ)) (y) :
    extend v w (Fin.cons u y) = if u = v then w y else 0 := by
  simp [extend]

@[simp] lemma const_cons (u : α 0) (w : Vec (fun i => α i.succ)) (y) :
    const w (Fin.cons u y) = w y := by
  simp [const]

lemma sum_cons {M : Type*} [AddCommMonoid M] (g : Pt α → M) :
    ∑ x, g x = ∑ v, ∑ y, g (Fin.cons v y) := by
  rw [← (Fin.consEquiv α).sum_comp g, Fintype.sum_prod_type]
  rfl

lemma hammingNorm_eq_sum_slices (z : Vec α) :
    hammingNorm z = ∑ v, hammingNorm (slice z v) := by
  unfold hammingNorm
  simp only [Finset.card_filter]
  rw [sum_cons]
  rfl

/-- Decomposition of `z` into its slices, relative to a base slice `v₀`. -/
lemma decomp (v₀ : α 0) (z : Vec α) :
    z = (∑ v, extend v (slice z v + slice z v₀)) + const (slice z v₀) := by
  funext x
  refine Fin.consCases (fun u y => ?_) x
  simp only [Pi.add_apply, Finset.sum_apply, extend_cons, const_cons, slice_apply]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, if_true]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma extend_line (v : α 0) (i : Fin l) (c : Pt fun i => α i.succ) :
    extend v (line i c) = line i.succ (Fin.cons v c) := by
  funext x
  refine Fin.consCases (fun u y => ?_) x
  simp only [extend_cons, line, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ne_eq,
    (Fin.succ_ne_zero i).symm, not_false_eq_true, Fin.succ_inj, true_implies]
  by_cases hu : u = v
  · simp [hu]
  · simp [hu]

lemma extend_mem (v : α 0) {w : Vec (fun i => α i.succ)}
    (hw : w ∈ lineSpan (fun i => α i.succ)) : extend v w ∈ lineSpan α := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨i, c⟩, rfl⟩ := hw
    rw [extend_line]
    exact line_mem_lineSpan _ _
  | zero =>
    have : extend v (0 : Vec (fun i => α i.succ)) = 0 := by
      funext x; simp [extend]
    rw [this]; exact zero_mem _
  | add w w' _ _ hw hw' =>
    have : extend v (w + w') = extend v w + extend v w' := by
      funext x; simp only [extend, Pi.add_apply]; split_ifs <;> simp
    rw [this]; exact add_mem hw hw'
  | smul a w _ hw =>
    have : extend v (a • w) = a • extend v w := by
      funext x; simp only [extend, Pi.smul_apply]; split_ifs <;> simp
    rw [this]; exact Submodule.smul_mem _ _ hw

lemma const_mem (v₀ : α 0) (w : Vec (fun i => α i.succ)) : const w ∈ lineSpan α := by
  have : const w = ∑ c, w c • line 0 (Fin.cons v₀ c) := by
    funext x
    refine Fin.consCases (fun u y => ?_) x
    simp only [const_cons, Finset.sum_apply, Pi.smul_apply, line, Fin.forall_fin_succ,
      Fin.cons_zero, Fin.cons_succ, ne_eq, not_true_eq_false, false_implies, true_and,
      Fin.succ_ne_zero, not_false_eq_true, true_implies, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    have : ∀ c : Pt (fun i => α i.succ), (∀ j, y j = c j) ↔ c = y := by
      intro c; rw [eq_comm, funext_iff]
    simp_rw [this]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, if_true]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (line_mem_lineSpan _ _)

/-- If all pairwise sums of slices lie in the smaller line span, `z` lies in the line span. -/
lemma mem_lineSpan_of_slices (v₀ : α 0) {z : Vec α}
    (h : ∀ v, slice z v + slice z v₀ ∈ lineSpan (fun i => α i.succ)) : z ∈ lineSpan α := by
  rw [decomp v₀ z]
  exact add_mem (Submodule.sum_mem _ fun v _ => extend_mem v (h v)) (const_mem v₀ _)

/-! #### Boxes and cubes under slicing -/

lemma Nondeg_succ (i : Fin l) (u u' : α 0) (a b : Pt fun i => α i.succ) :
    Nondeg i.succ (Fin.cons u a) (Fin.cons u' b) ↔ u ≠ u' ∧ Nondeg i a b := by
  simp [Nondeg, Fin.forall_fin_succ, (Fin.succ_ne_zero i).symm]

lemma Nondeg_zero (u u' : α 0) (a b : Pt fun i => α i.succ) :
    Nondeg 0 (Fin.cons u a) (Fin.cons u' b) ↔ CubeNondeg a b := by
  simp [Nondeg, CubeNondeg, Fin.forall_fin_succ]

lemma CubeNondeg_cons (u u' : α 0) (a b : Pt fun i => α i.succ) :
    CubeNondeg (Fin.cons u a) (Fin.cons u' b) ↔ u ≠ u' ∧ CubeNondeg a b := by
  simp [CubeNondeg, Fin.forall_fin_succ]

lemma boxSum_succ (z : Vec α) (i : Fin l) {u u' : α 0} (huu' : u ≠ u')
    (a b : Pt fun i => α i.succ) :
    boxSum z i.succ (Fin.cons u a) (Fin.cons u' b) = boxSum (slice z u + slice z u') i a b := by
  unfold boxSum
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ne_eq,
    (Fin.succ_ne_zero i).symm, not_false_eq_true, true_implies, Fin.succ_inj]
  by_cases hy : ∀ j, ¬ j = i → y j = a j ∨ y j = b j
  · simp only [eq_true hy, and_true, if_true]
    rw [sum_ite_or huu']
    rfl
  · simp [hy]

lemma boxSum_zero (z : Vec α) (u u' : α 0) (a b : Pt fun i => α i.succ) :
    boxSum z 0 (Fin.cons u a) (Fin.cons u' b) = cubeSum (∑ v, slice z v) a b := by
  unfold boxSum cubeSum
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ne_eq, not_true_eq_false,
    false_implies, true_and, Fin.succ_ne_zero, not_false_eq_true, true_implies,
    Finset.sum_apply, slice_apply]
  by_cases hy : ∀ j, y j = a j ∨ y j = b j
  · simp [hy]
  · simp [hy]

lemma cubeSum_cons (z : Vec α) {u u' : α 0} (huu' : u ≠ u') (a b : Pt fun i => α i.succ) :
    cubeSum z (Fin.cons u a) (Fin.cons u' b) = cubeSum (slice z u + slice z u') a b := by
  unfold cubeSum
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases hy : ∀ j, y j = a j ∨ y j = b j
  · simp only [eq_true hy, and_true, if_true]
    rw [sum_ite_or huu']
    rfl
  · simp [hy]

lemma Cent_slices {z : Vec α} (hz : Cent z) {u u' : α 0} (huu' : u ≠ u') :
    Cent (slice z u + slice z u') := by
  intro i a b hab
  rw [← boxSum_succ z i huu']
  exact hz _ _ _ ((Nondeg_succ i u u' a b).2 ⟨huu', hab⟩)

lemma sum_slices_mem_of_Cent {z : Vec α} (hz : Cent z) (v₀ : α 0)
    (ih : ∀ w : Vec (fun i => α i.succ),
      (∀ a b, CubeNondeg a b → cubeSum w a b = 0) → w ∈ lineSpan (fun i => α i.succ)) :
    ∑ v, slice z v ∈ lineSpan (fun i => α i.succ) := by
  refine ih _ fun a b hab => ?_
  rw [← boxSum_zero z v₀ v₀]
  exact hz _ _ _ ((Nondeg_zero v₀ v₀ a b).2 hab)

end slice

/-! ### Cube kernel equals line span -/

theorem mem_lineSpan_of_cubeSum : ∀ (l : ℕ) (α : Fin l → Type u) [∀ i, Fintype (α i)]
    [∀ i, DecidableEq (α i)] [∀ i, Nonempty (α i)] (z : Vec α),
    (∀ a b, CubeNondeg a b → cubeSum z a b = 0) → z ∈ lineSpan α := by
  intro l
  induction l with
  | zero => intro α _ _ _ z hz; exact mem_lineSpan_zero_dim z hz
  | succ l ih =>
    intro α _ _ _ z hz
    let v₀ : α 0 := Classical.arbitrary _
    refine mem_lineSpan_of_slices v₀ fun v => ?_
    by_cases hv : v = v₀
    · subst hv; rw [vec_add_self]; exact zero_mem _
    · refine ih (fun i => α i.succ) _ fun a b hab => ?_
      rw [← cubeSum_cons z hv]
      exact hz _ _ ((CubeNondeg_cons v v₀ a b).2 ⟨hv, hab⟩)

/-! ### The weight bound -/

section star

variable {α : Fin (l + 1) → Type u} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- The star case: if all slices other than `u₀` are pairwise gauge-equivalent, parity of the
side length forces `z` into the line span. -/
lemma mem_lineSpan_of_star {z : Vec α} (hodd : Odd (Fintype.card (α 0) - 1))
    (hsum : ∑ v, slice z v ∈ lineSpan (fun i => α i.succ)) (u₀ : α 0)
    (hstar : ∀ u u', u ≠ u₀ → u' ≠ u₀ → slice z u + slice z u' ∈ lineSpan (fun i => α i.succ)) :
    z ∈ lineSpan α := by
  have hnt : Nontrivial (α 0) := Fintype.one_lt_card_iff_nontrivial.1 (by
    have := hodd.pos; omega)
  obtain ⟨u₁, hu₁⟩ := exists_ne u₀
  set D := lineSpan (fun i => α i.succ)
  -- the sum over the slices other than `u₀`
  have hT : ∑ v ∈ univ.erase u₀, (slice z v + slice z u₁) ∈ D :=
    Submodule.sum_mem _ fun v hv => hstar v u₁ (Finset.ne_of_mem_erase hv) hu₁
  have hsplit : ∑ v, slice z v = slice z u₀ + ∑ v ∈ univ.erase u₀, slice z v :=
    (Finset.add_sum_erase _ _ (mem_univ _)).symm
  have hrest : ∑ v ∈ univ.erase u₀, slice z v
      = ∑ v ∈ univ.erase u₀, (slice z v + slice z u₁) + slice z u₁ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ, odd_nsmul_vec hodd, vec_add_add_cancel]
  have h01 : slice z u₀ + slice z u₁ ∈ D := by
    have : slice z u₀ + slice z u₁ =
        (∑ v, slice z v) - ∑ v ∈ univ.erase u₀, (slice z v + slice z u₁) := by
      rw [hsplit, hrest]; abel
    rw [this]; exact Submodule.sub_mem _ hsum hT
  refine mem_lineSpan_of_slices u₀ fun u => ?_
  by_cases hu : u = u₀
  · subst hu; rw [vec_add_self]; exact zero_mem _
  · rw [← vec_add_add_add_cancel_right (slice z u) (slice z u₁) (slice z u₀)]
    exact add_mem (hstar u u₁ hu hu₁) h01

end star

theorem two_pow_le_hammingNorm : ∀ (l : ℕ) (α : Fin l → Type u) [∀ i, Fintype (α i)]
    [∀ i, DecidableEq (α i)],
    (∀ i, Even (Fintype.card (α i)) ∧ 4 ≤ Fintype.card (α i)) →
    ∀ z : Vec α, Cent z → z ∉ lineSpan α → 2 ^ l ≤ hammingNorm z := by
  intro l
  induction l with
  | zero =>
    intro α _ _ _ z _ hz
    have : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
    rw [pow_zero]
    exact Nat.one_le_iff_ne_zero.2 fun h => this (hammingNorm_eq_zero.1 h)
  | succ l ih =>
    intro α _ _ hα z hcent hz
    have hne : ∀ i, Nonempty (α i) := fun i =>
      Fintype.card_pos_iff.1 (by have := (hα i).2; omega)
    set D := lineSpan (fun i => α i.succ)
    -- gauge equivalence of slices
    let R : α 0 → α 0 → Prop := fun u u' => slice z u + slice z u' ∈ D
    have Rrefl : ∀ u, R u u := fun u => by
      show slice z u + slice z u ∈ D; rw [vec_add_self]; exact zero_mem _
    have Rsymm : ∀ {u u'}, R u u' → R u' u := fun {u u'} h => by
      show _ ∈ D; rw [add_comm]; exact h
    have Rtrans : ∀ {u u' u''}, R u u' → R u' u'' → R u u'' := fun {u u' u''} h h' => by
      show slice z u + slice z u'' ∈ D
      rw [← vec_add_add_add_cancel_mid (slice z u) (slice z u') (slice z u'')]
      exact add_mem h h'
    -- the parity of the first side
    have hodd : Odd (Fintype.card (α 0) - 1) :=
      Nat.Even.sub_odd (by have := (hα 0).2; omega) (hα 0).1 odd_one
    have hsum : ∑ v, slice z v ∈ D :=
      sum_slices_mem_of_Cent hcent (Classical.arbitrary _)
        (fun w hw => mem_lineSpan_of_cubeSum l (fun i => α i.succ) w hw)
    -- weight of a bad pair
    have hpair : ∀ {u u'}, ¬ R u u' →
        2 ^ l ≤ hammingNorm (slice z u) + hammingNorm (slice z u') := by
      intro u u' h
      have huu' : u ≠ u' := fun e => h (e ▸ Rrefl u)
      exact le_trans (ih (fun i => α i.succ) (fun i => hα i.succ) _ (Cent_slices hcent huu') h)
        (hammingNorm_add_le _ _)
    -- from two disjoint bad pairs
    have hfour : ∀ {a b a' b' : α 0}, a ≠ a' → a ≠ b' → b ≠ a' → b ≠ b' →
        ¬ R a b → ¬ R a' b' → 2 ^ (l + 1) ≤ hammingNorm z := by
      intro a b a' b' haa' hab' hba' hbb' hab ha'b'
      rw [hammingNorm_eq_sum_slices, pow_succ, mul_two]
      have h1 := hpair hab
      have h2 := hpair ha'b'
      have h3 := sum_four_le (fun v => hammingNorm (slice z v))
        (fun e => hab (by rw [e]; exact Rrefl b)) haa' hab' hba' hbb'
        (fun e => ha'b' (by rw [e]; exact Rrefl b'))
      dsimp only at h3
      omega
    -- a bad pair exists
    obtain ⟨u₀, u₁, hu, h01⟩ : ∃ u₀ u₁, u₀ ≠ u₁ ∧ ¬ R u₀ u₁ := by
      by_contra hcon
      push Not at hcon
      refine hz (mem_lineSpan_of_slices (Classical.arbitrary _) fun v => ?_)
      by_cases hv : v = Classical.arbitrary (α 0)
      · rw [hv]; exact Rrefl _
      · exact hcon v _ hv
    -- two further slices
    have hS : 1 < ((univ.erase u₀).erase u₁).card := by
      rw [Finset.card_erase_of_mem (mem_erase.2 ⟨hu.symm, mem_univ _⟩),
        Finset.card_erase_of_mem (mem_univ _), Finset.card_univ]
      have := (hα 0).2; omega
    obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 hS
    simp only [mem_erase, mem_univ, and_true] at hr hr'
    obtain ⟨hr1, hr0⟩ := hr
    obtain ⟨hr'1, hr'0⟩ := hr'
    -- either two disjoint inequivalent pairs exist, or one of `u₀, u₁` is the center of a star
    by_cases hbad : ∃ s s', s ≠ u₀ ∧ s ≠ u₁ ∧ s' ≠ u₀ ∧ s' ≠ u₁ ∧ ¬ R s s'
    · obtain ⟨s, s', hs0, hs1, hs'0, hs'1, hss'⟩ := hbad
      exact hfour hs0.symm hs'0.symm hs1.symm hs'1.symm h01 hss'
    · push Not at hbad
      by_cases h0r : R u₀ r
      · exfalso
        refine hz (mem_lineSpan_of_star hodd hsum u₁ fun u u' hu1 hu'1 => ?_)
        have key : ∀ u, u ≠ u₁ → R u r := fun u hu1 => by
          by_cases hu0 : u = u₀
          · rw [hu0]; exact h0r
          · exact hbad u r hu0 hu1 hr0 hr1
        exact Rtrans (key u hu1) (Rsymm (key u' hu'1))
      · by_cases h1r' : R u₁ r'
        · exfalso
          refine hz (mem_lineSpan_of_star hodd hsum u₀ fun u u' hu0 hu'0 => ?_)
          have key : ∀ u, u ≠ u₀ → R u r' := fun u hu0 => by
            by_cases hu1 : u = u₁
            · rw [hu1]; exact h1r'
            · exact hbad u r' hu0 hu1 hr'0 hr'1
          exact Rtrans (key u hu0) (Rsymm (key u' hu'0))
        · exact hfour hu hr'0.symm hr1 hrr' h0r h1r'

end Grid
