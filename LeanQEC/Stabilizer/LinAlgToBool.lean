import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.CSS


def I_to_vec (n d : ℕ) (I : ℕ → ℕ) : Fin n → (ZMod 2) :=
  fun i => if (∃ j, j < d ∧ I j = i) then 1 else 0

-- need to extract the nonzero indices...
def vec_to_I {n} [NeZero n] (v : Fin n -> ZMod 2) (i : ℕ) : ℕ := sorry

lemma Finset.vec_inner_product_eq_inner_product
  {n k d j : ℕ} {I : ℕ → ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)} (hj : j < k) :
  vec_inner_product n (indexed_by I d) (M.castnat.castbool j) =
  Bool.ofNat ((M.row ⟨j, hj⟩) ⬝ᵥ (I_to_vec n d I)).val := by
  sorry

lemma Bool.ofNat_ZMod2_false {x : ZMod 2} : Bool.ofNat x.val = false ↔ x = 0 := by
  unfold Bool.ofNat
  simp

lemma Bool.ofNat_ZMod2_true {x : ZMod 2} : Bool.ofNat x.val = true ↔ x = 1 := by
  unfold Bool.ofNat
  fin_cases x <;> simp

lemma Finset.fold_true_to_prop {n : ℕ} {p : ℕ → Bool}:
  (Finset.range n).fold and true p = true ↔ ∀ i, i < n → (p i = true) := by
  constructor
  · intro hf i hi
    by_contra!
    rw [←Bool.eq_false_iff] at this
    have range_eq : range n = insert i (range n \ {i})
    · symm
      apply Finset.insert_sdiff_self_of_mem
      apply Finset.mem_range.2 hi
    rw [range_eq, Finset.fold_insert, this] at hf
    · simp at hf
    exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self _)
  intro h_p
  induction' n with n ih
  · simp only [range_zero, fold_empty]
  rw [Finset.fold_range_add_one, Bool.and_eq_true]
  refine ⟨h_p n (by aesop), ih (fun x hx => h_p x ?_)⟩
  apply lt_of_lt_of_le hx (Nat.le_succ _)


lemma Finset.fold_false_to_prop {n : ℕ} {p : ℕ → Bool}:
  (Finset.range n).fold or false p = true ↔ ∃ i, i < n ∧ (p i = true) := by
  constructor
  · rintro hf
    induction' n with n ih
    · simp at hf
    rw [Finset.fold_range_add_one, Bool.or_eq_true] at hf
    rcases hf with hf | hf
    · refine ⟨n, ⟨Nat.lt_succ_self _, hf⟩⟩
    rcases (ih hf) with ⟨i, ile, hi⟩
    refine ⟨i, ⟨lt_of_lt_of_le ile (Nat.le_succ _), hi⟩⟩
  rintro ⟨i, ile, hi⟩
  have range_eq : range n = insert i (range n \ {i})
  · symm
    apply Finset.insert_sdiff_self_of_mem
    apply Finset.mem_range.2 ile
  rw [range_eq, Finset.fold_insert, Bool.or_eq_true]
  · exact Or.inl hi
  exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self _)

instance {n : ℕ} : Fintype ((Fin n) → (ZMod 2)) := by infer_instance

lemma mem_ker_iff {n k d : ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)} {I : ℕ → ℕ} :
  mem_ker_bool k n M.castnat.castbool (indexed_by I d) = true ↔
  (I_to_vec n d I) ∈ LinearMap.ker M.toLin' := by
  unfold mem_ker_bool
  simp [Finset.fold_true_to_prop]
  unfold Matrix.mulVec
  simp
  constructor
  · intro hp
    ext x
    dsimp
    have:= hp x.1 x.2
    rw [Finset.vec_inner_product_eq_inner_product, Bool.ofNat_ZMod2_false] at this
    exact this
  intro hp i hi
  rw [Finset.vec_inner_product_eq_inner_product, Bool.ofNat_ZMod2_false]
  rw [funext_iff] at hp
  convert (hp ⟨i, hi⟩)
  assumption

lemma Matrix.mem_rowSpace_ZMod2 {n₁ n₂ : ℕ}
  {M : Matrix (Fin n₁) (Fin n₂) (ZMod 2)}
  {x : Fin n₂ → (ZMod 2)} :
  x ∈ M.rowSpace ↔
  ∃ (S : Finset ((Fin n₂) → (ZMod 2))),
    S ⊆ (Finset.image M.row Finset.univ) ∧ S.sum id = x := by
  unfold Matrix.rowSpace
  rw [←@Set.coe_toFinset _ (Set.range M.row)]
  rw [Submodule.mem_span_finset]
  constructor
  · rintro ⟨f, ⟨fsupp, fsum⟩⟩
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Function.support_subset_iff, ne_eq, Set.mem_range] at fsupp
    let S := (Set.range M.row).toFinset.filter (fun i => f i = 1)
    use S
    constructor
    · simp [S]
    unfold S
    convert fsum using 1
    have h_union : (Set.range M.row).toFinset = ({x | f x = 1} : Finset _) ∪ ({x | f x = 0} : Finset _) := sorry
    nth_rw 2 [h_union]
    rw [Finset.sum_union]
    · /-
      have hzero : ∑ x with f x = 0, f x • x = 0 := by
        apply Finset.sum_eq_zero
        aesop
      rw [hzero, add_zero]
      -/
      sorry
      /-
      have hone : ∑ x with f x = 1, f x • x = ∑ x with f x = 1, x := by
        rw [Finset.sum_filter]
        have : ∀ a, (if f a = 1 then (f a • a) else 0) = ( if f a = 1 then a else 0) := by
          intro a
          by_cases hfa : f a = 1
          · simp [hfa]
          simp [hfa]
        simp_rw [this, ←Finset.sum_filter]


      rw [hone]
      simp only [id_eq, Set.toFinset_range]
      congr 1
      apply subset_antisymm
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi.2
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases fsupp x _ with ⟨y, hy⟩
      refine ⟨⟨y, hy⟩, hx⟩
      -/
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    intro a ha b hb hf
    rw [hf, hb] at ha
    norm_num at ha
  sorry


lemma Matrix.ZMod_sum_dotprod_exists {n₁ n₂ : ℕ} {S : Finset (Fin n₁)} {f : Fin n₁ → (Fin n₂ → (ZMod 2))}
  {x₁ x₂ : Fin n₂ → (ZMod 2)} (hsum : S.sum f = x₁) (hprod : x₁ ⬝ᵥ x₂ = 1) : ∃ r ∈ S, (f r) ⬝ᵥ x₂ = 1 := sorry


lemma not_mem_rowspace_iff {n k₁ k₂ d : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  {I : ℕ → ℕ}
  (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin'))) :
  not_mem_rowspace k₂ n M₂.castnat.castbool (indexed_by I d) = true ↔
  (I_to_vec n d I) ∉ M₁.rowSpace := by
  rw [not_mem_rowspace_iff_exists_mem_ker]
  unfold not_mem_rowspace
  simp [Finset.fold_false_to_prop]

  constructor
  · rintro ⟨i, ⟨hi₁, hi₂⟩⟩
    rw [Finset.vec_inner_product_eq_inner_product] at hi₂
    refine ⟨M₂.row ⟨i, hi₁⟩, ⟨?_, ?_⟩⟩
    · rw [←Matrix.toLin'_apply, ←LinearMap.mem_ker, ←hK]
      exact Matrix.row_mem_rowSpace
    rw [Bool.ofNat_ZMod2_true] at hi₂
    exact hi₂
  rintro ⟨y, ⟨hy₁, hy₂⟩⟩
  sorry

/-
lemma norm_of_is_index {n d : ℕ} {I : ℕ → ℕ}
  (h_ind : is_index_bool I d n = true) : hammingNorm (I_to_vec n d I) = d := by
  unfold is_index_bool at h_ind
  rw [Bool.and_eq_true, Finset.fold_true_to_prop, Finset.fold_true_to_prop] at h_ind
  simp only [decide_eq_true_eq] at h_ind
  unfold hammingNorm I_to_vec
  let ind_set := (Finset.range d).image I
  have hinj : Set.InjOn I ↑(Finset.range d) := sorry
  have h_ind : ind_set.card = d
  · rw [←@Finset.card_range d]
    apply Finset.card_image_iff.2 hinj
  convert h_ind
  simp
  rw [Finset.card_filter]
  sorry
  -/

lemma norm_of_is_index (n d : ℕ) (I : ℕ → ℕ)
  (is_index: is_index_bool I d n) :
  hammingNorm (I_to_vec n d I) <= d := by
  sorry

lemma hamming_ge_min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (v : Fin n → ZMod 2)
  (h_ker : v ∉ M₂.rowSpace)
  (h_ker : v ∈ LinearMap.ker (Matrix.toLin' M₁)) :
  hammingNorm v ≥ min_weight_ker_not_mem_rowspace M₁ M₂ := by
  --have hnorm := norm_of_is_index hind
  /-
  have hnorm₂ : min_weight_ker_not_mem_rowspace M₁ M₂ ≤ hammingNorm (I_to_vec n (min_weight_ker_not_mem_rowspace M₁ M₂ - 1) I) := by
    apply Finset.min'_le
    apply Finset.mem_image_of_mem
    rw [Set.mem_toFinset]
    refine ⟨⟨hker, hrs⟩, ?_⟩
    rw [Set.notMem_singleton_iff]
    intro h_f
    rw [h_f] at hnorm
    simp [hammingNorm] at hnorm
    sorry --i messed up here, figure out edge case constraint...
  rw [hnorm] at hnorm₂
  apply absurd (Nat.lt_of_le_sub_one _ hnorm₂) (by aesop)
  exact min_weight_ker_not_mem_rowspace_pos
  -/
  sorry

-- This is the completeness side
-- i.e. our SAT formula accepts the true distance
lemma dist_index_x_le_complete {n k₁ k₂ k₃ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  {K₂ : Matrix (Fin k₃) (Fin n) (ZMod 2)}
  (hK : K₂.rowSpace = (LinearMap.ker M₂.toLin')) :
  let dist := min_weight_ker_not_mem_rowspace M₁ M₂
  dist_index_le n k₁ k₃ (M₁.castnat.castbool) (K₂.castnat.castbool) dist := by
  unfold dist_index_le
  intro dist I
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  by_contra
  push_neg at this
  simp only [ne_eq, Bool.not_eq_false] at this
  rcases this with ⟨⟨hind, hker⟩, hrs⟩
  have vec_hamming_le: hammingNorm (I_to_vec n (dist - 1) I) <= (dist - 1) := by
    apply norm_of_is_index
    assumption
  rw [not_mem_rowspace_iff hK] at hrs
  rw [mem_ker_iff] at hker
  suffices: hammingNorm (I_to_vec n (dist - 1) I) ≥ dist
  · have (a b : ℕ) : (b > 0) -> (a ≤ b - 1) -> (a ≥ b) -> False
    · smt
    apply (this (hammingNorm (I_to_vec n (dist - 1) I)) dist)
    · apply min_weight_ker_not_mem_rowspace_pos
    · assumption
    · assumption
  apply hamming_ge_min_weight_ker_not_mem_rowspace
  · assumption
  · assumption
