import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.CSS
--import LeanQEC.Stabilizer.LinAlgToBoolHelper

def I_to_vec (n d : ℕ) (I : ℕ → ℕ) : Fin n → (ZMod 2) :=
  fun i => if (∃ j, j < d ∧ I j = i) then 1 else 0

-- need to extract the nonzero indices...
def vec_to_I {n} [NeZero n] (v : Fin n -> ZMod 2) (i : ℕ) : ℕ :=
  let support := ((Finset.univ.filter (fun j : Fin n => v j = 1)).sort (· ≤ ·)).map Fin.val
  if h : i < support.length then support[i] else (if h2 : 0 < support.length then support[support.length - 1] else 0)

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
  constructor <;> intro hx' <;> simp_all +decide [Matrix.rowSpace]
  · refine' Submodule.span_induction _ _ _ _ hx'
    · exact fun x hx => ⟨{x}, by aesop⟩
    · exact ⟨∅, Finset.empty_subset _, rfl⟩
    · rintro x y hx hy ⟨S, hS₁, hS₂⟩ ⟨T, hT₁, hT₂⟩
      use S \ T ∪ T \ S
      simp_all +decide [Finset.subset_iff, Finset.sum_union]
      rw [Finset.sum_union]
      · rw [← hS₂, ← hT₂,
          ← Finset.sum_sdiff (Finset.inter_subset_left : S ∩ T ⊆ S),
          ← Finset.sum_sdiff (Finset.inter_subset_right : S ∩ T ⊆ T)]
        simp +decide [Finset.sum_add_distrib]; ring!; aesop
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
    · rintro a x hx ⟨S, hS₁, hS₂⟩
      fin_cases a <;> simp_all +decide [Finset.sum_smul]
      · exact ⟨∅, by norm_num⟩
      · use S
  · exact hx'.choose_spec.2 ▸ Submodule.sum_mem _ fun y hy =>
      Submodule.subset_span <| Set.mem_range.mpr <| by
        have := hx'.choose_spec.1 hy; aesop

lemma Matrix.ZMod_sum_dotprod_exists {n₁ n₂ : ℕ} {S : Finset (Fin n₁)} {f : Fin n₁ → (Fin n₂ → (ZMod 2))}
  {x₁ x₂ : Fin n₂ → (ZMod 2)} (hsum : S.sum f = x₁) (hprod : x₁ ⬝ᵥ x₂ = 1) : ∃ r ∈ S, (f r) ⬝ᵥ x₂ = 1 := sorry

private lemma sum_id_dotProduct_eq {n : ℕ} (S : Finset (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
  S.sum id ⬝ᵥ x = S.sum (fun s => s ⬝ᵥ x) := by
  induction' S using Finset.induction_on with a s ha ih
  · simp [dotProduct]
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, id, add_dotProduct]; congr 1

private lemma exists_dotProduct_one_of_sum
  {n : ℕ} {S : Finset (Fin n → ZMod 2)} {y x : Fin n → ZMod 2}
  (hS_sum : S.sum id = y) (hy : y ⬝ᵥ x = 1) :
  ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_contra h_all
  push_neg at h_all
  have h_zero : ∀ s ∈ S, s ⬝ᵥ x = 0 := by
    intro s hs
    rcases Fin.exists_fin_two.mp ⟨s ⬝ᵥ x, rfl⟩ with h | h
    · exact h
    · exact absurd h (h_all s hs)
  have : S.sum id ⬝ᵥ x = 0 := by
    rw [sum_id_dotProduct_eq]
    exact Finset.sum_eq_zero (fun s hs => h_zero s hs)
  rw [hS_sum] at this
  exact absurd this (by rw [hy]; decide)

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
  have hy_ker : y ∈ LinearMap.ker M₁.toLin' := hy₁
  have hy_rs : y ∈ M₂.rowSpace := hK ▸ hy_ker
  rw [Matrix.mem_rowSpace_ZMod2] at hy_rs
  obtain ⟨S, hS_sub, hS_sum⟩ := hy_rs
  obtain ⟨s, hs_mem, hs_dot⟩ := exists_dotProduct_one_of_sum hS_sum hy₂
  have hs_row := hS_sub hs_mem
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs_row
  obtain ⟨i, hi⟩ := hs_row
  refine ⟨i.val, i.isLt, ?_⟩
  rw [Finset.vec_inner_product_eq_inner_product (hj := i.isLt), Bool.ofNat_ZMod2_true]
  simp only [Fin.eta]
  rw [hi]
  exact hs_dot

lemma norm_of_is_index (n d : ℕ) (I : ℕ → ℕ)
  (is_index: is_index_bool I d n) :
  hammingNorm (I_to_vec n d I) <= d := by
  unfold hammingNorm I_to_vec
  have h_card : Finset.card (Finset.filter (fun i => ∃ j < d, I j = i) (Finset.range n)) ≤ d := by
    exact le_trans (Finset.card_le_card (show Finset.filter (fun i => ∃ j < d, I j = i)
      (Finset.range n) ⊆ Finset.image I (Finset.range d) by aesop_cat))
      (Finset.card_image_le.trans (by simpa))
  convert h_card using 1
  rw [Finset.card_filter, Finset.card_filter]
  rw [Finset.sum_range]; aesop

lemma hamming_ge_min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (v : Fin n → ZMod 2)
  (h_not_rs : v ∉ M₂.rowSpace)
  (h_ker : v ∈ LinearMap.ker (Matrix.toLin' M₁)) :
  hammingNorm v ≥ min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  simp +zetaDelta at *
  convert Finset.min_le _
  any_goals exact hammingNorm v
  rotate_left
  exact inferInstance
  exact Finset.image hammingNorm ((LinearMap.ker M₁.toLin' : Set (Fin n → ZMod 2)).toFinset \
    (M₂.rowSpace : Set (Fin n → ZMod 2)).toFinset)
  · aesop
  · cases h : Finset.min (Finset.image hammingNorm ((LinearMap.ker M₁.toLin' : Set (Fin n → ZMod 2)).toFinset \
      (M₂.rowSpace : Set (Fin n → ZMod 2)).toFinset)) <;>
      simp_all +decide [Finset.min_le]
    exact absurd (h h_ker) h_not_rs

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
