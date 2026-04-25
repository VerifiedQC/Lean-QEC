import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.CSS

def I_to_vec (n d : ℕ) (I : ℕ → ℕ) : Fin n → (ZMod 2) :=
  fun i => if (∃ j, j < d ∧ I j = i) then 1 else 0

-- need to extract the nonzero indices...
def vec_to_I {n} [NeZero n] (v : Fin n -> ZMod 2) (i : ℕ) : ℕ :=
  let support := ((Finset.univ.filter (fun j : Fin n => v j = 1)).sort (· ≤ ·)).map Fin.val
  if h : i < support.length then support[i] else (if h2 : 0 < support.length then support[support.length - 1] else 0)

lemma Bool.ofNat_ZMod2_false {x : ZMod 2} : Bool.ofNat x.val = false ↔ x = 0 := by
  unfold Bool.ofNat
  simp

lemma Bool.ofNat_ZMod2_true {x : ZMod 2} : Bool.ofNat x.val = true ↔ x = 1 := by
  unfold Bool.ofNat
  fin_cases x <;> simp

lemma Bool.ofNat_ZMod2_mul (x y : ZMod 2) :
  Bool.and (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x * y).val) := by
  fin_cases x <;> fin_cases y <;> decide

lemma Finset.vec_inner_product_eq_sum_range
  {n : ℕ} {v₁ v₂ : ℕ → Bool} {w₁ w₂ : ℕ → ZMod 2}
  (h₁ : ∀ i, i < n → v₁ i = Bool.ofNat (w₁ i).val)
  (h₂ : ∀ i, i < n → v₂ i = Bool.ofNat (w₂ i).val) :
  vec_inner_product n v₁ v₂ =
    Bool.ofNat ((Finset.sum (Finset.range n) fun i => w₁ i * w₂ i).val) := by
  induction n with
  | zero =>
      simp [vec_inner_product]
  | succ n ih =>
      rw [vec_inner_product, Finset.fold_range_add_one, Finset.sum_range_succ]
      rw [h₁ n (Nat.lt_succ_self _), h₂ n (Nat.lt_succ_self _)]
      have ih' :=
        ih (fun i hi => h₁ i (Nat.lt_succ_of_lt hi)) (fun i hi => h₂ i (Nat.lt_succ_of_lt hi))
      have hfold :
          fold xor false (fun i => v₁ i && v₂ i) (Finset.range n) =
            Bool.ofNat ((Finset.sum (Finset.range n) fun i => w₁ i * w₂ i).val) := by
        simpa [vec_inner_product] using ih'
      rw [hfold]
      rw [Bool.ofNat_ZMod2_mul, Bool.ofNat_ZMod2_add]
      congr 1
      abel_nf

lemma Finset.vec_inner_product_eq_inner_product
  {n k d j : ℕ} {I : ℕ → ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)} (hj : j < k) :
  vec_inner_product n (indexed_by I d) (M.castnat.castbool j) =
  Bool.ofNat ((M.row ⟨j, hj⟩) ⬝ᵥ (I_to_vec n d I)).val := by
  let w₁ : ℕ → ZMod 2 := fun i => if hi : i < n then I_to_vec n d I ⟨i, hi⟩ else 0
  let w₂ : ℕ → ZMod 2 := fun i => M.castnat j i
  rw [Finset.vec_inner_product_eq_sum_range
    (w₁ := w₁) (w₂ := w₂)]
  · have hsum :
        Finset.sum (Finset.range n) (fun i => w₁ i * w₂ i) =
          (M.row ⟨j, hj⟩) ⬝ᵥ (I_to_vec n d I) := by
      calc
        Finset.sum (Finset.range n) (fun i => w₁ i * w₂ i)
            = Finset.sum (Finset.range n) (fun i => w₂ i * w₁ i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
        _ = ∑ i : Fin n, w₂ i * w₁ i := by
              symm
              exact Fin.sum_univ_eq_sum_range (fun i => w₂ i * w₁ i) n
        _ = (M.row ⟨j, hj⟩) ⬝ᵥ (I_to_vec n d I) := by
              simp [dotProduct, w₁, w₂, Matrix.castnat, hj]
    rw [hsum]
  · intro i hi
    by_cases hex : ∃ r, r < d ∧ I r = i
    · have hvec : I_to_vec n d I ⟨i, hi⟩ = 1 := by
        simp [I_to_vec, hex]
      have hexFin : ∃ k : Fin d, i = I k := by
        rcases hex with ⟨r, hr, hri⟩
        exact ⟨⟨r, hr⟩, by simpa [eq_comm] using hri⟩
      have hind : indexed_by I d i = true := by
        simpa [indexed_by_correct] using hexFin
      have hw₁ : Bool.ofNat (w₁ i).val = true := by
        simp [Bool.ofNat, w₁, hi, hvec]
      rw [hw₁]
      exact hind
    · have hvec : I_to_vec n d I ⟨i, hi⟩ = 0 := by
        simp [I_to_vec, hex]
      have hnot : ¬ ∃ k : Fin d, i = I k := by
        rintro ⟨k, hik⟩
        exact hex ⟨k, k.2, by simpa [eq_comm] using hik⟩
      have hind : indexed_by I d i = false := by
        cases hidx : indexed_by I d i with
        | false =>
            rfl
        | true =>
            exfalso
            have hexFin : ∃ k : Fin d, i = I k := by
              simpa [indexed_by_correct] using hidx
            exact hnot hexFin
      have hw₁ : Bool.ofNat (w₁ i).val = false := by
        simp [Bool.ofNat, w₁, hi, hvec]
      rw [hw₁]
      exact hind
  · intro i hi
    rfl

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
      simp_all +decide [Finset.subset_iff]
      rw [Finset.sum_union]
      · rw [← hS₂, ← hT₂,
          ← Finset.sum_sdiff (Finset.inter_subset_left : S ∩ T ⊆ S),
          ← Finset.sum_sdiff (Finset.inter_subset_right : S ∩ T ⊆ T)]
        simp +decide; ring_nf!; aesop
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
    · rintro a x hx ⟨S, hS₁, hS₂⟩
      fin_cases a <;> simp_all +decide
      · exact ⟨∅, by norm_num⟩
      · use S
  · exact hx'.choose_spec.2 ▸ Submodule.sum_mem _ fun y hy =>
      Submodule.subset_span <| Set.mem_range.mpr <| by
        have := hx'.choose_spec.1 hy; aesop

lemma Matrix.ZMod_sum_dotprod_exists {n₁ n₂ : ℕ} {S : Finset (Fin n₁)} {f : Fin n₁ → (Fin n₂ → (ZMod 2))}
  {x₁ x₂ : Fin n₂ → (ZMod 2)} (hsum : S.sum f = x₁) (hprod : x₁ ⬝ᵥ x₂ = 1) : ∃ r ∈ S, (f r) ⬝ᵥ x₂ = 1 := by
  by_contra h_all
  push_neg at h_all
  have h_zero : ∀ r ∈ S, (f r) ⬝ᵥ x₂ = 0 := by
    intro r hr
    rcases Fin.exists_fin_two.mp ⟨(f r) ⬝ᵥ x₂, rfl⟩ with h | h
    · exact h
    · exact absurd h (h_all r hr)
  have hsum_zero : S.sum f ⬝ᵥ x₂ = 0 := by
    suffices hsum_zero_aux :
        ∀ T : Finset (Fin n₁), (∀ r ∈ T, (f r) ⬝ᵥ x₂ = 0) → T.sum f ⬝ᵥ x₂ = 0 by
      exact hsum_zero_aux S h_zero
    intro T
    induction' T using Finset.induction_on with a s ha ih
    · intro _
      simp [dotProduct]
    · intro hT_zero
      have hs_zero : ∀ r ∈ s, (f r) ⬝ᵥ x₂ = 0 := by
        intro r hr
        exact hT_zero r (Finset.mem_insert_of_mem hr)
      have ha_zero : (f a) ⬝ᵥ x₂ = 0 := hT_zero a (Finset.mem_insert_self _ _)
      simpa [Finset.sum_insert ha, add_dotProduct, ha_zero] using ih hs_zero
  have hprod_ne : x₁ ⬝ᵥ x₂ ≠ 0 := by
    rw [hprod]
    decide
  exact hprod_ne (hsum ▸ hsum_zero)

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
  -- (is_index: is_index_bool I d n)
  : hammingNorm (I_to_vec n d I) <= d := by
  unfold hammingNorm I_to_vec
  have h_card : Finset.card (Finset.filter (fun i => ∃ j < d, I j = i) (Finset.range n)) ≤ d := by
    exact le_trans (Finset.card_le_card (show Finset.filter (fun i => ∃ j < d, I j = i)
      (Finset.range n) ⊆ Finset.image I (Finset.range d) by aesop_cat))
      (Finset.card_image_le.trans (by simp))
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
      simp_all +decide
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
    -- assumption
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
