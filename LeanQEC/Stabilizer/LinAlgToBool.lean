import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.CSS
import Mathlib.Data.Finset.Sort

open scoped BigOperators


def I_to_vec (n d : ℕ) (I : ℕ → ℕ) : Fin n → (ZMod 2) :=
  fun i => if (∃ j, j < d ∧ I j = i) then 1 else 0

-- need to extract the nonzero indices...
def vec_to_I {n} [NeZero n] (v : Fin n -> ZMod 2) (i : ℕ) : ℕ :=
  let support : Finset (Fin n) := Finset.univ.filter fun j => v j ≠ 0
  if hi : i < support.card then
    support.orderEmbOfFin rfl ⟨i, hi⟩
  else if hs : support.Nonempty then
    support.max' hs
  else
    0

lemma Bool.ofNat_ZMod2_false {x : ZMod 2} : Bool.ofNat x.val = false ↔ x = 0 := by
  unfold Bool.ofNat
  simp

lemma Bool.ofNat_ZMod2_true {x : ZMod 2} : Bool.ofNat x.val = true ↔ x = 1 := by
  unfold Bool.ofNat
  fin_cases x <;> simp

lemma Bool.ofNat_ZMod2_mul (x y : ZMod 2) :
  Bool.and (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x * y).val) := by
  fin_cases x <;> fin_cases y <;> decide

lemma Bool.ofNat_ZMod2_add (x y : ZMod 2) :
  Bool.xor (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x + y).val) := by
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
      abel

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
  unfold Matrix.rowSpace
  constructor
  · rw [Submodule.mem_span_set]
    rintro ⟨c, hc, hsum⟩
    refine ⟨c.support, ?_, ?_⟩
    · intro y hy
      rcases hc hy with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rw [← hsum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro y hy
      have hcy : c y ≠ 0 := by
        exact Finsupp.mem_support_iff.mp hy
      rcases ZMod2_eq_zero_or_eq_one (c y) with h0 | h1
      · exact False.elim (hcy h0)
      · simpa [h1]
  · rintro ⟨S, hS, hsum⟩
    have hmem : S.sum (fun y => y) ∈ Submodule.span (ZMod 2) (Set.range M.row) := by
      exact (Submodule.span (ZMod 2) (Set.range M.row)).sum_mem (fun y hy => by
        apply Submodule.subset_span
        rcases Finset.mem_image.mp (hS hy) with ⟨i, -, rfl⟩
        exact Set.mem_range_self i)
    rw [← hsum]
    exact hmem


lemma Matrix.ZMod_sum_dotprod_exists {n₁ n₂ : ℕ} {S : Finset (Fin n₁)} {f : Fin n₁ → (Fin n₂ → (ZMod 2))}
  {x₁ x₂ : Fin n₂ → (ZMod 2)} (hsum : S.sum f = x₁) (hprod : x₁ ⬝ᵥ x₂ = 1) : ∃ r ∈ S, (f r) ⬝ᵥ x₂ = 1 := by
  let T : Set (Fin n₂ → ZMod 2) := Set.range (fun r : S => f r)
  have hx₁ : x₁ ∈ Submodule.span (ZMod 2) T := by
    have hsum_mem : S.sum f ∈ Submodule.span (ZMod 2) T := by
      exact (Submodule.span (ZMod 2) T).sum_mem (fun r hr =>
        Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩)
    simpa [hsum] using hsum_mem
  rcases
      (exists_mem_submodule_non_orth_iff_exists_mem_basis_non_orth
        (S := T) (x := x₂)).1 ⟨x₁, hx₁, hprod⟩ with
    ⟨y, ⟨r, rfl⟩, hyr⟩
  exact ⟨r, r.2, hyr⟩


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
  have hy_rowspace : y ∈ M₂.rowSpace := by
    rw [hK]
    exact hy₁
  have hrow :
      ∃ r ∈ Set.range M₂.row, r ⬝ᵥ (I_to_vec n d I) = 1 := by
    exact
      (exists_mem_submodule_non_orth_iff_exists_mem_basis_non_orth
        (S := Set.range M₂.row) (x := I_to_vec n d I)).1 ⟨y, hy_rowspace, hy₂⟩
  rcases hrow with ⟨r, ⟨i, rfl⟩, hi₂⟩
  refine ⟨i, ?_, ?_⟩
  · exact i.2
  · rw [Finset.vec_inner_product_eq_inner_product, Bool.ofNat_ZMod2_true]
    exact hi₂

lemma norm_of_is_index {n d : ℕ} {I : ℕ → ℕ}
  (h_ind : is_index_bool I d n = true) : hammingNorm (I_to_vec n d I) = d := by
  unfold is_index_bool at h_ind
  rw [Bool.and_eq_true, Finset.fold_true_to_prop, Finset.fold_true_to_prop] at h_ind
  simp only [decide_eq_true_eq] at h_ind
  unfold hammingNorm I_to_vec
  let ind_set := (Finset.range d).image I
  have hinj : Set.InjOn I ↑(Finset.range d) := by
    aesop
  have h_ind : ind_set.card = d
  · rw [←@Finset.card_range d]
    apply Finset.card_image_iff.2 hinj
  convert h_ind
  simp
  rw [Finset.card_filter]
  aesop

lemma norm_of_is_index (n d : ℕ) (I : ℕ → ℕ)
  (is_index: is_index_bool I d n) :
  hammingNorm (I_to_vec n d I) <= d := by
  classical
  rw [is_index_bool_correct] at is_index
  rw [Bool.and_eq_true] at is_index
  have hbounded : ∀ i : Fin d, I i < n := by
    simpa using is_index.1
  let support : Finset (Fin n) := Finset.univ.filter fun i => I_to_vec n d I i ≠ 0
  let imageI : Finset (Fin n) :=
    Finset.univ.image fun j : Fin d => ⟨I j, hbounded j⟩
  have hsupp_sub : support ⊆ imageI := by
    intro i hi
    have hi' : I_to_vec n d I i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hex : ∃ j, j < d ∧ I j = i := by
      by_contra hno
      have hzero : I_to_vec n d I i = 0 := by
        simp [I_to_vec, hno]
      exact hi' hzero
    rcases hex with ⟨j, hj, hji⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext hji
  have hsupp_le : support.card ≤ d := by
    calc
      support.card ≤ imageI.card := Finset.card_le_card hsupp_sub
      _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
      _ = Fintype.card (Fin d) := Finset.card_univ
      _ = d := Fintype.card_fin d
  unfold hammingNorm
  simpa [support]

lemma hamming_ge_min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (v : Fin n → ZMod 2)
  (hnot_row : v ∉ M₂.rowSpace)
  (hker_mem : v ∈ LinearMap.ker (Matrix.toLin' M₁)) :
  hammingNorm v ≥ min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  set undetectable_errors : Set (Fin n → ZMod 2) := LinearMap.ker M₁.toLin' \ M₂.rowSpace
  set s : Finset ℕ := Finset.image hammingNorm undetectable_errors.toFinset
  have hv_mem : v ∈ undetectable_errors.toFinset := by
    simp [undetectable_errors, hker_mem, hnot_row]
  have hv_img :
      hammingNorm v ∈ s := by
    simpa [s] using Finset.mem_image_of_mem hammingNorm hv_mem
  have hs : s.Nonempty := ⟨hammingNorm v, hv_img⟩
  have hmin : s.min' hs ≤ hammingNorm v := Finset.min'_le _ _ hv_img
  have hrew :
      (let undetectable_errors := (↑(LinearMap.ker M₁.toLin') : Set (Fin n → ZMod 2)) \ (↑M₂.rowSpace : Set (Fin n → ZMod 2))
       match (Finset.image hammingNorm undetectable_errors.toFinset).min with
       | ⊤ => n + 1
       | some a => a) = s.min' hs := by
    have := congrArg
      (fun m : WithTop ℕ =>
        match m with
        | ⊤ => n + 1
        | some a => a)
      (Finset.coe_min' hs).symm
    simpa [undetectable_errors, s] using this
  exact hrew.trans_le hmin

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
