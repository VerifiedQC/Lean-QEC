import LeanQEC.Classical_EC.Basic --need fintype instance for Codespace
import Smt

def Matrix.rowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) := (Submodule.span γ (Set.range M.row))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M.row i ∈ M.rowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

-- rowspace already contains the zero vector
-- no need to remove it again
noncomputable def min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : ℕ :=
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    (LinearMap.ker M₁.toLin' \ M₂.rowSpace)
  match Finset.min (Finset.image hammingNorm undetectable_errors.toFinset) with
  | ⊤ => n + 1
  | some a => a

lemma min_weight_ker_not_mem_rowspace_pos {n k₁ k₂ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} :
  0 < min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  extract_lets undetectable_errors
  rcases h: (Finset.image hammingNorm undetectable_errors.toFinset).min with _ | m'
  · simp
  simp only
  apply Finset.mem_of_min at h
  simp only [Finset.mem_image] at h
  rcases h with ⟨nontrivial_error, h, rfl⟩
  by_contra
  apply Nat.eq_zero_of_not_pos at this
  rw [hammingNorm_eq_zero] at this
  subst this undetectable_errors
  simp at h

lemma mem_ker_iff_dotProd_rows_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M.row i) ⬝ᵥ x = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro hx i
    have := congrFun hx i
    simpa [Matrix.mulVec, dotProduct] using this
  · intro hx
    ext i
    simpa [Matrix.mulVec, dotProduct] using hx i

lemma ZMod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∉ M.rowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  have hkerdual : LinearMap.ker M.toLin' = CodeSpace.dualCode M.rowSpace := by
    ext y
    constructor
    · intro hy
      rw [CodeSpace.dualCode, Submodule.mem_orthogonalBilin_iff]
      intro z hz
      unfold Matrix.rowSpace at hz
      refine Submodule.span_induction
        (p := fun z _ => (dotProductBilin (ZMod 2) (ZMod 2)).IsOrtho z y) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        simpa [LinearMap.IsOrtho, dotProductBilin] using
          (mem_ker_iff_dotProd_rows_eq_zero M y).1 hy i
      · simp [LinearMap.IsOrtho, dotProductBilin]
      · intro z₁ z₂ hz₁ hz₂ h₁ h₂
        have hz₁zero : z₁ ⬝ᵥ y = 0 := by
          simpa [LinearMap.IsOrtho, dotProductBilin] using h₁
        have hz₂zero : z₂ ⬝ᵥ y = 0 := by
          simpa [LinearMap.IsOrtho, dotProductBilin] using h₂
        simp [LinearMap.IsOrtho, dotProductBilin, dotProduct_add, hz₁zero, hz₂zero]
      · intro a z hz hzy
        fin_cases a <;> simpa [LinearMap.IsOrtho, dotProductBilin, hzy]
    · intro hy
      rw [mem_ker_iff_dotProd_rows_eq_zero]
      intro i
      have hrow := hy (M.row i) Matrix.row_mem_rowSpace
      simpa [CodeSpace.dualCode, LinearMap.IsOrtho, dotProductBilin] using hrow
  constructor
  · intro hx
    by_contra h
    have hxdual : x ∈ CodeSpace.dualCode (LinearMap.ker M.toLin') := by
      rw [CodeSpace.dualCode, Submodule.mem_orthogonalBilin_iff]
      intro y hy
      have hyne : y ⬝ᵥ x ≠ 1 := by
        intro hyx
        exact h ⟨y, hy, hyx⟩
      rcases ZMod2_eq_zero_or_eq_one (y ⬝ᵥ x) with hy0 | hy1
      · exact hy0
      · exact False.elim (hyne hy1)
    apply hx
    rwa [hkerdual, dual_dual_eq] at hxdual
  · rintro ⟨y, hy, hyx⟩ hx
    have hxdual : x ∈ CodeSpace.dualCode (LinearMap.ker M.toLin') := by
      rwa [hkerdual, dual_dual_eq]
    rw [CodeSpace.dualCode, Submodule.mem_orthogonalBilin_iff] at hxdual
    have hzero := hxdual y hy
    have : (1 : ZMod 2) = 0 := by
      simpa [LinearMap.IsOrtho, dotProductBilin] using hyx.symm.trans hzero
    exact one_ne_zero this

lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_cases hS : ∃ s ∈ S, s ⬝ᵥ x = 1
  · rcases hS with ⟨s, hs, hsx⟩
    refine ⟨s, Submodule.mem_span_of_mem hs, ?_⟩
    constructor
    · intro _
      exact ⟨s, hs, hsx⟩
    · intro _
      exact hsx
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    constructor
    · intro hzero
      have : (1 : ZMod 2) = 0 := by simpa using hzero.symm
      exact False.elim (one_ne_zero this)
    · intro hs
      exact False.elim (hS hs)

lemma exists_mem_submodule_non_orth_iff_exists_mem_basis_non_orth {n : ℕ}
  (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2)) :
  (∃ y ∈ Submodule.span (ZMod 2) S, y ⬝ᵥ x = 1) ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_contra hS
    have hzero : ∀ z ∈ Submodule.span (ZMod 2) S, z ⬝ᵥ x = 0 := by
      intro z hz
      refine Submodule.span_induction
        (p := fun z _ => z ⬝ᵥ x = 0) ?_ ?_ ?_ ?_ hz
      · intro s hs
        have hsne : s ⬝ᵥ x ≠ 1 := by
          intro hsx
          exact hS ⟨s, hs, hsx⟩
        rcases ZMod2_eq_zero_or_eq_one (s ⬝ᵥ x) with h0 | h1
        · exact h0
        · exact False.elim (hsne h1)
      · simp
      · intro z₁ z₂ hz₁ hz₂ h₁ h₂
        rw [add_dotProduct, h₁, h₂]
        simp
      · intro a z hz hzx
        fin_cases a <;> simpa [hzx]
    exact one_ne_zero (hyx.symm.trans (hzero y hy))
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, Submodule.mem_span_of_mem hs, hsx⟩

def finsetOr {α : Type*} (S : Finset α) (f : α → Prop) := S.fold (· ∨ ·) False f

lemma finsetOr_iff_exists {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Prop) :
  (∃ a ∈ S, f a) ↔ finsetOr S f := by
  constructor
  · rintro ⟨a, ha₁, ha₂⟩
    unfold finsetOr
    rw [←(Finset.insert_eq_of_mem ha₁), Finset.fold_insert_idem]
    apply Or.inl ha₂
  · contrapose!
    intro h_f
    induction S using Finset.induction_on with
    | empty => simp [finsetOr]
    | insert a s ha ih =>
      simp [finsetOr]
      refine' ⟨h_f a (Finset.mem_insert_self _ _), ?_⟩
      apply ih
      intro x xs
      apply h_f _ (Finset.mem_insert_of_mem xs)


lemma weight_le_disj {n k : ℕ} {z : Fin n → (ZMod 2)} : hammingNorm z ≤ k ↔ ∑ i, (z i).1 ≤ k := by
  simp [hammingNorm]
  suffices heq : Finset.card {i | ¬(z i) = 0} = ∑ i, (z i).1
  · rw [heq]
  have hsum : ∑ i, (z i).1 = ∑ i ∈ {i | ¬(z i) = 0}, (z i).1
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hz : z i = 0 <;> simp [hz]
  rw [hsum, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hz : z i ≠ 0 := by
    simpa using hi
  rcases ZMod2_eq_zero_or_eq_one (z i) with h0 | h1
  · exact False.elim (hz h0)
  · simpa [h1]



--lemma ex_mem_finset_non_orth_iff_sat
