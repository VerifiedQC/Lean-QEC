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
  exact ⟨ fun h i => by simpa [ Matrix.mulVec, dotProduct ] using congr_fun h i, fun h => by ext i; simpa [ Matrix.mulVec, dotProduct ] using h i ⟩


lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∉ M.rowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  refine' ⟨ _, fun h => _ ⟩;
  · intro hx;
    contrapose! hx with h;
    have h_double_orthogonal : ∀ y : Fin n → ZMod 2, (∀ z ∈ (M.rowSpace : Submodule (ZMod 2) (Fin n → ZMod 2)), z ⬝ᵥ y = 0) → y ⬝ᵥ x = 0 := by
      intro y hy
      have hy_ker : y ∈ LinearMap.ker (Matrix.toLin' M) := by
        ext i; specialize hy ( M.row i ) ( Submodule.subset_span ( Set.mem_range_self i ) ) ; aesop;
      cases Fin.exists_fin_two.mp ⟨ y ⬝ᵥ x, rfl ⟩ <;> aesop;
    contrapose! h_double_orthogonal;
    obtain ⟨y, hy⟩ : ∃ y : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, y x ≠ 0 ∧ ∀ z ∈ M.rowSpace, y z = 0 := by
      exact Submodule.exists_le_ker_of_notMem h_double_orthogonal
    -- Since $y$ is a linear functional, there exists a vector $z$ such that $y(w) = w \cdot z$ for all $w$.
    obtain ⟨z, hz⟩ : ∃ z : Fin n → ZMod 2, ∀ w : Fin n → ZMod 2, y w = w ⬝ᵥ z := by
      use fun i => y ( Pi.single i 1 );
      intro w; erw [ y.pi_apply_eq_sum_univ ] ; simp +decide [ dotProduct ] ;
      exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop;
    exact ⟨ z, fun w hw => by simpa [ hz ] using hy.2 w hw, by simpa [ hz, dotProduct_comm ] using hy.1 ⟩;
  · obtain ⟨ y, hy₁, hy₂ ⟩ := h;
    -- By definition of row space, if $x$ is in the row space of $M$, then there exists a vector $z$ such that $x = M^T z$.
    by_contra h_contra
    obtain ⟨z, hz⟩ : ∃ z : Fin k → ZMod 2, x = M.transpose.mulVec z := by
      convert Submodule.mem_span_range_iff_exists_fun _ |>.1 h_contra using 1;
      ext; simp +decide [ funext_iff, Matrix.mulVec, dotProduct ] ;
      simp +decide only [mul_comm, eq_comm];
    simp_all +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose ]

lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
    by_cases h : ∃ s ∈ S, s ⬝ᵥ x = 1 <;> simp_all +decide [ Submodule.mem_span ];
    · exact ⟨ h.choose, fun p hp => hp h.choose_spec.1, h.choose_spec.2 ⟩;
    · use 0; aesop;

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
  ·
    rw [ Finset.sum_filter_of_ne ] ; aesop
  rw [hsum, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun x hx => by have := Fin.exists_fin_two.mp ⟨ z x, rfl ⟩ ; aesop;
