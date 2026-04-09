import Smt
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.InformationTheory.Hamming

noncomputable instance Submodule_set_fintype (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance

def Matrix.rowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) := (Submodule.span γ (Set.range M.row))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M.row i ∈ M.rowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma Submodule.mem_span_range_iff_sum {α : Type*} [Fintype α] {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n → (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by
  sorry

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
  sorry

lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  sorry

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
  sorry
