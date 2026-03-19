import LeanQEC.Classical_EC.Basic --need fintype instance for Codespace


def Matrix.rowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) := (Submodule.span γ (Set.range M.row))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M.row i ∈ M.rowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

noncomputable def min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : ℕ :=
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    LinearMap.ker M₁.toLin' \ M₂.rowSpace
  let nontrivial_errors := (undetectable_errors \ {0}).toFinset
  match Finset.min (Finset.image hammingNorm nontrivial_errors) with
  | ⊤ => n + 1
  | some a => a

lemma min_weight_ker_not_mem_rowspace_pos {n k₁ k₂ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} :
  --{hne : (((LinearMap.ker M₁.toLin') \ M₂.rowSpace : Set (Fin n → (ZMod 2))) \ {0}).toFinset.Nonempty} :
  0 < min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  by_contra
  have hz := Nat.eq_zero_of_not_pos this
  /-
  rw [Finset.min'_eq_iff, Finset.mem_image] at hz
  rcases hz with ⟨⟨a, ⟨a_mem, a_norm⟩⟩, _⟩
  rw [hammingNorm_eq_zero] at a_norm
  rw [a_norm, Set.mem_toFinset, Set.mem_diff_singleton] at a_mem
  apply absurd rfl a_mem.2
  -/
  sorry


lemma mem_ker_iff_dotProd_rows_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M.row i) ⬝ᵥ x = 0 := sorry

lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∉ M.rowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := sorry

lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := sorry

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
  · sorry
  rw [hsum, Finset.card_eq_sum_ones]
  sorry



--lemma ex_mem_finset_non_orth_iff_sat
