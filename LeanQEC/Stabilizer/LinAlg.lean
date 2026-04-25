import Smt
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable instance Submodule_set_fintype (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance

def Matrix.rowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) := (Submodule.span γ (Set.range M.row))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M.row i ∈ M.rowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma Submodule.mem_span_range_iff_sum {α : Type*} [Fintype α] {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n → (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by
  refine' ⟨ fun hx => _, _ ⟩;
  · rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx;
    obtain ⟨ c, rfl ⟩ := hx; use Finset.univ.filter fun a => c a = 1; simp +decide [ Finsupp.sum_fintype ] ;
    rw [ Finset.sum_filter ] ; congr ; ext x ; rcases c x with ( _ | _ | c ) <;> norm_num ; tauto;
  · exact fun ⟨ S, hS ⟩ => hS ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ( Set.mem_range_self _ )

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

/-
Helper: backward direction - if y is in ker and y ⬝ x = 1, then x is not in rowSpace
-/
lemma ker_dotProduct_rowSpace_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (x : Fin n → ZMod 2)
    (hy : y ∈ LinearMap.ker M.toLin') (hx : x ∈ M.rowSpace) : y ⬝ᵥ x = 0 := by
  revert x;
  intro x hx; induction hx using Submodule.span_induction <;> simp_all +decide [ dotProduct ] ;
  · obtain ⟨ i, rfl ⟩ := ‹_›; simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ] ;
    simpa only [ mul_comm ] using hy i;
  · simp_all +decide [ mul_add, Finset.sum_add_distrib ];
  · rename_i a x hx ih; rw [ ← Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _ ] ; simp_all +decide [ ← Finset.mul_sum _ _ _ ] ;

lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
  convert f.pi_apply_eq_sum_univ v using 1;
  simp +decide [ dotProduct, mul_comm ];
  exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop;
-- Helper: if x ∉ rowSpace, we can construct a y in ker with y ⬝ x = 1
lemma exists_ker_dotProduct_eq_one_of_not_mem_rowSpace {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) (hx : x ∉ M.rowSpace) :
    ∃ y ∈ LinearMap.ker M.toLin', y ⬝ᵥ x = 1 := by
  unfold Matrix.rowSpace at hx
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Module.Free (ZMod 2) ((Fin n → ZMod 2) ⧸ Submodule.span (ZMod 2) (Set.range M.row)) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (ZMod 2) _)

  obtain ⟨f, hfx, hf_bot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    rw [dotProduct_comm]
    rw [← dual_eq_dotProduct]
    have : f (M.row i) ∈ Submodule.map f (Submodule.span (ZMod 2) (Set.range M.row)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))
    rw [hf_bot] at this
    exact (Submodule.mem_bot _).mp this
  · rw [← dual_eq_dotProduct]
    generalize h : f x = y
    fin_cases y <;> simp_all

lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∉ M.rowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  constructor
  · exact exists_ker_dotProduct_eq_one_of_not_mem_rowSpace M x
  · rintro ⟨y, hy_ker, hy_dot⟩ hx
    have := ker_dotProduct_rowSpace_eq_zero M y x hy_ker hx
    simp_all


lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_cases h : ∃ s ∈ S, s ⬝ᵥ x = 1;
  · exact ⟨ h.choose, Submodule.subset_span h.choose_spec.1, by simpa [ h.choose_spec.2 ] ⟩;
  · exact ⟨ 0, Submodule.zero_mem _, by simp +decide [ h ] ⟩

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
  simp +decide only [hammingNorm];
  rw [ Finset.card_filter ];
  exact iff_of_eq ( by congr; ext i; rcases z i with ( _ | _ | i ) <;> trivial )
