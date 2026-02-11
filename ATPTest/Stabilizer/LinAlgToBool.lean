import ATPTest.Stabilizer.LinAlgSMT
import ATPTest.Stabilizer.CSS


def I_to_vec (n d : ℕ) (I : ℕ → ℕ) : Fin n → (ZMod 2) := fun i => if (indexed_by I d) i then 1 else 0

lemma not_mem_rowspace_iff {n k₁ k₂ d : ℕ} {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} {I : ℕ → ℕ}
  (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin'))) :

  not_mem_rowspace k₂ n M₂.castnat.castbool (indexed_by I d) = true ↔
  (I_to_vec n d I) ∉ M₁.rowSpace := sorry

lemma mem_ker_iff {n k d : ℕ} {M : Matrix (Fin k) (Fin n) (ZMod 2)} {I : ℕ → ℕ} :
  mem_ker_bool k n M.castnat.castbool (indexed_by I d) = true ↔
  (I_to_vec n d I) ∈ LinearMap.ker M.toLin' := sorry

lemma norm_of_is_index {n d : ℕ} {I : ℕ → ℕ}
  (h_ind : is_index_bool I d n = true) : 0 < hammingNorm (I_to_vec n d I) ∧ hammingNorm (I_to_vec n d I) ≤ d := sorry

theorem dist_index_x_le_iff_dist {n k₁ k₂ k₃ : ℕ} {M₁ : Matrix (Fin k₁)
 (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} {K₂ : Matrix (Fin k₃) (Fin n) (ZMod 2)}
  (hK : K₂.rowSpace = (LinearMap.ker M₂.toLin'))
  (hne : (((LinearMap.ker M₁.toLin') \ M₂.rowSpace : Set (Fin n → (ZMod 2))) \ {0}).toFinset.Nonempty):
  dist_index_le n k₁ k₃ (M₁.castnat.castbool) (K₂.castnat.castbool) (min_weight_ker_not_mem_rowspace M₁ M₂ hne) := by
  unfold dist_index_le
  intro I
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  by_contra
  push_neg at this
  simp only [ne_eq, Bool.not_eq_false] at this
  rcases this with ⟨⟨hind, hker⟩, hrs⟩
  rw [not_mem_rowspace_iff hK] at hrs
  rw [mem_ker_iff] at hker
  have hnorm := norm_of_is_index hind
  have hnorm₂ : min_weight_ker_not_mem_rowspace M₁ M₂ hne ≤ hammingNorm (I_to_vec n (min_weight_ker_not_mem_rowspace M₁ M₂ hne - 1) I) := by
    apply Finset.min'_le
    apply Finset.mem_image_of_mem
    rw [Set.mem_toFinset]
    refine ⟨⟨hker, hrs⟩, ?_⟩
    rw [Set.notMem_singleton_iff]
    intro h_f
    rw [h_f] at hnorm
    simp [hammingNorm] at hnorm
  rw [Nat.le_sub_one_iff_lt] at hnorm
  · linarith [hnorm, hnorm₂]
  exact min_weight_ker_not_mem_rowspace_pos
