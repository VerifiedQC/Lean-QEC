import LeanQEC.Stabilizer.Basic
import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.LinAlgToBool

def forget {a b : ℕ} [NeZero a] [NeZero b]
  (M : Matrix (Fin a) (Fin b) (ZMod 2)) :
  Matrix ℕ ℕ Bool :=
  Matrix.of (fun i j =>
    if i < a && j < b then
      M (Fin.ofNat a i) (Fin.ofNat b j) = 1
    else false)

def kergen_correct {a b n : ℕ}
  (M : Matrix (Fin a) (Fin b) (ZMod 2))
  (gen : Fin n -> Fin b -> ZMod 2) : Prop :=
  LinearMap.ker M.toLin' =
  Submodule.span (ZMod 2) (Finset.image gen Finset.univ)

-- special handling for edge case
-- minimum taken over empty set gives default value
lemma dist_index_le_empty
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : ℕ)
  (is_empty : ¬∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace) :
  ¬(dist_index_le n k₁ (n - k₂)
    (forget H₁) (forget (Matrix.of H₂_kergen)) dist) := by
  sorry

-- property of minimum
-- if minimum is less than a certain number, then there exists a witness
lemma dist_index_some
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : ℕ)
  (non_empty : ∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ∃x, x ∈ LinearMap.ker H₁.toLin' /\
    x ∉ H₂.rowSpace /\ hammingNorm x < dist := by
  sorry

lemma dist_index_le_sound_contrapositive
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : ℕ)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ¬(dist_index_le n k₁ (n - k₂)
    (forget H₁) (forget (Matrix.of H₂_kergen)) dist) := by
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    LinearMap.ker H₁.toLin' \ H₂.rowSpace
  by_cases (undetectable_errors = ∅)
  · apply dist_index_le_empty
    · assumption
    -- boilerplate
    -- empty set => does not exist element
    sorry
  let exists_vec := dist_index_some H₁ H₂ H₂_kergen H₂_kergen_correct dist (by
    -- more boilerplate
    -- nonempty set => exists element
    sorry
  ) hdist
  rcases exists_vec with ⟨x, ker_x, rowspace_x, hamming_x⟩
  unfold dist_index_le
  push_neg; simp only
  exists (vec_to_I x)
  simp
  constructor
  · constructor
    · -- vec_to_I outputs correct index fn
      sorry
    · have: forget H₁ = H₁.castnat.castbool
      · sorry
      rw [this]
      rw [mem_ker_iff]
      -- TODO I_to_vec and vec_to_I are inverses
      sorry
  · have: forget (Matrix.of H₂_kergen) = (Matrix.of H₂_kergen).castnat.castbool
    · -- low level nonsense
      sorry
    rw [this]
    rw [not_mem_rowspace_iff]
    · -- TODO I_to_vec and vec_to_I are inverses
      sorry
    unfold kergen_correct at H₂_kergen_correct
    rw [H₂_kergen_correct]
    aesop

lemma dist_index_le_sound
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : ℕ)
  (test_dist : dist_index_le n k₁ (n - k₂)
    (forget H₁) (forget (Matrix.of H₂_kergen)) dist) :
  dist ≤ min_weight_ker_not_mem_rowspace H₁ H₂ := by
  by_contra
  suffices: ¬(dist_index_le n k₁ (n - k₂) (forget H₁) (forget (Matrix.of H₂_kergen)) dist)
  · simp_all only
  apply dist_index_le_sound_contrapositive
  · assumption
  · simp_all only [not_le, gt_iff_lt]

theorem sat_translation_correct
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xkergen : Fin (n - k₁) → Fin n → ZMod 2)
  (xkergen_correct : kergen_correct css.H₁ xkergen)
  (zkergen : Fin (n - k₂) → Fin n → ZMod 2)
  (zkergen_correct : kergen_correct css.H₂ zkergen)
  (dist : ℕ) :
  let _ : NeZero (k₁ + k₂) := by
    rcases css with ⟨_, _, _, _, _, _, _, gt0_k₁⟩
    constructor; smt [gt0_k₁]
  dist_index_le n k₁ (n - k₂) (forget css.H₁) (forget (Matrix.of zkergen)) dist →
  dist_index_le n k₂ (n - k₁) (forget css.H₂) (forget (Matrix.of xkergen)) dist →
  dist ≤ css.toBSM.distance (by apply NeZero.pos) := by
  simp only
  intros h₁ h₂
  rw [CSS.toBSM_dist_eq]
  rcases css with ⟨C₁, C₂, _, H₁, H₂⟩
  simp only [CSS_pair.dX, CSS_pair.dZ
    ] at xkergen_correct zkergen_correct h₁ h₂ ⊢
  apply le_min
  · apply dist_index_le_sound
    · exact xkergen_correct
    · assumption
  · apply dist_index_le_sound
    · exact zkergen_correct
    · assumption
