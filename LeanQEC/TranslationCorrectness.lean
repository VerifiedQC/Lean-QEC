import LeanQEC.Stabilizer.Basic
import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlgSMT

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

lemma dist_index_le_correct
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : ℕ) :
  dist_index_le n k₁ (n - k₂) (forget H₁) (forget (Matrix.of H₂_kergen)) dist →
  dist ≤ min_weight_ker_not_mem_rowspace H₁ H₂ := by
  sorry

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
  · apply dist_index_le_correct
    · exact xkergen_correct
    · assumption
  · apply dist_index_le_correct
    · exact zkergen_correct
    · assumption
