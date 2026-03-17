import LeanQEC.Stabilizer.Basic
import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlgSMT

def forget {a b : ℕ} [NeZero a] [NeZero b]
  (M : Matrix (Fin a) (Fin b) (ZMod 2)) :
  Matrix ℕ ℕ Bool :=
  Matrix.of (fun i j =>
    if i < a && j < b then
      M (Fin.ofNat a i) (Fin.ofNat b j) == 1
    else false)

def kergen_correct {a b n : ℕ}
  (M : Matrix (Fin a) (Fin b) (ZMod 2))
  (gen : Fin n -> Fin b -> ZMod 2) : Prop :=
  LinearMap.ker M.toLin' =
  Submodule.span (ZMod 2) (Finset.image gen Finset.univ)

theorem sat_translation_correct
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xkergen : Fin (n - k₁) → Fin n → ZMod 2)
  (xkergen_correct : kergen_correct css.H₁ xkergen)
  (zkergen : Fin (n - k₂) → Fin n → ZMod 2)
  (zkergen_correct : kergen_correct css.H₂ zkergen)
  (dist : ℕ) :
  let _ : NeZero (k₁ + k₂) := by
    rcases css with ⟨_, _, _, _, _, _, _, gt0_k₁⟩
    constructor; smt [gt0_k₁]
  let bsm := css.toBSM
  dist_index_le n k₁ (n - k₂) (forget bsm.X) (forget (Matrix.of zkergen)) dist →
  dist_index_le n k₂ (n - k₁) (forget bsm.Z) (forget (Matrix.of xkergen)) dist →
  dist ≤ bsm.distance (by apply NeZero.pos) := by
  sorry
