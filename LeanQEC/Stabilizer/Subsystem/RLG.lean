import Mathlib
import LeanQEC.Stabilizer.Subsystem.Basic

structure RLG (l : ℕ) where
  q : Fin l → ℕ
  h_ge4 : ∀ i, 4 ≤ q i
  h_even : ∀ i, Even (q i)

namespace RLG
variable {l : ℕ} (r : RLG l)

def n : ℕ := ∏ i, r.q i

abbrev Coord := (i : Fin l) → Fin (r.q i)

/-- Coordinates are in bijection with `Fin r.n`. -/
def coordEquiv : r.Coord ≃ Fin r.n := finPiFinEquiv

theorem n_pos : 0 < r.n :=
  Finset.prod_pos fun i _ => by have := r.h_ge4 i; omega

end RLG
