import Mathlib

lemma raw_uphase_eq_is_1 {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  {u : Matrix T U ℂ} (ne0_u : u ≠ 0)
  {z : ℂ}
  (eq : z • u = u) :
  z = 1 := by sorry

lemma raw_phase_star_move (a b c : ℂ) (ne0_a : a ≠ 0) (ne0_b : b ≠ 0) :
  a * star b = c <-> a = b * c := by sorry

lemma raw_uphase_div {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  (z z' : ℂ) (u u' : Matrix T U ℂ) (ne0_z' : z' ≠ 0)
  (ne0_u' : u' ≠ 0)
  (eq : z • u = z' • u') :
  let r := z * star z'
  r • u = u' := by sorry
