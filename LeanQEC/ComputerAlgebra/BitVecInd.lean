import Mathlib.Data.BitVec

@[simp]
def nonzero_aux {r : ℕ} (coeffs : BitVec r) (i : ℕ) :=
  match i with
  | 0 => coeffs[0]!
  | i₀ + 1 => (coeffs[i]!) ∨ nonzero_aux coeffs i₀

@[simp]
def nonzero {r : ℕ} (coeffs : BitVec r) := nonzero_aux coeffs (r-1)

@[simp]
def dot_col_aux {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) (i : ℕ) :=
  let k := i * n + c
  match i with
  | 0 => coeffs[i]! && mat[k]!
  | i₀ + 1 => (coeffs[i]! && mat[k]!) ^^ dot_col_aux coeffs mat c i₀

@[simp]
def dot_col_zero {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  let dot := dot_col_aux coeffs mat c (r-1)
  !dot

@[simp]
def all_dot_zero_aux {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  match c with
  | 0 => dot_col_zero coeffs mat 0
  | c₀ + 1 => dot_col_zero coeffs mat c && all_dot_zero_aux coeffs mat c₀

@[simp]
def all_dot_zero {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) := all_dot_zero_aux coeffs mat (n-1)

def linear_indep_SAT {r n : ℕ} (mat : BitVec (r * n)) : Prop := ∀ coeffs, !(nonzero coeffs && all_dot_zero coeffs mat)
