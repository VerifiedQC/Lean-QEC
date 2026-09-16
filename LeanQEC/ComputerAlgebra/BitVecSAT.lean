import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.BitVec
import LeanQEC.LinearAlgebra.RowspaceKernel
import Init.Data.BitVec.Basic

--locs : BitVec (k * nlog), where nlog is ceiling of log_2 n
@[simp]
def loc_constraints_ith_jth
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  ((locs.extractLsb' (j * nlog) nlog) = i)
  --obtain jth entry of locs, which is a BitVec of length nlog
  --and test it against i, which is a natural number

@[simp]
def loc_constraints_ith_jth_aux
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  match j with
  | 0 => loc_constraints_ith_jth locs i 0
  | j' + 1 => loc_constraints_ith_jth locs i j ∨
              loc_constraints_ith_jth_aux locs i j'

@[simp]
def loc_constraints_ith
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (i : ℕ) :=
  errs[i]! = loc_constraints_ith_jth_aux locs i (k-1)

@[simp]
def loc_constraints_aux
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (c : ℕ) :=
  match c with
  | 0 => loc_constraints_ith locs errs 0
  | c' + 1 =>
    loc_constraints_ith locs errs c ∧
    loc_constraints_aux locs errs c'

def loc_constraints
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n) :=
  loc_constraints_aux locs errs (n-1)

/--
The one-hot vector picked out by index slot `j` of `locs`: bit `locs[j]` set, everything else clear.
A slot naming a position at or past `n` shifts the bit out entirely and so contributes nothing,
which matches `loc_constraints`, where such a slot satisfies no `loc_constraints_ith`.
-/
def loc_slot {n nlog k : ℕ} (locs : BitVec (k * nlog)) (j : ℕ) : BitVec n :=
  (1 : BitVec n) <<< (locs.extractLsb' (j * nlog) nlog)

/-- Union of the one-hot vectors for slots `0 … c`. -/
def loc_union_aux {n nlog k : ℕ} (locs : BitVec (k * nlog)) (c : ℕ) : BitVec n :=
  match c with
  | 0 => loc_slot locs 0
  | c' + 1 => loc_slot locs c ||| loc_union_aux locs c'

/--
`errs` is exactly the set of positions named by the `k` index slots of `locs`, as a single bitvector
equation.

Equivalent to `loc_constraints` (`loc_constraints_iff_fast`), but `k` terms rather than `n * k`:
`loc_constraints` compares every slot against every position, where this shifts each slot into place
once. It is also a plain `BitVec` equation, so unlike `loc_constraints_ith` -- which equates a
`Bool` to a `Prop` and so needs a `Decidable` instance per position -- it costs no typeclass search.
-/
def loc_constraints_fast {n nlog k : ℕ} (locs : BitVec (k * nlog)) (errs : BitVec n) : Prop :=
  errs = loc_union_aux locs (k - 1)

def symmetry_constraints_aux
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (c : ℕ) (prev : BitVec nlog) : Bool :=
  let val := locs.extractLsb' (c * nlog) nlog
  match c with
  | 0 => val ≤ prev
  | c' + 1 => (val ≤ prev) && (symmetry_constraints_aux locs c' val)

def symmetry_constraints
  {nlog k : ℕ}
  (locs : BitVec (k * nlog)) :=
  symmetry_constraints_aux locs (k - 1) (BitVec.allOnes nlog)

def dot_product_aux {n : ℕ} [NeZero n] (x y : BitVec n) (c : ℕ) (hc : c < n) : Bool :=
  let b := x[c] && y[c]
  match c with
  | 0 => b
  | c' + 1 => b ^^ dot_product_aux x y c' (lt_of_le_of_lt (Nat.le_succ _) hc)

/--
XOR of bits `j, j+1, …, j+c-1` of `v`. Bits at or past the width count as `false`, which is what
lets `xorFold` be correct at every width rather than only at powers of two.
-/
def BitVec.xorRange {n : ℕ} (v : BitVec n) (j : ℕ) : ℕ → Bool
  | 0 => false
  | c + 1 => v.getLsbD j ^^ v.xorRange (j + 1) c

theorem BitVec.xorRange_add {n : ℕ} (v : BitVec n) :
    ∀ (a j b : ℕ), v.xorRange j (a + b) = (v.xorRange j a ^^ v.xorRange (j + a) b) := by
  intro a
  induction a with
  | zero => intro j b; simp [BitVec.xorRange]
  | succ a ih =>
    intro j b
    have hab : a + 1 + b = (a + b) + 1 := by omega
    have hj : j + 1 + a = j + (a + 1) := by omega
    rw [hab]
    simp only [BitVec.xorRange, ih (j + 1) b, hj]
    exact (Bool.xor_assoc _ _ _).symm

/-- A range starting at or past the width contributes nothing: every such bit is `false`. -/
theorem BitVec.xorRange_of_width_le {n : ℕ} (v : BitVec n) :
    ∀ (c j : ℕ), n ≤ j → v.xorRange j c = false := by
  intro c
  induction c with
  | zero => intro j _; rfl
  | succ c ih =>
    intro j hj
    simp [BitVec.xorRange, BitVec.getLsbD_of_ge v j hj, ih (j + 1) (by omega)]

/--
Halving XOR fold: bit `j` of `v.xorFold k` is the XOR of bits `j … j + 2^k - 1` of `v`, so once
`2^k ≥ n` bit `0` is the XOR of every bit of `v`.

Unfolding this costs `k = ⌈log₂ n⌉` steps where the bit-by-bit chain of `dot_product_aux` costs `n`.
That is the point of it: the `simp` that prepares a distance goal, and `bv_decide`'s own
normalization, are both proportional to the size of the term they are handed.
-/
def BitVec.xorFold {n : ℕ} (v : BitVec n) : ℕ → BitVec n
  | 0 => v
  | k + 1 => (v.xorFold k) ^^^ ((v.xorFold k) >>> (2 ^ k))

theorem BitVec.getLsbD_xorFold {n : ℕ} (v : BitVec n) :
    ∀ (k j : ℕ), (v.xorFold k).getLsbD j = v.xorRange j (2 ^ k) := by
  intro k
  induction k with
  | zero => intro j; simp [BitVec.xorFold, BitVec.xorRange]
  | succ k ih =>
    intro j
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hcomm : 2 ^ k + j = j + 2 ^ k := by omega
    simp only [BitVec.xorFold, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, ih, hcomm, hpow,
      BitVec.xorRange_add]

theorem dot_product_aux_eq_xorRange {n : ℕ} [NeZero n] (x y : BitVec n) :
    ∀ (c : ℕ) (hc : c < n), dot_product_aux x y c hc = (x &&& y).xorRange 0 (c + 1) := by
  intro c
  induction c with
  | zero =>
    intro hc
    show (x[0] && y[0]) = _
    simp [BitVec.xorRange, BitVec.getLsbD_eq_getElem hc]
  | succ c ih =>
    intro hc
    have hc' : c < n := Nat.lt_of_succ_lt hc
    show ((x[c + 1] && y[c + 1]) ^^ dot_product_aux x y c hc') = _
    rw [ih hc', BitVec.xorRange_add (x &&& y) (c + 1) 0 1]
    simp only [BitVec.xorRange, Nat.zero_add, BitVec.getLsbD_and,
      BitVec.getLsbD_eq_getElem hc, BitVec.getElem_and, Bool.xor_false]
    exact Bool.xor_comm _ _

/--
Parity of the bitwise AND, computed by the halving fold.

This is definitionally different from, but provably equal to (`BitVec.dot_product_eq_aux`), the
bit-by-bit XOR chain it replaces.
-/
def BitVec.dot_product {n : ℕ} [NeZero n] (x y : BitVec n) : Bool :=
  ((x &&& y).xorFold (Nat.clog 2 n)).getLsbD 0

theorem BitVec.dot_product_eq_aux {n : ℕ} [NeZero n] (x y : BitVec n) :
    x.dot_product y = dot_product_aux x y (n - 1) (Nat.sub_one_lt (NeZero.ne _)) := by
  have hn : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  have hsucc : n - 1 + 1 = n := Nat.sub_one_add_one (NeZero.ne n)
  rw [dot_product_aux_eq_xorRange x y (n - 1) (Nat.sub_one_lt (NeZero.ne _)), hsucc]
  show ((x &&& y).xorFold (Nat.clog 2 n)).getLsbD 0 = _
  rw [BitVec.getLsbD_xorFold]
  have hsplit : 2 ^ Nat.clog 2 n = n + (2 ^ Nat.clog 2 n - n) := by omega
  rw [hsplit, BitVec.xorRange_add,
    BitVec.xorRange_of_width_le (x &&& y) (2 ^ Nat.clog 2 n - n) (0 + n) (by omega)]
  simp

--updated definition to account for r unknown at runtime
def BitVec.row {n k : ℕ} (M : BitVec (k * n)) (r : ℕ) : BitVec n := (M >>> (r * n)).extractLsb' 0 n

def BitVec.row_bv {n k klog : ℕ} (M : BitVec (k * n)) (r : BitVec klog) : BitVec n := (M >>> ((r.zeroExtend (k * n) * (n : BitVec (k * n))))).extractLsb' 0 n



@[simp]
def parity_constraints_aux {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => !(errs.dot_product (stabs.row 0))
  | r' + 1 => !(errs.dot_product (stabs.row r)) ∧ parity_constraints_aux stabs errs r'


def parity_constraints {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) :=
  parity_constraints_aux stabs errs (stabdim-1)

@[simp]
def rowspace_constraints_aux
  {kerdim n : ℕ}
  [NeZero n]
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => (errs.dot_product (ker.row 0))
  | r' + 1 => (errs.dot_product (ker.row r)) ∨
      rowspace_constraints_aux ker errs r'

def rowspace_constraints
  {kerdim n : ℕ}
  [NeZero n]
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) :=
  rowspace_constraints_aux ker errs (kerdim - 1)

def lt_dist_sat
  {n stabdim kerdim : ℕ}
  [NeZero n]
  (stabs : BitVec (stabdim * n))
  (ker : BitVec (kerdim * n))
  (k nlog : ℕ) : Prop :=
  ∀ (locs : (BitVec (k * nlog))) (errs : BitVec n),
  ¬ (loc_constraints locs errs ∧ symmetry_constraints locs ∧ parity_constraints stabs errs ∧ rowspace_constraints ker errs)


def bitvec_mutually_orth
  {n k₁ k₂ : ℕ}
  [NeZero n]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n)) : Prop :=
  ∀ (i : BitVec (Nat.clog 2 k₁)) (j : BitVec (Nat.clog 2 k₂)), !((M₁.row_bv i).dot_product (M₂.row_bv j) && i < k₁ && j < k₂)

def mutually_orth_row_sat_aux
  {n k₁ k₂ : ℕ}
  [NeZero n]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n))
  (i j : ℕ) : Bool :=
  match j with
  | 0 => !((M₁.row i).dot_product (M₂.row 0))
  | j' + 1 => !((M₁.row i).dot_product (M₂.row j)) && mutually_orth_row_sat_aux M₁ M₂ i j'

def mutually_orth_sat_aux
  {n k₁ k₂ : ℕ}
  [NeZero n]
  [NeZero k₂]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n))
  (i : ℕ) : Bool :=
  match i with
  | 0 => mutually_orth_row_sat_aux M₁ M₂ 0 (k₂ - 1)
  | i' + 1 => mutually_orth_row_sat_aux M₁ M₂ i (k₂ - 1) && mutually_orth_sat_aux M₁ M₂ i'

def bitvec_mutually_orth_nat
  {n k₁ k₂ : ℕ}
  [NeZero n]
  [NeZero k₁]
  [NeZero k₂]
  (M₁ : BitVec (k₁ * n))
  (M₂ : BitVec (k₂ * n)) : Prop :=
  mutually_orth_sat_aux M₁ M₂ (k₁ - 1)

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
  | 0 => (dot_col_zero coeffs mat 0)
  | c₀ + 1 => dot_col_zero coeffs mat c && all_dot_zero_aux coeffs mat c₀

@[simp]
def all_dot_zero {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) := all_dot_zero_aux coeffs mat (n-1)

def linear_indep_SAT {r n : ℕ} (mat : BitVec (r * n)) : Prop := ∀ coeffs, !(nonzero coeffs && all_dot_zero coeffs mat)


def inds_strict_mono_aux {k r : ℕ} (inds : Fin r → Fin k) (i : Fin r) (prev : ℕ) : Bool :=
  let b := (inds i).1.blt prev
  match i with
  | ⟨0, _⟩ => b
  | ⟨i' + 1, h⟩ => b && (inds_strict_mono_aux inds ⟨i', (Nat.lt_succ_self _).trans h⟩ (inds i).1)

def inds_strict_mono {k r : ℕ} [NeZero r] (inds : Fin r → Fin k) : Prop := inds_strict_mono_aux inds ⟨r-1, Nat.sub_one_lt (NeZero.ne _)⟩ k
