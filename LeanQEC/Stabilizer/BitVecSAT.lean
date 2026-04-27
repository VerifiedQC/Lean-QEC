import Mathlib.Data.BitVec


--locs : BitVec (k * nlog), where nlog is ceiling of log_2 n
def loc_constraints_ith_jth
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  ((locs.extractLsb' (j * nlog) nlog) = i)
  --obtain jth entry of locs, which is a BitVec of length nlog
  --and test it against i, which is a natural number

def loc_constraints_ith_jth_aux
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ) :=
  match j with
  | 0 => loc_constraints_ith_jth locs i 0
  | j' + 1 => loc_constraints_ith_jth locs i j ∨
              loc_constraints_ith_jth_aux locs i j'

def loc_constraints_ith
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (i : ℕ) :=
  errs[i]! = loc_constraints_ith_jth_aux locs i (k-1)

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

def row_inner_product_aux {n k : ℕ} (M : BitVec (k * n)) (x : BitVec n) (r c : ℕ) : Bool :=
  let i := (r * k) + c
  match c with
  | 0 => x[c]! && M[i]!
  | c' + 1 => (x[c]! && M[k]!) ^^ row_inner_product_aux M x r c'

def row_inner_product {n k : ℕ} (M : BitVec (k * n)) (x : BitVec n) (r : ℕ) : Bool :=
  row_inner_product_aux M x r (n-1)

def parity_constraints_aux {stabdim n : ℕ} (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => !(row_inner_product stabs errs 0)
  | r' + 1 => !(row_inner_product stabs errs r) ∧ parity_constraints_aux stabs errs r'

def parity_constraints {stabdim n : ℕ} (stabs : BitVec (stabdim * n)) (errs : BitVec n) :=
  parity_constraints_aux stabs errs (stabdim-1)

def rowspace_constraints_aux
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => (row_inner_product ker errs 0)
  | r' + 1 => (row_inner_product ker errs r) ∨
      rowspace_constraints_aux ker errs r'

def rowspace_constraints
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) :=
  rowspace_constraints_aux ker errs (kerdim - 1)

def lt_dist_sat
  {n stabdim kerdim : ℕ}
  (stabs : BitVec (stabdim * n))
  (ker : BitVec (kerdim * n))
  (k nlog : ℕ) : Prop :=
  ∀ (locs : (BitVec (k * nlog))) (errs : BitVec n),
  ¬ (loc_constraints locs errs ∧ parity_constraints stabs errs ∧ rowspace_constraints ker errs)
