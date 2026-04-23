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


def row_parity_constraint_aux {n stabdim : ℕ} (stabs : BitVec (stabdim * n))
  (errs : BitVec n) (r : ℕ) (c : ℕ) :=
  let k := r + stabdim * c
  match c with
  | 0 => errs[c]! && stabs[k]!
  | c' + 1 => (errs[c]! && stabs[k]!) ^^ row_parity_constraint_aux stabs errs r c'

def row_parity_constraint {stabdim n : ℕ} (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  !(row_parity_constraint_aux stabs errs r (n-1))

def parity_constraints_aux {stabdim n : ℕ} (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => row_parity_constraint stabs errs 0
  | r' + 1 => row_parity_constraint stabs errs r ∧ parity_constraints_aux stabs errs r'

def parity_constraints {stabdim n : ℕ} (stabs : BitVec (stabdim * n)) (errs : BitVec n) :=
  parity_constraints_aux stabs errs (stabdim-1)

def row_stabilizer_constraint_aux
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) (c : ℕ) :=
  let k := r + (kerdim) * c
  match c with
  | 0 => (errs[c]! && ker[k]!)
  | c' + 1 => (errs[c]! && ker[k]!) ^^ row_stabilizer_constraint_aux ker errs r c'

def row_stabilizer_constraint
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) :=
  row_stabilizer_constraint_aux ker errs r (n-1)

def stabilizer_constraints_aux
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => row_stabilizer_constraint ker errs 0
  | r' + 1 => row_stabilizer_constraint ker errs r ∨
      stabilizer_constraints_aux ker errs r'

def stabilizer_constraints
  {kerdim n : ℕ}
  (ker : BitVec (kerdim * n))
  (errs : BitVec n) :=
  stabilizer_constraints_aux ker errs (kerdim - 1)

def all_dist_constraints
  {n stabdim kerdim : ℕ}
  (stabs : BitVec (stabdim * n))
  (ker : BitVec (kerdim * n))
  (k nlog : ℕ) : Prop :=
  ∀ (locs : (BitVec (k * nlog))) (errs : BitVec n),
  ¬ (loc_constraints locs errs ∧ parity_constraints stabs errs ∧ stabilizer_constraints ker errs)
