import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Inv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

structure pivot_t {a b : ℕ} where
  rk : ℕ
  locs : Fin rk → Fin b
  locs_increasing : StrictMono locs
  le_dim_rank : rk ≤ a

-- Aristotle
lemma pivot_locs_injective {a b} (p : @pivot_t a b) :
  Function.Injective p.locs := by
  apply p.locs_increasing.injective

def pivots_are_1s {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivot : @pivot_t a b) :=
    ∀ i : Fin pivot.rk,
    m (Fin.castLE pivot.le_dim_rank i) (pivot.locs i) = 1

def Matrix.is_zeroes_below
  {a b : ℕ} [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (i : Fin a) (j : Fin b) : Prop :=
  forall (i₀ : Fin a), (i₀ > i -> m i₀ j = 0)

def is_rref_with_pivots {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b) :=
  pivots_are_1s m pivots /\
  match pivots with
  | ⟨0, _, _, _⟩ => (m = 0)
  | ⟨rk₀ + 1, locs, _, le_dim_rank⟩ =>
    -- all 0s before first pivot
    (forall j, j < locs 0 -> forall i, m i j = 0) /\
    -- between pivots, 0s below
    (forall (i : Fin rk₀) (j : Fin b),
      let i' := Fin.castSucc i
      let iₐ : Fin a := Fin.castLE le_dim_rank i'
      locs i' ≤ j ->
      j < locs (i' + 1) ->
      m.is_zeroes_below iₐ j) /\
    -- after last pivot, 0s below
    (forall (j : Fin b),
      let rk₀' := Fin.last rk₀
      let i : Fin a := Fin.castLE le_dim_rank rk₀'
      (locs rk₀' ≤ j) ->
      (m.is_zeroes_below i j))

-- TODO edge case fixed, let Aristotle try again
#check Matrix.rank_eq_finrank_span_row
lemma pivot_rank_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (is_pivot : is_rref_with_pivots m pivots) :
  Matrix.rank m = pivots.rk := by sorry

def kernel_from_non_pivot {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (j : Fin b) (i : Fin b) : ZMod 2 :=
  if i == j then 1
  else if is_pivot : i ∈ Finset.image pivots.locs Finset.univ then
    let i' : Set.range pivots.locs := ⟨i, by grind⟩
    let x := Function.Injective.invOfMemRange (by apply pivot_locs_injective) i'
    let xr : Fin a := Fin.castLE pivots.le_dim_rank x
    m xr j
  else 0

lemma ker_from_non_pivot_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) j :
  kernel_from_non_pivot m pivots j ∈ m.toLin'.ker := by
  sorry

def ker_from_rref_aux {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (j : ℕ) (lt_j_b : j < b) : List (Fin b -> ZMod 2) :=
  let tail := match j with
  | 0 => []
  | j₀ + 1 => ker_from_rref_aux m pivots j₀ (by apply Nat.lt_of_succ_lt lt_j_b)
  let jfin : Fin b := Fin.ofNat b j
  if jfin ∈ Finset.image pivots.locs Finset.univ then
    tail
  else
    kernel_from_non_pivot m pivots jfin :: tail

def ker_from_rref {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b) : List (Fin b -> ZMod 2) :=
  ker_from_rref_aux m pivots (b - 1) (by simp [NeZero.pos])

#check finrank_span_eq_card

lemma ker_from_rref_lin_indep {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  let ker := ker_from_rref m pivots
  LinearIndependent (ZMod 2) (fun (i : Fin (ker.length)) => ker[i]) := by
  sorry

lemma ker_from_rref_le_ker {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  Submodule.span (ZMod 2) (ker_from_rref m pivots).toFinset ≤ m.toLin'.ker := by
  sorry

#check Submodule.eq_of_le_of_finrank_eq
-- TODO some sort of rank-nullity trick...

lemma ker_from_rref_correct {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivots : @pivot_t a b)
  (pivots_correct : is_rref_with_pivots m pivots) :
  m.toLin'.ker = Submodule.span (ZMod 2) (ker_from_rref m pivots).toFinset := by
  sorry

/-
def demo_mat : Matrix (Fin 5) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0]]

def demo_pivots : @pivot_t 5 6 where
  rk := 4
  locs := ![0, 1, 3, 5]
  locs_increasing := by
    intros i j; fin_cases i <;> fin_cases j <;> simp
  le_dim_rank := by simp

#eval ker_from_rref demo_mat demo_pivots
-/

-- RREF

def swap_rows {a b} (m : Matrix (Fin a) (Fin b) (ZMod 2)) (i₁ i₂ : Fin a)
  : Matrix (Fin a) (Fin b) (ZMod 2) :=
  Matrix.of (fun i j =>
    if i == i₁ then
      m i₂ j
    else if i == i₂ then
      m i₁ j
    else m i j)

def add_row_i₁_to_i₂ {a b} (m : Matrix (Fin a) (Fin b) (ZMod 2)) (i₁ i₂ : Fin a)
  : Matrix (Fin a) (Fin b) (ZMod 2) :=
  Matrix.of (fun i j =>
    if i == i₂ then
      m i₁ j + m i₂ j
    else m i j)

def try_ensure1_aux {a b}
  [NeZero a]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (i : Fin a) (j : Fin b) (fuel : ℕ)
  : Matrix (Fin a) (Fin b) (ZMod 2) :=
  let r : Fin a := Fin.ofNat a (a - 1 - fuel)
  if m r j == 1 then
    swap_rows m i r
  else
    match fuel with
    | 0 => m
    | k + 1 => try_ensure1_aux m i j k

-- Swap rows with below if possible, so an entry becomes 1
def try_ensure1 {a b}
  [NeZero a]
  (m : Matrix (Fin a) (Fin b) (ZMod 2)) (i : Fin a) (j : Fin b) :=
  try_ensure1_aux m i j (a - i - 2)

def make_1_pivot_aux {a b}
  [NeZero a]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (i : Fin a) (j : Fin b) (k : ℕ) :=
  let r : Fin a := Fin.ofNat a k
  let needs_op := r != i && m r j == 1
  let m_op := add_row_i₁_to_i₂ m i r
  let m' := if needs_op then m_op else m
  match k with
  | 0 => m'
  | k' + 1 => make_1_pivot_aux m' i j k'

-- Given a leading 1, remove 1s in other rows of the same column through row op
def make_1_pivot {a b}
  [NeZero a]
  (m : Matrix (Fin a) (Fin b) (ZMod 2)) (i : Fin a) (j : Fin b) :=
  make_1_pivot_aux m i j (a - 1)

def pivot₀ {a b : ℕ} : @pivot_t a b where
  rk := 0
  locs := fun x => nomatch x
  locs_increasing := by simp [StrictMono]
  le_dim_rank := by apply zero_le

def v_gt_tail {r b} [NeZero b] (locs : Fin r -> Fin b) (v : ℕ) :=
  match r with
  | 0 => true
  | r₀ + 1 =>
    v > locs (Fin.ofNat (r₀ + 1) r₀)

def append_to_pivot {a b : ℕ}
  [NeZero b]
  (pivot : @pivot_t a b) (v : ℕ)
  (v_inc : v_gt_tail pivot.locs v)
  (v_bounded : pivot.rk < a)
  : @pivot_t a b where
  rk := pivot.rk + 1
  locs := fun x => if H: x < pivot.rk then
    let x' : Fin pivot.rk := Fin.castLT x (by assumption)
    pivot.locs x'
  else
    Fin.ofNat b v
  locs_increasing := (by sorry)
  le_dim_rank := (by simp_all only [Order.add_one_le_iff])

def rref_aux {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2))
  (pivot : @pivot_t a b)
  -- fuel is just (b-j-1), i.e. number of remaining columns
  -- need to be decreasing for recursion and termination
  (fuel : ℕ)
  : Matrix (Fin a) (Fin b) (ZMod 2) × @pivot_t a b :=
  let i := Fin.ofNat a pivot.rk
  let j : Fin b := Fin.ofNat b (b - 1 - fuel)
  let m1 := try_ensure1 m i j
  if m1 i j == 1 then
    let pivot' := append_to_pivot pivot j (by sorry) (by sorry)
    let m' := make_1_pivot m1 i j
    match fuel with
    | 0 => (m', pivot')
    | f + 1 =>
      if pivot'.rk = a then
        (m', pivot')
      else
        rref_aux m' pivot' f
  else
    match fuel with
    | 0 => (m1, pivot)
    | f + 1 => rref_aux m1 pivot f

def rref {a b}
  [NeZero a] [NeZero b]
  (m : Matrix (Fin a) (Fin b) (ZMod 2)) :=
  rref_aux m pivot₀ (b - 1)

def test_mat : Matrix (Fin 5) (Fin 7) (ZMod 2) :=
  ![![0, 1, 0, 1, 0, 1, 1],
    ![1, 0, 0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 1]]

def test_kernel :=
  let (m, p) := rref test_mat
  ker_from_rref m p

-- unbelievably slow
#eval! test_kernel
