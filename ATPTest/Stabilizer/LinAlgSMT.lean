import Smt
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Fold


variable (e : ℕ → Bool)

def n : ℕ := 5
def r₁ : ℕ := 4
def r₂ : ℕ := 5
def H_x : Matrix ℕ ℕ Bool := fun _ _ => false
def H_z : Matrix ℕ ℕ Bool := fun _ _ => true
def wt : ℕ := 3
def H_x_ker : Matrix ℕ ℕ Bool := fun _ _ => false
def x_ker_size := 2
def H_z_ker : Matrix ℕ ℕ Bool := fun _ _ => false
def z_ker_size := 2

--don't work with fin at all, just define your matrices so they return 0 on other nats
--resolved compile time when unfolding matrix defs


--indexing function: ℕ → ℕ
def is_index_bool (I : ℕ → ℕ) (d n : ℕ) : Bool :=
  (Finset.range d).fold and true (fun i => (I i) < n)


def indexed_by (I : ℕ → ℕ) (d : ℕ) : ℕ → Bool := --
  fun i => (Finset.range d).fold or false (fun k => i = (I k))

instance : Std.Commutative Bool.xor := by
  constructor
  simp

def vec_inner_product (n : ℕ) (v₁ v₂ : ℕ → Bool) : Bool :=
  (Finset.range n).fold xor false (fun i => and (v₁ i) (v₂ i))

def mem_ker_bool (r : ℕ) (n : ℕ) (H : Matrix ℕ ℕ Bool) (x : ℕ → Bool) : Bool :=
  (Finset.range r).fold and true (fun k => ¬(vec_inner_product n (H k) x))

def not_mem_rowspace (ker_size n : ℕ) (H_ker : Matrix ℕ ℕ Bool) (x : ℕ → Bool) : Bool :=
  (Finset.range ker_size).fold or false (fun k => vec_inner_product n (H_ker k) x)

def nontrivial_bool (n : ℕ) (x : ℕ → Bool) : Bool :=
  (Finset.range n).fold or false x

def dist_index_le (n r₁ z_ker_size : ℕ) (Hₓ H_z_ker : Matrix ℕ ℕ Bool) (d : ℕ) : Prop :=
  ∀ (I : ℕ → ℕ), let x := indexed_by I d;
  (is_index_bool I d n) && (nontrivial_bool n x)
    && (mem_ker_bool r₁ n Hₓ x) && (not_mem_rowspace z_ker_size n H_z_ker x)

open Lean Meta Elab Tactic Syntax
elab "unfold_range"
 : tactic => do
  evalTactic (← `(tactic| repeat rw [Finset.range_add_one]))
  evalTactic (← `(tactic| repeat rw [Finset.fold_insert (by aesop)]))
  evalTactic (← `(tactic| repeat rw [Finset.range_zero]))
  evalTactic (← `(tactic| repeat rw [Finset.fold_empty]))

--before calling:
elab "prep_smt"
 : tactic => do
  evalTactic (← `(tactic| dsimp))
  evalTactic (← `(tactic| unfold is_index_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.and_true]))
  evalTactic (← `(tactic| unfold nontrivial_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.or_false]))
  evalTactic (← `(tactic| unfold mem_ker_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.and_true]))
  evalTactic (← `(tactic| unfold vec_inner_product))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.xor_false]))
  evalTactic (← `(tactic| unfold not_mem_rowspace))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| unfold vec_inner_product))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.xor_false]))
  evalTactic (← `(tactic| unfold indexed_by))
  evalTactic (← `(tactic| unfold_range))

  --evalTactic (← `(tactic| repeat rw [Finset.range_zero, Finset.fold_empty, Bool.xor_false]))



theorem dist_test : dist_index_le n r₁ z_ker_size H_x H_z_ker 2 := by
  intro I
  unfold n r₁ z_ker_size
  prep_smt
  unfold H_z_ker H_x
  --smt --observe: no error! accepted input!
  sorry
