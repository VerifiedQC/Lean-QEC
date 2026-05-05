import LeanQEC.Stabilizer.CSS
import LeanQEC.LinearAlgebra.RowspaceKernel


@[simp]
def cyclic_shift (n k : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i + k) = j then 1 else 0

@[simp]
def x (l m k : ℕ) [NeZero l] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker (cyclic_shift l k) 1

@[simp]
def y (l m k : ℕ) [NeZero m] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker 1 (cyclic_shift m k)

variable (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)

@[simp]
def BB_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)
 : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (x l m M₁.2) else (y l m M₁.2)
  let N₂ := if M₂.1 then (x l m M₂.2) else (y l m M₂.2)
  let N₃ := if M₃.1 then (x l m M₃.2) else (y l m M₃.2)
  N₁ + N₂ + N₃

variable {l m : ℕ} [NeZero l] [NeZero m] {M₁ M₂ M₃ : Bool × ℕ}

variable {l m : ℕ} [NeZero l] [NeZero m] {A₁ A₂ A₃ B₁ B₂ B₃ : Bool × ℕ}

def BB_72_A :=
  let l := 6
  let m := 6
  BB_matrix l m (true, 3) (false, 1) (false, 2)

def BB_72_B :=
  let l := 6
  let m := 6
  BB_matrix l m (false, 3) (true, 1) (true, 2)

--also doesn't unfold :/
def BB_castfin {α : Type*} {n m : ℕ} :  (Matrix ((Fin n) × (Fin m)) ((Fin n) × (Fin m)) α) ≃ Matrix (Fin (n * m)) (Fin (n * m)) α
  := finProdFinEquiv.arrowCongr (finProdFinEquiv.arrowCongr (Equiv.refl α))


--unfolds... up to finProdFinEquiv
def BB_castfin' {α : Type*} {n m : ℕ} (M : Matrix ((Fin n) × (Fin m)) ((Fin n) × (Fin m)) α) : Matrix (Fin (n * m)) (Fin (n * m)) α :=
  fun i j => M (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)

#check BB_castfin BB_72_A

def Matrix.hstack {α β₁ β₂ γ : Type*} (M₁ : Matrix α β₁ γ) (M₂ : Matrix α β₂ γ) : Matrix α (β₁ ⊕ β₂) γ :=
  fun i j => match j with
  | (Sum.inl j) => M₁ i j
  | (Sum.inr j) => M₂ i j


def H_x_72 : Matrix (Fin (6*6)) (Fin (6*6) ⊕ Fin (6*6)) (ZMod 2) :=
  (BB_castfin BB_72_A).hstack (BB_castfin BB_72_B)

def H_Z_72 : Matrix (Fin (6*6)) (Fin (6*6) ⊕ Fin (6*6)) (ZMod 2) :=
  (BB_castfin BB_72_A).transpose.hstack ((BB_castfin BB_72_B).transpose)

/- --doesn't unfold ... :/
def BB_castsum {α β : Type*} {n m : ℕ} : Matrix α (Fin n ⊕ Fin m) β ≃ Matrix α (Fin (n + m)) β
  := (Equiv.refl _).arrowCongr (finSumFinEquiv.arrowCongr (Equiv.refl _))
-/
def BB_castsum {α β : Type*} {n m : ℕ} (M : Matrix α (Fin n ⊕ Fin m) β) : Matrix α (Fin (n + m)) β := fun i j =>
  if h : j < n then M i (Sum.inl ⟨j, h⟩) else M i (Sum.inr ⟨j-n, by
    push_neg at h
    apply Nat.sub_lt_right_of_lt_add h
    simp_rw [add_comm]
    exact j.2
  ⟩)
