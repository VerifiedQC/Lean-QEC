import ATPTest.Stabilizer.CSS



def cyclic_shift (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i + 1) = j then 1 else 0

def x (l m : ℕ) [NeZero l] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker (cyclic_shift l) 1

def y (l m : ℕ) [NeZero m] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker 1 (cyclic_shift m)

def BB_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)
 : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (x l m) else (y l m)
  let N₂ := if M₂.1 then (x l m) else (y l m)
  let N₃ := if M₃.1 then (x l m) else (y l m)
  (N₁ ^ M₁.2) + (N₂ ^ M₂.2) + (N₃ ^ M₃.2)

--define BB code
