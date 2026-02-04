import ATPTest.Stabilizer.CSS
import ATPTest.Stabilizer.LinAlgSMT
import ATPTest.Stabilizer.LinAlg


def cyclic_shift (n k : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i + k) = j then 1 else 0

def x (l m k : ℕ) [NeZero l] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker (cyclic_shift l k) 1

def y (l m k : ℕ) [NeZero m] : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  Matrix.kronecker 1 (cyclic_shift m k)

variable (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)

def BB_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)
 : Matrix ((Fin l) × (Fin m)) ((Fin l) × (Fin m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (x l m M₁.2) else (y l m M₁.2)
  let N₂ := if M₂.1 then (x l m M₂.2) else (y l m M₂.2)
  let N₃ := if M₃.1 then (x l m M₃.2) else (y l m M₃.2)
  N₁ + N₂ + N₃

variable {l m : ℕ} [NeZero l] [NeZero m] {M₁ M₂ M₃ : Bool × ℕ}

lemma BB_ind : LinearIndependent (ZMod 2) (BB_matrix l m M₁ M₂ M₃) := sorry

variable {l m : ℕ} [NeZero l] [NeZero m] {A₁ A₂ A₃ B₁ B₂ B₃ : Bool × ℕ}

def BB_castfin {m n : ℕ} {α : Type*} : Matrix (Fin m × Fin n) (Fin m × Fin n) α ≃ Matrix (Fin (m*n)) (Fin (m*n)) α :=
  Equiv.arrowCongr finProdFinEquiv (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))

def ZMod_Bool_equiv : (ZMod 2) ≃ Bool where
  toFun := Bool.ofNat ∘ ZMod.val
  invFun := fun b => if b then 1 else 0
  left_inv := by
   intro a
   fin_cases a <;> simp [Bool.ofNat]
  right_inv := by
    rintro (b | b) <;> simp [Bool.ofNat]


def BB_castbool {α β : Type*} : Matrix α β (ZMod 2) ≃ Matrix α β Bool :=
  Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (Equiv.refl _) ZMod_Bool_equiv)

lemma BB_comm : (CSS_BSM (BB_castfin (BB_matrix l m A₁ A₂ A₃)) (BB_castfin (BB_matrix l m B₁ B₂ B₃))).isCommuting := sorry

def BB_castnat {a b : ℕ} {α : Type*} [Zero α] (M : Matrix (Fin a) (Fin b) α) : Matrix ℕ ℕ α
  := fun i j => if h₁: i < a then (if h₂: j < b then M ⟨i, h₁⟩ ⟨j, h₂⟩ else 0) else 0

def BB_72_A :=
  let l := 6
  let m := 6
  BB_matrix l m (true, 3) (false, 1) (false, 2)

def BB_72_B :=
  let l := 6
  let m := 6
  BB_matrix l m (false, 3) (true, 1) (true, 2)

#eval (BB_castfin BB_72_A)

#eval (BB_castfin (y 6 6 1)) 0 1



def ker_test : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![0, 1; 1, 0]

def BB_A_ker : Matrix (Fin 12) (Fin (6*6)) (ZMod 2) :=
!![1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
1,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;
1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,1,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0;
0,0,0,0,0,0,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0;
0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1;
]

lemma BB_A_ker_ker : ∀ i j, dotProduct (BB_A_ker.row i) ((BB_castfin BB_72_A).row j) = 0 := sorry



--define BB code
