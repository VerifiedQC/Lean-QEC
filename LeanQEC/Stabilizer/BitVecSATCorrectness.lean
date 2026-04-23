import LeanQEC.Stabilizer.BitVecSat
import LeanQEC.Stabilizer.CSS


--translation: need function going from BSM to bitvec


instance {n : Nat} : Coe ((Fin n) → ZMod 2) ((Fin n) → Bool) where
  coe f := fun i => (f i).val == 1

def row_to_BitVec {j : ℕ} (r : (Fin j) → (ZMod 2)) : BitVec j := BitVec.ofFnBE r


--terrible?
def BitVec.appendList {i j : ℕ} (f : (Fin i) → (BitVec j)) : BitVec (i * j) :=
  match i with
  | 0 => (BitVec.zero 0).cast (by rw [MulZeroClass.zero_mul])
  | 1 => (f 0).cast (by rw [one_mul])
  | i' + 1 => ((BitVec.appendList (fun (j : Fin i') => f ⟨j, by simp⟩)).append (f ⟨i', Nat.lt_succ_self _⟩)).cast (by rw [Nat.succ_mul])

def Matrix.toBitVecs {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : (Fin i) → (BitVec j) :=
  fun a => row_to_BitVec (M a)


def flatten_matrix {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : BitVec (i * j) :=
  BitVec.appendList M.toBitVecs

def T : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]

#eval! flatten_matrix T -- evaluates to 13: successully flattened
