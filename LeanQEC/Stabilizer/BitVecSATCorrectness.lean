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

--def T : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]
--#eval! flatten_matrix T -- evaluates to 13: successully flattened

def kergen_correct {a b n : ℕ}
  (M : Matrix (Fin a) (Fin b) (ZMod 2))
  (gen : Fin n -> Fin b -> ZMod 2) : Prop :=
  LinearMap.ker M.toLin' =
  Submodule.span (ZMod 2) (Finset.image gen Finset.univ)



theorem sat_translation_correct
  {n nlog k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xkergen : Fin (n - k₁) → Fin n → ZMod 2)
  (xkergen_correct : kergen_correct css.H₁ xkergen)
  (zkergen : Fin (n - k₂) → Fin n → ZMod 2)
  (zkergen_correct : kergen_correct css.H₂ zkergen)
  (dist : ℕ) :
  lt_dist_sat (flatten_matrix css.H₁) (flatten_matrix (Matrix.of xkergen)) dist nlog →
  lt_dist_sat (flatten_matrix css.H₂) (flatten_matrix (Matrix.of zkergen)) dist nlog →
  dist ≤ css.toBSM.distance (by apply NeZero.pos) := sorry
