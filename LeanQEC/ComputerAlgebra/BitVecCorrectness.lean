import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Log
import LeanQEC.LinearAlgebra.RowspaceKernel
import LeanQEC.ComputerAlgebra.BitVecSAT
import LeanQEC.ComputerAlgebra.BitVecInd

instance {n : Nat} : Coe ((Fin n) → ZMod 2) ((Fin n) → Bool) where
  coe f := fun i => (f i).val == 1



def vec_to_BitVec {j : ℕ} (r : (Fin j) → (ZMod 2)) : BitVec j := BitVec.ofFnLE r

def BitVec_to_vec {n : ℕ} (x : BitVec n) : (Fin n) → (ZMod 2) := fun i => x[i].toNat




--for Fin j → Fin n
def vec_to_BitVec' {j n : ℕ} (r : (Fin j) → (Fin n)) : BitVec (j * (Nat.clog 2 n)) :=
  match j with
  | 0 => (BitVec.zero 0).cast (by rw [zero_mul])
  | 1 => (r 0)
  | j' + 1 => ((r ⟨j', Nat.lt_succ_self _⟩ : BitVec (Nat.clog 2 n)).append (vec_to_BitVec' (fun i : Fin j' => r ⟨i, by simp⟩))).cast (by rw [Nat.succ_mul, Nat.add_comm])


--terrible?
def BitVec.appendList {i j : ℕ} (f : (Fin i) → (BitVec j)) : BitVec (i * j) :=
  match i with
  | 0 => (BitVec.zero 0).cast (by rw [MulZeroClass.zero_mul])
  | 1 => (f 0).cast (by rw [one_mul])
  | i' + 1 => (((f ⟨i', Nat.lt_succ_self _⟩).append (BitVec.appendList (fun (j : Fin i') => f ⟨j, by simp⟩)))).cast (by rw [Nat.succ_mul, Nat.add_comm])

def Matrix.toBitVecs {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : (Fin i) → (BitVec j) :=
  fun a => vec_to_BitVec (M a)


def flatten_matrix {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : BitVec (i * j) :=
  BitVec.appendList M.toBitVecs

--function transforming error vector with limited support into index vector
def index_vec {n k : ℕ} (x : Fin n → ZMod 2) (hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) : Fin k → Fin n :=
  let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0);
  let I : Fin (hammingNorm x) → Fin n := fun j =>
        (S.orderEmbOfFin rfl j)
  fun y => if h : y < hammingNorm x then I ⟨y, h⟩ else I ⟨hammingNorm x - 1, by apply Nat.sub_one_lt hx'⟩

lemma index_vec_eq_one_of_exists {n k : ℕ} {x : Fin n → ZMod 2} {hx : hammingNorm x ≤ k} {hx' : hammingNorm x ≠ 0}
  {y : Fin k} {i : Fin n}
  (h_ind : index_vec x hx hx' y = i) :
  x i ≠ 0 := sorry


--def T : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]
--#eval! flatten_matrix T -- evaluates to 11: successully flattened
--#eval! (flatten_matrix T)[1]


lemma vec_to_BitVec'_correct {i n : ℕ} {r : (Fin i) → (Fin n)} (j : Fin i) :
  (vec_to_BitVec' r).extractLsb' (j * (Nat.clog 2 n)) (Nat.clog 2 n) = r j := sorry




lemma vec_to_BitVec_correct {j : ℕ} (r : (Fin j) → (ZMod 2)) (i : Fin j) : (vec_to_BitVec r)[i]! = ((r i).val == 1) := by
  simp [vec_to_BitVec]

lemma BitVec_to_vec_correct {n : ℕ} (x : BitVec n) (i : Fin n) : (BitVec_to_vec x) i = x[i].toNat := sorry

lemma vec_to_BitVec_BitVec_to_vec {n : ℕ} (x : BitVec n) : x = (vec_to_BitVec (BitVec_to_vec x)) := sorry


lemma flatten_matrix_correct {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) (r : Fin i) (c : Fin j) :
  (flatten_matrix M)[(r * i) + c]! = ((M r c).val == 1) := sorry


lemma loc_constraints_ascent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : ∀ (i : Fin n), loc_constraints_ith locs errs i)
 : loc_constraints locs errs := sorry

lemma loc_constraints_descent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : loc_constraints locs errs)
  (i : Fin n)
  : loc_constraints_ith locs errs i := sorry

lemma loc_constraints_ith_jth_aux_correct
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ)
  : loc_constraints_ith_jth_aux locs i j =  (∃ l : Fin k, locs.extractLsb' (l * nlog) nlog = i) := sorry

lemma fin_to_bitvec_clog {n : ℕ} {x : Fin n} : (x : BitVec (Nat.clog 2 n)) = BitVec.ofNat (Nat.clog 2 n) x := by
  simp only [BitVec.natCast_eq_ofNat]

lemma BitVec.ofNat_clog_eq_iff {n : ℕ} {x y : Fin n} :
  BitVec.ofNat (Nat.clog 2 n) x = BitVec.ofNat (Nat.clog 2 n) y ↔ x = y := sorry

lemma loc_constraints_of_index {n k : ℕ} (x : Fin n → (ZMod 2)) (hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) :
  loc_constraints (vec_to_BitVec' (index_vec x hx hx')) (vec_to_BitVec x) := by
  apply loc_constraints_ascent
  intro i
  unfold loc_constraints_ith
  rw [loc_constraints_ith_jth_aux_correct]
  by_cases h : (x i = 0)
  · simp [vec_to_BitVec, h]
    intro y
    rw [vec_to_BitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    intro h_f
    apply absurd h
    apply index_vec_eq_one_of_exists h_f
  sorry





def row_inner_product_correct {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) (r : Fin k):
  row_inner_product (flatten_matrix M) (vec_to_BitVec x) r = ((M r) ⬝ᵥ x == 1) := sorry

lemma parity_constraints_descent {stabdim n : ℕ} {stabs : BitVec (stabdim * n)} {errs : BitVec n} {r : Fin stabdim} (hpc : parity_constraints stabs errs) :
  !(row_inner_product stabs errs r) := sorry

lemma parity_constraints_ascent {stabdim n : ℕ} {stabs : BitVec (stabdim * n)}
{errs : BitVec n} (hpaux : ∀ (r : Fin stabdim), !(row_inner_product stabs errs r))
 : parity_constraints stabs errs := sorry

lemma parity_constraints_correct {k n : ℕ} {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x : Fin n → ZMod 2} :
  parity_constraints (flatten_matrix M) (vec_to_BitVec x) ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [LinearMap.mem_ker]
  have pc_correct_aux : ∀ (i : Fin k),
  !row_inner_product (flatten_matrix M) (vec_to_BitVec x) i ↔ (M.mulVec x) i = 0 := sorry
  rw [Matrix.toLin'_apply]
  constructor
  · intro hpar
    ext i
    apply (pc_correct_aux i).1
    apply parity_constraints_descent hpar
  intro hmul
  apply parity_constraints_ascent
  intro r
  apply (pc_correct_aux r).2
  rw [hmul]
  simp only [Pi.zero_apply]

lemma rowspace_constraints_descent {kerdim n} {ker : BitVec (kerdim * n)}
{errs : BitVec n} (r : Fin kerdim) (hr : row_inner_product ker errs r)
: rowspace_constraints ker errs := sorry


lemma rowspace_constraints_ascent {kerdim n} {ker : BitVec (kerdim * n)}
{errs : BitVec n} (hconstr : rowspace_constraints ker errs)
: ∃ (r : Fin kerdim), row_inner_product ker errs r := sorry


lemma rowspace_constraints_correct {k₁ k₂ n : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin')))
  {x : Fin n → ZMod 2} :
  rowspace_constraints (flatten_matrix M₂) (vec_to_BitVec x) ↔ x ∉ M₁.rowSpace := by
  rw [not_mem_rowspace_iff_exists_mem_ker]
  constructor
  · intro hrc
    rcases rowspace_constraints_ascent hrc with ⟨r, hrp⟩
    refine ⟨M₂ r, ⟨?_, ?_⟩⟩
    · rw [←hK]
      exact Matrix.row_mem_rowSpace
    rw [row_inner_product_correct] at hrp
    simp only [beq_iff_eq] at hrp
    assumption
  rintro ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [←hK] at hy₁
  obtain ⟨s, hs⟩ := exists_row_of_exists_mem_rowspace_non_orth hy₁ hy₂
  apply rowspace_constraints_descent s
  rwa [row_inner_product_correct, beq_iff_eq]


lemma nonzero_correct {r : ℕ} (x : Fin r → (ZMod 2))
  : nonzero (vec_to_BitVec x) ↔ x ≠ 0 := sorry

lemma all_dot_zero_correct {r n : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → (ZMod 2))
  : all_dot_zero (vec_to_BitVec coeffs) (flatten_matrix M) ↔ M.vecMul coeffs = 0 := sorry


lemma linear_indep_of_forall_vecmul_nz {r n : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
  : LinearIndependent (ZMod 2) M ↔ ∀ coeffs, coeffs ≠ 0 → M.vecMul coeffs ≠ 0 := sorry

lemma linear_indep_SAT_correct {r n : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2)) :
  LinearIndependent (ZMod 2) M ↔ linear_indep_SAT (flatten_matrix M) := by
  rw [linear_indep_of_forall_vecmul_nz]
  constructor
  · intro hcoeffs coeffs
    simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    by_cases h: BitVec_to_vec coeffs ≠ 0
    · right
      rw [←Bool.not_eq_true]
      rw [vec_to_BitVec_BitVec_to_vec coeffs, all_dot_zero_correct M]
      apply hcoeffs _ h
    left
    rwa [←Bool.not_eq_true, vec_to_BitVec_BitVec_to_vec coeffs, nonzero_correct]
  intro hlin coeffs hnz
  rw [ne_eq, ←all_dot_zero_correct]
  intro h_f
  unfold linear_indep_SAT at hlin
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
  ←Bool.not_eq_true] at hlin
  rcases hlin (vec_to_BitVec coeffs) with hz | hd
  · apply hz
    rwa [nonzero_correct]
  apply (hd h_f)
