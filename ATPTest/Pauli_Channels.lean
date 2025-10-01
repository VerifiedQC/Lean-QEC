import ATPTest.Basic
-- Define multi-qubit pauli channels to model errors

-- First define single-qubit bit-flip channel
open Qubit

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

variable (U : 𝐔[Qubit])

noncomputable section


def kraus_unitary (p : ℝ) (i : Qubit): Matrix Qubit Qubit ℂ :=
  match i with
  | 0 => √(1-p) • 1
  | 1 => √p • U

@[simp] lemma kraus_unitary_0 : kraus_unitary U p 0 = √(1 - p) • 1 := by rfl

@[simp] lemma kraus_unitary_1 : kraus_unitary U p 1 = √p • U := by rfl

def kraus_bit_flip := kraus_unitary X

@[simp] lemma kraus_bit_flip_0 : kraus_bit_flip p 0 = √(1 - p) • 1 := by
  rfl

@[simp] lemma kraus_bit_flip_1 : kraus_bit_flip p 1 = √p • X := by
  rfl

def kraus_dephasing := kraus_unitary Z

@[simp] lemma kraus_dephasing_0 : kraus_dephasing p 0 = √(1 - p) • 1 := by
  rfl

@[simp] lemma kraus_dephasing_1 : kraus_dephasing p 1 = √p • Z := by
  rfl

lemma unitary_ct : (U: Matrix Qubit Qubit ℂ).conjTranspose * (U: Matrix Qubit Qubit ℂ) = 1 := by
  rw [←Matrix.star_eq_conjTranspose]
  simp only [SetLike.coe_mem, unitary.star_mul_self_of_mem]

def unitary_p_channel (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) := CPTPMap.of_kraus_CPTPMap (kraus_unitary U p) (
  by
    simp [unitary_ct, smul_smul, ←add_smul, Real.mul_self_sqrt hp1, Real.mul_self_sqrt hp2]
)

def bit_flip_channel (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) := unitary_p_channel Z p hp1 hp2

def kraus_pauli (p1 p2 p3 p4 : ℝ) (i : Fin 4): Matrix Qubit Qubit ℂ :=
  match i with
  | 0 => √p1 • 1
  | 1 => √p2 • X
  | 2 => √p3 • Y
  | 3 => √p4 • Z

def pauli_channel (p1 p2 p3 p4 : ℝ) (hp1: 0 ≤ p1) (hp2: 0 ≤ p2) (hp3: 0 ≤ p3) (hp4: 0 ≤ p4)
(hp : p1 + p2 + p3 + p4 = 1)
 := CPTPMap.of_kraus_CPTPMap (kraus_pauli p1 p2 p3 p4)
 ( by
  simp [Fin.sum_univ_four, kraus_pauli, unitary_ct, smul_smul, Real.mul_self_sqrt hp1,
    Real.mul_self_sqrt hp2, Real.mul_self_sqrt hp3, Real.mul_self_sqrt hp4, ←add_smul, hp]
 )





def kraus_depolarizing (p : ℝ) (i : Fin 4): Matrix Qubit Qubit ℂ := kraus_pauli (1-p) (p/3) (p/3) (p/3) i

def depolarizing_channel (p : ℝ) (hp1: 0 ≤ p) (hp2 : 0 ≤ 1-p) :=
pauli_channel (1-p) (p/3) (p/3) (p/3) hp2 (by linarith) (by linarith) (by linarith)

--reason about the kraus operators of channel products

variable {k : Type*} [Fintype k] [DecidableEq k]

variable (A : Matrix m m' ℂ) (B : Matrix n n' ℂ)

theorem kronecker_conjTranspose : (A.kronecker B).conjTranspose = (Matrix.kronecker A.conjTranspose B.conjTranspose) := by
  ext; simp


theorem Matrix.finset_sum_kronecker {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α]  (K : Finset (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k ∈ K, k) B = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) k B  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_left, IH]
    intros c d e
    rw [right_distrib]

theorem Matrix.sum_kronecker_label_finset_left {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] (K : Finset κ) (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k ∈ K, (M k)) B = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) (M k) B  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_left, IH]
    intros c d e
    rw [right_distrib]

theorem Matrix.sum_kronecker_label_finset_right {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] (K : Finset κ) (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (∑ k ∈ K, (M k)) = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (M k)  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_right, IH]
    intros c d e
    rw [left_distrib]


theorem Matrix.sum_kronecker_left {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] [Fintype κ] (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k, M k) B = ∑ k, kroneckerMap (fun (x1 x2 : α) => x1 * x2) (M k) B  := Matrix.sum_kronecker_label_finset_left (Finset.univ) M B

theorem Matrix.sum_kronecker_right {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] [Fintype κ] (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (∑ k, M k) = ∑ k, kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (M k)  := Matrix.sum_kronecker_label_finset_right (Finset.univ) M B






def kraus_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ)
(M₂ : κ₂ → Matrix dO₂ dI₂ ℂ) (hM₁ : ∑ k, (M₁ k).conjTranspose * M₁ k = 1) (hM₂ : ∑ k, (M₂ k).conjTranspose * M₂ k = 1) :
CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) ℂ := CPTPMap.of_kraus_CPTPMap (fun (i : κ₁ × κ₂) => Matrix.kronecker (M₁ i.1) (M₂ i.2)) ( by
  simp [-Matrix.kronecker, kronecker_conjTranspose]
  simp [←Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  simp [←Matrix.sum_kronecker_right, ←Matrix.sum_kronecker_left, hM₁, hM₂]
)



-- (CPTPMap.of_kraus_CPTPMap M₁ hM₁) ⊗ₖ (CPTPMap.of_kraus_CPTPMap M₂ hM₂) =


def two_qubit_bit_flip (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1-p) := (bit_flip_channel p hp1 hp2) ⊗ₖ (bit_flip_channel p hp1 hp2)

def of_kraus_prob_unitary {n : ℕ} (pfun : Fin n → ℝ) (hpfun1 : ∀ i, 0 ≤ pfun i) (hpfun2 : ∀ i, 0 ≤ 1 - pfun i)
: CPTPMap Qubit Qubit ℂ := sorry
