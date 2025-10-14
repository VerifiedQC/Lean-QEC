import QuantumInfo
import ClassicalInfo
import ClassicalInfo.Capacity
import ATPTest.Tensors

open Qubit

def I : 𝐔[Qubit] :=
  ⟨!![Complex.I, 0; 0, Complex.I], by constructor <;> matrix_expand⟩

def qub_zero : Ket Qubit := {
  vec := ![1, 0]
  normalized' := (by simp
  )
}

def qub_one : Ket Qubit := {
  vec := ![0, 1]
  normalized' := (by simp
  )
}

noncomputable def qub_plus : Ket Qubit := {
  vec := ![(√2)⁻¹, (√2)⁻¹]
  normalized' := (by norm_num)
}

noncomputable def qub_minus : Ket Qubit := {
  vec := ![(√2)⁻¹, -(√2)⁻¹]
  normalized' := (by norm_num)
}

variable {k : Type*} [Fintype k] [DecidableEq k]

--thanks aristotle
theorem unitary_norm_preserve {k : Type*} [Fintype k] [DecidableEq k] (U : 𝐔[k]) (v: k → ℂ) :
  ∑ x, ‖(U.1.toLin' v) x‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  have h_norm : ∀ (v : k → ℂ), (∑ x : k, ‖(Matrix.toLin' U.val v) x‖ ^ 2) = (∑ x : k, ‖v x‖ ^ 2) := by
    -- Since $U$ is unitary, we have $\langle Uv, Uv \rangle = \langle v, v \rangle$.
    have h_inner : ∀ (v : k → ℂ), ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, v x * starRingEnd ℂ (v x) := by
      intro v
      have h_unitary : U.val.conjTranspose * U.val = 1 := by
        aesop;
        cases property ; aesop
      have h_unitary : ∀ (v : k → ℂ), ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, v x * starRingEnd ℂ (v x) := by
        intro v
        have h_inner : ∑ x : k, (U.val.mulVec v) x * starRingEnd ℂ ((U.val.mulVec v) x) = ∑ x : k, ∑ y : k, v y * starRingEnd ℂ (v x) * (U.val.conjTranspose * U.val) x y := by
          simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
          simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
        simp_all +decide [ Matrix.one_apply];
      exact h_unitary v;
    -- Since the norm squared of a complex number z is z * conjugate(z), we can rewrite the sums in terms of the inner product.
    have h_norm_sq : ∀ (v : k → ℂ), ∑ x : k, ‖(Matrix.toLin' U.val v) x‖ ^ 2 = ∑ x : k, (Matrix.toLin' U.val v) x * starRingEnd ℂ ((Matrix.toLin' U.val v) x) := by
      simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    intro v; specialize h_norm_sq v; specialize h_inner v; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;
    exact_mod_cast h_inner;
  -- Apply the hypothesis `h_norm` to the vector `v`.
  apply h_norm

def Ket.uapply (psi : Ket k) (U : 𝐔[k]) : Ket k where
  vec := U.1.toLin' psi.vec
  normalized' := by
    rewrite [unitary_norm_preserve]
    exact psi.normalized'

open Matrix

def unitary_fin_equiv {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (h: a ≃ b) :(𝐔[a] ≃ 𝐔[b]) where
  toFun U := ⟨(reindex h h) U.1, by
    have h_mem := U.2
    rw [mem_unitaryGroup_iff] at h_mem ⊢
    simp
    rw [star_eq_conjTranspose, conjTranspose_submatrix]
    simp [←star_eq_conjTranspose, h_mem]
    ⟩
  invFun U := ⟨(Matrix.reindex h.symm h.symm) U.1, by
    have h_mem := U.2
    rw [mem_unitaryGroup_iff] at h_mem ⊢
    simp [star_eq_conjTranspose]
    simp [←star_eq_conjTranspose, h_mem]
    ⟩
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    simp

def fin_pow_succ_equiv {n : ℕ} : (Fin 2 × Fin (2^n)) ≃ Fin (2^(n+1)) := by
  rewrite [Nat.pow_succ']
  exact finProdFinEquiv

def qubit_tensor {n : ℕ} (m : Fin n → 𝐔[Qubit]) : 𝐔[Fin (2^n)] :=
match n with
| 0 => 1
| n0+1 => (unitary_fin_equiv fin_pow_succ_equiv).toFun ((m 0) ⊗ᵤ (qubit_tensor (λ (x : Fin n0) => m ⟨x.val + 1, by simp [x.isLt]⟩)))

def herm_of_qubit_tensor_herm {n : ℕ} (m : Fin n → 𝐔[Qubit]) (Hm : ∀ x, Matrix.IsHermitian (m x).1) :
  Matrix.IsHermitian (qubit_tensor m).1 := by
  induction n with
  | zero => simp [qubit_tensor]
  | succ n ih => simp only [qubit_tensor, unitary_fin_equiv, reindex_apply, Equiv.symm_symm,
    unitary_kron, Equiv.toFun_as_coe, Equiv.coe_fn_mk, isHermitian_submatrix_equiv]
                 refine is_herm_of_kron_herm (Hm 0) ?_
                 refine ih ?_ (fun x => ?_)
                 apply Hm

noncomputable def Pauli : Finset (𝐔[Qubit]):= {1, X, Y, Z}

lemma pauli_herm {p : Pauli} : IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl) <;> matrix_expand [X, Y, Z]

variable {n : ℕ} (m : Fin n → Pauli)

def pauli_tensor : 𝐔[Fin (2^n)] :=
  qubit_tensor (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]


def pauli_tensor_herm : HermitianMat (Fin (2^n)) ℂ :=
  ⟨(pauli_tensor m).1, pauli_tensor_hermitian m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1) := sorry

--define negative and imaginary phase factors on unitary matrices

noncomputable def U_phase (U : 𝐔[k]) (z : ℂ) (hp: ‖z‖ = 1) : 𝐔[k] := ⟨z • U.val, by
  simp [unitary.mem_iff, smul_smul, mul_comm]
  rw [mul_comm, ←Complex.normSq_eq_conj_mul_self, Complex.coe_smul, Complex.normSq_eq_norm_sq, hp]
  simp
⟩

noncomputable def u_neg (U : 𝐔[k]) : 𝐔[k] := (U_phase U (-1) (by norm_num))

noncomputable def u_im (U : 𝐔[k]) : 𝐔[k] := (U_phase U Complex.I (by norm_num))

variable {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]

--aristotle generated!
theorem dotProduct_mul_eq {v₁ ψ₁: k₁ → ℂ} {v₂ ψ₂: k₂ → ℂ} :
  (fun (j : k₁ × k₂) => (v₁ j.1) * (v₂ j.2)) ⬝ᵥ (fun x => (ψ₁ x.1) * (ψ₂ x.2)) =
  (v₁ ⬝ᵥ ψ₁) * (v₂ ⬝ᵥ ψ₂) := by
    -- Apply the definition of matrix multiplication and the fact that the sum over a product space can be factored into the product of sums.
    have h_factor : ∑ x : k₁ × k₂, v₁ x.1 * ψ₁ x.1 * (v₂ x.2 * ψ₂ x.2) = (∑ x : k₁, v₁ x * ψ₁ x) * (∑ x : k₂, v₂ x * ψ₂ x) := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ x : k₁ × k₂, v₁ x.1 * ψ₁ x.1 * (v₂ x.2 * ψ₂ x.2) = ∑ x₁ : k₁, ∑ x₂ : k₂, v₁ x₁ * ψ₁ x₁ * (v₂ x₂ * ψ₂ x₂) := by
        -- Apply the theorem that allows us to rewrite the sum over a product type as an iterated sum.
        apply Finset.sum_product;
      simp +decide only [h_fubini, Finset.mul_sum _ _ _, Finset.sum_mul];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    -- By the properties of the dot product and matrix multiplication, we can rewrite the left-hand side of the equation.
    convert h_factor using 1;
    -- By the properties of the dot product and matrix multiplication, we can rewrite the left-hand side of the equation using the commutativity of multiplication.
    simp [dotProduct, mul_comm, mul_left_comm]


lemma Ket.prod_mul_kron (M₁ : Matrix k₁ k₁ ℂ) (M₂ : Matrix k₂ k₂ ℂ) (ψ₁ : Ket k₁) (ψ₂ : Ket k₂):
  (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M₁ M₂) *ᵥ (ψ₁ ⊗ ψ₂).vec = fun (i, j) ↦ ((M₁ *ᵥ ψ₁) i) * ((M₂ *ᵥ ψ₂) j) := by
  ext ⟨i₁, i₂⟩
  simp only [mulVec, kroneckerMap_apply, DFunLike.coe, prod]
  exact dotProduct_mul_eq

variable [DecidableEq k₁] [DecidableEq k₂]

lemma Ket.uapply_kron (U₁ : 𝐔[k₁]) (U₂ : 𝐔[k₂]) (ψ₁ : Ket k₁) (ψ₂ : Ket k₂) :
  (ψ₁ ⊗ ψ₂).uapply (Matrix.unitary_kron U₁ U₂) = (ψ₁.uapply U₁) ⊗ (ψ₂.uapply U₂) := by
  unfold Ket.uapply unitary_kron
  rw [Ket.mk.injEq, toLin'_apply, Ket.prod_mul_kron]
  simp only [toLin'_apply]
  simp [Ket.prod, DFunLike.coe]
