import QuantumInfo
import ClassicalInfo
import ClassicalInfo.Capacity
import ATPTest.Tensors

open Qubit

def I : 𝐔[Qubit] :=
  ⟨!![Complex.I, 0; 0, Complex.I], by constructor <;> matrix_expand⟩

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

def unitary_n_tensor {n : ℕ} (hn : 0 < n) (m : Fin n → 𝐔[Qubit]) : 𝐔[Fin (2^n)] :=
match n with
| 0 => by contradiction
| 1 => (m 0)
| n₀+2 => (unitary_fin_equiv fin_pow_succ_equiv).toFun ((m 0) ⊗ᵤ (unitary_n_tensor (by norm_num) (λ (x : Fin (n₀+1)) => m ⟨x.val + 1, by simp [x.isLt]⟩)))

def herm_of_qubit_tensor_herm {n : ℕ} (hn : 0 < n) (m : Fin n → 𝐔[Qubit]) (Hm : ∀ x, Matrix.IsHermitian (m x).1) :
  Matrix.IsHermitian (unitary_n_tensor hn m).1 := by
  induction n with
  | zero => contradiction
  | succ n ih => cases n
                 · simp [unitary_n_tensor, (Hm 0)]
                 · simp only [unitary_n_tensor, unitary_fin_equiv, reindex_apply, Equiv.symm_symm, unitary_kron, Equiv.toFun_as_coe, Equiv.coe_fn_mk, isHermitian_submatrix_equiv]
                   refine is_herm_of_kron_herm (Hm 0) ?_
                   apply ih
                   intro x
                   apply Hm

noncomputable def Pauli : Finset (𝐔[Qubit]):= {1, X, Y, Z}

lemma pauli_herm {p : Pauli} : IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl) <;> matrix_expand [X, Y, Z]

variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

def pauli_tensor : 𝐔[Fin (2^n)] :=
  unitary_n_tensor hn (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor hn m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]


def pauli_tensor_herm : HermitianMat (Fin (2^n)) ℂ :=
  ⟨(pauli_tensor hn m).1, pauli_tensor_hermitian hn m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)


--define negative and imaginary phase factors on unitary matrices

variable {k : Type*} [Fintype k] [DecidableEq k]

noncomputable section

structure phase where
  z : ℂ
  z_norm : ‖z‖ = 1
deriving DecidableEq

noncomputable def U_phase (U : 𝐔[k]) (z : phase) : 𝐔[k] := ⟨z.1 • U.val, by
  simp [unitary.mem_iff, smul_smul, mul_comm]
  rw [mul_comm, ←Complex.normSq_eq_conj_mul_self, Complex.coe_smul, Complex.normSq_eq_norm_sq, z.2]
  simp
⟩

noncomputable def u_neg (U : 𝐔[k]) : 𝐔[k] := (U_phase U ⟨-1, by norm_num⟩)

noncomputable def u_im (U : 𝐔[k]) : 𝐔[k] := (U_phase U ⟨Complex.I, by norm_num⟩)

def is_pauli_product (U : 𝐔[Fin (2^n)]) := ∃ (m : Fin n → Pauli), pauli_tensor hn m = U

noncomputable def pgroup_phases : Finset phase := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨Complex.I, by norm_num⟩, ⟨-Complex.I, by norm_num⟩}

--instance : Fintype (Fin n → { x // x ∈ Pauli }) := sorry

noncomputable def pauli_products_n : Finset (𝐔[Fin (2^n)]) := Finset.image (λ m => pauli_tensor hn m) Finset.univ

--see how much i can do with set

--def PauliGroup : Set 𝐔[(Fin (2^n))] := {U_phase (pauli_tensor hn m) z | (m : Fin n → Pauli) (z : phase)}

--def PauliGroup : Finset 𝐔[Fin (2^n)] := Finset.image (λ (x : (pauli_products_n hn) × pgroup_phases) => U_phase x.1 x.2 sorry) (Finset.univ pgroup_phases)
noncomputable def PauliGroup (hn : 0 < n) : Finset 𝐔[(Fin (2^n))] :=
  (Finset.univ.product pgroup_phases).image (λ mp =>
    let m := mp.1
    let z := mp.2
    U_phase (pauli_tensor hn m) z)

lemma mem_PauliGroup_iff (U : 𝐔[Fin (2^n)]) (hn : 0 < n) : U ∈ PauliGroup hn ↔ ∃ m, (∃ z : pgroup_phases, U_phase (pauli_tensor hn m) z = U) := by
  unfold PauliGroup
  rw [Finset.mem_image]
  simp

def PauliGroup.map {U : 𝐔[Fin (2^n)]} (hn : 0 < n)
(hU : U ∈ PauliGroup hn) : Fin n → Pauli := Classical.choose ((mem_PauliGroup_iff U hn).1 hU)


def PauliGroup.phase {U : 𝐔[Fin (2^n)]} (hn : 0 < n)
(hU : U ∈ PauliGroup hn) : pgroup_phases := Classical.choose ((mem_PauliGroup_iff U hn).mp hU).choose_spec

lemma mem_PauliGroup_id (hn : 0 < n) : 1 ∈ PauliGroup hn := sorry

lemma rep_unique {U : 𝐔[Fin (2^n)]} (m₁ m₂ : Fin n → Pauli)
(z₁ z₂ : pgroup_phases) (hm₁ : U_phase (pauli_tensor hn m₁) z₁ = U) (hm₂ : U_phase (pauli_tensor hn m₂) z₂ = U)
 : m₁ = m₂ ∧ z₁ = z₂ := sorry

def pauli_weight {U : 𝐔[Fin (2^n)]} (hU : U ∈ PauliGroup hn) : ℕ := (Finset.univ.filter (fun i => (PauliGroup.map hn hU) i ≠ I)).card
