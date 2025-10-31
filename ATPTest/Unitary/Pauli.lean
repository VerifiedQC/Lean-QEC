import ATPTest.Unitary.Basic

open Qubit

def pX := (unitary_fin_equiv beq) X
def pY := (unitary_fin_equiv beq) Y
def pZ := (unitary_fin_equiv beq) Z


noncomputable def Pauli : Finset (𝐔ₙ[1]):= {1, pX, pY, pZ}

lemma pauli_herm {p : Pauli} : Matrix.IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  sorry
  --rcases hx with (rfl | rfl | rfl | rfl) <;> matrix_expand [X, Y, Z]

variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

def pauli_tensor : 𝐔ₙ[n] :=
  unitary_n_nkron hn (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor hn m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]

  def pauli_tensor_herm : HermitianMat (BitVec n) ℂ :=
  ⟨_, pauli_tensor_hermitian hn m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)

def is_pauli_product (U : 𝐔ₙ[n]) := ∃ (m : Fin n → Pauli), pauli_tensor hn m = U

noncomputable def pgroup_phases : Finset phase := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨Complex.I, by norm_num⟩, ⟨-Complex.I, by norm_num⟩}

--instance : Fintype (Fin n → { x // x ∈ Pauli }) := sorry

noncomputable def pauli_products_n : Finset (𝐔ₙ[n]) := Finset.image (λ m => pauli_tensor hn m) Finset.univ

--see how much i can do with set

--def PauliGroup : Set 𝐔[(Fin (2^n))] := {U_phase (pauli_tensor hn m) z | (m : Fin n → Pauli) (z : phase)}

--def PauliGroup : Finset 𝐔[Fin (2^n)] := Finset.image (λ (x : (pauli_products_n hn) × pgroup_phases) => U_phase x.1 x.2 sorry) (Finset.univ pgroup_phases)
noncomputable def PauliGroup : Finset 𝐔ₙ[n] :=
  (Finset.univ.product pgroup_phases).image (λ mp =>
    let m := mp.1
    let z := mp.2
    U_phase (pauli_tensor hn m) z)

lemma mem_PauliGroup_iff (U : 𝐔ₙ[n]) : U ∈ PauliGroup hn ↔ ∃ m, (∃ z : pgroup_phases, U_phase (pauli_tensor hn m) z = U) := by
  unfold PauliGroup
  rw [Finset.mem_image]
  simp

noncomputable def PauliGroup.map {U : 𝐔ₙ[n]}
(hU : U ∈ PauliGroup hn) : Fin n → Pauli := Classical.choose ((mem_PauliGroup_iff hn U).1 hU)


noncomputable def PauliGroup.phase {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn)
: pgroup_phases := Classical.choose ((mem_PauliGroup_iff hn U).mp hU).choose_spec

lemma mem_PauliGroup_id : 1 ∈ PauliGroup hn := sorry

lemma rep_unique {U : 𝐔ₙ[n]} (m₁ m₂ : Fin n → Pauli)
(z₁ z₂ : pgroup_phases) (hm₁ : U_phase (pauli_tensor hn m₁) z₁ = U) (hm₂ : U_phase (pauli_tensor hn m₂) z₂ = U)
 : m₁ = m₂ ∧ z₁ = z₂ := sorry

noncomputable def pauli_weight {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) : ℕ := (Finset.univ.filter (fun i => (PauliGroup.map hn hU) i ≠ (1 : 𝐔ₙ[1]))).card

def pauli_only {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) (P : Pauli) := ∀ x, ((PauliGroup.map hn hU) x = (1 : 𝐔ₙ[1]) ∨ (PauliGroup.map hn hU) x = P)
