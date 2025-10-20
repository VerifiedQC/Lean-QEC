import ATPTest.Braket

variable {k : Type*} [Fintype k] [DecidableEq k]

def stabilizes (U : 𝐔[k]) (ψ : Ket k) := ψ.uapply U = ψ

@[simp]
lemma stabilizes_apply (U : 𝐔[k]) (ψ : Ket k) (hstab : stabilizes U ψ) : ψ.uapply U = ψ := hstab

@[simp]
lemma stabilizes_apply' {U : 𝐔[k]} {ψ : Ket k} (hstab : stabilizes U ψ) : Matrix.mulVec U ψ.vec = ψ.vec := by
  simp only [stabilizes, Ket.uapply, Matrix.toLin'_apply] at hstab
  rwa [Ket.mk.injEq] at hstab



--prove:
-- X stabilizes +
-- Z stabilizes 0
-- a product of stabilizers stabilizes
-- n-product of stabilizers stabilizes

open Qubit

theorem X_stab_plus : stabilizes X qub_plus := by
  unfold stabilizes Ket.uapply qub_plus
  rw [Ket.mk.injEq, Matrix.toLin'_apply]
  funext i
  fin_cases i <;> simp [X]

theorem Z_stab_zero : stabilizes Z qub_zero := by
  unfold stabilizes Ket.uapply qub_zero
  rw [Ket.mk.injEq, Matrix.toLin'_apply]
  funext i
  fin_cases i <;> simp [Z]

variable {k₁ k₂ : Type*} [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]

theorem stab_prod {U₁ : 𝐔[k₁]} {U₂ : 𝐔[k₂]} {ψ₁ : Ket k₁} {ψ₂ : Ket k₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs₂ : stabilizes U₂ ψ₂) :
  stabilizes (Matrix.unitary_kron U₁ U₂) (ψ₁ ⊗ ψ₂) := by
  unfold stabilizes
  rw [Ket.uapply_kron, hs₁, hs₂]

theorem stab_of_stab_equiv {U : 𝐔[k₁]} {ψ : Ket k₁} (e : k₁ ≃ k₂) (hstab: stabilizes U ψ) :
  stabilizes (unitary_fin_equiv e U) (ket_fin_equiv e ψ) := sorry

theorem stab_n_prod {n : ℕ} {um : Fin n → 𝐔[Qubit]} {km : Fin n → Ket Qubit} (hn : 0 < n)
  (hstab : ∀ x, stabilizes (um x) (km x)) :
  stabilizes (unitary_n_tensor hn um) (ket_n_tensor hn km) := by
    induction n with
    | zero => contradiction
    | succ n ih =>
      rcases n
      · exact hstab 0
      · simp only [unitary_n_tensor, Equiv.toFun_as_coe, ket_n_tensor]
        apply stab_of_stab_equiv fin_pow_succ_equiv (stab_prod (hstab 0)
         (ih _ (fun x => (hstab _))))

theorem one_stab_all (ψ : Ket k) : stabilizes 1 ψ := by simp [stabilizes, Ket.uapply]

theorem inv_stab {U : 𝐔[k]} {ψ : Ket k} (hstab : stabilizes U ψ) : stabilizes U⁻¹ ψ := by
  simp [stabilizes, Ket.uapply]
  rw [Ket.mk.injEq]
  nth_rw 2 [←(Matrix.one_mulVec ψ.vec)]
  rw [←U.2.1, ←Matrix.mulVec_mulVec, stabilizes_apply' hstab]

--theorem for stabilizing sums?

def Ket.sum (ψ₁ ψ₂ : Ket k) (a b : ℂ) (hab: ‖a^2‖+‖b^2‖ = 1) : Ket k where
  vec := a • ψ₁.vec + b • ψ₂.vec
  normalized' := sorry


theorem sum_stab {ψ₁ ψ₂ : Ket k} {a b : ℂ} {U : 𝐔[k]} (hab: ‖a^2‖+‖b^2‖ = 1)
  (hstab1 : stabilizes U ψ₁) (hstab2 : stabilizes U ψ₂) :
  stabilizes U (ψ₁.sum ψ₂ a b hab) := by
  simp [stabilizes, Ket.uapply, Ket.sum, Matrix.mulVec_add, Matrix.mulVec_smul,
  stabilizes_apply' hstab1, stabilizes_apply' hstab2]



--think harder about how i want to define this: subtype for pauli tensors?
def stabilizer_set (ψ : Ket k) :=
  {U // stabilizes U ψ}

variable {n : ℕ}

open Qubit

variable (ψ : Ket Qubit)

--wait, how do i cX transversally? just controllize 1 ⊗ X?
--clearly if this is to be easier to work with i have to
--change how this is done
def three_qubit_encode : Ket (Qubit × Qubit × Qubit) :=
  ((Ket.prod ψ (Ket.prod qub_zero qub_zero)).uapply
   (unitary_fin_equiv (Equiv.prodAssoc _ _ _)
   (Matrix.unitary_kron C[X] (1 : 𝐔[Qubit])))).uapply --CX(2, 3)
   C[Matrix.unitary_kron (1 : 𝐔[Qubit]) X] --CX(1, 3)

lemma single_qub_normalized : ‖(ψ.vec 0)^2‖+‖(ψ.vec 1)^2‖ = 1 := by
  convert ψ.normalized'
  simp

lemma one_qub_decomp : ψ = qub_zero.sum qub_one (ψ.vec 0) (ψ.vec 1) (single_qub_normalized _) := sorry

lemma three_qubit_encode_correct : three_qubit_encode ψ =
  (qub_zero ⊗ (qub_zero ⊗ qub_zero)).sum
  (qub_one ⊗ (qub_one ⊗ qub_one)) (ψ.vec 0) (ψ.vec 1) (single_qub_normalized _)
  := sorry

/-
structure code (l c : ℕ) where --l is logical qubits, c is code size
  encoding : Ket (Fin (2^l)) → Ket (Fin (2^c))
  stabilizers : Finset 𝐔[Fin (2^c)]
  stab_cond : ∀ ψ, ∀ U ∈ stabilizers, stabilizes U (encoding ψ)

--requires 0 < c as can't call a unitary on 0 qubits a pauli matrix for
--various ease of use reasons
structure pauli_code (l c : ℕ) (hc : 0 < c) where
  code : code l c
  stab_pauli : ∀ U ∈ code.stabilizers, is_pauli_product hc U
-/



variable {n : ℕ} (hn : 0 < n)

def QCode (k : ℕ) := Ket (Fin (2^k)) → Ket (Fin (2^n))

noncomputable section

def QCode.stabilizers {k : ℕ} (C : QCode k) :=
  {U | (∀ ψ, stabilizes U (C ψ)) ∧ U ∈ PauliGroup hn}

lemma pauli_commute_with_phase {U₁ U₂ : 𝐔[Fin (2^n)]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : ∃ (p : pgroup_phases),  U₁ * U₂ = U_phase (U₂ * U₁) p := sorry

def pauli_pauli_phase {U₁ U₂ : 𝐔[Fin (2^n)]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pgroup_phases := Classical.choose (pauli_commute_with_phase hn h1 h2)

def syndrome {k : ℕ} {E : 𝐔[Fin (2^n)]} (hE : E ∈ PauliGroup hn)
  (C : QCode k) : C.stabilizers hn → pgroup_phases := fun U => pauli_pauli_phase hn hE U.2.2

lemma pauli_weight {U : 𝐔[Fin (2^n)]} (hU : U ∈ PauliGroup hn) : ℕ := sorry




--maybe ensure that stabilizers are pauli matrices?
--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?
