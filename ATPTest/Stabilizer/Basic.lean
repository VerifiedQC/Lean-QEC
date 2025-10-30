import ATPTest.States.Basic

variable {n : ℕ}

def stabilizes (U : 𝐔ₙ[n]) (ψ : PState n) := ψ.apply U = ψ

@[simp]
lemma stabilizes_apply (U : 𝐔ₙ[n]) (ψ : PState n) (hstab : stabilizes U ψ) : ψ.apply U = ψ := hstab

@[simp]
lemma stabilizes_apply' {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : Matrix.mulVec U ψ.vec = ψ.vec := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply] at hstab
  rwa [PState.mk.injEq] at hstab

variable {n₁ n₂ : ℕ}

theorem stab_prod {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} {ψ₁ : PState n₁} {ψ₂ : PState n₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs₂ : stabilizes U₂ ψ₂) :
  stabilizes (U₁ ⊗ₙ U₂) (ψ₁ ⊗ₖ ψ₂) := by
  unfold stabilizes
  rw [kron_mul_kron, hs₁, hs₂]
/-
theorem stab_of_stab_equiv {U : 𝐔[k₁]} {ψ : Ket k₁} (e : k₁ ≃ k₂) (hstab: stabilizes U ψ) :
  stabilizes (unitary_fin_equiv e U) (ket_fin_equiv e ψ) := sorry
-/

theorem stab_n_prod {n : ℕ} {um : Fin n → 𝐔ₙ[1]} {km : Fin n → PState 1} (hn : 0 < n)
  (hstab : ∀ x, stabilizes (um x) (km x)) :
  stabilizes (unitary_n_nkron hn um) (pstate_n_kron hn km) := by
    induction n with
    | zero => contradiction
    | succ n ih =>
      rcases n
      · exact hstab 0
      · simp only [unitary_n_nkron, pstate_n_kron]
        apply stab_prod (ih _ (fun x => (hstab _))) (hstab 0)

theorem one_stab_all {n : ℕ} (ψ : PState n) : stabilizes 1 ψ := by simp [stabilizes]

theorem inv_stab {n : ℕ} {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : stabilizes U⁻¹ ψ := by
  simp [stabilizes]
  rw [PState.mk.injEq]
  nth_rw 2 [←(Matrix.one_mulVec ψ.vec)]
  rw [←U.2.1, ←Matrix.mulVec_mulVec, stabilizes_apply' hstab]

--theorem for stabilizing sums?


theorem sum_stab {n : ℕ} {ψ₁ ψ₂ : PState n} {a b : ℂ} {U : 𝐔ₙ[n]} (hab: ‖a^2‖+‖b^2‖ = 1) (h_orth : ψ₁.orth ψ₂)
  (hstab1 : stabilizes U ψ₁) (hstab2 : stabilizes U ψ₂) :
  stabilizes U (ψ₁.sum ψ₂ a b hab h_orth) := by
  simp [stabilizes, PState.sum, Matrix.mulVec_add, Matrix.mulVec_smul,
  stabilizes_apply' hstab1, stabilizes_apply' hstab2]



--think harder about how i want to define this: subtype for pauli tensors?
def stabilizer_set {n : ℕ} (ψ : PState n) :=
  {U // stabilizes U ψ}

variable {n : ℕ}



--wait, how do i cX transversally? just controllize 1 ⊗ X?
--clearly if this is to be easier to work with i have to
--change how this is done



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



variable (n : ℕ) (k : ℕ)

def QCode := PState k → PState n

noncomputable section

variable {n : ℕ} {k : ℕ} (hn : 0 < n)


def QCode.stabilizers (C : QCode n k) :=
  {U | (∀ ψ, stabilizes U (C ψ)) ∧ U ∈ PauliGroup hn}

lemma pauli_commute_with_phase {U₁ U₂ : 𝐔[Fin (2^n)]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : ∃ (p : pgroup_phases),  U₁ * U₂ = U_phase (U₂ * U₁) p := sorry

def pauli_pauli_phase {U₁ U₂ : 𝐔[Fin (2^n)]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pgroup_phases := Classical.choose (pauli_commute_with_phase hn h1 h2)

def QCode.syndrome {k : ℕ} (C : QCode n k) {E : 𝐔[Fin (2^n)]} (hE : E ∈ PauliGroup hn)
   : C.stabilizers hn → pgroup_phases := fun U => pauli_pauli_phase hn hE U.2.2

def QCode.distinguishes (C : QCode n k) {E₁ E₂} (hE₁ : E₁ ∈ PauliGroup hn) (hE₂ : E₂ ∈ PauliGroup hn) := C.syndrome hn hE₁ ≠ C.syndrome hn hE₂

--to detect errors, it suffices to distinguish an error and the I pauli
def Qcode.detects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ E (hE : E ∈ PauliGroup hn),
  pauli_weight hn hE ≤ w → C.distinguishes hn hE (mem_PauliGroup_id hn)

def Qcode.corrects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ E₁ (hE₁ : E₁ ∈ PauliGroup hn), ∀ E₂ (hE₂ : E₂ ∈ PauliGroup hn),
  (PauliGroup.phase hn hE₁).1 = ⟨1, by norm_num⟩ → (PauliGroup.phase hn hE₂).1 = ⟨1, by norm_num⟩ →
  pauli_weight hn hE₁ ≤ w → pauli_weight hn hE₂ ≤ w → C.distinguishes hn hE₁ hE₂

def Qcode.detects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli):= ∀ E (hE : E ∈ PauliGroup hn),
  (pauli_only hn hE P) → pauli_weight hn hE ≤ w → C.distinguishes hn hE (mem_PauliGroup_id hn)

def Qcode.corrects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli) := ∀ E₁ (hE₁ : E₁ ∈ PauliGroup hn), ∀ E₂ (hE₂ : E₂ ∈ PauliGroup hn),
  (pauli_only hn hE₁ P) → (pauli_only hn hE₂ P) → (PauliGroup.phase hn hE₁).1 = ⟨1, by norm_num⟩ → (PauliGroup.phase hn hE₂).1 = ⟨1, by norm_num⟩ →
  pauli_weight hn hE₁ ≤ w → pauli_weight hn hE₂ ≤ w → C.distinguishes hn hE₁ hE₂

--maybe ensure that stabilizers are pauli matrices?
--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?
