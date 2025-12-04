import ATPTest.States.Basic
import ATPTest.Unitary.Paulis.Basic
variable {n : ℕ}

def stabilizes (U : 𝐔ₙ[n]) (ψ : PState n) := ψ.apply U = ψ

@[simp]
lemma stabilizes_apply (U : 𝐔ₙ[n]) (ψ : PState n) (hstab : stabilizes U ψ) : ψ.apply U = ψ := hstab

@[simp]
lemma stabilizes_apply' {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : Matrix.mulVec U ψ.vec = ψ.vec := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply] at hstab
  rwa [Ket.mk.injEq] at hstab

variable {n₁ n₂ : ℕ}

theorem stab_prod {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} {ψ₁ : PState n₁} {ψ₂ : PState n₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs₂ : stabilizes U₂ ψ₂) :
  stabilizes (U₁ ⊗ₙ U₂) (ψ₁ ⊗ₚ ψ₂) := by
  unfold stabilizes
  rw [kron_mul_kron, hs₁, hs₂]
/-
theorem stab_of_stab_equiv {U : 𝐔[k₁]} {ψ : Ket k₁} (e : k₁ ≃ k₂) (hstab: stabilizes U ψ) :
  stabilizes (unitary_fin_equiv e U) (ket_fin_equiv e ψ) := by admit
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
  rw [Ket.mk.injEq]
  nth_rw 2 [←(Matrix.one_mulVec ψ.vec)]
  rw [←U.2.1, ←Matrix.mulVec_mulVec, stabilizes_apply' hstab]

theorem mul_stab {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]} {ψ : PState n} (hstab₁ : stabilizes U₁ ψ) (hstab₂ : stabilizes U₂ ψ) :
  stabilizes (U₁ * U₂) ψ := by
  simp [stabilizes]
  rw [Ket.mk.injEq, ←Matrix.mulVec_mulVec,
  stabilizes_apply' hstab₂, stabilizes_apply' hstab₁]


--theorem for stabilizing sums?


theorem sum_stab {n : ℕ} {ψ₁ ψ₂ : PState n} {a b : ℂ} {U : 𝐔ₙ[n]} (hab: ‖a‖^2+‖b‖^2 = 1) (h_orth : ψ₁.orth ψ₂)
  (hstab1 : stabilizes U ψ₁) (hstab2 : stabilizes U ψ₂) :
  stabilizes U (ψ₁.sum ψ₂ a b hab h_orth) := by
  simp [stabilizes, PState.sum, Matrix.mulVec_add, Matrix.mulVec_smul]
  simp [DFunLike.coe, stabilizes_apply' hstab1, stabilizes_apply' hstab2]

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


--MOVE TO PAULI FILE AFTER YI FINISHES HIS REWRITE:
lemma pauli_mul {n : ℕ} (hn : 0 < n) {U₁ U₂ : 𝐔ₙ[n]}
 (hP₁ : U₁ ∈ PauliGroup hn) (hP₂ : U₂ ∈ PauliGroup hn) :
 U₁ * U₂ ∈ PauliGroup hn := by sorry

--maybe tedious proof?
lemma pauli_inv {n : ℕ} (hn : 0 < n) {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn)
  : U⁻¹ ∈ PauliGroup hn := by sorry

--want to prove this one soon
lemma pauli_commute_or_anticommute {n : ℕ} (hn : 0 < n) {U₁ U₂ : 𝐔ₙ[n]}
  (hU₁ : U₁ ∈ PauliGroup hn) (hU₂ : U₂ ∈ PauliGroup hn) : U₁ * U₂ = U₂ * U₁ ∨ U₁ * U₂ = - U₂ * U₁ := sorry


variable (n : ℕ) (k : ℕ)

def QCode := PState k → PState n

noncomputable section

variable {n : ℕ} {k : ℕ} (hn : 0 < n)

def QCode.stabilizers (C : QCode n k) :=
  {U | (∀ ψ, stabilizes U (C ψ)) ∧ U ∈ PauliGroup hn}


lemma QCode.stabilizer_closed_under_mul (C : QCode n k) {a b : 𝐔ₙ[n]} (ha : a ∈ C.stabilizers hn) (hb : b ∈ C.stabilizers hn)
  : a * b ∈ C.stabilizers hn := by
  rcases ha with ⟨a_stab, a_pauli⟩
  rcases hb with ⟨b_stab, b_pauli⟩
  constructor
  · intros ψ
    exact mul_stab (a_stab _) (b_stab _)
  exact pauli_mul hn a_pauli b_pauli

lemma QCode.stabilizer_closed_under_inv (C : QCode n k) {x : 𝐔ₙ[n]} (hx : x ∈ C.stabilizers hn) : x⁻¹ ∈ C.stabilizers hn := by
  rcases hx with ⟨x_stab, x_pauli⟩
  refine ⟨fun ψ => inv_stab (x_stab ψ), pauli_inv hn x_pauli⟩

def stabilizer_group (C : QCode n k) : Subgroup (𝐔ₙ[n]) where
  carrier := C.stabilizers hn
  mul_mem' := by intros a b ha hb; exact C.stabilizer_closed_under_mul hn ha hb
  one_mem' := by refine ⟨fun ψ => one_stab_all _, mem_PauliGroup_id hn⟩
  inv_mem' := by intros x hx; exact C.stabilizer_closed_under_inv hn hx

def PState.zero {n : ℕ} (hn : 0 < n) := pstate_n_kron hn (fun _ => qub_zero)



--easy proof, see if aristotle can do this
lemma PState.ne_zero {n : ℕ} {ψ : PState n} : ψ.vec ≠ 0 := sorry

lemma neg_one_not_stab (C : QCode n k) (hk : 0 < k) : u_neg 1 ∉ C.stabilizers hn := by
  rintro ⟨h_stab, h_pauli⟩
  have:= h_stab (PState.zero hk)
  unfold stabilizes PState.apply u_neg U_phase at this
  rw [Ket.mk.injEq, Matrix.toLin'_apply] at this
  simp [Matrix.neg_mulVec] at this
  apply PState.ne_zero
  rw [←neg_eq_self]
  exact this


--this is untrue if k=0: If the message space is trivial, then every member of pauli group is a stabilizer.
--As pauli group is noncommutative, this is then untrue
theorem stab_comm (C : QCode n k) (hk : 0 < k) : IsMulCommutative (stabilizer_group hn C) := by
  refine ⟨⟨by rintro ⟨a, ha⟩ ⟨b, hb⟩
              simp
              rcases pauli_commute_or_anticommute hn ha.2 hb.2 with comm | anticomm
              · assumption
              have abstab := ((stabilizer_group hn C).mul_mem' ha hb).1 (PState.zero hk)
              rw [anticomm] at abstab
              unfold stabilizes PState.apply at abstab
              rw [Ket.mk.injEq, Matrix.toLin'_apply] at abstab
              simp only [neg_mul, Matrix.neg_unitary_val,
                Submonoid.coe_mul, Matrix.neg_mulVec, ←Matrix.mulVec_mulVec,
                stabilizes_apply' (ha.1 _), stabilizes_apply' (hb.1 _)
                ] at abstab
              apply absurd (neg_eq_self.1 abstab) (PState.ne_zero)

  ⟩⟩

abbrev Pauli_of_stab {k} {C : QCode n k} (S : C.stabilizers hn) : PauliGroup hn :=
  ⟨S.1, S.2.2⟩

def QCode.syndrome {k : ℕ} (C : QCode n k) (E : PauliGroup hn)
   : C.stabilizers hn → pgroup_phases := fun U => pauli_pauli_phase hn E (Pauli_of_stab hn U)

def QCode.distinguishes (C : QCode n k) (E₁ : PauliGroup hn) (E₂ : PauliGroup hn) := C.syndrome hn E₁ ≠ C.syndrome hn E₂

--to detect errors, it suffices to distinguish an error and the I pauli
def Qcode.unique_detects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ (E : PauliGroup hn),
  pauli_weight hn E ≤ w → E ≠ Pauli1 hn → C.distinguishes hn E (Pauli1 hn)

def Qcode.unique_corrects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ (E₁ E₂ : PauliGroup hn),
  (PauliGroup.phase hn E₁).1 = ⟨1, by norm_num⟩ → (PauliGroup.phase hn E₂).1 = ⟨1, by norm_num⟩ →
  pauli_weight hn E₁ ≤ w → pauli_weight hn E₂ ≤ w → E₁ ≠ E₂ → C.distinguishes hn E₁ E₂

def Qcode.unique_detects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli):= ∀ (E : PauliGroup hn),
  (pauli_only hn E P) → pauli_weight hn E ≤ w → E ≠ Pauli1 hn → C.distinguishes hn E (Pauli1 hn)

--unique distinguishing
def Qcode.unique_corrects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli) := ∀ (E₁ E₂ : PauliGroup hn),
  (pauli_only hn E₁ P) → (pauli_only hn E₂ P) →
  PauliGroup.phase hn E₁ = 1 → PauliGroup.phase hn E₂ = 1 →
  pauli_weight hn E₁ ≤ w → pauli_weight hn E₂ ≤ w → E₁ ≠ E₂ → C.distinguishes hn E₁ E₂

theorem QCode.distinguishes_of_exists_dist_stab {k : ℕ} (C : QCode n k) (E₁ : PauliGroup hn) (E₂ : PauliGroup hn) :
  C.distinguishes hn E₁ E₂ ↔
  ∃ S : C.stabilizers hn,
    let SP : PauliGroup hn := Pauli_of_stab hn S
    pauli_pauli_phase hn E₁ SP ≠ pauli_pauli_phase hn E₂ SP := by
  constructor
  · -- aesop?
    sorry
  -- TODO FIX
  /-
  constructor
  · intro hD
    rcases (Function.ne_iff.1 hD) with ⟨S, hS⟩
    refine ⟨S, hS⟩
  rintro ⟨S, hS⟩
  apply Function.ne_iff.2 ⟨S, hS⟩
  -/
  sorry

--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?
