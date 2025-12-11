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

theorem one_stab_all {n : ℕ} (ψ : PState n) : stabilizes 1 ψ := by simp [stabilizes]


theorem stab_n_prod {n : ℕ} {um : Fin n → 𝐔ₙ[1]} {km : Fin n → PState 1}
  (hstab : ∀ x, stabilizes (um x) (km x)) :
  stabilizes (unitary_n_nkron um) (pstate_n_kron km) := by
    induction n with
    | zero => simp [unitary_n_nkron, one_stab_all]
    | succ n ih =>
      simp only [unitary_n_nkron, pstate_n_kron]
      apply stab_prod (ih (fun x => (hstab _))) (hstab 0)

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



variable (n : ℕ) (k : ℕ)

def QCode := PState k → PState n

noncomputable section

variable {n : ℕ} {k : ℕ} (hn : 0 < n)

def QCode.stabilizers (C : QCode n k) :=
  {U : PauliGroup n | (∀ ψ, stabilizes U (C ψ))}


lemma QCode.stabilizer_closed_under_mul (C : QCode n k) {a b : PauliGroup n} (ha : a ∈ C.stabilizers) (hb : b ∈ C.stabilizers)
  : ⟨(a : 𝐔ₙ[n]) * b, pauli_mul' _ _⟩  ∈ C.stabilizers := by
  intros ψ
  exact mul_stab (ha _) (hb _)

lemma QCode.stabilizer_closed_under_inv (C : QCode n k) {x : PauliGroup n} (hx : x ∈ C.stabilizers) : ⟨x⁻¹, pauli_inv (by aesop)⟩ ∈ C.stabilizers := by
  intros ψ
  exact inv_stab (hx ψ)

def stabilizer_group (C : QCode n k) : Subgroup (@PauliGroup_group n) where
  carrier := C.stabilizers
  mul_mem' := by intros a b ha hb; exact C.stabilizer_closed_under_mul ha hb
  one_mem' := fun ψ => one_stab_all (C ψ)
  inv_mem' := by intros x hx; exact C.stabilizer_closed_under_inv hx

def PState.zero {n : ℕ} := pstate_n_kron (fun (_ : Fin n) => qub_zero)


--easy proof, see if aristotle can do this
lemma PState.ne_zero {n : ℕ} {ψ : PState n} : ψ.vec ≠ 0 := sorry


--oops it's not actually easy to state -1 as a pauli
/-
lemma neg_one_not_stab (C : QCode n k) : U_neg 1 ∉ C.stabilizers := by
  rintro ⟨h_stab, h_pauli⟩
  have:= h_stab PState.zero
  unfold stabilizes PState.apply u_neg U_phase at this
  rw [Ket.mk.injEq, Matrix.toLin'_apply] at this
  simp [Matrix.neg_mulVec] at this
  apply PState.ne_zero
  rw [←neg_eq_self]
  exact this
-/

--i messed this one up too

/-
theorem stab_comm (C : QCode n k) : IsMulCommutative (stabilizer_group C) := by
  refine ⟨⟨by intro a b
              rcases pauli_commute_or_anticommute a.1.2 b.1.2 with comm | anticomm
              ·
              have abstab := ((stabilizer_group C).mul_mem' ha hb).1 PState.zero
              rw [anticomm] at abstab
              unfold stabilizes PState.apply at abstab
              rw [Ket.mk.injEq, Matrix.toLin'_apply] at abstab
              simp only [neg_mul, Matrix.neg_unitary_val,
                Submonoid.coe_mul, Matrix.neg_mulVec, ←Matrix.mulVec_mulVec,
                stabilizes_apply' (ha.1 _), stabilizes_apply' (hb.1 _)
                ] at abstab
              apply absurd (neg_eq_self.1 abstab) (PState.ne_zero)
  ⟩⟩
-/

/-
abbrev Pauli_of_stab {k} {C : QCode n k} (S : C.stabilizers) : PauliGroup n :=
  ⟨S.1, S.2.2⟩
-/


noncomputable instance {n k} (C : QCode n k) : DecidablePred (fun (N : ↑𝐔ₙ[n]) => ∀ S ∈ C.stabilizers, N * S = S * N) := Classical.decPred _

def QCode.normalizer {k : ℕ} (C : QCode n k)  := {N : PauliGroup n | ∀ S ∈ C.stabilizers, (S : 𝐔ₙ[n]) * N = N * S}

lemma not_mem_normalizer_iff {k : ℕ} (C : QCode n k) (E : PauliGroup n) : E ∉ C.normalizer ↔ ∃ S ∈ C.stabilizers, (S : 𝐔ₙ[n]) * E ≠ E * S := by
  unfold QCode.normalizer
  constructor <;> simp

def QCode.normalizer' {k : ℕ} (C : QCode n k) := {N : PauliGroup n | ∀ S ∈ C.stabilizers, (S : 𝐔ₙ[n]) * N = N * S ∧ PauliGroup.phase N = pgphase_1}

def QCode.undetectable {k : ℕ} (C : QCode n k) (E : PauliGroup n) := E ∈ C.normalizer ∧ ↑E ∉ C.stabilizers

def QCode.detectable {k : ℕ} (C : QCode n k) (E : PauliGroup n) := ¬ C.undetectable E

def QCode.corrects_error_set {k : ℕ} (C : QCode n k) (E_set : Finset (PauliGroup n)) :=
  ∀ E F : (PauliGroup n), E ∈ E_set → F ∈ E_set → ⟨(E.1)⁻¹ * F.1, pauli_mul (pauli_inv (by aesop)) (by aesop)⟩ ∉ (C.normalizer \ C.stabilizers)

def QCode.syndrome {k : ℕ} (C : QCode n k) (E : PauliGroup n)
   : C.stabilizers → pgroup_phases := fun U => pauli_pauli_phase E U

def QCode.distinguishes (C : QCode n k) (E₁ : PauliGroup n) (E₂ : PauliGroup n) := C.syndrome E₁ ≠ C.syndrome E₂

--to detect errors, it suffices to distinguish an error and the I pauli
def QCode.unique_detects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ (E : PauliGroup n),
  pauli_weight E ≤ w → E ≠ Pauli1 → C.distinguishes E Pauli1

def QCode.unique_corrects_error_of_weight (C : QCode n k) (w : ℕ) := ∀ (E₁ E₂ : PauliGroup n),
  (PauliGroup.phase E₁).1 = ⟨1, by norm_num⟩ → (PauliGroup.phase E₂).1 = ⟨1, by norm_num⟩ →
  pauli_weight E₁ ≤ w → pauli_weight E₂ ≤ w → E₁ ≠ E₂ → C.distinguishes E₁ E₂

def QCode.unique_detects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli):= ∀ (E : PauliGroup n),
  (pauli_only E P) → pauli_weight E ≤ w → E ≠ Pauli1 → C.distinguishes E Pauli1

--unique distinguishing
def QCode.unique_corrects_P_error_of_weight (C : QCode n k) (w : ℕ) (P : Pauli) := ∀ (E₁ E₂ : PauliGroup n),
  (pauli_only E₁ P) → (pauli_only E₂ P) →
  PauliGroup.phase E₁ = 1 → PauliGroup.phase E₂ = 1 →
  pauli_weight E₁ ≤ w → pauli_weight E₂ ≤ w → E₁ ≠ E₂ → C.distinguishes E₁ E₂

theorem QCode.distinguishes_of_exists_dist_stab {k : ℕ} (C : QCode n k) (E₁ E₂ : PauliGroup n) :
  C.distinguishes E₁ E₂ ↔
  ∃ S : C.stabilizers,
    pauli_pauli_phase E₁ S ≠ pauli_pauli_phase E₂ S := by
  unfold distinguishes syndrome
  rw [Function.ne_iff]

lemma commuteₘ_1x {n} (P : Fin n -> Pauli) :
  !anticommuteₘ (λ _ => Pauli_I) P := by
  induction n with
  | zero => rfl
  | succ n₀ IH =>
    rw [anticommuteₘ]
    have: (Fin.tail (λ _ => Pauli_I)) = (λ _ => Pauli_I)
    · apply funext
      intro x
      simp [Fin.tail]
    rw [this]
    have IH' := IH (Fin.tail P)
    simp at IH'
    rw [IH']
    simp [commute₁]

lemma commute_1x (P : PauliGroup n) : !(anticommute Pauli1 P) := by
  rw [anticommute]
  have: PauliGroup.map (Pauli1 (n := n)) = λ i => Pauli_I
  · rw [Pauli1_unfold]
    simp [PauliGroup.map]
  rw [this]
  apply commuteₘ_1x

lemma pphase_Pauli1_left {P : PauliGroup n} : pauli_pauli_phase Pauli1 P = pgphase_1 := by
  rw [pauli_pauli_phase]
  have: !anticommute Pauli1 P := commute_1x P
  simp at this
  simp [this]

lemma anticommute_of_anticommute {P₁ P₂ : PauliGroup n} (h_anti : anticommute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = - (P₂ * P₁) := sorry

lemma Matrix.unitaryGroup.neg_ne {k : Type*} [Fintype k] [DecidableEq k] [Inhabited k] {M : Matrix.unitaryGroup k ℂ} : -M ≠ M := by
  intros h_f
  have hm : M * M⁻¹ = -1
  · nth_rw 1 [←h_f]
    simp
  rw [mul_inv_cancel] at hm
  obtain i : k := default
  have:= congrArg (fun M => M i i) hm
  simp only [OneMemClass.coe_one, one_apply_eq, neg_unitary_val, neg_apply] at this
  norm_num at this


theorem QCode.detectable_of_distinguishes_Pauli1 (C : QCode n k) (E : PauliGroup n) (hd : C.distinguishes E Pauli1) : C.detectable E := by
  unfold detectable undetectable
  apply not_and_of_not_left
  rw [not_mem_normalizer_iff]
  rw [C.distinguishes_of_exists_dist_stab] at hd
  rcases hd with ⟨S, hS⟩
  refine ⟨S, ⟨by aesop, ?_⟩⟩
  simp_rw [pphase_Pauli1_left] at hS
  unfold pauli_pauli_phase at hS
  by_cases h: anticommute E S
  · suffices h_anti : E * (S : 𝐔ₙ[n]) = - (S * E)
    · rw [h_anti]
      symm
      apply Matrix.unitaryGroup.neg_ne
    convert anticommute_of_anticommute h
  simp [←Bool.ne_false_iff, h] at hS

theorem QCode.corrects_of_distinguishes (C : QCode n k) (E_set : Finset (PauliGroup n))
(hd : ∀ E₁ E₂, E₁ ∈ E_set → E₂ ∈ E_set → C.distinguishes E₁ E₂) :
  C.corrects_error_set E_set := by
  unfold corrects_error_set normalizer
  intros E F hE hF
  have hdef := hd E F hE hF
  rw [C.distinguishes_of_exists_dist_stab] at hdef
  rcases hdef with ⟨S, hS⟩
  sorry

--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?
