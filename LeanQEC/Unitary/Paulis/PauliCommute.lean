import LeanQEC.Unitary.Paulis.PauliMul

open Matrix

noncomputable section

variable {n : ℕ}

def commute₁ (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

def commSign₁ (P Q : Pauli) : ℂ := if commute₁ P Q then 1 else -1

lemma pauliMat_mul_comm₁ (P Q : Pauli) :
    pauliMat P * pauliMat Q = commSign₁ P Q • (pauliMat Q * pauliMat P) := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    · simp only [commSign₁, commute₁]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma commute₁_right (P Q : Pauli) :
    (mul_Pauli1 P Q).2 = (mul_Pauli1 Q P).2 := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [mul_Pauli1]

lemma commute₁_sym (P P' : Pauli) :
    commute₁ P P' ↔ commute₁ P' P := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases P' with rfl | rfl | rfl | rfl <;>
    simp [commute₁]

lemma commute₁_xx (P : Pauli) : commute₁ P P := by simp [commute₁]

/- Two Pauli strings anticommute iff they anticommute on an odd number of sites -/
def anticommuteₘ {n} (m m' : Fin n → Pauli) : Bool :=
  match n with
  | 0 => false
  | _ + 1 =>
    (!commute₁ (m 0) (m' 0)) ^^ anticommuteₘ (Fin.tail m) (Fin.tail m')

lemma prod_commSign₁ (m m' : Fin n → Pauli) :
    ∏ i, commSign₁ (m i) (m' i) = if anticommuteₘ m m' then -1 else 1 := by
  induction n with
  | zero => simp [anticommuteₘ]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have := ih (Fin.tail m) (Fin.tail m')
    simp only [Fin.tail] at this
    rw [this, anticommuteₘ]
    unfold commSign₁
    cases commute₁ (m 0) (m' 0) <;> cases anticommuteₘ (Fin.tail m) (Fin.tail m') <;> simp

lemma pauliString_mul_comm (m m' : Fin n → Pauli) :
    (pauliString m : Matrix (Qubits n) (Qubits n) ℂ) * pauliString m' =
      (if anticommuteₘ m m' then -1 else 1 : ℂ) •
        ((pauliString m' : Matrix (Qubits n) (Qubits n) ℂ) * pauliString m) := by
  rw [pauliString_val, pauliString_val, ← piProd_mul, ← piProd_mul, ← prod_commSign₁,
    ← piProd_smul]
  congr 1
  funext i
  exact pauliMat_mul_comm₁ _ _

lemma anticommuteₘ_correct {n} (m m' : Fin n → Pauli) :
    (anticommuteₘ m m' → (pauliString m * pauliString m' = -pauliString m' * pauliString m)) ∧
    (!(anticommuteₘ m m') → (pauliString m * pauliString m' = pauliString m' * pauliString m)) := by
  have h := pauliString_mul_comm m m'
  constructor
  · intro H
    apply Subtype.ext
    rw [if_pos H] at h
    simp [h]
  · intro H
    apply Subtype.ext
    simp only [Bool.not_eq_true'] at H
    rw [H] at h
    simpa using h

lemma anticommuteₘ_correct_true {n} (m m' : Fin n → Pauli) (H : anticommuteₘ m m') :
    pauliString m * pauliString m' = -pauliString m' * pauliString m :=
  (anticommuteₘ_correct m m').1 H

lemma anticommuteₘ_correct_false {n} (m m' : Fin n → Pauli) (H : anticommuteₘ m m' = false) :
    pauliString m * pauliString m' = pauliString m' * pauliString m :=
  (anticommuteₘ_correct m m').2 (by simp [H])

private lemma xor_decide_aux (c : Bool) (S T : ZMod 2) (h : S = T) :
    ((!c) ^^ decide (S = 1)) = decide ((if c then 0 else 1) + T = 1) := by
  subst h
  cases c <;> revert S <;> decide

lemma anticommuteₘ_eq_sum (m m' : Fin n → Pauli) :
    anticommuteₘ m m' = decide ((∑ i, if commute₁ (m i) (m' i) then 0 else 1 : ZMod 2) = 1) := by
  induction n with
  | zero => simp [anticommuteₘ]
  | succ n ih =>
    rw [anticommuteₘ, ih, Fin.sum_univ_succ]
    exact xor_decide_aux _ _ _ (Finset.sum_congr rfl fun i _ => rfl)

lemma anticommuteₘ_cat {n₁ n₂}
    (m₁ m₁' : Fin n₁ → Pauli) (m₂ m₂' : Fin n₂ → Pauli) :
    anticommuteₘ (Fin.append m₁ m₂) (Fin.append m₁' m₂') =
      (anticommuteₘ m₁ m₁' ^^ anticommuteₘ m₂ m₂') := by
  simp only [anticommuteₘ_eq_sum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  generalize (∑ i : Fin n₁, if commute₁ (m₁ i) (m₁' i) then (0 : ZMod 2) else 1) = a
  generalize (∑ i : Fin n₂, if commute₁ (m₂ i) (m₂' i) then (0 : ZMod 2) else 1) = b
  revert a b; decide

lemma anticommuteₘ_sym (m₁ m₂ : Fin n → Pauli) :
    anticommuteₘ m₁ m₂ = anticommuteₘ m₂ m₁ := by
  have hc : ∀ i, commute₁ (m₁ i) (m₂ i) = commute₁ (m₂ i) (m₁ i) :=
    fun i => Bool.eq_iff_iff.2 (commute₁_sym _ _)
  simp only [anticommuteₘ_eq_sum, hc]

lemma anticommuteₘ_xx (m : Fin n → Pauli) :
    anticommuteₘ m m = false := by
  simp [anticommuteₘ_eq_sum, commute₁_xx]

def anticommute {n : ℕ} (U₁ U₂ : PauliGroup n) :=
  anticommuteₘ (PauliGroup.map U₁) (PauliGroup.map U₂)

lemma anticommute_kron {n₁ n₂}
    (U₁ U₁' : PauliGroup n₁) (U₂ U₂' : PauliGroup n₂) :
    anticommute (kronOfPauli U₁ U₂) (kronOfPauli U₁' U₂') =
      (anticommute U₁ U₁' ^^ anticommute U₂ U₂') := by
  unfold anticommute
  rw [map_kron_of_Pauli, map_kron_of_Pauli, anticommuteₘ_cat]

lemma anticommute_sym (U₁ U₂ : PauliGroup n) :
    anticommute U₁ U₂ = anticommute U₂ U₁ := by
  unfold anticommute
  rw [anticommuteₘ_sym]

lemma anticommute_xx (P : PauliGroup n) :
    anticommute P P = false := by
  unfold anticommute
  rw [anticommuteₘ_xx]

lemma PauliGroup.eq_fold (P : PauliGroup n) :
    P.val = pgroup_phases.toCircle (PauliGroup.phase P) • pauliString (PauliGroup.map P) := by
  conv_lhs => rw [← foldPauli_phase_map P]
  rfl

lemma anticommute_correct_true {n} (P Q : PauliGroup n)
    (H : anticommute P Q) :
    P.val * Q.val = -Q.val * P.val := by
  rw [PauliGroup.eq_fold P, PauliGroup.eq_fold Q, smul_mul_smul_comm,
    anticommuteₘ_correct_true _ _ H, neg_mul, neg_mul, smul_mul_smul_comm,
    neg_eq_circle_negOne_smul, neg_eq_circle_negOne_smul, smul_smul, smul_smul]
  congr 1
  ac_rfl

lemma anticommute_correct_false {n} (P Q : PauliGroup n)
    (H : anticommute P Q = false) :
    P.val * Q.val = Q.val * P.val := by
  rw [PauliGroup.eq_fold P, PauliGroup.eq_fold Q, smul_mul_smul_comm,
    anticommuteₘ_correct_false _ _ H, smul_mul_smul_comm, mul_comm (pgroup_phases.toCircle _)]

end
