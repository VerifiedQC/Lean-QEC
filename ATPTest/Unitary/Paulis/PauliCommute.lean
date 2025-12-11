import ATPTest.Unitary.Paulis.PauliMul

noncomputable section

def neg_phase (c : phase) : phase where
  z := -c.z
  z_norm := by
    norm_num
    apply c.z_norm

instance : Neg phase where
  neg := neg_phase

def commute₁ (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

lemma mem_neg_pphase (c : pgroup_phases) :
  -c.val ∈ pgroup_phases := by sorry

def neg_pphase (c : pgroup_phases) : pgroup_phases :=
  ⟨-c.val, mem_neg_pphase c⟩

instance : Neg pgroup_phases where
  neg := neg_pphase

lemma commute₁_correct_true (P Q : Pauli)
  (commutePQ : commute₁ P Q):
  (mul_Pauli1 P Q).1 = (mul_Pauli1 Q P).1 := by
  sorry

lemma commute₁_correct_false (P Q : Pauli)
  (commutePQ : commute₁ P Q = false):
  (mul_Pauli1 P Q).1 = -(mul_Pauli1 Q P).1 := by
  sorry

lemma commute₁_sym P P' :
  commute₁ P P' ↔ commute₁ P' P := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases P') with rfl | rfl | rfl | rfl
  all_goals simp [commute₁]
  all_goals tauto

lemma commute₁_xx P : commute₁ P P := by simp [commute₁]

def anticommuteₘ {n} (m m' : Fin n -> Pauli) :=
  match n with
  | 0 => false
  | _ + 1 =>
    (!commute₁ (m 0) (m' 0)) ^^ anticommuteₘ (Fin.tail m) (Fin.tail m')

lemma anticommuteₘ_cat {n₁ n₂}
  (m₁ m₁' : Fin n₁ -> Pauli)
  (m₂ m₂' : Fin n₂ -> Pauli) :
  anticommuteₘ (cast_fin_append m₁ m₂) (cast_fin_append m₁' m₂') =
  (anticommuteₘ m₁ m₁' ^^ anticommuteₘ m₂ m₂') := by
  induction n₁ with
  | zero =>
    simp [anticommuteₘ]
    -- this is terrible
    induction n₂ with
    | zero => simp [anticommuteₘ]
    | succ n₀ IH =>
      simp [anticommuteₘ, cast_fin_append, Fin.append, Fin.addCases]
      simp [cast_fin_append_iter2, IH]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [cast_fin_append_iter1]
    simp [IH]

lemma anticommuteₘ_sym (m₁ m₂ : Fin n -> Pauli) :
  anticommuteₘ m₁ m₂ = anticommuteₘ m₂ m₁ := by
  induction n with
  | zero => simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    rw [IH]
    suffices: commute₁ (m₁ 0) (m₂ 0) = commute₁ (m₂ 0) (m₁ 0)
    · rw [this]
    rw [Bool.eq_iff_iff]
    rw [commute₁_sym]

lemma anticommuteₘ_xx (m : Fin n -> Pauli) :
  anticommuteₘ m m = false := by
  induction n with
  | zero =>
    simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [IH]
    rw [commute₁_xx]

def anticommute (U₁ U₂ : PauliGroup n) :=
  anticommuteₘ (PauliGroup.map U₁) (PauliGroup.map U₂)

lemma anticommute_kron {n₁ n₂}
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  anticommute (kronOfPauli U₁ U₂) (kronOfPauli U₁' U₂') =
  (anticommute U₁ U₁' ^^ anticommute U₂ U₂') := by
  unfold anticommute
  rw [map_kron_of_Pauli]
  rw [map_kron_of_Pauli]
  rw [anticommuteₘ_cat]
  rw [Bool.xor_comm]

lemma anticommute_sym (U₁ U₂ : PauliGroup n) :
  anticommute U₁ U₂ = anticommute U₂ U₁ := by
  unfold anticommute
  rw [anticommuteₘ_sym]

lemma anticommute_xx (P : PauliGroup n) :
  anticommute P P = false := by
  unfold anticommute
  rw [anticommuteₘ_xx]
