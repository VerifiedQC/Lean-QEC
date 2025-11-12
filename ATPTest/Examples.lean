
import ATPTest.Stabilizer.Basic

def three_qubit_encode : QCode 3 1:= fun (ψ : PState 1) =>
  (((ψ ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply
    (Cₙ[pX] ⊗ₙ p1)).apply
    (Cₙ[p1 ⊗ₙ pX])


lemma three_qubit_encode_correct (ψ : PState 1) : three_qubit_encode ψ =
  PState.sum (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  (qub_one ⊗ₚ qub_one ⊗ₚ qub_one) (ψ 0) (ψ 1) (single_qub_normalized _)
  (prod_orth_left zero_one_orth)
  := sorry

/- --alas, this doesn't typecheck. am i cooked?
lemma unitary_kron_assoc {n₁ n₂ n₃ : ℕ} {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} {U₃ : 𝐔ₙ[n₃]} :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ = (U₁ ⊗ₙ (U₂ ⊗ₙ U₃) : 𝐔ₙ[(n₁ + n₂) + n₃]) := sorry
-/

lemma unitary_kron_assoc {U₁ U₂ U₃ : 𝐔ₙ[1]}  :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ = U₁ ⊗ₙ (U₂ ⊗ₙ U₃) := sorry

lemma PState.apply_orth {n : ℕ} {ψ φ : PState n} (h_orth : ψ.orth φ) {U : 𝐔ₙ[n]} :
  (ψ.apply U).orth (φ.apply U) := by
  sorry

lemma PState.sum_apply {n : ℕ} {ψ φ : PState n} {a b : ℂ} (hab : ‖a‖^2 + ‖b‖^2 = 1) (h_orth : ψ.orth φ) (U : 𝐔ₙ[n]) :
  (PState.sum ψ φ a b hab h_orth).apply U = PState.sum (ψ.apply U) (φ.apply U) a b hab (PState.apply_orth h_orth) := sorry

lemma IZZ_in_stab : 1 ⊗ₙ pZ ⊗ₙ pZ ∈ QCode.stabilizers (by norm_num) three_qubit_encode := by
  refine' ⟨fun ψ => _, _⟩
  · rewrite [three_qubit_encode_correct]
    unfold stabilizes
    rw [PState.sum_apply]
    sorry
  rw [mem_PauliGroup_iff]
  refine' ⟨![Pauli_Z, Pauli_Z, Pauli_I],⟨pgphase_1, _⟩⟩
  simp [-phase_id, pauli_tensor, unitary_n_nkron, Pauli_I, Pauli_Z]
  rw [unitary_kron_assoc]


lemma ZIZ_in_stab : pZ ⊗ₙ p1 ⊗ₙ pZ ∈ QCode.stabilizers (by norm_num) three_qubit_encode := sorry
lemma ZZI_in_stab : pZ ⊗ₙ pZ ⊗ₙ p1 ∈ QCode.stabilizers (by norm_num) three_qubit_encode := sorry

lemma IXI_pg : p1 ⊗ₙ pX ⊗ₙ p1 ∈ PauliGroup (by norm_num) := by
  apply (kron_mem_PauliGroup_iff (by norm_num) (by norm_num)).2 ⟨pg1.2, _⟩
  apply (kron_mem_PauliGroup_iff zero_lt_one zero_lt_one).2 ⟨pgX.2, pg1.2⟩

lemma XII_pg : pX ⊗ₙ p1 ⊗ₙ p1 ∈ PauliGroup (by norm_num) := by
  apply (kron_mem_PauliGroup_iff (by norm_num) (by norm_num)).2 ⟨pgX.2, _⟩
  apply (kron_mem_PauliGroup_iff zero_lt_one zero_lt_one).2 ⟨pg1.2, pg1.2⟩

lemma IIX_pg : p1 ⊗ₙ p1 ⊗ₙ pX ∈ PauliGroup (by norm_num) := by
  apply (kron_mem_PauliGroup_iff (by norm_num) (by norm_num)).2 ⟨pg1.2, _⟩
  apply (kron_mem_PauliGroup_iff zero_lt_one zero_lt_one).2 ⟨pg1.2, pgX.2⟩

lemma IZZ_pg : p1 ⊗ₙ pZ ⊗ₙ pZ ∈ PauliGroup (by norm_num) := by
  apply (kron_mem_PauliGroup_iff (by norm_num) (by norm_num)).2 ⟨pg1.2, _⟩
  apply (kron_mem_PauliGroup_iff zero_lt_one zero_lt_one).2 ⟨pgZ.2, pgZ.2⟩

lemma ZZI_pg : pZ ⊗ₙ pZ ⊗ₙ p1 ∈ PauliGroup (by norm_num) := by
  apply (kron_mem_PauliGroup_iff (by norm_num) (by norm_num)).2 ⟨pgZ.2, _⟩
  apply (kron_mem_PauliGroup_iff zero_lt_one zero_lt_one).2 ⟨pgZ.2, pg1.2⟩

lemma pphase_IXI_IZZ : pauli_pauli_phase (by norm_num) IXI_pg IZZ_pg = pgphase_n1 := by
  rw [pauli_pauli_phase_kron (by norm_num) (by norm_num), pauli_pauli_phase_kron (by norm_num) (by norm_num)]
  · rw [pauli_pauli_phase_self (by norm_num), pphase_XZ, pphase_id_right]
    simp
  all_goals try exact pgX.2
  all_goals try exact pgZ.2
  all_goals try exact pg1.2
  all_goals try rw [kron_mem_PauliGroup_iff zero_lt_one zero_lt_one]
  exact ⟨pgX.2, pg1.2⟩
  exact ⟨pgZ.2, pgZ.2⟩

lemma pphase_XII_IZZ : pauli_pauli_phase (by norm_num) XII_pg IZZ_pg = pgphase_1 := by
  rw [pauli_pauli_phase_kron (by norm_num) (by norm_num), pauli_pauli_phase_kron (by norm_num) (by norm_num)]
  · rw [pphase_id_right, pphase_id_left]
    simp
  all_goals try exact pgX.2
  all_goals try exact pgZ.2
  all_goals try exact pg1.2
  all_goals try rw [kron_mem_PauliGroup_iff zero_lt_one zero_lt_one]
  exact ⟨pg1.2, pg1.2⟩
  exact ⟨pgZ.2, pgZ.2⟩

lemma pphase_IIX_IZZ : pauli_pauli_phase (by norm_num) IIX_pg IZZ_pg = pgphase_n1 := by
  rw [pauli_pauli_phase_kron (by norm_num) (by norm_num), pauli_pauli_phase_kron (by norm_num) (by norm_num)]
  · rw [pphase_id_right, pphase_XZ, pphase_id_right]
    simp
  all_goals try exact pgX.2
  all_goals try exact pgZ.2
  all_goals try exact pg1.2
  all_goals try rw [kron_mem_PauliGroup_iff zero_lt_one zero_lt_one]
  exact ⟨pg1.2, pgX.2⟩
  exact ⟨pgZ.2, pgZ.2⟩

lemma pphase_IIX_ZZI : pauli_pauli_phase (by norm_num) IIX_pg ZZI_pg = pgphase_1 := by
  rw [pauli_pauli_phase_kron (by norm_num) (by norm_num), pauli_pauli_phase_kron (by norm_num) (by norm_num)]
  · rw [pphase_id_right, pphase_id_left]
    simp
  all_goals try exact pgX.2
  all_goals try exact pgZ.2
  all_goals try exact pg1.2
  all_goals try rw [kron_mem_PauliGroup_iff zero_lt_one zero_lt_one]
  exact ⟨pg1.2, pgX.2⟩
  exact ⟨pgZ.2, pg1.2⟩

lemma pphase_IXI_ZZI : pauli_pauli_phase (by norm_num) IXI_pg ZZI_pg = pgphase_n1 := by
  rw [pauli_pauli_phase_kron (by norm_num) (by norm_num), pauli_pauli_phase_kron (by norm_num) (by norm_num)]
  · rw [pphase_id_right, pphase_id_left]
    simp
  all_goals try exact pgX.2
  all_goals try exact pgZ.2
  all_goals try exact pg1.2
  all_goals try rw [kron_mem_PauliGroup_iff zero_lt_one zero_lt_one]
  exact ⟨pgX.2, pg1.2⟩
  exact ⟨pgZ.2, pg1.2⟩





theorem three_qub_corrects_one_x : Qcode.corrects_P_error_of_weight (by norm_num) three_qubit_encode 1
 ⟨pX, by simp[Pauli]⟩ := by
  intros E₁ hE₁ E₂ hE₂ hE₁' hE₂' hE₁'' hE₂'' hW₁ hW₂ hne
  have h_or : ∀ E : 𝐔ₙ[3], (hE : E ∈ PauliGroup (by norm_num)) → pauli_only (by norm_num) hE ⟨pX, by simp[Pauli]⟩
   → (PauliGroup.phase (by norm_num) hE).1 = ⟨1, by norm_num⟩  → pauli_weight (by norm_num) hE ≤ 1 →
   E = pX ⊗ₙ (1 : 𝐔ₙ[1]) ⊗ₙ (1 : 𝐔ₙ[1]) ∨ E = (1 : 𝐔ₙ[1]) ⊗ₙ pX ⊗ₙ (1 : 𝐔ₙ[1]) ∨ E = (1 : 𝐔ₙ[1]) ⊗ₙ (1 : 𝐔ₙ[1]) ⊗ₙ pX
  · intros E hE hE' hE'' hW
    sorry
  rcases h_or E₁ hE₁ hE₁' hE₁'' hW₁ with rfl | rfl | rfl; all_goals rcases h_or E₂ hE₂ hE₂' hE₂'' hW₂ with rfl | rfl | rfl
  all_goals rw [QCode.distinguishes_of_exists_dist_stab]
  · contradiction --case where errors are identical
  · refine ⟨⟨p1 ⊗ₙ pZ ⊗ₙ pZ, IZZ_in_stab⟩, ?_⟩
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · refine ⟨⟨p1 ⊗ₙ pZ ⊗ₙ pZ, IZZ_in_stab⟩, ?_⟩
    simp [pphase_XII_IZZ, pphase_IIX_IZZ]
    norm_num
  · refine ⟨⟨p1 ⊗ₙ pZ ⊗ₙ pZ, IZZ_in_stab⟩, ?_⟩
    simp [pphase_IXI_IZZ, pphase_XII_IZZ]
    norm_num
  · contradiction
  · refine ⟨⟨pZ ⊗ₙ pZ ⊗ₙ p1, ZZI_in_stab⟩, ?_⟩
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · refine ⟨⟨p1 ⊗ₙ pZ ⊗ₙ pZ, IZZ_in_stab⟩, ?_⟩
    simp [pphase_IIX_IZZ, pphase_XII_IZZ]
    norm_num
  · refine ⟨⟨pZ ⊗ₙ pZ ⊗ₙ p1, ZZI_in_stab⟩, ?_⟩
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · contradiction
