
import ATPTest.Stabilizer.Basic
import ATPTest.QuantumInfoSkeleton

noncomputable section

def three_qubit_encode : QCode 3 1:= fun (ψ : PState 1) =>
  (((ψ ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply
    (Cₙ[pX] ⊗ₙ p1)).apply
    (Cₙ[p1 ⊗ₙ pX])

lemma three_qubit_encode_correct (ψ : PState 1) : three_qubit_encode ψ =
  PState.sum (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  (qub_one ⊗ₚ qub_one ⊗ₚ qub_one) (ψ 0) (ψ 1) (single_qub_normalized _)
  (prod_orth_left zero_one_orth) := by
  admit

@[simp]
lemma qub_zero_Z : qub_zero.apply pZ = qub_zero := by admit

@[simp]
lemma qub_one_Z : qub_one.apply pZ = Ket.phase_mul qub_one ⟨-1, by simp⟩ := by admit

abbrev fold1 {n} (t : Fin n → Pauli) := foldPauli (1, t)

abbrev IXI_pg := fold1 ![Pauli_I, Pauli_X, Pauli_I]
abbrev XII_pg := fold1 ![Pauli_X, Pauli_I, Pauli_I]
abbrev IIX_pg := fold1 ![Pauli_I, Pauli_I, Pauli_X]
abbrev IZZ_pg := fold1 ![Pauli_I, Pauli_Z, Pauli_Z]
abbrev ZZI_pg := fold1 ![Pauli_Z, Pauli_Z, Pauli_I]
abbrev stab := QCode.stabilizers three_qubit_encode


lemma IZZ_in_stab :
  (fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) ∈
  QCode.stabilizers three_qubit_encode := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    rw [PState.apply_id]
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [←PState.kron_assoc, PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]

lemma ZIZ_in_stab : (fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) ∈ stab := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    simp
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [←PState.kron_assoc, PState.apply_id]
    nth_rewrite 2 [←@Ket.mul_phase_id _ _ qub_one]
    simp_rw [PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]

lemma ZZI_in_stab : (fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) ∈ stab := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    simp
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]

lemma commute₁_XZ : commute₁ Pauli_X Pauli_Z = false := by simp [commute₁]

lemma pphase_IXI_IZZ : pauli_pauli_phase IXI_pg IZZ_pg = pgphase_n1 := by
   simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_XII_IZZ : pauli_pauli_phase XII_pg IZZ_pg = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_XII_ZZI : pauli_pauli_phase XII_pg ZZI_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IIX_IZZ : pauli_pauli_phase IIX_pg IZZ_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IIX_ZZI : pauli_pauli_phase IIX_pg ZZI_pg = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IXI_ZZI : pauli_pauli_phase IXI_pg ZZI_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_pauli1 {n : ℕ} {p : PauliGroup n} :
  pauli_pauli_phase Pauli1 p = pgphase_1 := by
  unfold pauli_pauli_phase anticommute
  sorry --induction proof


lemma pauli_weight_one_contra {n : ℕ} {E : PauliGroup n}
(hpw : pauli_weight E ≤ 1)
 (i₁ i₂ : Fin n) (hne : i₁ ≠ i₂): ((PauliGroup.map E) i₁ = Pauli_I) ∨ ((PauliGroup.map E) i₂ = Pauli_I) := by
  by_cases heq₁: ((PauliGroup.map E) i₁ = Pauli_I)
  · exact Or.inl heq₁
  by_cases heq₂ : ((PauliGroup.map E) i₂ = Pauli_I)
  · exact Or.inr heq₂
  unfold pauli_weight PauliGroup.map at hpw
  have hsub: {i₁, i₂} ⊆ ({i | (PauliGroup.map E) i ≠ Pauli_I} : Finset (Fin n))
  · rintro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl <;> assumption
  apply absurd hpw (not_le_of_gt (lt_of_lt_of_le one_lt_two _))
  convert (Finset.card_le_card hsub)
  symm
  rw [Finset.card_eq_two]
  refine ⟨i₁, i₂, hne, rfl⟩

lemma pauli_only_X_contra_Y {n : ℕ} {E : PauliGroup n}
(hpo : pauli_only E Pauli_X) {i : Fin n} :
  (PauliGroup.map E) i ≠ Pauli_Y := by
  unfold pauli_only at hpo
  have hpoi:= hpo i
  unfold PauliGroup.map at hpoi
  rcases hpoi with hi | hx
  · exact fun hf => pgYnepgI (hf.symm.trans hi)
  exact fun hf => pgXnepgY (hx.symm.trans hf)

lemma pauli_only_X_contra_Z {n : ℕ} {E : PauliGroup n}
(hpo : pauli_only E Pauli_X) {i : Fin n} :
  (PauliGroup.map E) i ≠ Pauli_Z := by
  unfold pauli_only at hpo
  have hpoi:= hpo i
  unfold PauliGroup.map at hpoi
  rcases hpoi with hi | hx
  · exact fun hf => pgZnepgI (hf.symm.trans hi)
  exact fun hf => pgXnepgZ (hx.symm.trans hf)


theorem three_qub_corrects_one_x : QCode.unique_corrects_P_error_of_weight three_qubit_encode 1
 ⟨pX, by simp[Pauli]⟩ := by
  intros E₁ E₂ only_E₁ only_E₂ p1_E₁ p1_E₂ hW₁ hW₂ hne
  have h_or :
    ∀ E,
    pauli_only E Pauli_X →
    PauliGroup.phase E = pgphase_1 →
    pauli_weight E ≤ 1 →
    E = fold1 ![Pauli_X, Pauli_I, Pauli_I] ∨
    E = fold1 ![Pauli_I, Pauli_X, Pauli_I] ∨
    E = fold1 ![Pauli_I, Pauli_I, Pauli_X] ∨
    E = Pauli1 := by
      intro E
      let pm := PauliGroup.map E
      let pp := PauliGroup.phase E
      intro hpo hpp hpw
      rcases (Pauli_cases (pm 0)) with h0x | hf | hf | h0i <;>
      rcases (Pauli_cases (pm 1)) with h1x | hf | hf | h1i
      · rcases (pauli_weight_one_contra hpw 0 1 (by norm_num)) with h0I | h1I
        · apply absurd (h0x.symm.trans h0I) pgXnepgI
        apply absurd (h1x.symm.trans h1I) pgXnepgI
      all_goals rcases (Pauli_cases (pm 2)) with h2x | hf | hf | h2i
      all_goals try apply absurd hf (pauli_only_X_contra_Y hpo)
      all_goals try apply absurd hf (pauli_only_X_contra_Z hpo)
      · rcases (pauli_weight_one_contra hpw 0 2 (by simp)) with h0I | h1I
        · apply absurd (h0x.symm.trans h0I) pgXnepgI
        apply absurd (h2x.symm.trans h1I) pgXnepgI
      · left
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · rcases (pauli_weight_one_contra hpw 1 2 (by simp)) with h1I | h2I
        · apply absurd (h1x.symm.trans h1I) pgXnepgI
        apply absurd (h2x.symm.trans h2I) pgXnepgI
      · apply Or.inr (Or.inl _)
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · apply (Or.inr (Or.inr (Or.inl _)))
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · apply (Or.inr (Or.inr (Or.inr _))) --wait, not actually sure how to do this
        rw [Pauli1_unfold]
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
  rcases h_or E₁ only_E₁ p1_E₁ hW₁ with rfl | rfl | rfl | rfl
  all_goals rcases h_or E₂ only_E₂ p1_E₂ hW₂ with rfl | rfl | rfl | rfl
  all_goals rw [QCode.distinguishes_of_exists_dist_stab]
  · contradiction --case where errors are identical
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --XII, IXI
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --XII, IIX
    simp [pphase_XII_IZZ, pphase_IIX_IZZ]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --XII, III
    simp [pphase_XII_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IXI, XII
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · contradiction
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, IIX
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, III
    simp [pphase_IXI_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --XII, IIX
    simp [pphase_XII_ZZI, pphase_IIX_ZZI]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IIX, IXI
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · contradiction
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IIX, III
    simp [pphase_IIX_IZZ, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IIX, III
    simp [pphase_XII_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, III
    simp [pphase_IXI_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IIX, III
    simp [pphase_IIX_IZZ, pphase_pauli1]
    norm_num
  contradiction
