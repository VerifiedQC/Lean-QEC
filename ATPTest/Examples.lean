
import ATPTest.Stabilizer.Basic
import ATPTest.QuantumInfoSkeleton

noncomputable section

def three_qubit_encode : QCode 3 1:= fun (ψ : PState 1) =>
  (((ψ ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply
    (Cₙ[pX] ⊗ₙ p1)).apply
    (Cₙ[p1 ⊗ₙ pX])

lemma gt0_3 : 0 < 3 := by norm_num

lemma three_qubit_encode_correct (ψ : PState 1) : three_qubit_encode ψ =
  PState.sum (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  (qub_one ⊗ₚ qub_one ⊗ₚ qub_one) (ψ 0) (ψ 1) (single_qub_normalized _)
  (prod_orth_left zero_one_orth) := by
  admit

lemma unitary_kron_assoc {U₁ U₂ U₃ : 𝐔ₙ[1]}  :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ = U₁ ⊗ₙ (U₂ ⊗ₙ U₃) := by
  ext i j;
  simp [ unitary_nkron, normalized_kron ];
  ring_nf
  fin_cases i <;> fin_cases j <;> rfl


lemma PState.apply_orth {n : ℕ} {ψ φ : PState n} (h_orth : ψ.orth φ) {U : 𝐔ₙ[n]} :
  (ψ.apply U).orth (φ.apply U) := by
  admit

lemma PState.sum_apply {n : ℕ} {ψ φ : PState n} {a b : ℂ} (hab : ‖a‖^2 + ‖b‖^2 = 1) (h_orth : ψ.orth φ) (U : 𝐔ₙ[n]) :
  (PState.sum ψ φ a b hab h_orth).apply U = PState.sum (ψ.apply U) (φ.apply U) a b hab (PState.apply_orth h_orth) := by admit

@[simp]
lemma Pstate.apply_id {n : ℕ} {ψ : PState n} : ψ.apply 1 = ψ := by simp

@[simp]
lemma qub_zero_Z : qub_zero.apply pZ = qub_zero := by admit

@[simp]
lemma qub_one_Z : qub_one.apply pZ = Ket.phase_mul qub_one ⟨-1, by simp⟩ := by admit

abbrev fold1 {n} (hn: n > 0) (t : Fin n -> Pauli) := foldPauli hn (1, t)

-- def IXI_pg := foldPauli 1 (pZ, p1, pZ)
abbrev IXI_pg := fold1 gt0_3 ![Pauli_I, Pauli_X, Pauli_I]
abbrev XII_pg := fold1 gt0_3 ![Pauli_X, Pauli_I, Pauli_I]
abbrev IIX_pg := fold1 gt0_3 ![Pauli_I, Pauli_I, Pauli_X]
abbrev IZZ_pg := fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z]
abbrev ZZI_pg := fold1 gt0_3 ![Pauli_Z, Pauli_Z, Pauli_I]
abbrev stab := QCode.stabilizers gt0_3 three_qubit_encode

lemma IZZ_in_stab :
  (fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z]).1 ∈
  QCode.stabilizers gt0_3 three_qubit_encode := by
  /-
  intro ψ
  rewrite [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : ((qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply (1 ⊗ₙ pZ ⊗ₙ pZ) : PState 3) = ((qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero) : PState 3) := by
    rw [kron_mul_kron, kron_mul_kron]
    admit
  have ho: (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply (1 ⊗ₙ pZ ⊗ₙ pZ) = ((qub_one ⊗ₚ qub_one ⊗ₚ qub_one) : PState 3) := by
    admit
  simp_rw [hz, ho]
  -/
  admit
  /- TODO FIX AND RESTORE -/
  /-
  rw [mem_PauliGroup_iff]
  refine' ⟨![Pauli_Z, Pauli_Z, Pauli_I],⟨pgphase_1, _⟩⟩
  simp [-phase_id, unitary_n_nkron, Pauli_I, Pauli_Z]
  rw [unitary_kron_assoc]
  -/


lemma ZIZ_in_stab : (fold1 gt0_3 ![Pauli_Z, Pauli_I, Pauli_Z]).1 ∈ stab := by admit
lemma ZZI_in_stab : (fold1 gt0_3 ![Pauli_Z, Pauli_Z, Pauli_I]).1 ∈ stab := by admit

/--
  The Pauli matrices X and I are not equal to each other

  PROVIDED SOLUTION:
  For these matrices to be unequal, it suffices that they differ in some
  index. X and I differ in the 0th row and the 0th column, so check those values
  to show they are unequal.
-/
@[simp] lemma pgXnepgI : Pauli_X ≠ Pauli_I := by
  -- To show that Pauli_X ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_X.val 0 0) ≠ (Pauli_I.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgZnepgI : Pauli_Z ≠ Pauli_I := by
  -- To show that Pauli_Z ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_Z.val 1 1) ≠ (Pauli_I.val 1 1) := by
    exact show ( -1 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgYnepgI : Pauli_Y ≠ Pauli_I := by
  -- To show that Pauli_Y ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_Y.val 0 0) ≠ (Pauli_I.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgXnepgZ : Pauli_X ≠ Pauli_Z := by
  -- To show that Pauli_X ≠ Pauli_Z, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_X.val 0 0) ≠ (Pauli_Z.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;


--can i make proving this a tactic?
lemma pphase_IXI_IZZ : pauli_pauli_phase gt0_3 IXI_pg IZZ_pg = pgphase_n1 := by
  unfold pauli_pauli_phase
  have h_anti : count_anticommutes gt0_3 IXI_pg IZZ_pg = 1
  · unfold count_anticommutes IXI_pg IZZ_pg
    have h_mem0 : (0 ∉ {i | ith_anticommute gt0_3 IXI_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem1 : (1 ∈ {i | ith_anticommute gt0_3 IXI_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem2 : (2 ∉ {i | ith_anticommute gt0_3 IXI_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h: ({1} : Finset (Fin 3)).card = 1:= by simp
    convert h
    ext x
    fin_cases x <;> simp at * <;> assumption
  simp [h_anti]

lemma pphase_XII_IZZ : pauli_pauli_phase gt0_3 XII_pg IZZ_pg = pgphase_1 := by
  unfold pauli_pauli_phase
  have comm : count_anticommutes gt0_3 XII_pg IZZ_pg = 0
  · unfold count_anticommutes XII_pg IZZ_pg
    have h_mem0 : (0 ∉ {i | ith_anticommute gt0_3 XII_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem1 : (1 ∉ {i | ith_anticommute gt0_3 XII_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem2 : (2 ∉ {i | ith_anticommute gt0_3 XII_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h: ({} : Finset (Fin 3)).card = 0:= by simp
    convert h
    ext x
    fin_cases x <;> simp at * <;> assumption
  simp [comm]

lemma pphase_IIX_IZZ : pauli_pauli_phase gt0_3 IIX_pg IZZ_pg = pgphase_n1 := by
  unfold pauli_pauli_phase
  have h_anti : count_anticommutes gt0_3 IIX_pg IZZ_pg = 1
  · unfold count_anticommutes IIX_pg IZZ_pg
    have h_mem0 : (0 ∉ {i | ith_anticommute gt0_3 IIX_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem1 : (1 ∉ {i | ith_anticommute gt0_3 IIX_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem2 : (2 ∈ {i | ith_anticommute gt0_3 IIX_pg IZZ_pg i = true})
    · simp [PauliGroup.map, commute]
    have h: ({2} : Finset (Fin 3)).card = 1:= by simp
    convert h
    ext x
    fin_cases x <;> simp at * <;> assumption
  simp [h_anti]

lemma pphase_IIX_ZZI : pauli_pauli_phase gt0_3 IIX_pg ZZI_pg = pgphase_1 := by
  unfold pauli_pauli_phase
  have comm : count_anticommutes gt0_3 IIX_pg ZZI_pg = 0
  · unfold count_anticommutes IIX_pg ZZI_pg
    have h_mem0 : (0 ∉ {i | ith_anticommute gt0_3 IIX_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem1 : (1 ∉ {i | ith_anticommute gt0_3 IIX_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem2 : (2 ∉ {i | ith_anticommute gt0_3 IIX_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h: ({} : Finset (Fin 3)).card = 0:= by simp
    convert h
    ext x
    fin_cases x <;> simp at * <;> assumption
  simp [comm]

lemma pphase_IXI_ZZI : pauli_pauli_phase gt0_3 IXI_pg ZZI_pg = pgphase_n1 := by
  unfold pauli_pauli_phase
  have h_anti : count_anticommutes gt0_3 IXI_pg ZZI_pg = 1
  · unfold count_anticommutes IXI_pg ZZI_pg
    have h_mem0 : (0 ∉ {i | ith_anticommute gt0_3 IXI_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem1 : (1 ∈ {i | ith_anticommute gt0_3 IXI_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h_mem2 : (2 ∉ {i | ith_anticommute gt0_3 IXI_pg ZZI_pg i = true})
    · simp [PauliGroup.map, commute]
    have h: ({1} : Finset (Fin 3)).card = 1:= by simp
    convert h
    ext x
    fin_cases x <;> simp at * <;> assumption
  simp [h_anti]

theorem three_qub_corrects_one_x : Qcode.unique_corrects_P_error_of_weight (by norm_num) three_qubit_encode 1
 ⟨pX, by simp[Pauli]⟩ := by
  intros E₁ E₂ only_E₁ only_E₂ p1_E₁ p1_E₂ hW₁ hW₂ hne
  have h_or :
    ∀(E : PauliGroup gt0_3),
    pauli_only gt0_3 E Pauli_X →
    PauliGroup.phase gt0_3 E = pgphase_1 ->
    pauli_weight gt0_3 E ≤ 1 →
    E = fold1 gt0_3 ![Pauli_X, Pauli_I, Pauli_I] ∨
    E = fold1 gt0_3 ![Pauli_I, Pauli_X, Pauli_I] ∨
    E = fold1 gt0_3 ![Pauli_I, Pauli_I, Pauli_X] := by
      admit
  rcases h_or E₁ only_E₁ p1_E₁ hW₁ with rfl | rfl | rfl
  all_goals rcases h_or E₂ only_E₂ p1_E₂ hW₂ with rfl | rfl | rfl
  all_goals rw [QCode.distinguishes_of_exists_dist_stab]
  · contradiction --case where errors are identical
  · exists ⟨fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · exists ⟨fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩
    simp [pphase_XII_IZZ, pphase_IIX_IZZ]
    norm_num
  · exists ⟨fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩
    simp [pphase_IXI_IZZ, pphase_XII_IZZ]
    norm_num
  · contradiction
  · exists ⟨fold1 gt0_3 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · exists ⟨fold1 gt0_3 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩
    simp [pphase_IIX_IZZ, pphase_XII_IZZ]
    norm_num
  · exists ⟨fold1 gt0_3 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · contradiction
