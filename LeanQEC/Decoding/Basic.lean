import LeanQEC.Decoding.Defs
import LeanQEC.Decoding.PauliChannel
import LeanQEC.Decoding.Recovery
import LeanQEC.Decoding.SyndromeAction
import LeanQEC.ForPhysLib.KetUniform


open Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

variable {n k m : ℕ} {C : StabCode n}

def PauliWeightLE (P : ProbDistribution (PauliGroup_group n)) (t : ℕ) : Prop :=
  ∀ E, (P E : ℝ) ≠ 0 → pauli_weight E ≤ t

theorem eq_one_of_sum_mul_eq_one {α : Type*} [Fintype α] {P f : α → ℝ} (hP0 : ∀ a, 0 ≤ P a)
    (hP1 : ∑ a, P a = 1) (hf : ∀ a, f a ≤ 1) (h : ∑ a, P a * f a = 1) {a : α} (ha : P a ≠ 0) :
    f a = 1 := by
  have hsum : ∑ b, P b * (1 - f b) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hP1, h, sub_self]
  have hnn : ∀ b ∈ Finset.univ, 0 ≤ P b * (1 - f b) := fun b _ =>
    mul_nonneg (hP0 b) (by linarith [hf b])
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact absurd h0 ha
  · linarith

theorem exp_val_logicalChannel_pauliErrorChannel (e : C.Encoder k) (G : C.Generators m)
    (dec : Decoder n m) (P : ProbDistribution (PauliGroup_group n)) (φ : Ket (Qubits k)) :
    (logicalChannel e G dec (pauliErrorChannel P) (MState.pure φ)).exp_val (MState.pure φ).M =
      ∑ E, (P E : ℝ) * e.recoveryFid (dec (G.pauliSyndrome E) * E) φ.vec φ.vec := by
  rw [exp_val_logicalChannel_eq_sum]
  simp_rw [syndromeIntegrand_pauliErrorChannel, errorIntegrand_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem BinSympPauli.add_self (x : BinSympPauli n) : x + x = 0 := by
  ext i <;> exact CharTwo.add_self_eq_zero _

theorem Pauli_toBinSympPauli_inv (E : PauliGroup_group n) :
    Pauli_toBinSympPauli E⁻¹ = Pauli_toBinSympPauli E := by
  have h := Pauli_to_BinSymp_correct E⁻¹ E
  rw [inv_mul_cancel, Pauli_toBinSympPauli_one] at h
  calc Pauli_toBinSympPauli E⁻¹
      = Pauli_toBinSympPauli E⁻¹ + (Pauli_toBinSympPauli E + Pauli_toBinSympPauli E) := by
        rw [BinSympPauli.add_self, add_zero]
    _ = (Pauli_toBinSympPauli E⁻¹ + Pauli_toBinSympPauli E) + Pauli_toBinSympPauli E := by abel
    _ = Pauli_toBinSympPauli E := by rw [← h, zero_add]

theorem BinSympPauli.weight_eq_card (x : BinSympPauli n) :
    x.weight = (Finset.univ.filter fun i => x.1 i ≠ 0 ∨ x.2 i ≠ 0).card := by
  unfold BinSympPauli.weight union_weight hammingNorm
  congr 1
  ext i
  simp only [ne_eq, ZMod2_or_eq_zero_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem BinSympPauli.weight_add_le (x y : BinSympPauli n) :
    (x + y).weight ≤ x.weight + y.weight := by
  rw [weight_eq_card, weight_eq_card, weight_eq_card]
  refine (Finset.card_le_card fun i hi => ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Prod.fst_add,
    Prod.snd_add, Pi.add_apply] at hi ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
  rw [h1, h2, h3, h4] at hi
  simp at hi

theorem pauliGroupMat_mul (A B : PauliGroup_group n) :
    pauliGroupMat (A * B) = pauliGroupMat A * pauliGroupMat B :=
  rfl

theorem pauliGroupMat_scalarPauli (z : pgroup_phases) :
    pauliGroupMat (scalarPauli z : PauliGroup_group n) =
      (pgroup_phases.toCircle z : ℂ) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  change ((fold (z, fun _ => Pauli_I) : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ) = _
  rw [fold_apply, fold_aux_val, ← pauliString_val, pauliString_I]
  rfl

/- A Pauli which is not a phase is traceless -/
theorem trace_pauliGroupMat_eq_zero {P : PauliGroup_group n} (h : Pauli_toBinSympPauli P ≠ 0) :
    trace (pauliGroupMat P) = 0 := by
  have hP : (P : 𝐔ₙ[n]) = fold (PauliGroup.phase P, PauliGroup.map P) := by
    rw [← foldPauli_val]
    exact congrArg Subtype.val (foldPauli_phase_map P).symm
  rw [pauliGroupMat, hP, trace_fold_eq, if_neg]
  intro hall
  exact h ((Pauli_toBinSympPauli_eq_zero_iff P).mpr (funext hall))

/- A trivial logical operator (a stabilizer up to phase) acts on the code space as a phase -/
theorem StabCode.exists_scalar_of_mem_trivialLogicals {M : PauliGroup_group n}
    (hM : M ∈ C.trivialLogicals) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v ∈ C.space, pauliGroupMat M *ᵥ v = c • v := by
  obtain ⟨s, hs, hphi⟩ := (C.mem_trivialLogicals_iff M).mp hM
  have hphase : M * s⁻¹ ∈ PauliGroup.phaseSubgroup n := by
    rw [PauliGroup.mem_phaseSubgroup_iff, Pauli_to_BinSymp_correct, Pauli_toBinSympPauli_inv, ← hphi,
      BinSympPauli.add_self]
  obtain ⟨z, hz⟩ := (PauliGroup.mem_phaseSubgroup_iff_scalar _).mp hphase
  have hM' : M = scalarPauli z * s := by rw [← hz]; group
  refine ⟨(pgroup_phases.toCircle z : ℂ), by simp, fun v hv => ?_⟩
  have hsv : pauliGroupMat s *ᵥ v = v := stabilizes_apply' (hv s hs)
  rw [hM', pauliGroupMat_mul, ← mulVec_mulVec, hsv, pauliGroupMat_scalarPauli, smul_mulVec,
    one_mulVec]

theorem StabCode.Encoder.recoveryFid_eq_one_of_mem_trivialLogicals (e : C.Encoder k)
    {M : PauliGroup_group n} (hM : M ∈ C.trivialLogicals) {ψ : Qubits k → ℂ} (hψ : nsq ψ = 1) :
    e.recoveryFid M ψ ψ = 1 := by
  obtain ⟨c, -, hcv⟩ := C.exists_scalar_of_mem_trivialLogicals hM
  have hw := e.nsq_amp_pauli_isom M ψ
  rw [hψ] at hw
  rw [StabCode.Encoder.recoveryFid, ← hw]
  refine (fidSum_eq_iff _ hψ).mpr ⟨fun a => c * if a = 0 then 1 else 0, fun i a => ?_⟩
  rw [hcv _ (e.isom_mulVec_mem_space ψ), e.amp_smul, e.amp_isom_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem StabCode.mem_trivialLogicals_of_scalar (hC : C.space ≠ ⊥) {L : PauliGroup_group n} {c : ℂ} (hc : ∀ v ∈ C.space, pauliGroupMat L *ᵥ v = c • v) :
    L ∈ C.trivialLogicals := by
  by_contra hT
  have htr : ∀ g ∈ C.stabs, trace (pauliGroupMat L * pauliGroupMat g) = 0 := by
    intro g hg
    rw [← pauliGroupMat_mul]
    apply trace_pauliGroupMat_eq_zero
    intro h0
    apply hT
    rw [C.mem_trivialLogicals_iff]
    refine ⟨g, hg, ?_⟩
    rw [Pauli_to_BinSymp_correct] at h0
    calc Pauli_toBinSympPauli g
        = Pauli_toBinSympPauli g + (Pauli_toBinSympPauli L + Pauli_toBinSympPauli g) := by
          rw [h0, add_zero]
      _ = Pauli_toBinSympPauli L + (Pauli_toBinSympPauli g + Pauli_toBinSympPauli g) := by abel
      _ = Pauli_toBinSympPauli L := by rw [BinSympPauli.add_self, add_zero]
  have hT1 : Matrix.toLin' (pauliGroupMat L) ∘ₗ C.projector = c • C.projector := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply]
    exact hc _ (C.projector_apply_mem v)
  have htrace1 : LinearMap.trace ℂ _ (Matrix.toLin' (pauliGroupMat L) ∘ₗ C.projector) =
      c * Module.finrank ℂ C.space := by
    rw [hT1, map_smul, C.projector_isProj.trace, smul_eq_mul]
  have htrace2 : LinearMap.trace ℂ _ (Matrix.toLin' (pauliGroupMat L) ∘ₗ C.projector) = 0 := by
    have hproj : C.projector = Matrix.toLin' ((Nat.card C.stabs : ℂ)⁻¹ •
        ∑ g : ↥C.stabs, pauliGroupMat (g : PauliGroup_group n)) := by
      simp [StabCode.projector, map_sum, map_smul]
    rw [hproj, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, Matrix.mul_smul, Matrix.mul_sum,
      trace_smul, trace_sum, Finset.sum_eq_zero fun g _ => htr g.1 g.2, smul_zero]
  have hfin : (Module.finrank ℂ C.space : ℂ) ≠ 0 := by
    exact_mod_cast fun h => hC (Submodule.finrank_eq_zero.mp h)
  have hc0 : c = 0 := by
    have := htrace1.symm.trans htrace2
    exact (mul_eq_zero.mp this).resolve_right hfin
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
  have h1 := nsq_mulVec_of_isometry (StabCode.Encoder.pauliGroupMat_isometry L) v
  rw [hc v hv, hc0, zero_smul, (nsq_eq_zero_iff _).mpr rfl, eq_comm, nsq_eq_zero_iff] at h1
  exact hv0 h1

/-- Elements of N(S) stay in the codespace -/
theorem StabCode.normalizer_mulVec_mem_space {L : PauliGroup_group n}
    (hL : L ∈ C.normalizerGroup) {v : Qubits n → ℂ} (hv : v ∈ C.space) :
    pauliGroupMat L *ᵥ v ∈ C.space := by
  rw [C.mem_space_iff_mulVec]
  intro s hs
  have hcomm : s * L = L * s := Subgroup.mem_centralizer_iff.mp hL s hs
  have hm : pauliGroupMat s * pauliGroupMat L = pauliGroupMat L * pauliGroupMat s :=
    congrArg (fun x : PauliGroup_group n => pauliGroupMat x) hcomm
  have hsv : pauliGroupMat s *ᵥ v = v := stabilizes_apply' (hv s hs)
  change pauliGroupMat s *ᵥ (pauliGroupMat L *ᵥ v) = _
  rw [mulVec_mulVec, hm, ← mulVec_mulVec, hsv]

theorem StabCode.Encoder.exists_scalar_of_recoveryFid_eq_one (e : C.Encoder k)
    {M L : PauliGroup_group n} (hL : L ∈ C.normalizerGroup)
    (h1 : ∀ ψ, nsq ψ = 1 → e.recoveryFid M ψ ψ = 1)
    (h2 : ∀ φ, nsq φ = 1 → e.recoveryFid (M * L) φ φ = 1) :
    ∃ c : ℂ, ∀ v ∈ C.space, pauliGroupMat L *ᵥ v = c • v := by
  set ℓ := e.isomᴴ * pauliGroupMat L * e.isom with hℓ
  have hLv : ∀ ψ, pauliGroupMat L *ᵥ (e.isom *ᵥ ψ) = e.isom *ᵥ (ℓ *ᵥ ψ) := by
    intro ψ
    have hmem := C.normalizer_mulVec_mem_space hL (e.isom_mulVec_mem_space ψ)
    conv_lhs => rw [← e.isom_mulVec_conjTranspose_mulVec hmem]
    simp only [hℓ, mulVec_mulVec, Matrix.mul_assoc]
  have hnorm : ∀ ψ, nsq (ℓ *ᵥ ψ) = nsq ψ := by
    intro ψ
    rw [← nsq_mulVec_of_isometry e.isom_isometry (ℓ *ᵥ ψ), ← hLv,
      nsq_mulVec_of_isometry (StabCode.Encoder.pauliGroupMat_isometry L),
      nsq_mulVec_of_isometry e.isom_isometry]
  have heig : ∀ φ, nsq φ = 1 → ∃ c : ℂ, ℓ *ᵥ φ = c • φ := by
    intro φ hφ
    set χ := ℓ *ᵥ φ with hχdef
    have hχ : nsq χ = 1 := by rw [hχdef, hnorm, hφ]
    set w := e.amp (pauliGroupMat M *ᵥ (e.isom *ᵥ χ)) with hwdef
    have hw : nsq w = 1 := by rw [hwdef, e.nsq_amp_pauli_isom, hχ]
    obtain ⟨a1, ha1⟩ := (fidSum_eq_iff w hχ).mp (by rw [hw]; exact h1 χ hχ)
    have h2' : fidSum w φ = nsq w := by
      rw [hw]
      have := h2 φ hφ
      rwa [StabCode.Encoder.recoveryFid, pauliGroupMat_mul, ← mulVec_mulVec, hLv] at this
    obtain ⟨a2, ha2⟩ := (fidSum_eq_iff w hφ).mp h2'
    have hex : ∃ a, a2 a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hw0 : w = 0 := funext fun ia => by
        obtain ⟨i, a⟩ := ia
        rw [ha2, hcon, mul_zero]
        rfl
      rw [hw0, (nsq_eq_zero_iff _).mpr rfl] at hw
      exact zero_ne_one hw
    obtain ⟨a, ha⟩ := hex
    have hrel : ∀ i, χ i * a1 a = φ i * a2 a := fun i => (ha1 i a).symm.trans (ha2 i a)
    have ha1' : a1 a ≠ 0 := by
      intro h0
      have hφ0 : φ = 0 := funext fun i => by
        have := hrel i
        rw [h0, mul_zero] at this
        exact (mul_eq_zero.mp this.symm).resolve_right ha
      rw [hφ0, (nsq_eq_zero_iff _).mpr rfl] at hφ
      exact zero_ne_one hφ
    refine ⟨a2 a / a1 a, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hrel i
  have hlin : ∀ v : Qubits k → ℂ, ¬ LinearIndependent ℂ ![v, Matrix.toLin' ℓ v] := by
    intro v hli
    have hv : v ≠ 0 := by simpa using hli.ne_zero 0
    rw [LinearIndependent.pair_iff' hv] at hli
    have hr : 0 < nsq v :=
      lt_of_le_of_ne (nsq_nonneg v) fun h => hv ((nsq_eq_zero_iff v).mp h.symm)
    set s : ℂ := (((Real.sqrt (nsq v))⁻¹ : ℝ) : ℂ) with hsdef
    have hs : s ≠ 0 := by
      rw [hsdef, Complex.ofReal_ne_zero]
      exact inv_ne_zero (Real.sqrt_pos.mpr hr).ne'
    have hφ : nsq (s • v) = 1 := by
      rw [nsq_smul, hsdef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow, Real.sq_sqrt hr.le,
        inv_mul_cancel₀ hr.ne']
    obtain ⟨c, hc⟩ := heig (s • v) hφ
    have h3 : s • (ℓ *ᵥ v) = s • (c • v) := by rw [← mulVec_smul, hc, smul_comm]
    apply hli c
    rw [Matrix.toLin'_apply]
    exact (smul_right_injective _ hs h3).symm
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hlin
  refine ⟨c, fun v hv => ?_⟩
  obtain ⟨ψ, rfl⟩ := e.exists_eq_isom_mulVec hv
  have hψ : ℓ *ᵥ ψ = c • ψ := by
    have := LinearMap.congr_fun hc ψ
    simpa [Matrix.toLin'_apply] using this
  rw [hLv, hψ, mulVec_smul]

theorem StabCode.Encoder.space_ne_bot (e : C.Encoder k) : C.space ≠ ⊥ := by
  intro h
  have hmem := e.isom_mulVec_mem_space (Pi.single (0 : Qubits k) (1 : ℂ))
  rw [h, Submodule.mem_bot] at hmem
  have := nsq_mulVec_of_isometry e.isom_isometry (Pi.single (0 : Qubits k) (1 : ℂ))
  have h1 : nsq (Pi.single (0 : Qubits k) (1 : ℂ)) = 1 := by
    unfold nsq
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h0 : nsq (0 : Qubits n → ℂ) = 0 := by simp [nsq]
  rw [hmem, h0, h1] at this
  exact zero_ne_one this

theorem pauli_weight_mul_le (E F : PauliGroup_group n) :
    pauli_weight (E * F) ≤ pauli_weight E + pauli_weight F := by
  rw [pauli_weight_eq_BinSympPauli_weight, pauli_weight_eq_BinSympPauli_weight,
    pauli_weight_eq_BinSympPauli_weight, Pauli_to_BinSymp_correct]
  exact BinSympPauli.weight_add_le _ _

theorem pauli_weight_inv (E : PauliGroup_group n) :
    pauli_weight (E⁻¹ : PauliGroup_group n) = pauli_weight E := by
  rw [pauli_weight_eq_BinSympPauli_weight, pauli_weight_eq_BinSympPauli_weight,
    Pauli_toBinSympPauli_inv]

/- A nontrivial logical has weight at least the distance -/
theorem StabCode.distance_le_pauli_weight {L : PauliGroup_group n} (hL : L ∈ C.normalizerGroup)
    (hL' : L ∉ C.trivialLogicals) : C.distance ≤ pauli_weight L := by
  have hU := C.undetectable_of_notMem_trivialLogicals hL hL'
  have hU' : BinSympPauli_toPauli (Pauli_toBinSympPauli L) ∈ C.undetectable_set := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩
  have hw : pauli_weight (BinSympPauli_toPauli (Pauli_toBinSympPauli L)) = pauli_weight L := by
    rw [pauli_weight_BinSympPauli_toPauli, pauli_weight_eq_BinSympPauli_weight]
  have hmem := Finset.mem_image_of_mem pauli_weight hU'
  rw [hw] at hmem
  obtain ⟨d, hd⟩ := Finset.min_of_mem hmem
  have hle := Finset.min_le hmem
  rw [hd] at hle
  unfold StabCode.distance
  rw [hd]
  exact_mod_cast hle

theorem StabCode.Encoder.exists_logical_weight_eq_distance (e : C.Encoder k) (hk : 0 < k) :
    ∃ L : PauliGroup_group n, L ∈ C.normalizerGroup ∧ L ∉ C.trivialLogicals ∧
      pauli_weight L = C.distance := by
  have hdim : C.logical_dim = 2 ^ k := by
    unfold StabCode.logical_dim
    rw [← e.range_eq, LinearMap.finrank_range_of_inj]
    · simp
    · intro x y hxy
      have h2 : e.isomᴴ *ᵥ (e.isom *ᵥ x) = e.isomᴴ *ᵥ (e.isom *ᵥ y) := by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hxy
        exact congrArg (e.isomᴴ *ᵥ ·) hxy
      rwa [mulVec_mulVec, mulVec_mulVec, e.isom_isometry, one_mulVec, one_mulVec] at h2
  have hcard : Nat.card C.logicalGroup = 4 ^ k := (C.dim_iff_card_logicalGroup k).mp hdim
  have hnt : Nontrivial C.logicalGroup := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow hk.ne' (by norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : C.logicalGroup)
  obtain ⟨⟨E, hE⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hET : E ∉ C.trivialLogicals := by
    intro h
    apply hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h
  have hU := C.undetectable_of_notMem_trivialLogicals hE hET
  have hU' : BinSympPauli_toPauli (Pauli_toBinSympPauli E) ∈ C.undetectable_set :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩
  have hmem := Finset.mem_image_of_mem pauli_weight hU'
  obtain ⟨d, hd⟩ := Finset.min_of_mem hmem
  obtain ⟨L, hL, hLw⟩ := Finset.mem_image.mp (Finset.mem_of_min hd)
  have hLu : C.undetectable L := (Finset.mem_filter.mp hL).2
  refine ⟨L, hLu.1, hLu.2.1, ?_⟩
  unfold StabCode.distance
  rw [hd]
  exact hLw

theorem exists_split_pauli {t : ℕ} (L : PauliGroup_group n) (hL : pauli_weight L ≤ 2 * t) :
    ∃ A B : PauliGroup_group n, pauli_weight A ≤ t ∧ pauli_weight B ≤ t ∧
      Pauli_toBinSympPauli (A⁻¹ * B) = Pauli_toBinSympPauli L := by
  classical
  set x := Pauli_toBinSympPauli L
  set supp := Finset.univ.filter fun i => x.1 i ≠ 0 ∨ x.2 i ≠ 0 with hsupp_def
  have hsupp : supp.card ≤ 2 * t := by
    rw [hsupp_def, ← BinSympPauli.weight_eq_card, ← pauli_weight_eq_BinSympPauli_weight]
    exact hL
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (min_le_right t supp.card)
  let xa : BinSympPauli n :=
    (fun i => if i ∈ S then x.1 i else 0, fun i => if i ∈ S then x.2 i else 0)
  let xb : BinSympPauli n :=
    (fun i => if i ∈ S then 0 else x.1 i, fun i => if i ∈ S then 0 else x.2 i)
  refine ⟨BinSympPauli_toPauli xa, BinSympPauli_toPauli xb, ?_, ?_, ?_⟩
  · rw [pauli_weight_BinSympPauli_toPauli, BinSympPauli.weight_eq_card]
    refine (Finset.card_le_card fun i hi => ?_).trans (hScard.le.trans (min_le_left _ _))
    by_contra hiS
    simp [xa, hiS] at hi
  · rw [pauli_weight_BinSympPauli_toPauli, BinSympPauli.weight_eq_card]
    have hsub : (Finset.univ.filter fun i => xb.1 i ≠ 0 ∨ xb.2 i ≠ 0) ⊆ supp \ S := by
      intro i hi
      by_cases hiS : i ∈ S
      · simp [xb, hiS] at hi
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, xb, hiS, if_false] at hi
        simp [hsupp_def, hiS, hi]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_sdiff_of_subset hS]
    omega
  · rw [Pauli_to_BinSymp_correct, Pauli_toBinSympPauli_inv,
      Pauli_toBinSympPauli_BinSympPauli_toPauli, Pauli_toBinSympPauli_BinSympPauli_toPauli]
    ext i <;> simp only [xa, xb, Prod.fst_add, Prod.snd_add, Pi.add_apply] <;> split_ifs <;> simp

theorem StabCode.mem_normalizerGroup_congr {L L' : PauliGroup_group n}
    (h : Pauli_toBinSympPauli L = Pauli_toBinSympPauli L') :
    L ∈ C.normalizerGroup ↔ L' ∈ C.normalizerGroup := by
  rw [C.normalizerGroup_eq_comap, Subgroup.mem_comap, Subgroup.mem_comap, PauliGroup.phi_apply,
    PauliGroup.phi_apply, h]

theorem StabCode.mem_trivialLogicals_congr {L L' : PauliGroup_group n}
    (h : Pauli_toBinSympPauli L = Pauli_toBinSympPauli L') :
    L ∈ C.trivialLogicals ↔ L' ∈ C.trivialLogicals := by
  rw [C.trivialLogicals_eq_comap, Subgroup.mem_comap, Subgroup.mem_comap, PauliGroup.phi_apply,
    PauliGroup.phi_apply, h]

open Classical in
def boundedWeightDecoder (G : C.Generators m) (t : ℕ) : Decoder n m := fun s =>
  if h : ∃ E : PauliGroup_group n, pauli_weight E ≤ t ∧ G.pauliSyndrome E = s then h.choose
  else 1

/-- If `2t < d`, then decoding always succeeds -/
theorem gfidelity_boundedWeightDecoder_eq_one (e : C.Encoder k) (G : C.Generators m) {t : ℕ}
    (ht : 2 * t < C.distance) (p : ProbabilityMeasure (Ket (Qubits k)))
    (P : ProbDistribution (PauliGroup_group n)) (hP : PauliWeightLE P t) :
    gfidelity e G (boundedWeightDecoder G t) p (pauliErrorChannel P) = 1 := by
  have key : ∀ E : PauliGroup_group n, pauli_weight E ≤ t →
      boundedWeightDecoder G t (G.pauliSyndrome E) * E ∈ C.trivialLogicals := by
    intro E hE
    have h : ∃ F : PauliGroup_group n, pauli_weight F ≤ t ∧
        G.pauliSyndrome F = G.pauliSyndrome E := ⟨E, hE, rfl⟩
    have hdec : boundedWeightDecoder G t (G.pauliSyndrome E) = h.choose := dif_pos h
    obtain ⟨hw, hs⟩ := h.choose_spec
    rw [hdec]
    by_contra hT
    have hN : h.choose * E ∈ C.normalizerGroup := by
      rw [G.mem_normalizerGroup_iff_pauliSyndrome, G.pauliSyndrome_mul, hs]
      funext j
      exact CharTwo.add_self_eq_zero (G.pauliSyndrome E j)
    have h1 := C.distance_le_pauli_weight hN hT
    have h2 := pauli_weight_mul_le h.choose E
    omega
  have hpt : ∀ φ : Ket (Qubits k), (logicalChannel e G (boundedWeightDecoder G t)
      (pauliErrorChannel P) (MState.pure φ)).exp_val (MState.pure φ).M = 1 := by
    intro φ
    rw [exp_val_logicalChannel_pauliErrorChannel]
    have hE : ∀ E, (P E : ℝ) * e.recoveryFid (boundedWeightDecoder G t (G.pauliSyndrome E) * E)
        φ.vec φ.vec = P E := by
      intro E
      by_cases hE : (P E : ℝ) = 0
      · simp [hE]
      · rw [e.recoveryFid_eq_one_of_mem_trivialLogicals (key E (hP E hE)) φ.normalized',
          mul_one]
    rw [Finset.sum_congr rfl fun E _ => hE E, P.normalized]
  unfold gfidelity
  simp_rw [hpt]
  simp

theorem two_mul_lt_distance_of_forall_exists_decoder (e : C.Encoder k) (G : C.Generators m)
    (hk : 0 < k) {p : ProbabilityMeasure (Ket (Qubits k))} (hp : Ket.FullSupport p) {t : ℕ}
    (h : ∀ P : ProbDistribution (PauliGroup_group n), PauliWeightLE P t →
      ∃ dec : Decoder n m, gfidelity e G dec p (pauliErrorChannel P) = 1) :
    2 * t < C.distance := by
  by_contra hd
  rw [not_lt] at hd
  obtain ⟨L, hLN, hLT, hLw⟩ := e.exists_logical_weight_eq_distance hk
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_split_pauli (t := t) L (hLw ▸ hd)
  have hN : A⁻¹ * B ∈ C.normalizerGroup := (C.mem_normalizerGroup_congr hAB).mpr hLN
  have hT : A⁻¹ * B ∉ C.trivialLogicals := fun h => hLT ((C.mem_trivialLogicals_congr hAB).mp h)
  classical
  let P : ProbDistribution (PauliGroup_group n) :=
    ProbDistribution.mk' (fun E => (if E = A then 1 / 2 else 0) + (if E = B then 1 / 2 else 0))
      (fun E => by positivity) (by simp [Finset.sum_add_distrib]; norm_num)
  have hPval : ∀ E, (P E : ℝ) = (if E = A then 1 / 2 else 0) + (if E = B then 1 / 2 else 0) :=
    fun E => rfl
  have hPw : PauliWeightLE P t := by
    intro E hE
    rw [hPval] at hE
    by_cases hEA : E = A
    · exact hEA ▸ hA
    · by_cases hEB : E = B
      · exact hEB ▸ hB
      · simp [hEA, hEB] at hE
  obtain ⟨dec, hdec⟩ := h P hPw
  set Λ := logicalChannel e G dec (pauliErrorChannel P) with hΛ
  have hpt : ∀ φ : Ket (Qubits k), (Λ (MState.pure φ)).exp_val (MState.pure φ).M = 1 := by
    intro φ
    have hL : Continuous (Λ.map : Matrix (Qubits k) (Qubits k) ℂ → _) :=
      LinearMap.continuous_of_finiteDimensional _
    have hc : Continuous fun v : Qubits k → ℂ =>
        (Matrix.trace (Λ.map (vecMulVec v (star v)) * vecMulVec v (star v))).re := by
      fun_prop
    have := Ket.eq_one_of_integral_eq_one hp hc
      (fun ψ => by rw [← Λ.exp_val_pure_eq_trace]; exact (MState.exp_val_pure_mem_Icc _ ψ).1)
      (fun ψ => by rw [← Λ.exp_val_pure_eq_trace]; exact (MState.exp_val_pure_mem_Icc _ ψ).2)
      (by simp_rw [← Λ.exp_val_pure_eq_trace]; exact hdec) φ
    rwa [← Λ.exp_val_pure_eq_trace] at this
  have hf : ∀ (E : PauliGroup_group n), (P E : ℝ) ≠ 0 → ∀ φ : Ket (Qubits k),
      e.recoveryFid (dec (G.pauliSyndrome E) * E) φ.vec φ.vec = 1 := by
    intro E hE φ
    have h1 := hpt φ
    rw [hΛ, exp_val_logicalChannel_pauliErrorChannel] at h1
    exact eq_one_of_sum_mul_eq_one (fun E => (P E).zero_le_coe) P.normalized
      (fun E => e.recoveryFid_le_one _ φ.normalized' φ.normalized') h1 hE
  have hs : G.pauliSyndrome B = G.pauliSyndrome A := by
    have hBA : B = A * (A⁻¹ * B) := by group
    rw [hBA, G.pauliSyndrome_mul, (G.mem_normalizerGroup_iff_pauliSyndrome _).mp hN, add_zero]
  have hPA : (P A : ℝ) ≠ 0 := by rw [hPval, if_pos rfl]; split_ifs <;> norm_num
  have hPB : (P B : ℝ) ≠ 0 := by rw [hPval, if_pos rfl]; split_ifs <;> norm_num
  obtain ⟨c, hc⟩ := e.exists_scalar_of_recoveryFid_eq_one (M := dec (G.pauliSyndrome A) * A) hN
    (fun ψ hψ => hf A hPA ⟨ψ, hψ⟩)
    (fun φ hφ => by
      rw [show dec (G.pauliSyndrome A) * A * (A⁻¹ * B) = dec (G.pauliSyndrome B) * B by
        rw [hs]; group]
      exact hf B hPB ⟨φ, hφ⟩)
  exact hT (C.mem_trivialLogicals_of_scalar e.space_ne_bot hc)

/- Decoding-centric characterization of code distance: for errors with weight bounded by `t`, a perfect decoder exists iff `2t < d` -/
theorem exists_decoder_gfidelity_eq_one_iff (e : C.Encoder k) (G : C.Generators m) (hk : 0 < k)
    (t : ℕ) :
    (∃ dec : Decoder n m, ∀ P : ProbDistribution (PauliGroup_group n), PauliWeightLE P t →
      gfidelity e G dec (Ket.uniform (Qubits k)) (pauliErrorChannel P) = 1) ↔
      2 * t < C.distance := by
  refine ⟨fun ⟨dec, hdec⟩ => two_mul_lt_distance_of_forall_exists_decoder e G hk
    Ket.uniform_fullSupport fun P hP => ⟨dec, hdec P hP⟩, fun ht =>
    ⟨boundedWeightDecoder G t, fun P hP => gfidelity_boundedWeightDecoder_eq_one e G ht _ P hP⟩⟩

end
