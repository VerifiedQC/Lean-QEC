import LeanQEC.Stabilizer.Distance

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000


noncomputable def StabCode.stabSymplecticSpace {n : ℕ} (C : StabCode n) :
    Submodule (ZMod 2) (BinSympPauli n) :=
  Submodule.span (ZMod 2)
    (Set.image Pauli_toBinSympPauli (C.stabs : Set (PauliGroup n)))

noncomputable def StabCode.numGenerators {n : ℕ} (C : StabCode n) : ℕ :=
  Module.finrank (ZMod 2) C.stabSymplecticSpace

lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

def StabCode.phiImage {n : ℕ} (C : StabCode n) : Submodule (ZMod 2) (BinSympPauli n) where
  carrier := Pauli_toBinSympPauli '' ((C.stabs : Set (PauliGroup n)))
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_mem hx hy, Pauli_to_BinSymp_correct x y⟩
  zero_mem' := ⟨1, one_mem _, Pauli_toBinSympPauli_one⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨x, hx, rfl⟩ := ha
    rcases zmod2_eq_zero_or_one c with h | h <;> subst h
    · exact ⟨1, one_mem _, by rw [zero_smul, Pauli_toBinSympPauli_one]⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

lemma StabCode.stabSymplecticSpace_eq_phiImage {n : ℕ} (C : StabCode n) :
    C.stabSymplecticSpace = C.phiImage :=
  Submodule.span_eq C.phiImage

lemma StabCode.mem_stabilizerSpace_iff {n : ℕ} (C : StabCode n) (x : BinSympPauli n) :
    x ∈ C.stabSymplecticSpace ↔ ∃ s ∈ C.stabs, Pauli_toBinSympPauli s = x := by
  rw [C.stabSymplecticSpace_eq_phiImage]
  exact ⟨fun ⟨s, hs, hEq⟩ => ⟨s, hs, hEq⟩, fun ⟨s, hs, hEq⟩ => ⟨s, hs, hEq⟩⟩

/-- The stabilizer group of a code we define using the check matrix is just the rowspace of the check matrix -/
lemma BinSympMatrix.stabSymplecticSpace_eq_rowSpace {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).stabSymplecticSpace = B.rowSpace := by
  ext x
  rw [StabCode.mem_stabilizerSpace_iff, B.mem_rowSpace_iff_exists_stab h_comm h_minus]

lemma BinSympMatrix.numGenerators_eq_finrank_rowSpace {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).numGenerators = Module.finrank (ZMod 2) B.rowSpace := by
  rw [StabCode.numGenerators, B.stabSymplecticSpace_eq_rowSpace h_comm h_minus]

def BinSympPauli.toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n)) :
    Subgroup (Multiplicative (BinSympPauli n)) :=
  AddSubgroup.toSubgroup V.toAddSubgroup

@[simp] lemma BinSympPauli.mem_toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n))
    (x : Multiplicative (BinSympPauli n)) :
    x ∈ BinSympPauli.toSubgroup V ↔ Multiplicative.toAdd x ∈ V := Iff.rfl

lemma BinSympPauli.card_toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n)) :
    Nat.card (BinSympPauli.toSubgroup V) = 2 ^ Module.finrank (ZMod 2) V := by
  have hequiv : ↥(BinSympPauli.toSubgroup V) ≃ ↥V :=
    ⟨fun x => ⟨Multiplicative.toAdd x.1, x.2⟩, fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr hequiv, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥V)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma StabCode.trivialLogicals_eq_comap_stabilizerSpace {n : ℕ} (C : StabCode n) :
    C.trivialLogicals
      = Subgroup.comap (PauliGroup.phi n) (BinSympPauli.toSubgroup C.stabSymplecticSpace) := by
  ext E
  rw [C.mem_trivialLogicals_iff, Subgroup.mem_comap, BinSympPauli.mem_toSubgroup]
  exact (C.mem_stabilizerSpace_iff (Pauli_toBinSympPauli E)).symm

noncomputable def StabCode.logical_dim {n : ℕ} (C : StabCode n) : ℕ :=
  Module.finrank ℂ C.space

noncomputable def BinSympPauli.form (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (BinSympPauli n) :=
  LinearMap.mk₂ (ZMod 2) symplecticProd
    (by intros; simp [symplecticProd, add_dotProduct]; abel)
    (by intros; simp [symplecticProd, smul_dotProduct, smul_add, mul_add])
    (by intros; simp [symplecticProd, dotProduct_add]; abel)
    (by intros; simp [symplecticProd, dotProduct_smul, smul_add, mul_add])

lemma BinSympPauli.form_apply {n : ℕ} (x y : BinSympPauli n) :
    BinSympPauli.form n x y = symplecticProd x y := by
  rfl

lemma BinSympPauli.form_nondegenerate (n : ℕ) :
    (BinSympPauli.form n).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate;
  simp +decide [ LinearMap.Nondegenerate ];
  constructor <;> intro x hx <;> ext i <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ, symplecticProd ];
  · specialize hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form ] ;
    unfold symplecticProd at hx; simp_all +decide [ dotProduct, Pi.single_apply ] ;
  · unfold form at hx; specialize hx ( Pi.single i 1 ) 0; simp_all +decide [ dotProduct ] ;
    simp_all +decide [ symplecticProd, dotProduct ];
    simp_all +decide [ Pi.single_apply ];
  · specialize hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form, symplecticProd ] ;
  · convert hx 0 ( Pi.single i 1 ) using 1 ; simp +decide [ form ];
    unfold symplecticProd; simp +decide [ Finset.sum_apply, Pi.single_apply ] ;
    have := hx ( Pi.single i 1 ) 0; have := hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form ] ;
    have := hx ( Pi.single i 1 ) 0; have := hx 0 ( Pi.single i 1 ) ; simp_all +decide [ symplecticProd ] ;

lemma BinSympPauli.form_isRefl (n : ℕ) :
    (BinSympPauli.form n).IsRefl := by
  unfold LinearMap.BilinForm.IsRefl; simp +decide [ form ] ;
  intro x; unfold symplecticProd; simp_all +decide [ dotProduct ] ;
  simp +decide [ mul_comm, add_comm ]

lemma BinSympPauli.finrank (n : ℕ) :
    Module.finrank (ZMod 2) (BinSympPauli n) = 2 * n := by
  unfold BinSympPauli; norm_num [ two_mul ] ;

noncomputable def StabCode.normalizerSpace {n : ℕ} (C : StabCode n) :
    Submodule (ZMod 2) (BinSympPauli n) :=
  (BinSympPauli.form n).orthogonal C.stabSymplecticSpace

lemma StabCode.stabSymplecticSpace_le_normalizerSpace {n : ℕ} (C : StabCode n) :
    C.stabSymplecticSpace ≤ C.normalizerSpace := by
  refine' Submodule.span_le.mpr _;
  intro x hx
  obtain ⟨s, hs, rfl⟩ := hx
  have h_comm : ∀ t ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli t) = 0 := by
    intro t ht
    have h_comm : commute s t := by
      have h_comm : s * t = t * s := by
        have h_comm : IsMulCommutative C.stabs := by
          exact C.h_comm;
        have h_comm : ∀ (s t : ↥C.stabs), s * t = t * s := by
          exact fun s t => mul_comm' s t;
        convert congr_arg Subtype.val ( h_comm ⟨ s, hs ⟩ ⟨ t, ht ⟩ ) using 1
      exact (commute_iff_commute s t).2 h_comm
    exact (commute_iff_symplecticProd_zero s t).1 h_comm
  rw [SetLike.mem_coe, StabCode.normalizerSpace, LinearMap.BilinForm.mem_orthogonal_iff]
  intro t ht
  have hle : C.stabSymplecticSpace ≤
      LinearMap.ker ((BinSympPauli.form n).flip (Pauli_toBinSympPauli s)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    show symplecticProd (Pauli_toBinSympPauli u) (Pauli_toBinSympPauli s) = 0
    rw [symplecticProd_comm]
    exact h_comm u hu
  exact hle ht

lemma StabCode.finrank_normalizerSpace {n : ℕ} (C : StabCode n) :
    Module.finrank (ZMod 2) C.normalizerSpace = 2 * n - C.numGenerators := by
  convert LinearMap.BilinForm.finrank_orthogonal ( BinSympPauli.form_nondegenerate n ) C.stabSymplecticSpace using 1;
  rw [ BinSympPauli.finrank ];
  rfl

lemma StabCode.numGenerators_le {n : ℕ} (C : StabCode n) : C.numGenerators ≤ n := by
  have h1 : C.numGenerators ≤ Module.finrank (ZMod 2) C.normalizerSpace :=
    Submodule.finrank_mono C.stabSymplecticSpace_le_normalizerSpace
  have h2 : C.numGenerators ≤ 2 * n := by
    have := Submodule.finrank_le C.stabSymplecticSpace
    rwa [BinSympPauli.finrank] at this
  rw [C.finrank_normalizerSpace] at h1
  omega

lemma StabCode.normalizerGroup_eq_comap {n : ℕ} (C : StabCode n) :
    C.normalizerGroup
      = Subgroup.comap (PauliGroup.phi n) (BinSympPauli.toSubgroup C.normalizerSpace) := by
  ext E
  rw [C.mem_normalizerGroup_iff_symplecticProd, Subgroup.mem_comap,
    BinSympPauli.mem_toSubgroup]
  show (∀ s ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli E) = 0)
    ↔ Pauli_toBinSympPauli E ∈ C.normalizerSpace
  constructor
  · intro hE y hy
    obtain ⟨s, hs, rfl⟩ := (C.mem_stabilizerSpace_iff y).1 hy
    simpa [BinSympPauli.form_apply, LinearMap.BilinForm.IsOrtho] using hE s hs
  · intro hE s hs
    have := hE (Pauli_toBinSympPauli s) ((C.mem_stabilizerSpace_iff _).2 ⟨s, hs, rfl⟩)
    simpa [BinSympPauli.form_apply, LinearMap.BilinForm.IsOrtho] using this

/-- There are 4^(n-generators) logical operators -/
theorem StabCode.card_logicalGroup {n : ℕ} (C : StabCode n) :
    Nat.card C.logicalGroup = 4 ^ (n - C.numGenerators) := by
  have hle : C.numGenerators ≤ n := C.numGenerators_le
  have hcard : Nat.card C.logicalGroup = C.trivialLogicals.relIndex C.normalizerGroup := rfl
  rw [hcard, C.trivialLogicals_eq_comap_stabilizerSpace, C.normalizerGroup_eq_comap,
    Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (PauliGroup.phi_surjective n)]
  set Sg := BinSympPauli.toSubgroup C.stabSymplecticSpace with hSg
  set Ng := BinSympPauli.toSubgroup C.normalizerSpace with hNg
  have hSN : Sg ≤ Ng := fun x hx => C.stabSymplecticSpace_le_normalizerSpace hx
  have hmul : Nat.card ↥(Sg.subgroupOf Ng) * (Sg.subgroupOf Ng).index = Nat.card ↥Ng :=
    Subgroup.card_mul_index _
  have hsub : Nat.card ↥(Sg.subgroupOf Ng) = Nat.card ↥Sg :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hScard : Nat.card ↥Sg = 2 ^ C.numGenerators := BinSympPauli.card_toSubgroup _
  have hNcard : Nat.card ↥Ng = 2 ^ (2 * n - C.numGenerators) := by
    rw [BinSympPauli.card_toSubgroup, C.finrank_normalizerSpace]
  rw [hsub, hScard, hNcard] at hmul
  have hpow : (2 : ℕ) ^ C.numGenerators * 4 ^ (n - C.numGenerators) = 2 ^ (2 * n - C.numGenerators) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have := hmul.trans hpow.symm
  exact Nat.eq_of_mul_eq_mul_left (by positivity) this

lemma StabCode.undetectable_of_notMem_trivialLogicals {n : ℕ} (C : StabCode n)
    {E : PauliGroup_group n} (hE : E ∈ C.normalizerGroup) (hE' : E ∉ C.trivialLogicals) :
    C.undetectable (BinSympPauli_toPauli (Pauli_toBinSympPauli E)) := by
  refine ⟨?_, ?_, BinSympPauli_toPauli_normalized _⟩
  · rw [C.mem_normalizerGroup_iff_symplecticProd] at hE ⊢
    simpa using hE
  · rw [C.mem_trivialLogicals_iff] at hE' ⊢
    simpa using hE'

/- Definition of saying that `C` is a `[[n, k]]` code -/
structure param_triple {n : ℕ} (C : StabCode n) (k d : ℕ) where
  achieves_k : C.logical_dim = 2^k
  achieves_d : d ≤ C.distance

lemma Pauli_toBinSympPauli_eq_zero_iff {n : ℕ} (P : PauliGroup_group n) :
    Pauli_toBinSympPauli P = 0 ↔ PauliGroup.map P = fun _ => Pauli_I := by
  simp +decide [ funext_iff, Prod.ext_iff, Pauli_toBinSympPauli ];
  constructor <;> intro h;
  · intro x;
    convert ( Z2Z2_Pauli_equiv.symm_apply_eq.mp _ );
    rotate_left;
    exact ( 0, 0 );
    · exact Prod.ext ( h.1 x ) ( h.2 x );
    · rfl;
  · have h_symm : Z2Z2_Pauli_equiv.symm Pauli_I = (0, 0) := by
      exact (Equiv.symm_apply_eq Z2Z2_Pauli_equiv).mpr rfl
    aesop

lemma PauliGroup.mem_phaseSubgroup_iff_scalar {n : ℕ} (P : PauliGroup_group n) :
    P ∈ PauliGroup.phaseSubgroup n ↔ ∃ z : pgroup_phases, P = scalarPauli z := by
  rw [PauliGroup.mem_phaseSubgroup_iff, Pauli_toBinSympPauli_eq_zero_iff]
  constructor
  · intro h
    refine ⟨PauliGroup.phase P, ?_⟩
    conv_lhs => rw [← foldPauli_phase_map P]
    rw [h]
    rfl
  · rintro ⟨z, rfl⟩
    simp [scalarPauli, PauliGroup.map]

lemma one_eq_scalarPauli_one {n : ℕ} :
    (1 : PauliGroup_group n) = scalarPauli 1 := by
  convert Pauli1_unfold

lemma pgphase_sq_eq (z : pgroup_phases) (hz1 : z ≠ 1) (hzn1 : z ≠ pgphase_n1) :
    z * z = pgphase_n1 := by
  revert z; decide

lemma ker_phi_trivial {n : ℕ} (C : StabCode n)
    (g : PauliGroup_group n) (hg : g ∈ C.stabs)
    (hphi : Pauli_toBinSympPauli g = 0) : g = 1 := by
  have hmap : PauliGroup.map g = fun _ => Pauli_I :=
    (Pauli_toBinSympPauli_eq_zero_iff g).mp hphi
  have hg' : g = scalarPauli (PauliGroup.phase g) := by
    unfold scalarPauli
    rw [← hmap]
    exact (foldPauli_phase_map g).symm
  set z := PauliGroup.phase g with hz
  by_cases hz1 : z = 1
  · rw [hg', hz1]
    exact one_eq_scalarPauli_one.symm
  · by_cases hzn1 : z = pgphase_n1
    · exfalso
      apply C.h_minus
      have hgn : g = negIdPauli n := by rw [hg', hzn1]; rfl
      rw [← hgn]; exact hg
    · exfalso
      apply C.h_minus
      have hsq : z * z = pgphase_n1 := pgphase_sq_eq z hz1 hzn1
      have hgg : g * g = negIdPauli n := by
        rw [hg', foldPauli_scalar_sq, hsq]; rfl
      rw [← hgg]
      exact mul_mem hg hg

/-- Elements of the stabilizer group square to the identity. -/
lemma StabCode.mul_self_of_mem {n : ℕ} (C : StabCode n) {g : PauliGroup_group n}
    (hg : g ∈ C.stabs) : g * g = 1 := by
  apply ker_phi_trivial C (g * g) (mul_mem hg hg)
  rw [Pauli_to_BinSymp_correct]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  ext i <;> simp [h2]

lemma phi_injOn {n : ℕ} (C : StabCode n) :
    Set.InjOn Pauli_toBinSympPauli (C.stabs : Set (PauliGroup n)) := by
  intro a ha b hb hab
  have := ker_phi_trivial C (a * b⁻¹) (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)) ?_
  · simpa using eq_inv_of_mul_eq_one_left this
  · rw [Pauli_to_BinSymp_correct, hab]
    rw [← Pauli_to_BinSymp_correct]
    simp +decide [Pauli_toBinSympPauli_one]

lemma StabCode.card_stabs {n : ℕ} (C : StabCode n) :
    Nat.card C.stabs = 2 ^ C.numGenerators := by
  have hinj := phi_injOn C
  have hgen : C.numGenerators = Module.finrank (ZMod 2) C.phiImage := by
    rw [StabCode.numGenerators, C.stabSymplecticSpace_eq_phiImage]
  have hcardV : Nat.card C.phiImage = 2 ^ Module.finrank (ZMod 2) C.phiImage := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C.phiImage)]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hcardG : Nat.card C.phiImage = Nat.card C.stabs := Nat.card_image_of_injOn hinj
  rw [← hcardG, hcardV, hgen]

instance PauliGroup_group.instFinite (n : ℕ) : Finite ↥(PauliGroup_group n) := by
  have : Fintype ↥(PauliGroup_group n) := FinsetCoe.fintype (PauliGroup n)
  exact Finite.of_fintype _

noncomputable instance StabCode.instFintypeStabs {n : ℕ} (C : StabCode n) :
    Fintype ↥C.stabs := Fintype.ofFinite _

lemma stabilizes_iff_mulVec {n : ℕ} (U : 𝐔ₙ[n]) (ψ : PState n) :
    stabilizes U ψ ↔ U.val.mulVec ψ = ψ := Iff.rfl

lemma StabCode.mem_space_iff_mulVec {n : ℕ} (C : StabCode n) (v : PState n) :
    v ∈ C.space ↔ ∀ s ∈ C.stabs, (s.val.val).mulVec v = v := by
  rw [StabCode.mem_space]
  simp only [stabilizes_iff_mulVec]

/- The projector onto the codespace -/
noncomputable def StabCode.projector {n : ℕ} (C : StabCode n) :
    (PState n) →ₗ[ℂ] (PState n) :=
  (Nat.card C.stabs : ℂ)⁻¹ • ∑ g : ↥C.stabs, Matrix.toLin' (g.val.val.val)

lemma StabCode.projector_apply {n : ℕ} (C : StabCode n) (v : PState n) :
    C.projector v
      = (Nat.card C.stabs : ℂ)⁻¹ • ∑ g : ↥C.stabs, (g.val.val.val).mulVec v := by
  simp [StabCode.projector, LinearMap.sum_apply, Matrix.toLin'_apply]

/- The projector is the identity in the codespace -/
lemma StabCode.projector_apply_id {n : ℕ} (C : StabCode n) (v : PState n)
    (hv' : v ∈ C.space) : C.projector v = v := by
  have hv : ∀ s ∈ C.stabs, (s.val.val).mulVec v = v := (C.mem_space_iff_mulVec v).mp hv'
  have h_sum : ∑ g : ↥C.stabs, (g.val.val.val).mulVec v = (Nat.card C.stabs : ℂ) • v := by
    convert Finset.sum_const v
    · rename_i x hx
      exact hv _ x.2
    · ext; simp [Nat.card]
  unfold StabCode.projector; simp +decide [h_sum]

/- The projector indeed is the projector -/
lemma StabCode.projector_apply_mem {n : ℕ} (C : StabCode n) (v : PState n) :
    C.projector v ∈ C.space := by
  rw [StabCode.mem_space_iff_mulVec]
  intro s hs
  unfold StabCode.projector
  simp
  rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft (⟨s, hs⟩ : ↥C.stabs))]
  simp +decide [Matrix.mulVec_mulVec]

lemma StabCode.projector_isProj {n : ℕ} (C : StabCode n) :
    LinearMap.IsProj C.space C.projector :=
  ⟨fun v => C.projector_apply_mem v, fun v hv => C.projector_apply_id v hv⟩

lemma trace_stab_elem {n : ℕ} (C : StabCode n)
    (g : PauliGroup_group n) (hg : g ∈ C.stabs) :
    Matrix.trace (g.val.val) = if g = 1 then (2 : ℂ) ^ n else 0 := by
  split_ifs with h
  · have h_card : Fintype.card (Qubits n) = 2 ^ n := card_qubits n
    aesop
  · have h_trace_zero : Matrix.trace (fold (PauliGroup.phase g, PauliGroup.map g)).val = 0 := by
      rw [ trace_fold_eq ];
      contrapose! h;
      exact ker_phi_trivial C g hg ( Pauli_toBinSympPauli_eq_zero_iff g |>.2 <| by aesop );
    convert h_trace_zero using 2;
    exact congr_arg ( fun x : PauliGroup_group n => x.val.val ) ( foldPauli_phase_map g |> Eq.symm )

lemma sum_trace_stabs {n : ℕ} (C : StabCode n) :
    ∑ g : ↥C.stabs, Matrix.trace (g.val.val.val) = (2 : ℂ) ^ n := by
  rw [ Finset.sum_congr rfl fun x hx => ?_ ];
  rotate_left;
  exact fun g => if g.val = 1 then ( 2 : ℂ ) ^ n else 0;
  · convert trace_stab_elem C x.val x.2 using 1;
  · rw [ Finset.sum_eq_single 1 ] <;> aesop

lemma StabCode.trace_projector {n : ℕ} (C : StabCode n) :
    LinearMap.trace ℂ _ C.projector = (Nat.card C.stabs : ℂ)⁻¹ * (2 : ℂ) ^ n := by
  unfold StabCode.projector; norm_num [ Matrix.trace_toLin'_eq ] ;
  convert sum_trace_stabs C using 1

lemma StabCode.logical_dim_mul_card {n : ℕ} (C : StabCode n) :
    C.logical_dim * Nat.card C.stabs = 2 ^ n := by
  have hproj := C.projector_isProj
  have htr := C.trace_projector
  have hfr : LinearMap.trace ℂ _ C.projector = (Module.finrank ℂ C.space : ℂ) := hproj.trace
  rw [hfr] at htr
  set N := Nat.card C.stabs with hN
  have hNpos : 0 < N := Nat.card_pos
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hnat : Module.finrank ℂ C.space * N = 2 ^ n := by
    have hcast : (Module.finrank ℂ C.space : ℂ) * (N : ℂ) = (2 : ℂ) ^ n := by
      rw [htr]; field_simp
    exact_mod_cast hcast
  exact hnat

theorem StabCode.dim_iff_generators {n : ℕ} (C : StabCode n) (k : ℕ) :
    C.logical_dim = 2 ^ k ↔ k = n - C.numGenerators := by
  have hcard := C.card_stabs
  have hmul := C.logical_dim_mul_card
  set d := C.logical_dim with hd
  set g := C.numGenerators with hg
  rw [hcard] at hmul
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, zero_mul] at hmul; exact absurd hmul.symm (by positivity)
    · exact h
  have hle : g ≤ n := by
    have hpow : (2 : ℕ) ^ g ≤ 2 ^ n := by
      calc (2 : ℕ) ^ g ≤ d * 2 ^ g := Nat.le_mul_of_pos_left _ hdpos
        _ = 2 ^ n := hmul
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hpow
  have hdg : d = 2 ^ (n - g) := by
    have h2 : (2 : ℕ) ^ (n - g) * 2 ^ g = 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hh : d * 2 ^ g = 2 ^ (n - g) * 2 ^ g := by rw [hmul, h2]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hh
  rw [hdg]
  constructor
  · intro h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  · intro h; rw [h]

theorem StabCode.dim_iff_card_logicalGroup {n : ℕ} (C : StabCode n) (k : ℕ) :
    C.logical_dim = 2 ^ k ↔ Nat.card C.logicalGroup = 4 ^ k := by
  rw [C.dim_iff_generators k, StabCode.card_logicalGroup]
  exact ⟨fun h => by rw [h], fun h => (Nat.pow_right_injective (by norm_num) h).symm⟩

theorem StabCode.param_triple_of {n : ℕ} (C : StabCode n) (k d : ℕ)
    (hk : k = n - C.numGenerators) (hd : d ≤ C.distance) : param_triple C k d :=
  ⟨(C.dim_iff_generators k).2 hk, hd⟩
