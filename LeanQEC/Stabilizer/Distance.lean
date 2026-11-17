import LeanQEC.Stabilizer.BinSymp

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-- Since we just want to talk about commutation, we can quotient out phases -/
def PauliGroup.phi (n : ℕ) : PauliGroup_group n →* Multiplicative (BinSympPauli n) where
  toFun P := Multiplicative.ofAdd (Pauli_toBinSympPauli P)
  map_one' := congrArg Multiplicative.ofAdd Pauli_toBinSympPauli_one
  map_mul' P Q := congrArg Multiplicative.ofAdd (Pauli_to_BinSymp_correct P Q)

@[simp] lemma PauliGroup.phi_apply {n : ℕ} (P : PauliGroup_group n) :
    PauliGroup.phi n P = Multiplicative.ofAdd (Pauli_toBinSympPauli P) := rfl

lemma PauliGroup.phi_surjective (n : ℕ) : Function.Surjective (PauliGroup.phi n) :=
  fun x => ⟨BinSympPauli_toPauli (Multiplicative.toAdd x), by simp⟩

/- The Paulis which are just the identity operator after you quotient out phases -/
def PauliGroup.phaseSubgroup (n : ℕ) : Subgroup (PauliGroup_group n) := (PauliGroup.phi n).ker

lemma PauliGroup.mem_phaseSubgroup_iff {n : ℕ} (P : PauliGroup_group n) :
    P ∈ PauliGroup.phaseSubgroup n ↔ Pauli_toBinSympPauli P = 0 := by
  simp [PauliGroup.phaseSubgroup, MonoidHom.mem_ker]

/- The normalizer and centralizer are equal for a stabilizer code -/
def StabCode.normalizerGroup {n : ℕ} (C : StabCode n) : Subgroup (PauliGroup_group n) :=
  Subgroup.centralizer (C.stabs : Set (PauliGroup_group n))

lemma StabCode.mem_normalizerGroup_iff {n : ℕ} (C : StabCode n) (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ ∀ s ∈ C.stabs, commute E s := by
  simp only [StabCode.normalizerGroup, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  exact ⟨fun h s hs => (commute_iff_commute E s).2 (h s hs).symm,
    fun h s hs => ((commute_iff_commute E s).1 (h s hs)).symm⟩

/-- Membership in the normalizer only has to be checked on any generating set of the
stabilizer group. -/
lemma StabCode.mem_normalizerGroup_of_closure {n : ℕ} (C : StabCode n)
    {T : Set (PauliGroup_group n)} (hT : Subgroup.closure T = C.stabs)
    (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ ∀ s ∈ T, commute E s := by
  rw [StabCode.normalizerGroup, ← hT, Subgroup.centralizer_closure]
  simp only [Subgroup.mem_centralizer_iff]
  exact ⟨fun h s hs => (commute_iff_commute E s).2 (h s hs).symm,
    fun h s hs => ((commute_iff_commute E s).1 (h s hs)).symm⟩

lemma StabCode.mem_normalizerGroup_of_StabSet {n : ℕ} (S : StabSet n)
    (h_minus : negIdPauli n ∉ Subgroup.closure (SetLike.coe S.stabs)) (E : PauliGroup_group n) :
    E ∈ (StabCode_of_StabSet S h_minus).normalizerGroup ↔ ∀ s ∈ S.stabs, commute E s :=
  (StabCode_of_StabSet S h_minus).mem_normalizerGroup_of_closure rfl E

/-- The operators which are (up to phase) the identity on the codespace -/
def StabCode.trivialLogicals {n : ℕ} (C : StabCode n) : Subgroup (PauliGroup_group n) :=
  C.stabs ⊔ PauliGroup.phaseSubgroup n

lemma StabCode.trivialLogicals_eq_comap {n : ℕ} (C : StabCode n) :
    C.trivialLogicals
      = Subgroup.comap (PauliGroup.phi n) (C.stabs.map (PauliGroup.phi n)) :=
  (Subgroup.comap_map_eq _ _).symm

lemma StabCode.mem_trivialLogicals_iff {n : ℕ} (C : StabCode n) (E : PauliGroup_group n) :
    E ∈ C.trivialLogicals ↔ ∃ s ∈ C.stabs, Pauli_toBinSympPauli s = Pauli_toBinSympPauli E := by
  rw [StabCode.trivialLogicals_eq_comap, Subgroup.mem_comap, Subgroup.mem_map]
  refine ⟨fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩, fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩⟩
  · simpa using congrArg Multiplicative.toAdd hEq
  · simpa using congrArg Multiplicative.ofAdd hEq

instance StabCode.trivialLogicals_normal {n : ℕ} (C : StabCode n) : C.trivialLogicals.Normal := by
  rw [StabCode.trivialLogicals_eq_comap]
  exact Subgroup.Normal.comap inferInstance _

/- The group of logical operators `N(S) / S` -/
abbrev StabCode.logicalGroup {n : ℕ} (C : StabCode n) : Type :=
  C.normalizerGroup ⧸ C.trivialLogicals.subgroupOf C.normalizerGroup

/-- An error is undetectable when it commutes with every stabilizer yet is not a stabilizer up
to phase, i.e. when it represents a nontrivial class in the logical group. -/
def StabCode.undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : Prop :=
  E ∈ SC.normalizerGroup ∧ E ∉ SC.trivialLogicals ∧ PauliGroup.normalized E

/-- Being undetectable is exactly having a nontrivial class in the logical group (plus the
phase convention `+1`). -/
lemma StabCode.undetectable_iff_class_ne_one {n : ℕ} (C : StabCode n)
    {E : PauliGroup_group n} (hE : E ∈ C.normalizerGroup) :
    C.undetectable E ↔
      (QuotientGroup.mk ⟨E, hE⟩ : C.logicalGroup) ≠ 1 ∧ PauliGroup.normalized E := by
  rw [StabCode.undetectable, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp [hE]

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun E => SC.undetectable E
 := Classical.decPred _

def StabCode.undetectable_set {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {E | SC.undetectable E}

/-- A code is nontrivial when its code space is not the zero space. -/
def StabCode.nontrivial {n : ℕ} (SC : StabCode n) : Prop := SC.space ≠ ⊥

/- TODO(?): Make this talk directly about logicalGroup instead? Would be somewhat cleaner -/
def StabCode.distance {n : ℕ} (SC : StabCode n) : ℕ :=
  match Finset.min (SC.undetectable_set.image pauli_weight) with
  | ⊤ => n + 1
  | some d => d

lemma commute_iff_norm_commute {n : ℕ} (P₁ P₂ : PauliGroup n) : commute P₁ P₂ ↔ commute (normalize_pauli P₁) P₂ := by
  simp [commute, anticommute_iff_normalize_anticommute P₁ P₂]

lemma commute_symm {n : ℕ} (P₁ P₂ : PauliGroup n) : commute P₁ P₂ ↔ commute P₂ P₁ := by
  simp [commute, anticommute_sym]

lemma commute_iff_commute_norm_right {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ commute P₁ (normalize_pauli P₂) := by
  rw [commute_symm, commute_iff_norm_commute, commute_symm]

lemma commute_iff_norm_commute_norm {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ commute (normalize_pauli P₁) (normalize_pauli P₂) := by
  rw [commute_iff_norm_commute, commute_iff_commute_norm_right]

lemma commute_iff_symplecticProd_zero {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ symplecticProd (Pauli_toBinSympPauli P₁) (Pauli_toBinSympPauli P₂) = 0 := by
  rw [commute_iff_norm_commute_norm]
  simpa using
    (BinSympPauli_toPauli_commute_iff_symplecticProd_zero
      (Pauli_toBinSympPauli P₁) (Pauli_toBinSympPauli P₂))

lemma StabCode.mem_normalizerGroup_iff_symplecticProd {n : ℕ} (C : StabCode n)
    (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔
      ∀ s ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli E) = 0 := by
  rw [C.mem_normalizerGroup_iff]
  exact forall₂_congr fun s _ =>
    (commute_iff_symplecticProd_zero E s).trans (by rw [symplecticProd_comm])

/- --restricted undetectable to phase 1, not necessary anymore
theorem StabCode.undetectable_iff_normalized_undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) :
  SC.undetectable E ↔ SC.undetectable (normalize_pauli E) := by
  unfold undetectable
  simp_rw [←mem_normalizer_iff_norm_mem]
-/

def BinSympMatrix.rowSpace {k n : ℕ} (B : BinSympMatrix k n):= Submodule.span (ZMod 2) (Set.range B.row)

lemma BinSympMatrix.mem_rowSpace_iff_exists_indicator {k n : ℕ} (B : BinSympMatrix k n)
    (bsp : BinSympPauli n) :
    bsp ∈ B.rowSpace ↔ ∃ ind : Fin k → ZMod 2,
      (B.X.transpose.mulVec ind, B.Z.transpose.mulVec ind) = bsp := by
  refine' ⟨ _, fun h ↦ _ ⟩;
  · intro h;
    refine' Submodule.span_induction _ _ _ _ h;
    · rintro _ ⟨ i, rfl ⟩ ; use Pi.single i 1; simp +decide [ Matrix.mulVec ] ;
      rfl;
    · exact ⟨ 0, by simp +decide ⟩;
    · rintro x y hx hy ⟨ ind₁, rfl ⟩ ⟨ ind₂, rfl ⟩ ; use ind₁ + ind₂; simp +decide [ Matrix.mulVec_add ] ;
    · rintro a x hx ⟨ ind, rfl ⟩ ; use a • ind; simp +decide [ Matrix.mulVec_smul ] ;
  · obtain ⟨ ind, rfl ⟩ := h;
    convert Submodule.sum_mem _ _ using 1;
    convert BinSympMatrix.selectedRows_sum_eq_mulVec B ind |> Eq.symm;
    intro i hi; split_ifs <;> [ exact Submodule.subset_span ( Set.mem_range_self i ) ; exact Submodule.zero_mem _ ] ;

def BinSympMatrix.undetectable {k n : ℕ} (B : BinSympMatrix k n) (bsp : BinSympPauli n) : Prop :=
  (∀ i, symplecticProd (B.row i) bsp = 0) ∧ bsp ∉ B.rowSpace

noncomputable instance {k n : ℕ} (B : BinSympMatrix k n) : DecidablePred fun E => B.undetectable E
 := Classical.decPred _

def BinSympMatrix.undetectable_set {k n : ℕ} (B : BinSympMatrix k n) : Finset (BinSympPauli n) := {bsp | B.undetectable bsp}

def BinSympMatrix.distance {k n : ℕ} (B : BinSympMatrix k n) (_hk : 0 < k) : ℕ :=
  match Finset.min (B.undetectable_set.image BinSympPauli.weight) with
  | ⊤ => n + 1
  | some d => d

theorem BinSympMatrix.undetectable_set_nonempty {k n : ℕ} (B : BinSympMatrix k n) (hk : 0 < k)
    (h_dist : B.distance hk ≤ n) : B.undetectable_set.Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  unfold BinSympMatrix.distance at h_dist
  rw [h_empty] at h_dist
  simp at h_dist

lemma BinSympMatrix.mem_rowSpace_iff_exists_stab {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm)
    (bsp : BinSympPauli n) :
    bsp ∈ B.rowSpace ↔
      ∃ s ∈ (StabCode_of_BinSympMatrix B h_comm h_minus).stabs, Pauli_toBinSympPauli s = bsp := by
  constructor
  · intro hbsp
    rcases (B.mem_rowSpace_iff_exists_indicator bsp).1 hbsp with ⟨ind, rfl⟩
    exact ⟨B.rowProduct h_comm ind,
      (BinSympCode_stab_eq_rowProduct B h_comm h_minus _).2 ⟨ind, rfl⟩,
      B.rowProduct_binaryImage h_comm ind⟩
  · rintro ⟨s, hs, rfl⟩
    rcases (BinSympCode_stab_eq_rowSpace B h_comm h_minus s).1 hs with ⟨ind, _, hsimg⟩
    exact (B.mem_rowSpace_iff_exists_indicator _).2 ⟨ind, hsimg.symm⟩

lemma BinSympMatrix.mem_normalizerGroup_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (E : PauliGroup n) :
    E ∈ (StabCode_of_BinSympMatrix B h_comm h_minus).normalizerGroup ↔
      ∀ i, symplecticProd (B.row i) (Pauli_toBinSympPauli E) = 0 := by
  rw [StabCode_of_BinSympMatrix, StabCode.mem_normalizerGroup_of_StabSet]
  constructor
  · intro hE i
    have hmem : BinSympPauli_toPauli (B.row i) ∈ (B.toStabSet h_comm).stabs :=
      Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    have := (commute_iff_symplecticProd_zero E _).1 (hE _ hmem)
    simpa [symplecticProd_comm] using this
  · intro hE s hs
    simp only [BinSympMatrix.toStabSet, Finset.mem_image, Finset.mem_univ, true_and] at hs
    obtain ⟨i, rfl⟩ := hs
    exact (commute_iff_symplecticProd_zero E _).2 (by simpa [symplecticProd_comm] using hE i)

lemma BinSympMatrix.stabCode_undetectable_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (E : PauliGroup n) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable E ↔
      B.undetectable (Pauli_toBinSympPauli E) ∧ PauliGroup.normalized E := by
  rw [StabCode.undetectable, BinSympMatrix.undetectable, B.mem_normalizerGroup_iff h_comm h_minus,
    StabCode.mem_trivialLogicals_iff, B.mem_rowSpace_iff_exists_stab h_comm h_minus]
  tauto

lemma BinSympMatrix.stabCode_undetectable_toPauli_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm)
    (bsp : BinSympPauli n) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable (BinSympPauli_toPauli bsp) ↔
      B.undetectable bsp := by
  simpa [BinSympPauli_toPauli_normalized] using
    (B.stabCode_undetectable_iff h_comm h_minus (BinSympPauli_toPauli bsp))

--ultimate theorem linking binSymp representation distance
theorem BinSympMatrix.distance_eq_distance {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting)
    (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm h_minus).distance = B.distance hk := by
  have hweights :
      (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable_set.image pauli_weight =
        B.undetectable_set.image BinSympPauli.weight := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨E, hE, rfl⟩
      have hE' : (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable E := by
        simpa [StabCode.undetectable_set] using hE
      refine Finset.mem_image.2 ⟨Pauli_toBinSympPauli E, ?_, ?_⟩
      · have hbsp := (B.stabCode_undetectable_iff h_comm h_minus E).1 hE'
        simpa [BinSympMatrix.undetectable_set] using hbsp.1
      · exact (pauli_weight_eq_BinSympPauli_weight E).symm
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : B.undetectable bsp := by
        simpa [BinSympMatrix.undetectable_set] using hbsp
      refine Finset.mem_image.2 ⟨BinSympPauli_toPauli bsp, ?_, ?_⟩
      · have hE : (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable (BinSympPauli_toPauli bsp) := by
          simpa [B.stabCode_undetectable_toPauli_iff h_comm h_minus bsp]
            using hbsp'
        simpa [StabCode.undetectable_set] using hE
      · exact pauli_weight_BinSympPauli_toPauli bsp
  unfold StabCode.distance BinSympMatrix.distance
  rw [hweights]
end
