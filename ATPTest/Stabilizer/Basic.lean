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


--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?

def commute {n : ℕ} (U₁ U₂ : PauliGroup n) : Prop := ¬ anticommute U₁ U₂

lemma commute_of_commute {n : ℕ} (P₁ P₂ : PauliGroup n) (h_comm : commute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = (P₂ * P₁) := sorry

--wait, should i be declaring things in PauliGroup_group then?
lemma commute_iff_commute {n : ℕ} (P₁ P₂ : PauliGroup_group n) : commute P₁ P₂ ↔ P₁ * P₂ = P₂ * P₁ := sorry

--If i define the codespace as a submodule ℂ (BitVec n → ℂ), it fails the additivity due
--to the normalization condition... so just a set then?
abbrev QCodeSpace (n : ℕ) := Set (PState n)

structure StabCode (n : ℕ) where
  space : QCodeSpace n
  stabs : Subgroup (@PauliGroup_group n)
  --h_comm : CommGroup stabs --DONT SAY THIS
  h_comm : IsMulCommutative stabs --SAY THIS INSTEAD
  hstab₁ : ∀ ψ ∈ space, ∀ S ∈ stabs, stabilizes S ψ
  hstab₂ : ∀ S ∈ stabs, PauliGroup.phase S = pgphase_1
--stab condition of pauli normalization

theorem PauliGroup.phase_mul_of_commutes {n : ℕ} (P₁ P₂ : ↥(PauliGroup_group n)) (hcomm : commute P₁ P₂) :
  PauliGroup.phase (P₁ * P₂) = (PauliGroup.phase P₁) * (PauliGroup.phase P₂) := sorry


theorem PauliGroup.inv_one {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.phase P = pgphase_1)
  : PauliGroup.phase (P⁻¹ : PauliGroup_group n) = pgphase_1 := by
  show PauliGroup.phase ⟨(P.1)⁻¹, pauli_inv (by aesop)⟩ = pgphase_1
  let FP := foldPauli.symm P
  have: P = foldPauli FP := by aesop
  rw [this]
  simp_rw [<- factored_inv_correct]
  unfold factored_inv
  have hfp1 : FP.1 = pgphase_1 := h_norm
  have inv1 : pgroup_phases.inv pgphase_1 = pgphase_1 := by simp [pgroup_phases.inv, Phase.phase_star]
  simp_rw [hfp1, inv1]
  simp [phase]

--should be pretty easy to prove
theorem PauliGroup.norm_self_inv {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.phase P = pgphase_1)
  : P⁻¹ = P := sorry

structure StabSet (n : ℕ) where
  stabs : Finset (PauliGroup_group n)
  comm : ∀ s₁ ∈ stabs, ∀ s₂ ∈ stabs, commute s₁ s₂
  norm : ∀ s ∈ stabs, PauliGroup.phase s = pgphase_1


instance {n : ℕ} {S : StabSet n} : IsMulCommutative (Subgroup.closure S.stabs.toSet) := by
  constructor
  constructor
  suffices h : ∀ a b, a ∈ Subgroup.closure (S.stabs.toSet) → b ∈ Subgroup.closure (S.stabs.toSet) → a * b = b * a
  · intros a b
    have:= h a.1 b.1 a.2 b.2
    rwa [←Subgroup.coe_mul, ←Subgroup.coe_mul, ←Subtype.ext_iff] at this
  apply Subgroup.closure_induction₂
  · intros x y hx hy
    rw [←commute_iff_commute]
    exact S.comm _ hx _ hy
  · simp only [one_mul, mul_one, implies_true]
  · simp only [mul_one, one_mul, implies_true]
  · intros x y z hx hy hz hcomm₁ hcomm₂
    rw [←mul_assoc, ←hcomm₁, mul_assoc x z y, ←hcomm₂, mul_assoc]
  · intros x y z hx hy hz hc₁ hc₂
    rw [←mul_assoc, hc₁, mul_assoc, hc₂, mul_assoc]
  · intros x y hx hy hcomm
    apply Commute.inv_left ((commute_iff_eq _ _).2 hcomm)
  intros x y hx hy hcomm
  apply Commute.inv_right ((commute_iff_eq _ _).2 hcomm)

lemma stab_closure_mul_self_eq_one {n : ℕ} {S : StabSet n} {P : (Subgroup.closure S.stabs.toSet)} : P * P = 1 := sorry

--also don't do this, apparently
/-
instance {n : ℕ} {S : StabSet n} : Monoid (Subgroup.closure S.stabs.toSet) := by
  apply Submonoid.toMonoid

instance {n : ℕ} {S : StabSet n} : CommMonoid (Subgroup.closure S.stabs.toSet) := by
  apply CommMonoid.ofIsMulCommutative
-/


lemma StabSet_closure_phase_one {n : ℕ} (S : StabSet n) : ∀ s ∈ (Subgroup.closure S.stabs.toSet), PauliGroup.phase s = pgphase_1 := by
  apply Subgroup.closure_induction
  · exact S.norm
  · show PauliGroup.phase (Pauli1) = pgphase_1
    rw [Pauli1_unfold, PauliGroup.phase]
    simp only [pgphase_1, phase_id, Equiv.symm_apply_apply]
  · intros x y hx hy hpx hpy
    rw [PauliGroup.phase_mul_of_commutes, hpx, hpy]
    · simp only [pgphase_1, phase_id, pgp_mul_eq, Phase.phase_mul_eq, mul_one]
    rw [commute_iff_commute]
    have hxy:= (Subgroup.closureCommGroupOfComm ?_).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    · simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] at hxy
      exact hxy
    exact fun x hx y hy => (commute_iff_commute _ _).1 (S.comm x hx y hy)
  intros x hx hp
  apply PauliGroup.inv_one x hp

--the way this is defined, the commutativity of the stabilizer isn't necessary
--how to square this?
def StabCode_of_StabSet {n : ℕ} (S : StabSet n)
 : StabCode n where
   space := {ψ | ∀ s ∈ S.stabs, stabilizes s ψ}
   stabs := Subgroup.closure S.stabs.toSet
   h_comm := by infer_instance
   hstab₁ := by
    intros ψ hs stab stab_mem
    revert stab_mem stab
    apply Subgroup.closure_induction --glad this works
    · intros x x_mem
      apply hs
      exact x_mem
    · apply one_stab_all
    · intros x y _ _ xstab ystab
      apply mul_stab xstab ystab
    intros x _ xstab
    apply inv_stab xstab
   hstab₂ := StabSet_closure_phase_one _



def isStabSet {n : ℕ} (C : StabCode n) (S : StabSet n) : Prop := (Subgroup.closure S.stabs.toSet) = C.stabs

def StabSet_isCommuting {n : ℕ} (S : Finset (PauliGroup n)) : Prop := ∀ s₁ ∈ S, ∀ s₂ ∈ S, commute s₁ s₂

def to_closure_map {n : ℕ} {S : Set (PauliGroup_group n)}
  (x : (PauliGroup_group n)) (hx : x ∈ S) : ↥(Subgroup.closure S) := ⟨x, Subgroup.subset_closure hx⟩

noncomputable def finset_subset_to_closure_map {n : ℕ} {S₁ S₂ : Finset (PauliGroup_group n)}
  (hsub : S₁ ⊆ S₂) : Finset ↥(Subgroup.closure S₂.toSet) := S₁.attach.image (fun x => to_closure_map x.1 (hsub x.2))

@[simp]
lemma Finset.attach_singleton {α : Type*} (x : α) : Finset.attach {x} = {⟨x, Finset.mem_singleton_self _⟩} := by
  apply subset_antisymm
  · intros x' x'_mem
    rw [Finset.mem_singleton]
    have hcard : (Finset.attach {x}).card ≤ 1
    · apply le_of_eq
      rw [Finset.card_attach, Finset.card_singleton]
    rw [Finset.card_le_one] at hcard
    apply hcard
    · exact x'_mem
    simp only [mem_attach]
  simp only [singleton_subset_iff, mem_attach]

lemma sdiff_decomp {α : Type*} [DecidableEq α] (x y : Finset α) : x = Finset.disjUnion _ _ (Finset.disjoint_sdiff_inter x y) := by
  rw [Finset.disjUnion_eq_union]
  apply subset_antisymm
  · intros a hax
    by_cases hay : a ∈ y
    · apply Finset.mem_union_right _ (Finset.mem_inter_of_mem hax hay)
    apply Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hax, hay⟩)
  intros a ha
  rcases (Finset.mem_union.1 ha) with (ha₁ | ha₂)
  · exact (Finset.mem_sdiff.1 ha₁).1
  exact (Finset.mem_inter.1 ha₂).1


lemma finset_subset_to_closure_map_union {n : ℕ} (S : StabSet n) {F A B : Finset (PauliGroup_group n)}
  (hF : F ⊆ S.stabs) {hdisj : Disjoint A B} (hF_eq : F = Finset.disjUnion _ _ hdisj) : (finset_subset_to_closure_map hF) = (@finset_subset_to_closure_map n A S.stabs (by
    apply subset_trans _ hF
    rw [hF_eq]
    exact fun a ha => Finset.mem_disjUnion.2 (Or.inl ha)
  )) ∪ (@finset_subset_to_closure_map n B S.stabs (by
    apply subset_trans _ hF
    rw [hF_eq]
    exact fun b hb => Finset.mem_disjUnion.2 (Or.inr hb) --oh god this is terrible
  )) := by
    apply subset_antisymm
    · unfold finset_subset_to_closure_map
      intro f f_mem
      rcases (Finset.mem_image.1 f_mem) with ⟨f', hf'⟩
      have hf'_mem : ↑f' ∈ F := by simp only [Finset.coe_mem]
      simp_rw [hF_eq, Finset.mem_disjUnion] at hf'_mem
      rcases hf'_mem with (hf'_a | hf'_b)
      · apply Finset.mem_union_left
        rw [Finset.mem_image]
        refine ⟨⟨↑f', hf'_a⟩, ⟨by simp, ?_⟩⟩
        rw [←hf'.2]
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨⟨↑f', hf'_b⟩, ⟨by simp, ?_⟩⟩
      rw [←hf'.2]
    unfold finset_subset_to_closure_map
    intro f f_mem
    rw [Finset.mem_image]
    rcases (Finset.mem_union.1 f_mem) with (hfa | hfb)
    · rcases (Finset.mem_image.1 hfa) with ⟨f', hf'⟩
      refine ⟨⟨↑f', ?_⟩, ?_⟩
      · rw [hF_eq, Finset.mem_disjUnion]
        exact Or.inl (by simp)
      rw [←hf'.2]
      simp
    rcases (Finset.mem_image.1 hfb) with ⟨f', hf'⟩
    refine ⟨⟨↑f', ?_⟩, ?_⟩
    · rw [hF_eq, Finset.mem_disjUnion]
      exact Or.inr (by simp)
    rw [←hf'.2]
    simp

theorem list_map_union_of_is_comm {G : Type*} [Group G] {H : Subgroup G} [IsMulCommutative H] {A B : Finset H}
  (hd : Disjoint A B) : (Finset.disjUnion A B hd).toList.prod = A.toList.prod * B.toList.prod := sorry

 --instructive example: delete later. Don't redefine group structure for a subgroup and you will end up
   --with two different multiplications and lose your mind, use IsMulCommutative instead
theorem lets_break_closure_induction {G : Type*} [Group G] (H : Subgroup G) {F : Set H} (s : H) [IsMulCommutative (Subgroup.closure F)]:
  s ∈ Subgroup.closure F → ∃ t : Subgroup.closure F, t = s := by
  revert s
  apply Subgroup.closure_induction
  · sorry
  · sorry
  · rintro x y x_mem y_mem ⟨tx, htx⟩ ⟨ty, hty⟩
    rw [←htx, ←hty, ←Subgroup.coe_mul]
    use ty * tx
    congr 1
    rw [IsMulCommutative.is_comm.comm]
  sorry


--can't use Finset.prod anymore, since ambient group is noncommutative...
theorem mem_stab_iff_prod_subset_stabSet {n : ℕ} (S : StabSet n) (s :  PauliGroup_group n) :
  s ∈ (StabCode_of_StabSet S).stabs ↔ ∃ F, ∃ h : F ⊆ S.stabs, (List.prod (finset_subset_to_closure_map h).toList : (Subgroup.closure S.stabs.toSet)).1 = s := by
  constructor
  · revert s
    unfold StabCode_of_StabSet
    simp only
    apply Subgroup.closure_induction
    · intros x x_mem
      refine ⟨{x}, ⟨Finset.singleton_subset_iff.2 x_mem, ?_⟩⟩
      unfold finset_subset_to_closure_map to_closure_map
      simp only [Finset.attach_singleton, Finset.image_singleton, Finset.toList_singleton, List.prod]
      unfold List.foldr List.foldr
      have hx : x = ↑(⟨x, Subgroup.mem_closure_of_mem x_mem⟩ : (Subgroup.closure S.stabs.toSet))
      · rfl
      rw [Subgroup.coe_mul, ←hx, Subgroup.coe_one, mul_one]
    · refine ⟨∅, ⟨Finset.empty_subset _, ?_⟩⟩
      unfold finset_subset_to_closure_map to_closure_map
      simp
    · rintro x y x_mem y_mem ⟨fx, hfx₁, hfx₂⟩ ⟨fy, hfy₁, hfy₂⟩
      let F := symmDiff fx fy
      refine ⟨F, ⟨subset_trans Finset.symmDiff_subset_union ?_, ?_⟩⟩
      · apply Finset.union_subset hfx₁ hfy₁
      --hard case

      rw [←hfx₂, ←hfy₂, ←Subgroup.coe_mul] --the culprit!
      --congr --maybe don't congr so we can move back to the ambient group for associativity?
      --rw [IsMulCommutative.is_comm.comm] works, but how do i do like, associativity?
      --lean no longer recognizes any group structure on ↥(Subgroup.closure ↑S.stabs)
      --despite the fact that an instance declares it a CommGroup earlier and also its
      --literally a closure

      have sd1:= sdiff_decomp fx fy
      have sd2:= sdiff_decomp fy fx
      simp_rw [Finset.disjUnion_comm _ (fy ∩ fx), Finset.inter_comm fy fx] at sd2
      rw [finset_subset_to_closure_map_union S hfx₁ sd1]
      rw [finset_subset_to_closure_map_union S hfy₁ sd2]
      nth_rw 3 [←Finset.disjUnion_eq_union _ _ sorry]
      nth_rw 2 [←Finset.disjUnion_eq_union _ _ sorry]
      rw [list_map_union_of_is_comm, list_map_union_of_is_comm]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc]
      rw [Subgroup.coe_mul]
      nth_rw 2 [←mul_assoc] --canceling prods now next to each other
      rw [←Subgroup.coe_mul, stab_closure_mul_self_eq_one, Subgroup.coe_one, one_mul]
      have hf : F = Finset.disjUnion (fx \ fy) (fy \ fx) (disjoint_sdiff_sdiff) := by
        unfold F symmDiff
        rw [Finset.disjUnion_eq_union]
        rfl
      simp only [hf]
      rw [finset_subset_to_closure_map_union S sorry sorry]
      rw [←Finset.disjUnion_eq_union _ _ sorry, list_map_union_of_is_comm]
      · rfl
      exact disjoint_sdiff_sdiff
    rintro x x_mem hx
    rw [PauliGroup.norm_self_inv]
    · assumption
    apply StabSet_closure_phase_one S x x_mem
  rintro ⟨F, hF₁, rfl⟩
  unfold StabCode_of_StabSet finset_subset_to_closure_map to_closure_map
  have h_mem : ∀ {x : ↥(Subgroup.closure S.stabs.toSet)}, (x : ↥(PauliGroup_group n)) ∈ (Subgroup.closure S.stabs.toSet)
  · aesop --???
  exact h_mem



--define binary symplectic representation, yielding Finset of PauliGroup n from matrix

def BinSympPauli (n : ℕ) := (Fin n → (ZMod 2)) × (Fin n → (ZMod 2))

def symplecticProd {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : (ZMod 2) :=
  dotProduct bp₁.1 bp₂.2 + dotProduct bp₁.2 bp₂.1

def BinSympPauli_add {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : BinSympPauli n := (bp₁.1 + bp₂.1, bp₁.2 + bp₂.2)

noncomputable section

def Z2Z2_Pauli_equiv : ((ZMod 2) × (ZMod 2)) ≃ Pauli where
  toFun := fun
  | (0, 0) => Pauli_I
  | (1, 0) => Pauli_X
  | (0, 1) => Pauli_Z
  | (1, 1) => Pauli_Y
  invFun := fun P => --this sucks. This is what i get for not defining paulis as a type
   if h : P = Pauli_I then (0, 0) else
  if h2 : P = Pauli_X then (1, 0) else
  if h3 : P = Pauli_Z then (0, 1) else (1, 1)
  left_inv := by
    intro x
    fin_cases x <;> simp
  right_inv := by
    intro x
    rcases Pauli_cases x with h | h | h | h <;> simp [h]

def BinSympPauli_toPauli {n : ℕ} (bs : BinSympPauli n) : PauliGroup n :=
  let pm := fun n => Z2Z2_Pauli_equiv (bs.1 n, bs.2 n)
  foldPauli (pgphase_1, pm)



structure BinSympMatrix (k n : ℕ) where
  X : Matrix (Fin k) (Fin n) (ZMod 2)
  Z : Matrix (Fin k) (Fin n) (ZMod 2)

def BinSympMatrix.row {n k : ℕ} (bsm : BinSympMatrix k n) (r : Fin k) : BinSympPauli n :=
  (bsm.X r, bsm.Z r)

def BinSympMatrix.rowProd {n k : ℕ} (bsm : BinSympMatrix k n) (r₁ r₂ : Fin k) : (ZMod 2) :=
  symplecticProd (bsm.row r₁) (bsm.row r₂)

def BinSympMatrix.isCommuting {n k : ℕ} (bsm : BinSympMatrix k n) : Prop :=
  ∀ r₁ r₂, bsm.rowProd r₁ r₂ = 0

def BinSympMatrix.toStabSet {n k : ℕ} (bsm : BinSympMatrix k n) : Finset (PauliGroup n) :=
  Finset.image (fun i => BinSympPauli_toPauli (bsm.row i)) Finset.univ



theorem binSympAdd_eq_mul {n : ℕ} {bp₁ bp₂ : BinSympPauli n} :
  BinSympPauli_toPauli (BinSympPauli_add bp₁ bp₂) = ((BinSympPauli_toPauli bp₁) : 𝐔ₙ[n]) * (BinSympPauli_toPauli bp₂) := sorry

theorem commutes_of_sympProd_zero {n : ℕ} {bp₁ bp₂ : BinSympPauli n}
  (h_prod : symplecticProd bp₁ bp₂ = 0) : commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) := by
  sorry

def StabCode_of_BinSympMatrix {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) : StabCode n :=
  StabCode_of_StabSet bsm.toStabSet (by
  unfold BinSympMatrix.toStabSet
  simp_rw [Finset.mem_image]
  rintro s₁ ⟨r₁, ⟨_, rfl⟩⟩ s₂ ⟨r₂, ⟨_, rfl⟩⟩
  apply commutes_of_sympProd_zero (h_comm _ _)
  ) (by
  unfold BinSympMatrix.toStabSet BinSympPauli_toPauli
  simp_rw [Finset.mem_image]
  rintro s ⟨r₁, ⟨_, rfl⟩⟩
  unfold PauliGroup.phase
  simp only [Equiv.symm_apply_apply]
  )

--should depend on theorem linking members of closure
theorem BinSympCode_stab_eq_rowSpace {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (s : ↥(PauliGroup_group n)) :
  s ∈ (StabCode_of_BinSympMatrix bsm h_comm).stabs ↔ ∃ x z, BinSympPauli_toPauli (bsm.X.transpose.mulVec x, bsm.Z.transpose.mulVec z) = s := by
  unfold StabCode_of_BinSympMatrix BinSympMatrix.toStabSet StabCode_of_StabSet
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  sorry

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun N => ∀ s ∈ SC.stabs, commute N s
 := Classical.decPred _

def StabCode.normalizer {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {N | ∀ s ∈ SC.stabs, commute N s}

def StabCode.undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : Prop := E ∈ SC.normalizer ∧ normalize_pauli E ∉ SC.stabs

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun E => SC.undetectable E
 := Classical.decPred _

def StabCode.undetectable_set {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {E | SC.undetectable E}

def StabCode.nontrivial {n : ℕ} (SC : StabCode n) : Prop := ∃ ψ₁ ∈ SC.space, ∃ ψ₂ ∈ SC.space, ψ₁ ≠ ψ₂

--wait, why is this true again? If there are at least two code words, then the pauli error that maps one to another is undetectable
theorem StabCode.undetectable_set_nonempty {n : ℕ} (SC : StabCode n) (hnt : SC.nontrivial) : SC.undetectable_set.Nonempty := sorry

def StabCode.distance {n : ℕ} (SC : StabCode n) (hnt : SC.nontrivial) : ℕ := Finset.min' (Finset.image (fun E => pauli_weight E) (SC.undetectable_set)) (by
rw [Finset.image_nonempty]
exact StabCode.undetectable_set_nonempty SC hnt
)

lemma commute_iff_norm_commute {n : ℕ} (P₁ P₂ : PauliGroup n) : commute P₁ P₂ ↔ commute (normalize_pauli P₁) P₂ := by
  simp [commute, anticommute_iff_normalize_anticommute P₁ P₂]

lemma mem_normalizer_iff_norm_mem {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : E ∈ SC.normalizer ↔ normalize_pauli E ∈ SC.normalizer := by
  unfold StabCode.normalizer
  simp_rw [Finset.mem_filter_univ, ←commute_iff_norm_commute]


theorem StabCode.undetectable_iff_normalized_undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) :
  SC.undetectable E ↔ SC.undetectable (normalize_pauli E) := by
  unfold undetectable
  simp_rw [←mem_normalizer_iff_norm_mem, normalize_pauli_idem]




end

--TODO:

--can i just define the code size as n - number of stabilizer generators? This requires

--theory of code size: how to do this without subspace rep due to pstate normalization condition?

--order of stabilizer subgroup?

--reduce to phase 1 case: lemma that says an undetectable error is still undetectable if phase is set
--to 1

--theory of codespace distance

--relate codespace distance to matrix vector multiplication of binsymp representation


/-
variable (n : ℕ) (k : ℕ)

def QCode := PState k → PState n

noncomputable section

variable {n : ℕ} {k : ℕ}

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
-/

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

--can probably safely forget about all this
/-
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
-/
