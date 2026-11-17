import Mathlib
import LeanQEC.States.Basic
import LeanQEC.LinearAlgebra.RowspaceKernel
import LeanQEC.Unitary.Paulis.Basic

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000

def stabilizes (U : 𝐔ₙ[n]) (ψ : PState n) := ψ.apply U = ψ

@[simp]
lemma stabilizes_apply (U : 𝐔ₙ[n]) (ψ : PState n) (hstab : stabilizes U ψ) : ψ.apply U = ψ := hstab

@[simp]
lemma stabilizes_apply' {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : Matrix.mulVec U ψ = ψ := by
  simpa only [stabilizes, PState.apply, Matrix.toLin'_apply] using hstab

variable {n₁ n₂ : ℕ}

theorem stab_prod {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} {ψ₁ : PState n₁} {ψ₂ : PState n₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs₂ : stabilizes U₂ ψ₂) :
  stabilizes (U₁ ⊗ₙ U₂) (ψ₁ ⊗ₚ ψ₂) := by
  unfold stabilizes
  rw [kron_mul_kron, hs₁, hs₂]

theorem one_stab_all {n : ℕ} (ψ : PState n) : stabilizes 1 ψ := by simp [stabilizes]

theorem stab_n_prod {n : ℕ} {um : Fin n → 𝐔[Qubit]} {km : Fin n → Qubit → ℂ}
  (hstab : ∀ x, Matrix.mulVec (um x : Matrix Qubit Qubit ℂ) (km x) = km x) :
  stabilizes (Matrix.unitaryPiProd um) (pstate_n_kron km) := by
    unfold stabilizes
    rw [pstate_n_kron_apply]
    simp only [hstab]

theorem inv_stab {n : ℕ} {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : stabilizes U⁻¹ ψ := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
  nth_rw 2 [←(Matrix.one_mulVec ψ)]
  rw [←U.2.1, ←Matrix.mulVec_mulVec, stabilizes_apply' hstab]
  rfl

theorem mul_stab {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]} {ψ : PState n} (hstab₁ : stabilizes U₁ ψ) (hstab₂ : stabilizes U₂ ψ) :
  stabilizes (U₁ * U₂) ψ := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
  rw [show ((U₁ * U₂ : 𝐔ₙ[n]) : Matrix _ _ ℂ) = U₁.val * U₂.val from rfl,
    ←Matrix.mulVec_mulVec, stabilizes_apply' hstab₂, stabilizes_apply' hstab₁]

theorem sum_stab {n : ℕ} {ψ₁ ψ₂ : PState n} {a b : ℂ} {U : 𝐔ₙ[n]}
  (hstab1 : stabilizes U ψ₁) (hstab2 : stabilizes U ψ₂) :
  stabilizes U (a • ψ₁ + b • ψ₂) := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_smul,
    stabilizes_apply' hstab1, stabilizes_apply' hstab2]

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

lemma pphase_Pauli1_left {P : PauliGroup n} : pauli_pauli_phase Pauli1 P = 1 := by
  rw [pauli_pauli_phase]
  have: !anticommute Pauli1 P := commute_1x P
  simp at this
  simp [this]

lemma anticommute_of_anticommute {P₁ P₂ : PauliGroup n} (h_anti : anticommute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = - (P₂ * P₁) := by
  simpa using anticommute_correct_true P₁ P₂ h_anti

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

noncomputable def scalarPauli {n : ℕ} (z : pgroup_phases) : PauliGroup_group n :=
  foldPauli (z, fun _ => Pauli_I)

noncomputable def negIdPauli (n : ℕ) : PauliGroup_group n :=
  scalarPauli pgphase_n1

lemma foldPauli_scalar_sq {n : ℕ} (z : pgroup_phases) :
    (scalarPauli z : PauliGroup_group n) * scalarPauli z = scalarPauli (z * z) := by
  apply Subtype.ext
  change (foldPauli (z, fun _ => Pauli_I)).val * (foldPauli (z, fun _ => Pauli_I)).val =
    (foldPauli (z * z, fun _ => Pauli_I)).val
  rw [← mul_factored_Paulis_correct]
  congr 2
  simp only [mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples_xx, unfolded1, mul_one]

--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?

def commute {n : ℕ} (U₁ U₂ : PauliGroup n) : Prop := ¬ anticommute U₁ U₂

lemma commute_of_commute {n : ℕ} (P₁ P₂ : PauliGroup n) (h_comm : commute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = (P₂ * P₁) := by
  have hfalse : anticommute P₁ P₂ = false := by
    simpa [commute, Bool.not_eq_true] using h_comm
  simpa using anticommute_correct_false P₁ P₂ hfalse

--wait, should i be declaring things in PauliGroup_group then?
lemma commute_iff_commute {n : ℕ} (P₁ P₂ : PauliGroup_group n) : commute P₁ P₂ ↔ P₁ * P₂ = P₂ * P₁ := by
  constructor
  · intro h_comm
    apply Subtype.ext
    exact commute_of_commute P₁ P₂ h_comm
  · intro h_eq
    unfold commute
    by_contra h_anti
    have hsame : ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) = ((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n]) := by
      exact congrArg (fun U : PauliGroup_group n => (U : 𝐔ₙ[n])) h_eq
    have hneg : ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) = - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) :=
      anticommute_of_anticommute h_anti
    have : - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) = (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) := by
      calc
        - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) = ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) := hneg.symm
        _ = (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) := hsame
    exact Matrix.unitaryGroup.neg_ne this

/- A stabilizer code is an abelian subgroup of the n-Pauli group that does not include -I -/
structure StabCode (n : ℕ) where
  stabs : Subgroup (@PauliGroup_group n)
  h_comm : IsMulCommutative stabs
  h_minus : negIdPauli n ∉ stabs

/- The codespace of a stabilizer code is the joint +1 eigenspace of all the elements of the stabilizer group -/
def StabCode.space {n : ℕ} (C : StabCode n) : Submodule ℂ (PState n) where
  carrier := {ψ : PState n | ∀ s ∈ C.stabs, stabilizes (s : 𝐔ₙ[n]) ψ}
  zero_mem' := by
    intro s _
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
    exact Matrix.mulVec_zero _
  add_mem' := by
    intro a b ha hb s hs
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_add,
      stabilizes_apply' (ha s hs), stabilizes_apply' (hb s hs)]
  smul_mem' := by
    intro c a ha s hs
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_smul,
      stabilizes_apply' (ha s hs)]

@[simp]
lemma StabCode.mem_space {n : ℕ} (C : StabCode n) (ψ : PState n) :
    ψ ∈ C.space ↔ ∀ s ∈ C.stabs, stabilizes (s : 𝐔ₙ[n]) ψ := Iff.rfl

/-- Elements of the stabilizer group commute. -/
lemma StabCode.commute_of_mem {n : ℕ} (C : StabCode n) {g h : PauliGroup_group n}
    (hg : g ∈ C.stabs) (hh : h ∈ C.stabs) : g * h = h * g := by
  have := C.h_comm.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩
  simpa using congrArg Subtype.val this

theorem PauliGroup.inv_one {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : PauliGroup.normalized (P⁻¹ : PauliGroup_group n)  := by
  show PauliGroup.phase ⟨(P.1)⁻¹, pauli_inv (by aesop)⟩ = 1
  let FP := foldPauli.symm P
  have: P = foldPauli FP := by aesop
  rw [this]
  simp_rw [<- factored_inv_correct]
  unfold factored_inv
  have hfp1 : FP.1 = 1 := h_norm
  simp only [PauliGroup.phase, Subtype.coe_eta, Equiv.symm_apply_apply, hfp1, _root_.inv_one]

--should be pretty easy to prove
theorem PauliGroup.norm_self_inv {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : P⁻¹ = P := by
  let FP := foldPauli.symm P
  have hP : P = foldPauli FP := by
    aesop
  have hphase : FP.1 = 1 := h_norm
  have hfact : factored_inv FP = FP := by
    rcases FP with ⟨p, m⟩
    change (p⁻¹, m) = (p, m)
    have hp : p = 1 := hphase
    rw [Prod.mk.injEq]
    constructor
    · calc
        p⁻¹ = (1 : pgroup_phases)⁻¹ := by simp [hp]
        _ = 1 := _root_.inv_one
        _ = p := by simp [hp]
    · rfl
  apply Subtype.ext
  rw [hP]
  calc
    (((foldPauli FP : PauliGroup n) : 𝐔ₙ[n])⁻¹) = (foldPauli (factored_inv FP) : 𝐔ₙ[n]) := by
      symm
      simpa using factored_inv_correct FP
    _ = (foldPauli FP : 𝐔ₙ[n]) := by simp [hfact]

structure StabSet (n : ℕ) where
  stabs : Finset (PauliGroup_group n)
  comm : ∀ s₁ ∈ stabs, ∀ s₂ ∈ stabs, commute s₁ s₂

structure NormalizedStabSet (n : ℕ) extends StabSet n where
  norm: ∀ s ∈ stabs, PauliGroup.normalized s

instance : Coe (NormalizedStabSet n) (StabSet n) where
  coe S := S.toStabSet


instance {n : ℕ} {S : StabSet n} : IsMulCommutative (Subgroup.closure (SetLike.coe S.stabs)) := by
  constructor
  constructor
  suffices h : ∀ a b, a ∈ Subgroup.closure (SetLike.coe S.stabs) → b ∈ Subgroup.closure (SetLike.coe S.stabs) → a * b = b * a
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



def StabCode_of_StabSet {n : ℕ} (S : StabSet n)
    (h_minus : negIdPauli n ∉ Subgroup.closure (SetLike.coe S.stabs))
 : StabCode n where
   stabs := Subgroup.closure (SetLike.coe S.stabs)
   h_comm := by infer_instance
   h_minus := h_minus

/-- Membership in the code space only has to be checked on any generating set of the
stabilizer group. -/
lemma StabCode.mem_space_of_closure {n : ℕ} (C : StabCode n)
    {T : Set (PauliGroup_group n)} (hT : Subgroup.closure T = C.stabs) (ψ : PState n) :
    ψ ∈ C.space ↔ ∀ s ∈ T, stabilizes (s : 𝐔ₙ[n]) ψ := by
  constructor
  · intro h s hs
    exact h s (hT ▸ Subgroup.subset_closure hs)
  · intro hs stab stab_mem
    revert stab_mem
    show stab ∈ C.stabs → _
    rw [← hT]
    revert stab
    apply Subgroup.closure_induction --glad this works
    · intros x x_mem
      exact hs x x_mem
    · apply one_stab_all
    · intros x y _ _ xstab ystab
      apply mul_stab xstab ystab
    intros x _ xstab
    apply inv_stab xstab

/- Packaging for generators -/
structure StabCode.Generators {n : ℕ} (C : StabCode n) (m : ℕ) where
  gen : Fin m → PauliGroup_group n
  closure_eq : Subgroup.closure (Set.range gen) = C.stabs

lemma StabCode.Generators.gen_mem {n m : ℕ} {C : StabCode n} (G : C.Generators m) (j : Fin m) :
    G.gen j ∈ C.stabs :=
  G.closure_eq ▸ Subgroup.subset_closure ⟨j, rfl⟩

lemma inv_eq_self_of_mul_self_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1) : g⁻¹ = g := by
  have h := congrArg (fun x => g⁻¹ * x) hg
  simpa [mul_assoc] using h.symm

noncomputable def subgroupCarrierCommGroup {G : Type*} [Group G] (H : Subgroup G)
    [IsMulCommutative ↥H] : CommGroup ↥H where
  toGroup := inferInstance
  mul_comm := by
    intro a b
    let hcomm : Std.Commutative (fun x y : ↥H => x * y) := IsMulCommutative.is_comm (M := ↥H)
    exact hcomm.comm a b

lemma sum_univ_if_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (ind : α → ZMod 2) (f : α → ZMod 2) :
    Finset.univ.sum (fun a => if ind a = 1 then f a else 0) =
      Finset.univ.sum (fun a => f a * ind a) := by
  exact Finset.sum_congr rfl fun x _ => by
    rcases Fin.exists_fin_two.mp ⟨ ind x, rfl ⟩ with h | h;
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num;
      rw [ h ];
      change (if (0 : ZMod 2) = 1 then f x else 0) = f x * (0 : ZMod 2);
      simp [ h01 ];
    · rw [ h ];
      change (if (1 : ZMod 2) = 1 then f x else 0) = f x * (1 : ZMod 2);
      simp;
