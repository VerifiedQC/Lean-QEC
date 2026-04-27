import LeanQEC.States.Basic
import LeanQEC.Stabilizer.LinAlg
import LeanQEC.Unitary.Paulis.Basic
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

--If i define the codespace as a submodule ℂ (BitVec n → ℂ), it fails the additivity due
--to the normalization condition... so just a set then?
abbrev QCodeSpace (n : ℕ) := Set (PState n)

structure StabCode (n : ℕ) where
  space : QCodeSpace n
  stabs : Subgroup (@PauliGroup_group n)
  h_comm : IsMulCommutative stabs
  hstab : ∀ ψ ∈ space, ∀ S ∈ stabs, stabilizes S ψ


theorem PauliGroup.inv_one {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : PauliGroup.normalized (P⁻¹ : PauliGroup_group n)  := by
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
theorem PauliGroup.norm_self_inv {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : P⁻¹ = P := by
  let FP := foldPauli.symm P
  have hP : P = foldPauli FP := by
    aesop
  have hphase : FP.1 = pgphase_1 := h_norm
  have hfact : factored_inv FP = FP := by
    rcases FP with ⟨p, m⟩
    change (pgroup_phases.inv p, m) = (p, m)
    have hp : p = pgphase_1 := hphase
    rw [Prod.mk.injEq]
    constructor
    · calc
        pgroup_phases.inv p = pgroup_phases.inv pgphase_1 := by simp [hp]
        _ = pgphase_1 := by simp [pgroup_phases.inv, Phase.phase_star]
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
 : StabCode n where
   space := {ψ | ∀ s ∈ S.stabs, stabilizes s ψ}
   stabs := Subgroup.closure (SetLike.coe S.stabs)
   h_comm := by infer_instance
   hstab := by
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


--unused
def isStabSet {n : ℕ} (C : StabCode n) (S : StabSet n) : Prop := (Subgroup.closure (SetLike.coe S.stabs)) = C.stabs

def StabSet_isCommuting {n : ℕ} (S : Finset (PauliGroup n)) : Prop := ∀ s₁ ∈ S, ∀ s₂ ∈ S, commute s₁ s₂

lemma inv_eq_self_of_mul_self_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1) : g⁻¹ = g := by
  have h := congrArg (fun x => g⁻¹ * x) hg
  simpa [mul_assoc] using h.symm

noncomputable def subgroupCarrierCommGroup {G : Type*} [Group G] (H : Subgroup G)
    [IsMulCommutative ↥H] : CommGroup ↥H where
  __ := inferInstanceAs (Group ↥H)
  mul_comm := by
    intro a b
    let hcomm : Std.Commutative (fun x y : ↥H => x * y) := IsMulCommutative.is_comm (M := ↥H)
    exact hcomm.comm a b

lemma sum_univ_if_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (ind : α → ZMod 2) (f : α → ZMod 2) :
    Finset.univ.sum (fun a => if ind a = 1 then f a else 0) =
      Finset.univ.sum (fun a => f a * ind a) := by
  refine Finset.sum_congr rfl ?_
  intro a ha
  rcases Fin.exists_fin_two.mp ⟨ind a, rfl⟩ with h | h <;> simp [h]






--define binary symplectic representation, yielding Finset of PauliGroup n from matrix

abbrev BinSympPauli (n : ℕ) := (Fin n → (ZMod 2)) × (Fin n → (ZMod 2))

--don't actually need these, right?
def ZMod2_or (a b : ZMod 2) := a + b + (a * b)

def union_weight (v₁ v₂ : Fin n → (ZMod 2)) : ℕ := hammingNorm (fun i => ZMod2_or (v₁ i) (v₂ i))

def BinSympPauli.weight {n : ℕ} (bsp : BinSympPauli n) : ℕ := union_weight bsp.1 bsp.2

@[simp]
lemma union_weight_zero_left (v : Fin n → ZMod 2) : union_weight 0 v = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

@[simp]
lemma union_weight_zero_right (v : Fin n → ZMod 2) : union_weight v 0 = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

def symplecticProd {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : (ZMod 2) :=
  dotProduct bp₁.1 bp₂.2 + dotProduct bp₁.2 bp₂.1

--don't need this, we get comm group structure for free!
--def BinSympPauli_add {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : BinSympPauli n := (bp₁.1 + bp₂.1, bp₁.2 + bp₂.2)

--wait, can't do this because Prod.fst isn't injective..
--lemma BinSympPauli_sum_eq (F : Finset (BinSympPauli n)) : Finset.sum F id = ((Finset.sum (F.map Prod.fst) id), (Finset.sum (F.map Prod.snd) id)) := by

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

lemma ZMod2_or_eq_zero_iff (a b : ZMod 2) :
    ZMod2_or a b = 0 ↔ a = 0 ∧ b = 0 := by
  fin_cases a <;> fin_cases b <;> simp [ZMod2_or] ; native_decide

lemma Z2Z2_Pauli_equiv_ne_I_iff (a b : ZMod 2) :
    Z2Z2_Pauli_equiv (a, b) ≠ Pauli_I ↔ ZMod2_or a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [Z2Z2_Pauli_equiv, ZMod2_or] ; native_decide

def BinSympPauli_toPauli {n : ℕ} (bs : BinSympPauli n) : ↥(PauliGroup_group n) :=
  let pm := fun n => Z2Z2_Pauli_equiv (bs.1 n, bs.2 n)
  foldPauli (pgphase_1, pm)

def Pauli_toBinSympPauli {n : ℕ} (P : ↥(PauliGroup_group n)) : BinSympPauli n :=
  let pm := fun n => Z2Z2_Pauli_equiv.symm (PauliGroup.map P n)
  ⟨fun n => (pm n).1, fun n => (pm n).2⟩

--three big linking theorems, rest is mostly extremely painful proof massaging

lemma Bool.ofNat_ZMod2_add (x y : ZMod 2) :
    Bool.xor (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x + y).val) := by
  fin_cases x <;> fin_cases y <;> decide

lemma local_mul_Pauli_toBinSymp (P Q : Pauli) :
    Z2Z2_Pauli_equiv.symm (mul_Pauli1 P Q).2 =
      Z2Z2_Pauli_equiv.symm P + Z2Z2_Pauli_equiv.symm Q := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [mul_Pauli1, Z2Z2_Pauli_equiv] <;> native_decide

lemma local_anticommute_eq_sympProd (P Q : Pauli) :
    (!commute₁ P Q) =
      Bool.ofNat
        (((Z2Z2_Pauli_equiv.symm P).1 * (Z2Z2_Pauli_equiv.symm Q).2) +
          ((Z2Z2_Pauli_equiv.symm P).2 * (Z2Z2_Pauli_equiv.symm Q).1)).val := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [commute₁, Z2Z2_Pauli_equiv, Bool.ofNat] ; native_decide

lemma local_anticommute_xor_tail (a b c d t : ZMod 2) :
    (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)) ^^ Bool.ofNat t.val) =
      Bool.ofNat (((a * d + b * c) + t).val) := by
  have hhead :
      (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d))) =
        Bool.ofNat ((a * d + b * c).val) := by
    simpa using
      (local_anticommute_eq_sympProd (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)))
  rw [hhead, Bool.ofNat_ZMod2_add]

@[simp]
lemma BinSympPauli_toPauli_zero {n : ℕ} : BinSympPauli_toPauli (0 : BinSympPauli n) = 1 := by
  change foldPauli (pgphase_1, fun _ : Fin n => Pauli_I) = Pauli1
  simpa using Pauli1_unfold.symm

lemma BinSympPauli_toPauli_normalized {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.normalized (BinSympPauli_toPauli bp) := by
  unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
  simp [Equiv.symm_apply_apply]

@[simp]
lemma Pauli_toBinSympPauli_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    Pauli_toBinSympPauli (BinSympPauli_toPauli bp) = bp := by
  ext i <;> simp [Pauli_toBinSympPauli, BinSympPauli_toPauli, PauliGroup.map]

@[simp]
lemma Pauli_toBinSympPauli_normalize_pauli {n : ℕ} (P : PauliGroup n) :
    Pauli_toBinSympPauli (normalize_pauli P) = Pauli_toBinSympPauli P := by
  ext i <;> simp [Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

@[simp]
lemma BinSympPauli_toPauli_Pauli_toBinSympPauli {n : ℕ} (P : PauliGroup n) :
    BinSympPauli_toPauli (Pauli_toBinSympPauli P) = normalize_pauli P := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli, Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

lemma PauliGroup.map_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.map (BinSympPauli_toPauli bp) = fun i => Z2Z2_Pauli_equiv (bp.1 i, bp.2 i) := by
  funext i
  have hx := congrArg (fun bp' => bp'.1 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hz := congrArg (fun bp' => bp'.2 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hpair : Z2Z2_Pauli_equiv.symm (PauliGroup.map (BinSympPauli_toPauli bp) i) = (bp.1 i, bp.2 i) := by
    exact Prod.ext hx hz
  have := congrArg Z2Z2_Pauli_equiv hpair
  simpa using this

@[simp]
lemma Pauli_toBinSympPauli_one {n : ℕ} :
    Pauli_toBinSympPauli (1 : PauliGroup_group n) = 0 := by
  simpa [BinSympPauli_toPauli_zero] using
    (Pauli_toBinSympPauli_BinSympPauli_toPauli (0 : BinSympPauli n))

lemma pauli_weight_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    pauli_weight (BinSympPauli_toPauli bp) = BinSympPauli.weight bp := by
  unfold pauli_weight BinSympPauli.weight union_weight hammingNorm
  congr
  ext i
  simp [PauliGroup.map_BinSympPauli_toPauli, Z2Z2_Pauli_equiv_ne_I_iff]

lemma pauli_weight_eq_BinSympPauli_weight {n : ℕ} (P : PauliGroup n) :
    pauli_weight P = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
  calc
    pauli_weight P = pauli_weight (normalize_pauli P) := by
      unfold pauli_weight
      rw [show PauliGroup.map (normalize_pauli P) = PauliGroup.map P from
        (normalize_pauli_map_eq P).symm]
    _ = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
      rw [← BinSympPauli_toPauli_Pauli_toBinSympPauli P]
      exact pauli_weight_BinSympPauli_toPauli (Pauli_toBinSympPauli P)

theorem Pauli_to_BinSymp_correct {n : ℕ} (P₁ P₂ : PauliGroup_group n) :
    Pauli_toBinSympPauli (P₁ * P₂) = (Pauli_toBinSympPauli P₁) + (Pauli_toBinSympPauli P₂) := by
  let FP₁ := foldPauli.symm P₁
  let FP₂ := foldPauli.symm P₂
  have hmul : foldPauli.symm (P₁ * P₂ : PauliGroup_group n) = mul_factored_Paulis FP₁ FP₂ := by
    apply foldPauli.injective
    apply Subtype.ext
    simpa [FP₁, FP₂] using (mul_factored_Paulis_correct FP₁ FP₂).symm
  ext i
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).1 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).1 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.fst (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).2 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).2 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.snd (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))

lemma symplecticProd_succ {n : ℕ} (bp₁ bp₂ : BinSympPauli (n + 1)) :
    symplecticProd bp₁ bp₂ =
      ((bp₁.1 0) * (bp₂.2 0) + (bp₁.2 0) * (bp₂.1 0)) +
        symplecticProd (Fin.tail bp₁.1, Fin.tail bp₁.2) (Fin.tail bp₂.1, Fin.tail bp₂.2) := by
  unfold symplecticProd dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.tail]
  abel_nf

lemma anticommute_eq_symplecticBool {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    anticommute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) =
      Bool.ofNat (symplecticProd bp₁ bp₂).val := by
  induction n with
  | zero =>
      simp [anticommute, anticommuteₘ, symplecticProd, dotProduct]
  | succ n ih =>
      rcases bp₁ with ⟨x₁, z₁⟩
      rcases bp₂ with ⟨x₂, z₂⟩
      have hmap₁ : PauliGroup.map (BinSympPauli_toPauli (x₁, z₁)) = fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₁, z₁)
      have hmap₂ : PauliGroup.map (BinSympPauli_toPauli (x₂, z₂)) = fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₂, z₂)
      have htail₁ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i) := by
        funext i
        simp [Fin.tail]
      have htail₂ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i) := by
        funext i
        simp [Fin.tail]
      rw [anticommute, hmap₁, hmap₂, anticommuteₘ, htail₁, htail₂]
      have htail :=
        ih (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)
      rw [show
          anticommuteₘ (fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i))
              (fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i)) =
            anticommute (BinSympPauli_toPauli (Fin.tail x₁, Fin.tail z₁))
              (BinSympPauli_toPauli (Fin.tail x₂, Fin.tail z₂)) by
              rw [anticommute, PauliGroup.map_BinSympPauli_toPauli, PauliGroup.map_BinSympPauli_toPauli],
        htail]
      simpa [symplecticProd_succ] using
        (local_anticommute_xor_tail
          (x₁ 0) (z₁ 0) (x₂ 0) (z₂ 0)
          (symplecticProd (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)))

lemma symplecticProd_comm {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    symplecticProd bp₁ bp₂ = symplecticProd bp₂ bp₁ := by
  unfold symplecticProd
  rw [show bp₁.2 ⬝ᵥ bp₂.1 = bp₂.1 ⬝ᵥ bp₁.2 by simpa using dotProduct_comm bp₁.2 bp₂.1]
  rw [show bp₁.1 ⬝ᵥ bp₂.2 = bp₂.2 ⬝ᵥ bp₁.1 by simpa using dotProduct_comm bp₁.1 bp₂.2]
  rw [add_comm]

lemma BinSympPauli_toPauli_commute_iff_symplecticProd_zero {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) ↔
      symplecticProd bp₁ bp₂ = 0 := by
  unfold commute
  rw [anticommute_eq_symplecticBool]
  rcases Fin.exists_fin_two.mp ⟨symplecticProd bp₁ bp₂, rfl⟩ with h | h
  · simp [h]
  · simp [h, Bool.ofNat]

theorem commutes_of_sympProd_zero {n : ℕ} {bp₁ bp₂ : BinSympPauli n}
    (h_prod : symplecticProd bp₁ bp₂ = 0) : commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) := by
  exact (BinSympPauli_toPauli_commute_iff_symplecticProd_zero _ _).2 h_prod


structure BinSympMatrix (k n : ℕ) where
  X : Matrix (Fin k) (Fin n) (ZMod 2)
  Z : Matrix (Fin k) (Fin n) (ZMod 2)

def BinSympMatrix.row {n k : ℕ} (bsm : BinSympMatrix k n) (r : Fin k) : BinSympPauli n :=
  (bsm.X r, bsm.Z r)

def BinSympMatrix.rowProd {n k : ℕ} (bsm : BinSympMatrix k n) (r₁ r₂ : Fin k) : (ZMod 2) :=
  symplecticProd (bsm.row r₁) (bsm.row r₂)

def BinSympMatrix.isCommuting {n k : ℕ} (bsm : BinSympMatrix k n) : Prop :=
  ∀ r₁ r₂, bsm.rowProd r₁ r₂ = 0

def BinSympMatrix.toStabSet {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) : NormalizedStabSet n where
  stabs := Finset.image (fun i => BinSympPauli_toPauli (bsm.row i)) Finset.univ
  comm := by
    simp_rw [Finset.mem_image]
    rintro s₁ ⟨r₁, ⟨_, rfl⟩⟩ s₂ ⟨r₂, ⟨_, rfl⟩⟩
    apply commutes_of_sympProd_zero (h_comm _ _)
  norm := by
    simp_rw [Finset.mem_image]
    rintro s ⟨r₁, ⟨_, rfl⟩⟩
    unfold PauliGroup.normalized PauliGroup.phase
    simp only [BinSympPauli_toPauli, Equiv.symm_apply_apply]

def StabCode_of_BinSympMatrix {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) : StabCode n :=
  StabCode_of_StabSet (bsm.toStabSet h_comm)

abbrev BinSympMatrix.stabClosure {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    Subgroup ↥(PauliGroup_group n) :=
  Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs)

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative (bsm.stabClosure h_comm) := by
  change IsMulCommutative (Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs))
  infer_instance

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative ↥(bsm.stabClosure h_comm) := by
  infer_instance

lemma BinSympPauli_toPauli_mul_self_eq_one {n : ℕ} (bp : BinSympPauli n) :
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp = 1 := by
  have hnorm : PauliGroup.normalized (BinSympPauli_toPauli bp) := by
    unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
    simp
  have hself : (BinSympPauli_toPauli bp : PauliGroup_group n)⁻¹ = BinSympPauli_toPauli bp :=
    PauliGroup.norm_self_inv _ hnorm
  calc
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp =
        BinSympPauli_toPauli bp * (BinSympPauli_toPauli bp)⁻¹ := by rw [hself]
    _ = 1 := by simp

def BinSympMatrix.rowStabElem {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ↥(bsm.stabClosure h_comm) :=
  ⟨BinSympPauli_toPauli (bsm.row i), by
    classical
    unfold BinSympMatrix.stabClosure BinSympMatrix.toStabSet
    apply Subgroup.subset_closure
    exact
      (Finset.mem_image.2
        ⟨i, Finset.mem_univ i, rfl⟩ :
          BinSympPauli_toPauli (bsm.row i) ∈
            Finset.image (fun j : Fin k => BinSympPauli_toPauli (bsm.row j)) Finset.univ)⟩

@[simp]
lemma BinSympMatrix.rowStabElem_coe {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ((bsm.rowStabElem h_comm i : bsm.stabClosure h_comm) : ↥(PauliGroup_group n)) =
      BinSympPauli_toPauli (bsm.row i) := rfl

@[simp]
lemma BinSympMatrix.rowStabElem_mul_self_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowStabElem h_comm i * bsm.rowStabElem h_comm i = 1 := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli_mul_self_eq_one]

noncomputable def BinSympMatrix.rowProductSub {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(bsm.stabClosure h_comm) :=
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  Finset.univ.prod (fun i => if ind i = 1 then bsm.rowStabElem h_comm i else (1 : ↥(bsm.stabClosure h_comm)))

def BinSympMatrix.rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(PauliGroup_group n) :=
  (bsm.rowProductSub h_comm ind : ↥(PauliGroup_group n))

@[simp]
lemma BinSympMatrix.rowProduct_zero {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    bsm.rowProduct h_comm (fun _ => (0 : ZMod 2)) = 1 := by
  simp [BinSympMatrix.rowProduct, BinSympMatrix.rowProductSub]

lemma BinSympMatrix.rowProduct_single {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowProduct h_comm (Pi.single i (1 : ZMod 2)) = BinSympPauli_toPauli (bsm.row i) := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsub : bsm.rowProductSub h_comm (Pi.single i (1 : ZMod 2)) = bsm.rowStabElem h_comm i := by
    unfold BinSympMatrix.rowProductSub
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hij
      simp [hij]
    · intro hi
      simp at hi
  simpa [BinSympMatrix.rowProduct] using congrArg Subtype.val hsub

lemma BinSympMatrix.rowProductSub_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProductSub h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProductSub h_comm ind₁ * bsm.rowProductSub h_comm ind₂ := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  let oneSub : ↥(bsm.stabClosure h_comm) := 1
  let f : Fin k → ↥(bsm.stabClosure h_comm) :=
    fun i => if ind₁ i = 1 then bsm.rowStabElem h_comm i else oneSub
  let g : Fin k → ↥(bsm.stabClosure h_comm) :=
    fun i => if ind₂ i = 1 then bsm.rowStabElem h_comm i else oneSub
  have hone_left_val (x : ↥(bsm.stabClosure h_comm)) :
      (((oneSub * x : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) = (x : ↥(PauliGroup_group n)) := by
    change (((oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n)) *
        ((x : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) = (x : ↥(PauliGroup_group n))
    simp [oneSub]
  have hone_right_val (x : ↥(bsm.stabClosure h_comm)) :
      (((x * oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) = (x : ↥(PauliGroup_group n)) := by
    change (((x : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n)) *
        ((oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) = (x : ↥(PauliGroup_group n))
    simp [oneSub]
  have hone_mul_val :
      (((oneSub * oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
        (oneSub : ↥(PauliGroup_group n)) := by
    change (((oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n)) *
        ((oneSub : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
        (oneSub : ↥(PauliGroup_group n))
    simp [oneSub]
  have hadd :
      (fun i : Fin k => if ind₁ i + ind₂ i = 1 then bsm.rowStabElem h_comm i else oneSub) =
        fun i => f i * g i := by
    funext i
    rcases Fin.exists_fin_two.mp ⟨ind₁ i, rfl⟩ with h₁ | h₁ <;>
      rcases Fin.exists_fin_two.mp ⟨ind₂ i, rfl⟩ with h₂ | h₂
    · unfold f g
      rw [h₁, h₂]
      apply Subtype.ext
      exact hone_mul_val.symm
    · unfold f g
      rw [h₁, h₂]
      apply Subtype.ext
      exact (hone_left_val (bsm.rowStabElem h_comm i)).symm
    · unfold f g
      rw [h₁, h₂]
      apply Subtype.ext
      exact (hone_right_val (bsm.rowStabElem h_comm i)).symm
    · unfold f g
      rw [h₁, h₂]
      apply Subtype.ext
      simp [oneSub]
  unfold BinSympMatrix.rowProductSub
  rw [hadd]
  simpa [f, g] using
    (Finset.prod_mul_distrib (s := Finset.univ) (f := f) (g := g))

lemma BinSympMatrix.rowProduct_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProduct h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProduct h_comm ind₁ * bsm.rowProduct h_comm ind₂ := by
  simpa [BinSympMatrix.rowProduct] using congrArg Subtype.val
    (BinSympMatrix.rowProductSub_add bsm h_comm ind₁ ind₂)

lemma BinSympMatrix.rowProduct_self_mul_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    bsm.rowProduct h_comm ind * bsm.rowProduct h_comm ind = 1 := by
  have hzero : (fun i => ind i + ind i) = (fun _ => (0 : ZMod 2)) := by
    funext i
    rcases Fin.exists_fin_two.mp ⟨ind i, rfl⟩ with h | h <;> simp [h] ; native_decide
  rw [← BinSympMatrix.rowProduct_add bsm h_comm ind ind, hzero, BinSympMatrix.rowProduct_zero]

lemma BinSympMatrix.rowProduct_inv_eq_self {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    (bsm.rowProduct h_comm ind)⁻¹ = bsm.rowProduct h_comm ind :=
  inv_eq_self_of_mul_self_eq_one (BinSympMatrix.rowProduct_self_mul_eq_one bsm h_comm ind)

lemma BinSympMatrix.rowProduct_binaryImage {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) :
    Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsum_aux :
      ∀ S : Finset (Fin k),
        Pauli_toBinSympPauli
          ((((S.prod fun i => if ind i = 1 then bsm.rowStabElem h_comm i else (1 : ↥(bsm.stabClosure h_comm)))
            : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
          S.sum (fun i => if ind i = 1 then bsm.row i else 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        rw [Finset.prod_empty, Finset.sum_empty]
        have hone : (((1 : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
            (1 : ↥(PauliGroup_group n)) := by
          simp
        exact (congrArg Pauli_toBinSympPauli hone).trans (Pauli_toBinSympPauli_one (n := n))
    | @insert a S ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have hco :
            ↑((if ind a = 1 then bsm.rowStabElem h_comm a else (1 : ↥(bsm.stabClosure h_comm))) *
                ∏ x ∈ S, if ind x = 1 then bsm.rowStabElem h_comm x else (1 : ↥(bsm.stabClosure h_comm))) =
              ((if ind a = 1 then ((bsm.rowStabElem h_comm a : ↥(bsm.stabClosure h_comm)) :
                  ↥(PauliGroup_group n)) else ((1 : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) *
                ↑(∏ x ∈ S, if ind x = 1 then bsm.rowStabElem h_comm x else (1 : ↥(bsm.stabClosure h_comm)))) := by
          by_cases hia : ind a = 1
          · rw [if_pos hia, if_pos hia]
            rfl
          · rw [if_neg hia, if_neg hia]
            rfl
        have hmul :
            Pauli_toBinSympPauli
                ((((if ind a = 1 then bsm.rowStabElem h_comm a else (1 : ↥(bsm.stabClosure h_comm))) *
                    ∏ x ∈ S, if ind x = 1 then bsm.rowStabElem h_comm x else (1 : ↥(bsm.stabClosure h_comm))
                  : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
              Pauli_toBinSympPauli
                ((((if ind a = 1 then bsm.rowStabElem h_comm a else (1 : ↥(bsm.stabClosure h_comm))) :
                    ↥(PauliGroup_group n)) *
                  (((∏ x ∈ S, if ind x = 1 then bsm.rowStabElem h_comm x else (1 : ↥(bsm.stabClosure h_comm)) :
                    ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))))) := by
          exact congrArg Pauli_toBinSympPauli hco
        rw [hmul, Pauli_to_BinSymp_correct, ih]
        by_cases hia : ind a = 1
        · simp [hia, Pauli_toBinSympPauli_BinSympPauli_toPauli]
        · have hone : Pauli_toBinSympPauli (((1 : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) = 0 := by
              have hco : (((1 : ↥(bsm.stabClosure h_comm)) : ↥(PauliGroup_group n))) =
                  (1 : ↥(PauliGroup_group n)) := by
                simp
              exact (congrArg Pauli_toBinSympPauli hco).trans (Pauli_toBinSympPauli_one (n := n))
          simp [hia]
  have hsum :
      Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) =
        Finset.univ.sum (fun i => if ind i = 1 then bsm.row i else 0) := by
    unfold BinSympMatrix.rowProduct BinSympMatrix.rowProductSub
    exact hsum_aux Finset.univ
  ext j
  · have hx := congrArg (fun bp => bp.1 j) hsum
    have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Pauli_toBinSympPauli (bsm.rowProduct h_comm ind)).1 j
          = (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j := by
              simpa using hx
      _ = Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.X i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.X.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).1 j := by
            rfl
  · have hz := congrArg (fun bp => bp.2 j) hsum
    have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Pauli_toBinSympPauli (bsm.rowProduct h_comm ind)).2 j
          = (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j := by
              simpa using hz
      _ = Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.Z i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.Z.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).2 j := by
            rfl

lemma BinSympMatrix.selectedRows_sum_eq_mulVec {n k : ℕ} (bsm : BinSympMatrix k n)
    (ind : Fin k → ZMod 2) :
    Finset.univ.sum (fun i => if ind i = 1 then bsm.row i else 0) =
      (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  ext j
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.X i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.X.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).1 j := by
            rfl
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.Z i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.Z.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).2 j := by
            rfl

theorem BinSympCode_stab_eq_rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm).stabs ↔ ∃ ind, bsm.rowProduct h_comm ind = s := by
  constructor
  · revert s
    unfold StabCode_of_BinSympMatrix StabCode_of_StabSet BinSympMatrix.toStabSet
    simp only
    apply Subgroup.closure_induction
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact ⟨Pi.single i (1 : ZMod 2), BinSympMatrix.rowProduct_single bsm h_comm i⟩
    · exact ⟨0, BinSympMatrix.rowProduct_zero bsm h_comm⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨ind₁, rfl⟩
      rcases hy with ⟨ind₂, rfl⟩
      exact ⟨fun i => ind₁ i + ind₂ i, BinSympMatrix.rowProduct_add bsm h_comm ind₁ ind₂⟩
    · intro x _ hx
      rcases hx with ⟨ind, rfl⟩
      exact ⟨ind, (BinSympMatrix.rowProduct_inv_eq_self bsm h_comm ind).symm⟩
  · rintro ⟨ind, rfl⟩
    simp [BinSympMatrix.rowProduct, BinSympMatrix.stabClosure, StabCode_of_BinSympMatrix,
      StabCode_of_StabSet]

theorem BinSympCode_stab_eq_rowSpace {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm).stabs ↔
      ∃ ind, bsm.rowProduct h_comm ind = s ∧
        Pauli_toBinSympPauli s = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  rw [BinSympCode_stab_eq_rowProduct]
  constructor
  · rintro ⟨ind, rfl⟩
    exact ⟨ind, rfl, BinSympMatrix.rowProduct_binaryImage bsm h_comm ind⟩
  · rintro ⟨ind, hs, _⟩
    exact ⟨ind, hs⟩

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun N => ∀ s ∈ SC.stabs, commute N s
 := Classical.decPred _

def StabCode.normalizer {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {N | ∀ s ∈ SC.stabs, commute N s}

def StabCode.undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : Prop :=
  E ∈ SC.normalizer ∧ (∀ s ∈ SC.stabs, Pauli_toBinSympPauli s ≠ Pauli_toBinSympPauli E) ∧
    PauliGroup.normalized E

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun E => SC.undetectable E
 := Classical.decPred _

def StabCode.undetectable_set {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {E | SC.undetectable E}

def StabCode.nontrivial {n : ℕ} (SC : StabCode n) : Prop := ∃ ψ₁ ∈ SC.space, ∃ ψ₂ ∈ SC.space, ψ₁ ≠ ψ₂

--wait, why is this true again? If there are at least two code words, then the pauli error that maps one to another is undetectable
theorem StabCode.undetectable_set_nonempty {n : ℕ} (SC : StabCode n) (hnt : SC.nontrivial) : SC.undetectable_set.Nonempty := sorry

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

lemma mem_normalizer_iff_norm_mem {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : E ∈ SC.normalizer ↔ normalize_pauli E ∈ SC.normalizer := by
  unfold StabCode.normalizer
  simp_rw [Finset.mem_filter_univ, ←commute_iff_norm_commute]

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
  constructor
  · intro hbsp
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := B.row) (x := bsp)).1 hbsp with
      ⟨ind, hind⟩
    refine ⟨ind, ?_⟩
    calc
      (B.X.transpose.mulVec ind, B.Z.transpose.mulVec ind)
          = Finset.univ.sum (fun i => if ind i = 1 then B.row i else 0) := by
              symm
              exact B.selectedRows_sum_eq_mulVec ind
      _ = ∑ i, ind i • B.row i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rcases Fin.exists_fin_two.mp ⟨ind i, rfl⟩ with h | h <;> simp [h]
      _ = bsp := hind
  · rintro ⟨ind, rfl⟩
    rw [← B.selectedRows_sum_eq_mulVec ind]
    exact Submodule.sum_mem _ (fun i _ => by
      rcases Fin.exists_fin_two.mp ⟨ind i, rfl⟩ with h | h
      · simp [h]
      · simpa [h] using (Submodule.subset_span (Set.mem_range_self i) : B.row i ∈ B.rowSpace))

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

lemma BinSympMatrix.binaryImage_mem_rowSpace_of_stab {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) {s : PauliGroup n}
    (hs : s ∈ (StabCode_of_BinSympMatrix B h_comm).stabs) :
    Pauli_toBinSympPauli s ∈ B.rowSpace := by
  rcases (BinSympCode_stab_eq_rowSpace B h_comm s).1 hs with ⟨ind, _, hsimg⟩
  exact (B.mem_rowSpace_iff_exists_indicator _).2 ⟨ind, hsimg.symm⟩

lemma BinSympMatrix.exists_stab_of_binaryImage_mem_rowSpace {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) {bsp : BinSympPauli n} (hbsp : bsp ∈ B.rowSpace) :
    ∃ s ∈ (StabCode_of_BinSympMatrix B h_comm).stabs, Pauli_toBinSympPauli s = bsp := by
  rcases (B.mem_rowSpace_iff_exists_indicator bsp).1 hbsp with ⟨ind, rfl⟩
  refine ⟨B.rowProduct h_comm ind, ?_, B.rowProduct_binaryImage h_comm ind⟩
  exact (BinSympCode_stab_eq_rowProduct B h_comm _).2 ⟨ind, rfl⟩

lemma BinSympMatrix.mem_normalizer_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (E : PauliGroup n) :
    E ∈ (StabCode_of_BinSympMatrix B h_comm).normalizer ↔
      ∀ i, symplecticProd (B.row i) (Pauli_toBinSympPauli E) = 0 := by
  constructor
  · intro hE i
    have hcomm :
        commute E (BinSympPauli_toPauli (B.row i)) := by
      have hmem : BinSympPauli_toPauli (B.row i) ∈ (StabCode_of_BinSympMatrix B h_comm).stabs := by
        exact (BinSympCode_stab_eq_rowProduct B h_comm _).2
          ⟨Pi.single i (1 : ZMod 2), B.rowProduct_single h_comm i⟩
      unfold StabCode.normalizer at hE
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
      exact hE _ hmem
    have hs :
        symplecticProd (Pauli_toBinSympPauli E)
          (Pauli_toBinSympPauli (BinSympPauli_toPauli (B.row i))) = 0 :=
      (commute_iff_symplecticProd_zero E (BinSympPauli_toPauli (B.row i))).1 hcomm
    simpa [symplecticProd_comm] using hs
  · intro hE
    unfold StabCode.normalizer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro s hs
    have hs' : s ∈ Subgroup.closure (SetLike.coe (B.toStabSet h_comm).stabs) := by
      simpa [StabCode_of_BinSympMatrix, StabCode_of_StabSet] using hs
    have hall : commute E s := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hs'
      · intro x hx
        simp only [BinSympMatrix.toStabSet, Finset.mem_coe, Finset.mem_image] at hx
        rcases hx with ⟨i, _, rfl⟩
        exact (commute_iff_symplecticProd_zero E (BinSympPauli_toPauli (B.row i))).2 <|
          by simpa [symplecticProd_comm] using hE i
      · simpa [commute, anticommute_sym] using commute_1x E
      · intro x y _ _ hx hy
        exact (commute_iff_commute _ _).2 <|
          (Commute.mul_right
            ((commute_iff_eq _ _).2 ((commute_iff_commute _ _).1 hx))
            ((commute_iff_eq _ _).2 ((commute_iff_commute _ _).1 hy))).eq
      · intro x _ hx
        exact (commute_iff_commute _ _).2 <|
          (Commute.inv_right
            ((commute_iff_eq _ _).2 ((commute_iff_commute _ _).1 hx))).eq
    exact hall

lemma BinSympMatrix.stabCode_undetectable_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (E : PauliGroup n) :
    (StabCode_of_BinSympMatrix B h_comm).undetectable E ↔
      B.undetectable (Pauli_toBinSympPauli E) ∧ PauliGroup.normalized E := by
  constructor
  · rintro ⟨h_norm, h_not_stab, hE_norm⟩
    refine ⟨?_, hE_norm⟩
    constructor
    · exact (B.mem_normalizer_iff h_comm E).1 h_norm
    · intro hbsp
      rcases B.exists_stab_of_binaryImage_mem_rowSpace h_comm hbsp with ⟨s, hs, hsimg⟩
      exact h_not_stab s hs hsimg
  · rintro ⟨hbsp, hE_norm⟩
    refine ⟨(B.mem_normalizer_iff h_comm E).2 hbsp.1, ?_, hE_norm⟩
    intro s hs hsimg
    exact hbsp.2 <| hsimg ▸ B.binaryImage_mem_rowSpace_of_stab h_comm hs

lemma BinSympMatrix.stabCode_undetectable_toPauli_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (bsp : BinSympPauli n) :
    (StabCode_of_BinSympMatrix B h_comm).undetectable (BinSympPauli_toPauli bsp) ↔
      B.undetectable bsp := by
  simpa [BinSympPauli_toPauli_normalized] using
    (B.stabCode_undetectable_iff h_comm (BinSympPauli_toPauli bsp))

lemma BinSympMatrix.toStabCodeNontrivial_of_k_pos {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm).nontrivial := sorry

--ultimate theorem linking binSymp representation distance
theorem BinSympMatrix.distance_eq_distance {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm).distance = B.distance hk := by
  have hweights :
      (StabCode_of_BinSympMatrix B h_comm).undetectable_set.image pauli_weight =
        B.undetectable_set.image BinSympPauli.weight := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨E, hE, rfl⟩
      have hE' : (StabCode_of_BinSympMatrix B h_comm).undetectable E := by
        simpa [StabCode.undetectable_set] using hE
      refine Finset.mem_image.2 ⟨Pauli_toBinSympPauli E, ?_, ?_⟩
      · have hbsp := (B.stabCode_undetectable_iff h_comm E).1 hE'
        simpa [BinSympMatrix.undetectable_set] using hbsp.1
      · exact (pauli_weight_eq_BinSympPauli_weight E).symm
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : B.undetectable bsp := by
        simpa [BinSympMatrix.undetectable_set] using hbsp
      refine Finset.mem_image.2 ⟨BinSympPauli_toPauli bsp, ?_, ?_⟩
      · have hE : (StabCode_of_BinSympMatrix B h_comm).undetectable (BinSympPauli_toPauli bsp) := by
          simpa [B.stabCode_undetectable_toPauli_iff h_comm bsp]
            using hbsp'
        simpa [StabCode.undetectable_set] using hE
      · exact pauli_weight_BinSympPauli_toPauli bsp
  unfold StabCode.distance BinSympMatrix.distance
  rw [hweights]
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
lemma PState.ne_zero {n : ℕ} {ψ : PState n} : ψ.vec ≠ 0 := by
  aesop
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
  aesop
-/
