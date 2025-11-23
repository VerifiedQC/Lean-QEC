import ATPTest.Unitary.Basic
import ATPTest.States.Phase
import ATPTest.AI_Generated.ne0_unitary
import ATPTest.AI_Generated.scalar_mat_is_one
import ATPTest.AI_Generated.KronNonsense
import ATPTest.AI_Generated.PauliBruteForce
import ATPTest.AI_Generated.TediousLinearAlgebra

open Qubit
open Function

noncomputable section

lemma unitary_ext {n} {U U' : 𝐔ₙ[n]} (vals_eq: U.1 = U'.1) : U = U' := by aesop

def pX := (unitary_fin_equiv beq) X
def pY := (unitary_fin_equiv beq) Y
def pZ := (unitary_fin_equiv beq) Z
def p1 : 𝐔ₙ[1] := 1

noncomputable def Pauli : Finset (𝐔ₙ[1]):= {1, pX, pY, pZ}

def Pauli_X : Pauli := ⟨pX, by simp [Pauli]⟩
def Pauli_Y : Pauli := ⟨pY, by simp [Pauli]⟩
def Pauli_Z : Pauli := ⟨pZ, by simp [Pauli]⟩
def Pauli_I : Pauli := ⟨1, by simp [Pauli]⟩

lemma Pauli_cases (a : Pauli) :
  a = Pauli_X ∨ a = Pauli_Y ∨ a = Pauli_Z ∨ a = Pauli_I := by
  rcases a with ⟨u, hu⟩
  have: u = 1 ∨ u = pX ∨ u = pY ∨ u = pZ := by
    simpa [Pauli, Finset.mem_insert, Finset.mem_singleton] using hu
  aesop

lemma mem_raw_paulis (u : Pauli) :
  (Matrix.reindex beq.symm beq.symm) u ∈ raw_Paulis := by
  have H := Pauli_cases u
  rcases H with HX | HY | HZ | HI
  · subst HX
    simp [Pauli_X, pX, unitary_fin_equiv, X, raw_Paulis]; tauto
  · subst HY
    simp [Pauli_Y, pY, unitary_fin_equiv, Y, raw_Paulis]; tauto
  · subst HZ
    simp [Pauli_Z, pZ, unitary_fin_equiv, Z, raw_Paulis]; tauto
  · subst HI
    simp [Pauli_I, raw_Paulis]; tauto

lemma paulis_distinct_aux {p p' : Pauli} (z : ℂ) (H: p ≠ p') :
  z • p.val.1 ≠ p'.val.1 := by
  let rawP : raw_Paulis := ⟨Matrix.reindex beq.symm beq.symm p.val.1, ?_⟩
  swap
  · apply mem_raw_paulis
  let rawP' : raw_Paulis := ⟨Matrix.reindex beq.symm beq.symm p'.val.1, ?_⟩
  swap
  · apply mem_raw_paulis
  suffices: z • rawP.1 ≠ rawP'.1
  · by_contra H'
    apply (congrArg (Matrix.reindex beq beq).symm) at H'
    tauto
  apply raw_paulis_distinct
  simp
  suffices: rawP.val ≠ rawP'.val
  · tauto
  by_contra H'
  apply (congrArg (Matrix.reindex beq beq)) at H'
  aesop

lemma paulis_distinct {p p' : Pauli} (z : phase) (H: p ≠ p') :
  (U_phase p.val z) ≠ p' := by
  suffices: z.1 • p.val.1 ≠ p'.val.1
  · rw [U_phase]
    aesop
  apply paulis_distinct_aux
  assumption

lemma ne0_phase (z : phase) : z.1 ≠ 0 := by
  by_contra H
  rcases z with ⟨zval, normed_z⟩
  simp at H
  subst H
  simp at normed_z

lemma uphase_div {n} (z z' : phase) (u u' : 𝐔ₙ[n])
  (eq : U_phase u z = U_phase u' z') :
  let r := z * Phase.phase_star z'
  U_phase u r = u' := by
  apply unitary_ext
  simp [U_phase, Phase.phase_star] at ⊢ eq
  apply raw_uphase_div
  · apply ne0_phase
  assumption

lemma phase_ext (z z' : phase) (eq_z : z.1 = z'.1) :
  z = z' := by cases z; aesop

lemma u_phase_eq_is_1 {n} {z : phase} {u : 𝐔ₙ[n]}
  (eq : U_phase u z = u) :
  z = phase_id := by
  cases z with | mk zval z_norm
  rw [U_phase] at eq
  cases u with | mk uval unitary_u
  simp_all
  apply raw_uphase_eq_is_1 at eq
  · assumption
  apply ne0_unitary
  aesop

lemma phase_star_move (a b c : phase) :
  a * Phase.phase_star b = c <-> a = b * c := by
  cases a with | mk aval norm_a
  cases b with | mk bval norm_b
  cases c with | mk cval norm_c
  rw [Phase.phase_star]
  simp
  apply raw_phase_star_move
  aesop

lemma phase_id_1 (a : phase) :
  a * phase_id = a := by
  cases a with | mk aval norm_a
  simp [phase_id]

lemma paulis_distinct' (z z' : phase) (p p' : Pauli)
  (eq: U_phase p.val z = U_phase p'.val z') :
  z = z' /\ p = p' := by
  let r := z * Phase.phase_star z'
  have eq' : U_phase p.val r = p'.val
  · apply uphase_div
    assumption
  suffices: (p = p' -> z = z') /\ p = p'
  · tauto
  constructor
  · intro H'
    subst H'
    suffices this: r = phase_id
    · rw [this] at eq'
      rw [phase_star_move] at this
      rw [phase_id_1] at this
      assumption
    apply u_phase_eq_is_1 at eq'
    assumption
  by_contra H
  let H' := paulis_distinct r H
  tauto

lemma isHermitian_X : Matrix.IsHermitian pX.1 := by
  rw [Matrix.IsHermitian, pX]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.X ]


  --rcases (BitVec1_cases i) with rfl | rfl
  --all_goals rcases (BitVec1_cases j) with rfl | rfl
  --all_goals simp [X]


lemma isHermitian_Y : Matrix.IsHermitian pY.1 := by
  rw [Matrix.IsHermitian, pY]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.Y ]


lemma isHermitian_Z : Matrix.IsHermitian pZ.1 := by
  rw [Matrix.IsHermitian, pZ]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.Z ]


lemma pauli_herm {p : Pauli} : Matrix.IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl)
  · simp
  · apply isHermitian_X
  · apply isHermitian_Y
  · apply isHermitian_Z

instance {n : ℕ} : Coe (Fin n → Pauli) (Fin n → ↥𝐔ₙ[1]) where
  coe m := fun i => (m i).val

def pauli_embedding {n : ℕ} : (Fin n → Pauli) ↪ (Fin n → ↥𝐔ₙ[1]) where
  toFun := fun m => m
  inj' := by
    intros m₁ m₂ hm
    funext k
    rw [funext_iff] at hm
    have:= hm k
    simp [←Subtype.ext_iff] at this
    assumption

instance {n : ℕ} : Coe (Finset (Fin n → Pauli)) (Finset (Fin n → ↥𝐔ₙ[1])) where
  coe S := S.map pauli_embedding

variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (unitary_n_nkron hn m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]

--Depend on LeanQuantumInfo i m p o r t s, shelved for the moment
/-
def pauli_tensor_herm : HermitianMat (BitVec n) ℂ :=
  ⟨_, pauli_tensor_hermitian hn m⟩


def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)
-/


def is_pauli_product (U : 𝐔ₙ[n]) := ∃ (m : Fin n → Pauli), unitary_n_nkron hn m = U

noncomputable def pgroup_phases : Finset phase := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨Complex.I, by norm_num⟩, ⟨-Complex.I, by norm_num⟩}

lemma pgphase_cases (a : pgroup_phases) : a.1 = ⟨1, by norm_num⟩ ∨ a.1 = ⟨-1, by norm_num⟩ ∨
  a.1 = ⟨Complex.I, by norm_num⟩ ∨ a.1 = ⟨-Complex.I, by norm_num⟩ := by
  have:= a.2
  simp [pgroup_phases, -Finset.coe_mem] at this
  exact this

@[simp]
def pgphase_1 : pgroup_phases := ⟨phase_id, by simp [pgroup_phases]⟩

@[simp]
def pgphase_n1 : pgroup_phases := ⟨⟨-1, by norm_num⟩, by simp [pgroup_phases]⟩

lemma pgroup_phases_closed_under_mul : ∀ a b : pgroup_phases, a.1 * b.1 ∈ pgroup_phases := by
  intros a b
  rcases (pgphase_cases a) with ha | ha | ha |ha; all_goals rcases (pgphase_cases b) with hb | hb | hb | hb
  all_goals simp [ha, hb, pgroup_phases]

def pgroup_phases.gmul (a b : pgroup_phases) : pgroup_phases := ⟨_, pgroup_phases_closed_under_mul a b⟩

lemma pgroup_phases_closed_under_inv : ∀ a : pgroup_phases, (Phase.phase_star a.1) ∈ pgroup_phases := by
  intros a
  rcases (pgphase_cases a) with ha | ha | ha | ha
  all_goals simp [ha, Phase.phase_star, pgroup_phases]

def pgroup_phases.inv (a : pgroup_phases) : pgroup_phases := ⟨_, pgroup_phases_closed_under_inv a⟩

instance : Group pgroup_phases where
  mul := pgroup_phases.gmul
  mul_assoc := by
    intros a b c
    suffices ((⟨a.1 * b.1 * c.1, pgroup_phases_closed_under_mul ⟨_,
     (pgroup_phases_closed_under_mul _ _)⟩ _⟩ : pgroup_phases) = ⟨a.1 * (b.1 * c.1),
      pgroup_phases_closed_under_mul _ (⟨_, pgroup_phases_closed_under_mul _ _⟩)⟩) by
      exact this
    simp [mul_assoc]
  one := pgphase_1
  one_mul := by
    intros a
    suffices ⟨pgphase_1.1 * a.1, pgroup_phases_closed_under_mul _ _⟩ = a by
      exact this
    simp
  mul_one := by
    intros a
    suffices ⟨a.1 * pgphase_1.1, pgroup_phases_closed_under_mul _ _⟩ = a by
      exact this
    simp
  inv := pgroup_phases.inv
  inv_mul_cancel := by
    intros a
    rw [pgroup_phases.inv]
    suffices ⟨Phase.phase_star a.1 * a.1, pgroup_phases_closed_under_mul ⟨_, (pgroup_phases_closed_under_inv _)⟩ _⟩ = pgphase_1 by
      exact this
    simp [Phase.phase_star]
    rcases (pgphase_cases a) with ha | ha | ha | ha
    all_goals simp [ha]

@[simp]
lemma pgp_mul_eq (p1 : pgroup_phases) (p2 : pgroup_phases) : p1 * p2 = ⟨p1.1 * p2.1, pgroup_phases_closed_under_mul _ _⟩ := by
  rfl

noncomputable def pauli_n_univ : Finset (Fin n → Pauli) := Finset.univ

noncomputable def pauli_products_n : Finset (𝐔ₙ[n]) := Finset.image (λ m => unitary_n_nkron hn m) (Finset.univ : Finset (Fin n → Pauli))

--see how much i can do with set

--def PauliGroup : Set 𝐔[(Fin (2^n))] := {U_phase (pauli_tensor hn m) z | (m : Fin n → Pauli) (z : phase)}

lemma unitary_nkron_valE {n₁ n₂}
  (M₁ : 𝐔ₙ[n₁]) (M₂ : 𝐔ₙ[n₂]) :
  (M₁ ⊗ₙ M₂).1 = normalize_mat (Matrix.kronecker M₁ M₂)
  := by simp [unitary_nkron, normalized_kron]

lemma normalize_mat_ext {n₁ n₂ m₁ m₂}
  (M : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ)
  (M' : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ) :
  normalize_mat M = normalize_mat M' ->
  M = M' := by
    intro H
    apply (congrArg normalize_mat.symm) at H
    aesop

lemma uphase_eqE {n} (s s' : phase) (U U' : 𝐔ₙ[n])
  (eq: U_phase U s = U_phase U' s') :
  s.1 • U.val = s'.1 • U'.val := by
  simp [U_phase] at eq
  assumption

lemma tuple_eqE_by_cons {n} {u : Type}
  (t t' : Fin (n + 1) → u)
  (eq_head : t 0 = t' 0)
  (eq_tail : Fin.tail t = Fin.tail t') :
  t = t' := by
  apply (Fin.consEquiv (fun _ => u)).symm.injective
  simp; constructor <;> assumption

def fold_pauli (z : phase) (m : Fin n -> Pauli) :=
  U_phase (unitary_n_nkron hn m) z

lemma uphase_of_kron {n₁ n₂} (z : phase) (m1 : 𝐔ₙ[n₁]) (m2 : 𝐔ₙ[n₂]) :
  U_phase m1 z ⊗ₙ m2 = U_phase (m1 ⊗ₙ m2) z := by
  apply unitary_ext
  simp [U_phase, unitary_nkron]
  simp [normalized_kron]
  simp [Matrix.smul_kronecker, Matrix.submatrix_smul]

lemma fold_pauli_iter (z : phase) (m : Fin (n + 1) -> Pauli) :
  fold_pauli (by simp) z m = unitary_nkron (fold_pauli hn z (Fin.tail m)) (m 0) := by
  rw [fold_pauli]
  rw [unitary_n_nkron.eq_def]
  rw [fold_pauli]
  cases n with
  | zero => cases hn
  | succ r => rw [uphase_of_kron]; rfl

lemma pauli_distinct'' {z : ℂ} {m m' : Pauli} (eq: m.val.1 = z • m'.val.1) :
  z = 1 := by
  by_cases H: m = m'
  · subst H
    symm at eq
    apply scalar_mat_is_one at eq
    · assumption
    apply ne0_unitary
    aesop
  revert eq
  suffices: z ≠ 1 -> m.val.1 ≠ z • ↑↑m'
  · tauto
  intro ne1_z
  symm
  apply paulis_distinct_aux
  symm
  assumption

lemma Pauli_ext {m m' : Pauli} (eq : m.val = m'.val) :
  m = m' := by aesop

lemma injective_fold_pauli (z z' : phase) (m m' : Fin n -> Pauli) :
  fold_pauli hn z m = fold_pauli hn z' m' ->
  z = z' /\ m = m' := by
  intro H
  rcases n with _ | n'
  · contradiction
  induction n' with
  | zero =>
    -- no two of IXYZ differ by only phase
    simp [fold_pauli] at H
    simp [unitary_n_nkron] at H
    suffices: z = z' /\ m 0 = m' 0
    · constructor
      · tauto
      -- some `Fin 1` nonsense
      rcases this with ⟨H, H'⟩
      funext x; fin_cases x
      simp; assumption
    apply paulis_distinct'; assumption
  | succ n ih =>
  replace H := by simpa [fold_pauli_iter] using H
  apply (congrArg (fun a => a.1)) at H
  rename_i H'; clear H'
  simp_rw [unitary_nkron_valE] at H
  apply normalize_mat_ext at H
  have ⟨w, HTails, HHeads⟩ :=
    kron_injective_up_to_scalar H ?_ ?_
  rotate_left
  · apply ne0_unitary; simp
  · apply ne0_unitary; aesop
  suffices: m 0 = m' 0 /\ (m 0 = m' 0 -> z = z' /\ Fin.tail m = Fin.tail m')
  · constructor
    · tauto
    · have eq_tails : Fin.tail m = Fin.tail m' := by tauto
      apply tuple_eqE_by_cons <;> tauto
  have eq1_w : w = 1 := by
    -- more Pauli distinction...
    apply pauli_distinct'' at HHeads
    aesop
  subst eq1_w
  constructor
  · simp_all
    apply Pauli_ext
    assumption
  intro eq_m0
  apply ih
  apply unitary_ext
  rw [HTails]
  simp

abbrev fold (mp : (Fin n → Pauli) × phase) :=
  let m := mp.1
  let z := mp.2
  U_phase (unitary_n_nkron hn m) z

lemma inj_fold : Injective (fold hn) := by
  rw [Injective]
  sorry

noncomputable def PauliGroup : Finset 𝐔ₙ[n] :=
  (pauli_n_univ.product pgroup_phases).image (fold hn)

def foldPauli (pm: pgroup_phases × (Fin n -> Pauli)) : PauliGroup hn :=
  let p := pm.1
  let m := pm.2
  let v := fold hn (m, p)
  ⟨v, by sorry⟩

lemma inj_foldPauli : Injective (foldPauli hn) := by
  sorry

local instance : Nonempty (pgroup_phases × (Fin n -> Pauli)) := by
  refine ⟨⟨?phase, ?paulis⟩⟩
  · exact 1
  · intro r
    exact Pauli_I

def unfoldPauli : PauliGroup hn ≃ (pgroup_phases × (Fin n -> Pauli)) where
  toFun := invFun (foldPauli hn)
  invFun := foldPauli hn
  left_inv := by
    sorry
  right_inv := by
    sorry

lemma mem_PauliGroup_iff (U : 𝐔ₙ[n]) : U ∈ PauliGroup hn ↔ ∃ (m : Fin n → Pauli), (∃ z : pgroup_phases, U_phase (unitary_n_nkron hn m) z = U) := by
  unfold PauliGroup
  rw [Finset.mem_image]
  simp
  constructor
  · rintro ⟨a, b, ⟨⟨hpu, hpg⟩, hab2⟩⟩
    refine ⟨a, b, ⟨hpg, ?_⟩⟩
    convert hab2
  rintro ⟨a, b, ⟨hpg, hpu⟩⟩
  refine ⟨a, b, ⟨⟨Finset.mem_univ _, hpg⟩, hpu⟩⟩

variable {l : ℕ} (m_test : Fin l → Pauli)

#check (m_test : Fin l → 𝐔ₙ[1])

noncomputable def PauliGroup.map {U : 𝐔ₙ[n]}
(hU : U ∈ PauliGroup hn) : Fin n → Pauli := Classical.choose ((mem_PauliGroup_iff hn U).1 hU)

--write something for m_cat_pauli

def unitary_map_to_pauli_map {n : ℕ} (m : Fin n → 𝐔ₙ[1]) (hm : ∀ x, (m x) ∈ Pauli) : Fin n → Pauli :=
  fun x => ⟨m x, hm x⟩

def m_cat_pauli {n₁ n₂ : ℕ} (m₁ : Fin n₁ → Pauli) (m₂ : Fin n₂ → Pauli) : Fin (n₁ + n₂) → Pauli :=
  unitary_map_to_pauli_map (unitaries_cat m₁ m₂) (by
    intros x
    unfold unitaries_cat
    by_cases h : x < n₁
    · simp [h]
    simp [h]
  )

theorem kron_mem_PauliGroup_iff {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
  {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} : U₁ ⊗ₙ U₂ ∈ PauliGroup (Nat.add_pos_left hn₁ n₂) ↔ (U₁ ∈ PauliGroup hn₁ ∧ U₂ ∈ PauliGroup hn₂) := by
  rw [mem_PauliGroup_iff, mem_PauliGroup_iff, mem_PauliGroup_iff]
  constructor
  · rintro ⟨m, z, hmz⟩
    sorry
  rintro ⟨⟨m₁, z₁, hU₁⟩, ⟨m₂, z₂, hU₂⟩⟩
  let m_cat := m_cat_pauli m₁ m₂
  refine ⟨m_cat, z₁ * z₂, ?_⟩
  rw [←hU₁, ←hU₂, U_phase_tensor]
  unfold m_cat m_cat_pauli
  rw [unitaries_cat_nkron]
  congr

noncomputable def PauliGroup.phase {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn)
: pgroup_phases := Classical.choose ((mem_PauliGroup_iff hn U).mp hU).choose_spec

lemma mem_PauliGroup_id : 1 ∈ PauliGroup hn := by
  rw [mem_PauliGroup_iff]
  revert hn
  induction' n with n ih;
  · intros hf; linarith
  intros hn
  cases n
  · refine ⟨fun x => Pauli_I, pgphase_1, ?_⟩
    unfold pgphase_1
    simp [-phase_id, U_phase_id, unitary_n_nkron, Pauli_I]
  sorry

   --this aristotle proof was invalidated when i messed around with pauli definitions again
  /-
  -- The identity matrix is in the Pauli group by definition.
  apply Finset.mem_image.mpr;
  use (fun _ => ⟨1, by
    exact Finset.mem_insert_self _ _⟩, pgphase_1);
  simp [Finset.mem_product, U_phase];
  -- The identity matrix is in the Pauli group by definition.
  simp [pgroup_phases];
  -- Apply the lemma that states the tensor product of identity matrices is the identity matrix.
  have h_tensor_id : ∀ (n : ℕ) (hn : 0 < n), unitary_n_nkron hn (fun _ => 1) = 1 := by
    -- We proceed by induction on $n$.
    intro n hn
    induction' n with n ih;
    · contradiction;
    · cases n <;> simp_all +decide [ unitary_n_nkron ];
      simp +decide [ unitary_nkron, normalized_kron ];
  -- Apply the hypothesis h_tensor_id with the specific n and hn from the goal.
  apply h_tensor_id n hn
  -/
/-
lemma rep_unique {U : 𝐔ₙ[n]} (m₁ m₂ : Fin n → Pauli)
(z₁ z₂ : pgroup_phases) (hm₁ : U_phase (pauli_tensor hn m₁) z₁ = U) (hm₂ : U_phase (pauli_tensor hn m₂) z₂ = U)
 : m₁ = m₂ ∧ z₁ = z₂ := by admit

-/

noncomputable def pauli_weight {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) : ℕ := (Finset.univ.filter (fun i => (PauliGroup.map hn hU) i ≠ Pauli_I)).card

def pauli_only {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) (P : Pauli) := ∀ x, ((PauliGroup.map hn hU) x = (1 : 𝐔ₙ[1]) ∨ (PauliGroup.map hn hU) x = P)

--rewrite this for
lemma pauli_commute_with_phase {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : ∃ (p : pgroup_phases),  U₁ * U₂ = U_phase (U₂ * U₁) p := by sorry

noncomputable def pauli_pauli_phase {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pgroup_phases := Classical.choose (pauli_commute_with_phase hn h1 h2)

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ} {U₁ U₁' : 𝐔ₙ[n₁]} {U₂ U₂' : 𝐔ₙ[n₂]} (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (hU₁ : U₁ ∈ PauliGroup hn₁) (hU₁' : U₁' ∈ PauliGroup hn₁) (hU₂ : U₂ ∈ PauliGroup hn₂) (hU₂' : U₂' ∈ PauliGroup hn₂)
  : pauli_pauli_phase (Nat.add_pos_left hn₁ n₂) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁, hU₂⟩) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁', hU₂'⟩) =
  (pauli_pauli_phase hn₁ hU₁ hU₁') * (pauli_pauli_phase hn₂ hU₂ hU₂') := by sorry

lemma pauli_pauli_phase_symm {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pauli_pauli_phase hn h1 h2 = pauli_pauli_phase hn h2 h1 := by admit

lemma pauli_pauli_phase_self {U : 𝐔ₙ[n]} (h : U ∈ PauliGroup hn) : pauli_pauli_phase hn h h  = pgphase_1 := by admit

def pgX : PauliGroup zero_lt_one := ⟨pX, by
  apply (mem_PauliGroup_iff (zero_lt_one) pX).2
  refine ⟨fun _ => Pauli_X, ⟨pgphase_1, ?_⟩⟩
  simp [unitary_n_nkron, U_phase, pgphase_1, Pauli_X]⟩

def pgY : PauliGroup zero_lt_one := ⟨pY, by
  apply (mem_PauliGroup_iff (zero_lt_one) pY).2
  refine ⟨fun _ => Pauli_Y, ⟨pgphase_1, ?_⟩⟩
  simp [unitary_n_nkron, U_phase, pgphase_1, Pauli_Y]⟩

def pgZ : PauliGroup zero_lt_one := ⟨pZ, by
  apply (mem_PauliGroup_iff (zero_lt_one) pZ).2
  refine ⟨fun _ => Pauli_Z, ⟨pgphase_1, ?_⟩⟩
  simp [unitary_n_nkron, U_phase, pgphase_1, Pauli_Z]⟩

def pg1 : PauliGroup zero_lt_one := ⟨1, by
  apply (mem_PauliGroup_iff (zero_lt_one) 1).2
  refine ⟨fun _ => Pauli_I, ⟨pgphase_1, ?_⟩⟩
  simp [unitary_n_nkron, U_phase, pgphase_1, Pauli_I]⟩

@[simp]
lemma pphase_XZ : pauli_pauli_phase zero_lt_one pgX.2 pgZ.2 = pgphase_n1 := by admit

@[simp]
lemma pphase_ZX : pauli_pauli_phase zero_lt_one pgZ.2 pgX.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XZ

@[simp]
lemma pphase_XY : pauli_pauli_phase zero_lt_one pgX.2 pgY.2 = pgphase_n1 := by admit

@[simp]
lemma pphase_YX : pauli_pauli_phase zero_lt_one pgY.2 pgX.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XY

@[simp]
lemma pphase_YZ : pauli_pauli_phase zero_lt_one pgY.2 pgZ.2 = pgphase_n1 := by admit

@[simp]
lemma pphase_ZY : pauli_pauli_phase zero_lt_one pgZ.2 pgY.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_YZ

@[simp]
lemma pphase_id_right {U : 𝐔ₙ[1]} {hU : U ∈ PauliGroup zero_lt_one}: pauli_pauli_phase zero_lt_one pg1.2 hU = pgphase_1 := by admit

@[simp]
lemma pphase_id_left {U : 𝐔ₙ[1]} {hU : U ∈ PauliGroup zero_lt_one}: pauli_pauli_phase zero_lt_one hU pg1.2 = pgphase_1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_id_right
