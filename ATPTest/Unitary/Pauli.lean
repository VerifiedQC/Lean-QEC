import ATPTest.Unitary.Basic

open Qubit

def pX := (unitary_fin_equiv beq) X
def pY := (unitary_fin_equiv beq) Y
def pZ := (unitary_fin_equiv beq) Z
def p1 : 𝐔ₙ[1] := 1

noncomputable def Pauli : Finset (𝐔ₙ[1]):= {1, pX, pY, pZ}

def Pauli_X : Pauli := ⟨pX, by simp [Pauli]⟩
def Pauli_Y : Pauli := ⟨pY, by simp [Pauli]⟩
def Pauli_Z : Pauli := ⟨pZ, by simp [Pauli]⟩
def Pauli_I : Pauli := ⟨1, by simp [Pauli]⟩

local instance : NatCast (Fin 2) := Fin.NatCast.instNatCast 2

lemma fin2Cast0E :
  Nat.cast (0 : ℕ) = (0 : Fin 2) := by rfl

lemma XIsHermitian : Matrix.IsHermitian pX.1 := by
  rw [Matrix.IsHermitian, pX]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases (BitVec1_cases i) with rfl | rfl
  all_goals rcases (BitVec1_cases j) with rfl | rfl
  all_goals simp [X, fin2Cast0E]

lemma YIsHermitian : Matrix.IsHermitian pY.1 := by
  rw [Matrix.IsHermitian, pY]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases (BitVec1_cases i) with rfl | rfl
  all_goals rcases (BitVec1_cases j) with rfl | rfl
  all_goals simp [Y, fin2Cast0E]

lemma ZIsHermitian : Matrix.IsHermitian pZ.1 := by
  rw [Matrix.IsHermitian, pZ]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases (BitVec1_cases i) with rfl | rfl
  all_goals rcases (BitVec1_cases j) with rfl | rfl
  all_goals simp [Z, fin2Cast0E]

lemma pauli_herm {p : Pauli} : Matrix.IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl)
  · simp
  · apply XIsHermitian
  · apply YIsHermitian
  · apply ZIsHermitian

variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

def pauli_tensor : 𝐔ₙ[n] :=
  unitary_n_nkron hn (λ x => (m x))


lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (pauli_tensor hn m).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]

  def pauli_tensor_herm : HermitianMat (BitVec n) ℂ :=
  ⟨_, pauli_tensor_hermitian hn m⟩

def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)

def is_pauli_product (U : 𝐔ₙ[n]) := ∃ (m : Fin n → Pauli), pauli_tensor hn m = U

noncomputable def pgroup_phases : Finset phase := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨Complex.I, by norm_num⟩, ⟨-Complex.I, by norm_num⟩}

lemma pgphase_cases (a : pgroup_phases) : a.1 = ⟨1, by norm_num⟩ ∨ a.1 = ⟨-1, by norm_num⟩ ∨
  a.1 = ⟨Complex.I, by norm_num⟩ ∨ a.1 = ⟨-Complex.I, by norm_num⟩ := by
  have:= a.2
  simp [pgroup_phases, -Finset.coe_mem] at this
  exact this

@[simp]
def pgphase_1 : pgroup_phases := ⟨⟨1, by norm_num⟩, by simp [pgroup_phases]⟩

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
    suffices : (⟨a.1 * b.1 * c.1, pgroup_phases_closed_under_mul ⟨_,
     (pgroup_phases_closed_under_mul _ _)⟩ _⟩ : pgroup_phases) = ⟨a.1 * (b.1 * c.1),
      pgroup_phases_closed_under_mul _ (⟨_, pgroup_phases_closed_under_mul _ _⟩)⟩
    exact this
    simp [mul_assoc]
  one := pgphase_1
  one_mul := by
    intros a
    suffices: ⟨pgphase_1.1 * a.1, pgroup_phases_closed_under_mul _ _⟩ = a
    exact this
    simp
  mul_one := by
    intros a
    suffices: ⟨a.1 * pgphase_1.1, pgroup_phases_closed_under_mul _ _⟩ = a
    exact this
    simp
  inv := pgroup_phases.inv
  inv_mul_cancel := by
    intros a
    rw [pgroup_phases.inv]
    suffices: ⟨Phase.phase_star a.1 * a.1, pgroup_phases_closed_under_mul ⟨_, (pgroup_phases_closed_under_inv _)⟩ _⟩ = pgphase_1
    exact this
    simp [Phase.phase_star]
    rcases (pgphase_cases a) with ha | ha | ha | ha
    all_goals simp [ha]

@[simp]
lemma pgp_mul_eq (p1 : pgroup_phases) (p2 : pgroup_phases) : p1 * p2 = ⟨p1.1 * p2.1, pgroup_phases_closed_under_mul _ _⟩ := by
  rfl

--instance : Fintype (Fin n → { x // x ∈ Pauli }) := sorry

noncomputable def pauli_products_n : Finset (𝐔ₙ[n]) := Finset.image (λ m => pauli_tensor hn m) Finset.univ

--see how much i can do with set

--def PauliGroup : Set 𝐔[(Fin (2^n))] := {U_phase (pauli_tensor hn m) z | (m : Fin n → Pauli) (z : phase)}

--def PauliGroup : Finset 𝐔[Fin (2^n)] := Finset.image (λ (x : (pauli_products_n hn) × pgroup_phases) => U_phase x.1 x.2 sorry) (Finset.univ pgroup_phases)
noncomputable def PauliGroup : Finset 𝐔ₙ[n] :=
  (Finset.univ.product pgroup_phases).image (λ mp =>
    let m := mp.1
    let z := mp.2
    U_phase (pauli_tensor hn m) z)

lemma mem_PauliGroup_iff (U : 𝐔ₙ[n]) : U ∈ PauliGroup hn ↔ ∃ m, (∃ z : pgroup_phases, U_phase (pauli_tensor hn m) z = U) := by
  unfold PauliGroup
  rw [Finset.mem_image]
  simp

noncomputable def PauliGroup.map {U : 𝐔ₙ[n]}
(hU : U ∈ PauliGroup hn) : Fin n → Pauli := Classical.choose ((mem_PauliGroup_iff hn U).1 hU)

theorem kron_mem_PauliGroup_iff {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
  {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} : U₁ ⊗ₙ U₂ ∈ PauliGroup (Nat.add_pos_left hn₁ n₂) ↔ (U₁ ∈ PauliGroup hn₁ ∧ U₂ ∈ PauliGroup hn₂) := sorry

noncomputable def PauliGroup.phase {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn)
: pgroup_phases := Classical.choose ((mem_PauliGroup_iff hn U).mp hU).choose_spec

lemma mem_PauliGroup_id : 1 ∈ PauliGroup hn := sorry

lemma rep_unique {U : 𝐔ₙ[n]} (m₁ m₂ : Fin n → Pauli)
(z₁ z₂ : pgroup_phases) (hm₁ : U_phase (pauli_tensor hn m₁) z₁ = U) (hm₂ : U_phase (pauli_tensor hn m₂) z₂ = U)
 : m₁ = m₂ ∧ z₁ = z₂ := sorry

noncomputable def pauli_weight {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) : ℕ := (Finset.univ.filter (fun i => (PauliGroup.map hn hU) i ≠ (1 : 𝐔ₙ[1]))).card

def pauli_only {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn) (P : Pauli) := ∀ x, ((PauliGroup.map hn hU) x = (1 : 𝐔ₙ[1]) ∨ (PauliGroup.map hn hU) x = P)

lemma pauli_commute_with_phase {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : ∃ (p : pgroup_phases),  U₁ * U₂ = U_phase (U₂ * U₁) p := sorry

noncomputable def pauli_pauli_phase {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pgroup_phases := Classical.choose (pauli_commute_with_phase hn h1 h2)

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ} {U₁ U₁' : 𝐔ₙ[n₁]} {U₂ U₂' : 𝐔ₙ[n₂]} (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (hU₁ : U₁ ∈ PauliGroup hn₁) (hU₁' : U₁' ∈ PauliGroup hn₁) (hU₂ : U₂ ∈ PauliGroup hn₂) (hU₂' : U₂' ∈ PauliGroup hn₂)
  : pauli_pauli_phase (Nat.add_pos_left hn₁ n₂) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁, hU₂⟩) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁', hU₂'⟩) =
  (pauli_pauli_phase hn₁ hU₁ hU₁') * (pauli_pauli_phase hn₂ hU₂ hU₂') := sorry

lemma pauli_pauli_phase_symm {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pauli_pauli_phase hn h1 h2 = pauli_pauli_phase hn h2 h1 := sorry

lemma pauli_pauli_phase_self {U : 𝐔ₙ[n]} (h : U ∈ PauliGroup hn) : pauli_pauli_phase hn h h  = pgphase_1 := sorry

def pgX : PauliGroup zero_lt_one := ⟨pX, by
  apply (mem_PauliGroup_iff (zero_lt_one) pX).2
  refine ⟨fun _ => Pauli_X, ⟨pgphase_1, ?_⟩⟩
  simp [pauli_tensor, unitary_n_nkron, U_phase, pgphase_1, Pauli_X]⟩

def pgY : PauliGroup zero_lt_one := ⟨pY, by
  apply (mem_PauliGroup_iff (zero_lt_one) pY).2
  refine ⟨fun _ => Pauli_Y, ⟨pgphase_1, ?_⟩⟩
  simp [pauli_tensor, unitary_n_nkron, U_phase, pgphase_1, Pauli_Y]⟩

def pgZ : PauliGroup zero_lt_one := ⟨pZ, by
  apply (mem_PauliGroup_iff (zero_lt_one) pZ).2
  refine ⟨fun _ => Pauli_Z, ⟨pgphase_1, ?_⟩⟩
  simp [pauli_tensor, unitary_n_nkron, U_phase, pgphase_1, Pauli_Z]⟩

def pg1 : PauliGroup zero_lt_one := ⟨1, by
  apply (mem_PauliGroup_iff (zero_lt_one) 1).2
  refine ⟨fun _ => Pauli_I, ⟨pgphase_1, ?_⟩⟩
  simp [pauli_tensor, unitary_n_nkron, U_phase, pgphase_1, Pauli_I]⟩

@[simp]
lemma pphase_XZ : pauli_pauli_phase zero_lt_one pgX.2 pgZ.2 = pgphase_n1 := sorry

@[simp]
lemma pphase_ZX : pauli_pauli_phase zero_lt_one pgZ.2 pgX.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XZ

@[simp]
lemma pphase_XY : pauli_pauli_phase zero_lt_one pgX.2 pgY.2 = pgphase_n1 := sorry

@[simp]
lemma pphase_YX : pauli_pauli_phase zero_lt_one pgY.2 pgX.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XY

@[simp]
lemma pphase_YZ : pauli_pauli_phase zero_lt_one pgY.2 pgZ.2 = pgphase_n1 := sorry

@[simp]
lemma pphase_ZY : pauli_pauli_phase zero_lt_one pgZ.2 pgY.2 = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_YZ

@[simp]
lemma pphase_id_right {U : 𝐔ₙ[1]} {hU : U ∈ PauliGroup zero_lt_one}: pauli_pauli_phase zero_lt_one pg1.2 hU = pgphase_1 := sorry

@[simp]
lemma pphase_id_left {U : 𝐔ₙ[1]} {hU : U ∈ PauliGroup zero_lt_one}: pauli_pauli_phase zero_lt_one hU pg1.2 = pgphase_1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_id_right
