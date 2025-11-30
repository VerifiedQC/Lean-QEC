import ATPTest.Unitary.Basic
import ATPTest.States.Phase
import ATPTest.AI_Generated.ne0_unitary
import ATPTest.AI_Generated.scalar_mat_is_one
import ATPTest.AI_Generated.KronNonsense
import ATPTest.AI_Generated.PauliBruteForce
-- import ATPTest.AI_Generated.TediousLinearAlgebra
import ATPTest.Unitary.Paulis.Pauli1
import ATPTest.Unitary.Paulis.PauliFolding

open Qubit
open Function

noncomputable section

-- variable {l : ℕ} (m_test : Fin l → Pauli)

/- TODO RESTORE -/
/-
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
  -/


/-
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
  -/

  /--

-- can get this from unfolding now
noncomputable def PauliGroup.phase {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup hn)
: pgroup_phases := Classical.choose ((mem_PauliGroup_iff hn U).mp hU).choose_spec

def unfolded1 := ((fun (_ : Fin n) => Pauli_I), phase_id)

lemma kron_of_1s {n₁ n₂} :
  (1 : 𝐔ₙ[n₁]) ⊗ₙ (1 : 𝐔ₙ[n₂]) = 1 := by
  simp [unitary_nkron, normalized_kron, normalize_mat]

lemma foldPauli1 : fold hn unfolded1 = 1 := by
  rcases n with _ | n'
  · contradiction
  induction n' with
  | zero =>
    simp [fold, unfolded1, unitary_n_nkron, U_phase, Pauli_I]
  | succ n'' H =>
    rw [fold, unfolded1]
    simp [unitary_n_nkron]
    rw [<- uphase_of_kron]
    specialize H (by simp)
    simp [fold, unfolded1] at H
    rw [H]
    have: Pauli_I = (1 : 𝐔ₙ[1]) := by rfl
    rw [this, kron_of_1s]

lemma mem_PauliGroup_id : 1 ∈ PauliGroup hn := by
  rw [PauliGroup, Finset.mem_image, pauli_n_univ]
  exists unfolded1
  constructor
  · simp [unfolded1, Finset.mem_product, pgroup_phases]
  · apply foldPauli1

-- TODO some kinda equiv thing?
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

-- BROKEN
/--
lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ} {U₁ U₁' : 𝐔ₙ[n₁]} {U₂ U₂' : 𝐔ₙ[n₂]} (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (hU₁ : U₁ ∈ PauliGroup hn₁) (hU₁' : U₁' ∈ PauliGroup hn₁) (hU₂ : U₂ ∈ PauliGroup hn₂) (hU₂' : U₂' ∈ PauliGroup hn₂)
  : pauli_pauli_phase (Nat.add_pos_left hn₁ n₂) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁, hU₂⟩) ((kron_mem_PauliGroup_iff hn₁ hn₂).2 ⟨hU₁', hU₂'⟩) =
  (pauli_pauli_phase hn₁ hU₁ hU₁') * (pauli_pauli_phase hn₂ hU₂ hU₂') := by sorry
  -/

lemma pauli_pauli_phase_symm {U₁ U₂ : 𝐔ₙ[n]} (h1 : U₁ ∈ PauliGroup hn)
  (h2 : U₂ ∈ PauliGroup hn) : pauli_pauli_phase hn h1 h2 = pauli_pauli_phase hn h2 h1 := by admit

lemma pauli_pauli_phase_self {U : 𝐔ₙ[n]} (h : U ∈ PauliGroup hn) : pauli_pauli_phase hn h h  = pgphase_1 := by admit

def pgX := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pgY := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pgZ := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pg1 := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)

/-
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
-/

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

-/
