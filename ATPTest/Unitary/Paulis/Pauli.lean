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
variable {n : ℕ} (hn : 0 < n) (m : Fin n → Pauli)

def unfolded1 := (pgphase_1, (fun (_ : Fin n) => Pauli_I))

lemma kron_of_1s {n₁ n₂} :
  (1 : 𝐔ₙ[n₁]) ⊗ₙ (1 : 𝐔ₙ[n₂]) = 1 := by
  simp [unitary_nkron, normalized_kron, normalize_mat]

lemma foldPauli1 : @fold n unfolded1 = 1 := by
  induction n with
  | zero =>
    simp [fold, fold_aux, unfolded1, unitary_n_nkron, U_phase, Pauli_I]
  | succ n' H =>
    rw [fold, fold_aux, unfolded1]
    simp [unitary_n_nkron]
    rw [<- uphase_of_kron]
    simp [fold, fold_aux, unfolded1] at H
    rw [H]
    have: Pauli_I = (1 : 𝐔ₙ[1]) := by rfl
    rw [this, kron_of_1s]

lemma mem_PauliGroup_id : 1 ∈ PauliGroup n := by
  rw [PauliGroup, Finset.mem_image, factored_Pauli_univ]
  exists unfolded1
  constructor
  · simp [unfolded1, pgroup_phases]
  · apply foldPauli1

def Pauli1 : PauliGroup n := ⟨1, mem_PauliGroup_id⟩

def PauliGroup.map (P : PauliGroup n) : (Fin n → Pauli) :=
  (foldPauli.symm P).2

def PauliGroup.phase (P : PauliGroup n) : pgroup_phases :=
  (foldPauli.symm P).1

-- trivial now, could possibly delete
lemma rep_unique (f₁ f₂ : factored_Pauli n) (H: foldPauli f₁ = foldPauli f₂) :
  f₁ = f₂ := by
  apply foldPauli.injective
  trivial

def pauli_weight (U : PauliGroup n) : ℕ :=
  (Finset.univ.filter (fun i => (PauliGroup.map U) i ≠ Pauli_I)).card

def pauli_only (U : PauliGroup n) (P : Pauli) :=
  ∀ x, ((PauliGroup.map U) x = Pauli_I ∨ (PauliGroup.map U) x = P)

def commute (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

def pauli1_pauli1_phase (P P' : Pauli) : pgroup_phases :=
  if commute P P' then 1 else pgphase_n1

abbrev ith_anticommute (U₁ U₂ : PauliGroup n) (i : Fin n) : Bool :=
  !(commute (PauliGroup.map U₁ i) (PauliGroup.map U₂ i))

def count_anticommutes (U₁ U₂ : PauliGroup n) : ℕ :=
  (Finset.univ.filter (fun i => ith_anticommute U₁ U₂ i)).card

def pauli_pauli_phase (U₁ U₂ : PauliGroup n) : pgroup_phases :=
  if count_anticommutes U₁ U₂ % 2 == 0 then pgphase_1 else pgphase_n1

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ}
  (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  (pauli_pauli_phase  U₁ U₁') * (pauli_pauli_phase U₂ U₂') =
  (pauli_pauli_phase
    (kronOfPauli U₁ U₂)) (kronOfPauli U₁' U₂') := by
  sorry

lemma pauli_pauli_phase_symm (U₁ U₂ : PauliGroup n) :
  pauli_pauli_phase U₁ U₂ = pauli_pauli_phase U₂ U₁ := by
  sorry

lemma pauli_pauli_phase_self (U : PauliGroup n) :
  pauli_pauli_phase U U = pgphase_1 := by admit

def pgX := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_X)
def pgY := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_X)
def pgZ := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_X)
def pg1 := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_X)

@[simp]
lemma pphase_XZ : pauli_pauli_phase pgX pgZ = pgphase_n1 := by admit

@[simp]
lemma pphase_ZX : pauli_pauli_phase pgZ pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XZ

@[simp]
lemma pphase_XY : pauli_pauli_phase pgX pgY = pgphase_n1 := by admit

@[simp]
lemma pphase_YX : pauli_pauli_phase pgY pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XY

@[simp]
lemma pphase_YZ : pauli_pauli_phase pgY pgZ = pgphase_n1 := by admit

@[simp]
lemma pphase_ZY : pauli_pauli_phase pgZ pgY = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_YZ

@[simp]
lemma pphase_id_right {U : PauliGroup 1} :
  pauli_pauli_phase pg1 U = pgphase_1 := by admit

@[simp]
lemma pphase_id_left (U : PauliGroup 1) :
  pauli_pauli_phase U pg1 = pgphase_1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_id_right

lemma pauli_mul {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]}
 (hP₁ : U₁ ∈ PauliGroup n) (hP₂ : U₂ ∈ PauliGroup n) :
 U₁ * U₂ ∈ PauliGroup n := by sorry

--maybe tedious proof?
lemma pauli_inv {n : ℕ} {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup n)
  : U⁻¹ ∈ PauliGroup n := by sorry

--want to prove this one soon
lemma pauli_commute_or_anticommute {n : ℕ}{U₁ U₂ : 𝐔ₙ[n]}
  (hU₁ : U₁ ∈ PauliGroup n) (hU₂ : U₂ ∈ PauliGroup n) : U₁ * U₂ = U₂ * U₁ ∨ U₁ * U₂ = - U₂ * U₁ := sorry
