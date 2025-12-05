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

lemma foldPauli1 : fold hn unfolded1 = 1 := by
  rcases n with _ | n'
  · contradiction
  induction n' with
  | zero =>
    simp [fold, fold_aux, unfolded1, unitary_n_nkron, U_phase, Pauli_I]
  | succ n'' H =>
    rw [fold, fold_aux, unfolded1]
    simp [unitary_n_nkron]
    rw [<- uphase_of_kron]
    specialize H (by simp)
    simp [fold, fold_aux, unfolded1] at H
    rw [H]
    have: Pauli_I = (1 : 𝐔ₙ[1]) := by rfl
    rw [this, kron_of_1s]

lemma mem_PauliGroup_id : 1 ∈ PauliGroup hn := by
  rw [PauliGroup, Finset.mem_image, factored_Pauli_univ]
  exists unfolded1
  constructor
  · simp [unfolded1, pgroup_phases]
  · apply foldPauli1

def Pauli1 : PauliGroup hn := ⟨1, mem_PauliGroup_id hn⟩

def PauliGroup.map (P : PauliGroup hn) : (Fin n → Pauli) :=
  ((foldPauli hn).symm P).2

def PauliGroup.phase (P : PauliGroup hn) : pgroup_phases :=
  ((foldPauli hn).symm P).1

-- trivial now, could possibly delete
lemma rep_unique (f₁ f₂ : factored_Pauli n) (H: foldPauli hn f₁ = foldPauli hn f₂) :
  f₁ = f₂ := by
  apply (foldPauli hn).injective
  trivial

def pauli_weight (U : PauliGroup hn) : ℕ :=
  (Finset.univ.filter (fun i => (PauliGroup.map hn U) i ≠ Pauli_I)).card

def pauli_only (U : PauliGroup hn) (P : Pauli) :=
  ∀ x, ((PauliGroup.map hn U) x = Pauli_I ∨ (PauliGroup.map hn U) x = P)

def commute₁ (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

lemma commute₁_commute P P' :
  commute₁ P P' ↔ commute₁ P' P := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases P') with rfl | rfl | rfl | rfl
  all_goals simp [commute₁]
  all_goals tauto

lemma commute₁_rfl P : commute₁ P P := by simp [commute₁]

def anticommuteₘ {n} (m m' : Fin n -> Pauli) :=
  match n with
  | 0 => false
  | _ + 1 =>
    (!commute₁ (m 0) (m' 0)) ^^ anticommuteₘ (Fin.tail m) (Fin.tail m')

lemma cast_fin_append_iter1 {t n₁ n₂} (m₁ : Fin (n₁ + 1) -> t) (m₂ : Fin n₂ -> t) :
  (cast_fin_append m₁ m₂) = Fin.cons (m₁ 0) (cast_fin_append (Fin.tail m₁) m₂) := by
  unfold cast_fin_append
  ext a
  rcases a with _ | a₀
  · simp [Fin.append, Fin.addCases, Fin.castLT]
  by_cases H: (a₀ < n₁)
  · simp [Fin.append, Fin.addCases, Fin.castLT]
    rw [dif_pos] <;> try assumption
    simp [Fin.cons]
    rw [dif_pos] <;> try assumption
    simp [Fin.tail]
  simp [Fin.append, Fin.addCases, Fin.castLT]
  rw [dif_neg] <;> try assumption
  simp [Fin.cons]
  intro H
  contradiction

lemma cast_fin_append_iter2 {t n₂} (m₁ : Fin 0 -> t) (m₂ : Fin (n₂ + 1) -> t) :
  (cast_fin_append m₁ m₂) = Fin.cons (m₂ 0) (cast_fin_append m₁ (Fin.tail m₂)) := by
  unfold cast_fin_append
  ext a
  rcases a with _ | a₀
  · simp [Fin.append, Fin.addCases]
  simp [Fin.append, Fin.addCases]

lemma anticommuteₘ_cat {n₁ n₂}
  (m₁ m₁' : Fin n₁ -> Pauli)
  (m₂ m₂' : Fin n₂ -> Pauli) :
  anticommuteₘ (cast_fin_append m₁ m₂) (cast_fin_append m₁' m₂') =
  (anticommuteₘ m₁ m₁' ^^ anticommuteₘ m₂ m₂') := by
  induction n₁ with
  | zero =>
    simp [anticommuteₘ]
    -- this is terrible
    induction n₂ with
    | zero => simp [anticommuteₘ]
    | succ n₀ IH =>
      simp [anticommuteₘ, cast_fin_append, Fin.append, Fin.addCases]
      simp [cast_fin_append_iter2, IH]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [cast_fin_append_iter1]
    simp [IH]

def anticommute (U₁ U₂ : PauliGroup hn) :=
  anticommuteₘ (PauliGroup.map hn U₁) (PauliGroup.map hn U₂)

lemma map_kron_of_Pauli {n₁ n₂} (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (P₁ : PauliGroup hn₁) (P₂ : PauliGroup hn₂) :
  PauliGroup.map (by aesop) (kronOfPauli hn₁ hn₂ P₁ P₂) =
  cast_fin_append (PauliGroup.map hn₂ P₂) (PauliGroup.map hn₁ P₁) := by
  let P₁f := (foldPauli hn₁).symm P₁
  let w₁ := P₁f.1
  let m₁ := P₁f.2
  let P₂f := (foldPauli hn₂).symm P₂
  let w₂ := P₂f.1
  let m₂ := P₂f.2
  rw [kronOfPauli]
  simp_rw [kron_PaulisE]
  simp [factored_kron, PauliGroup.map]

lemma anticommute_kron {n₁ n₂} (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (U₁ U₁' : PauliGroup hn₁)
  (U₂ U₂' : PauliGroup hn₂) :
  anticommute (by aesop) (kronOfPauli hn₁ hn₂ U₁ U₂) (kronOfPauli hn₁ hn₂ U₁' U₂') =
  (anticommute hn₁ U₁ U₁' ^^ anticommute hn₂ U₂ U₂') := by
  unfold anticommute
  rw [map_kron_of_Pauli]
  rw [map_kron_of_Pauli]
  rw [anticommuteₘ_cat]
  rw [Bool.xor_comm]

def pauli_pauli_phase (U₁ U₂ : PauliGroup hn) : pgroup_phases :=
  if anticommute hn U₁ U₂ then pgphase_n1 else pgphase_1

lemma pauli_pauli_phase_commute (P₁ P₂ : PauliGroup hn) :
  pauli_pauli_phase hn P₁ P₂ = pauli_pauli_phase hn P₂ P₁ := by
  sorry

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ}
  (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (U₁ U₁' : PauliGroup hn₁)
  (U₂ U₂' : PauliGroup hn₂) :
  (pauli_pauli_phase hn₁ U₁ U₁') * (pauli_pauli_phase hn₂ U₂ U₂') =
  (pauli_pauli_phase (Nat.add_pos_left hn₁ n₂)
    (kronOfPauli hn₁ hn₂ U₁ U₂)) (kronOfPauli hn₁ hn₂ U₁' U₂') := by
  unfold pauli_pauli_phase
  rw [anticommute_kron]
  rcases (anticommute hn₁ U₁ U₁') with Ht | Hf
  all_goals rcases (anticommute hn₂ U₂ U₂') with Ht₂ | Hf₂
  all_goals simp

lemma pauli_pauli_phase_symm (U₁ U₂ : PauliGroup hn) :
  pauli_pauli_phase hn U₁ U₂ = pauli_pauli_phase hn U₂ U₁ := by
  sorry

lemma pauli_pauli_phase_self (U : PauliGroup hn) :
  pauli_pauli_phase hn U U = pgphase_1 := by admit

def pgX := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pgY := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pgZ := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)
def pg1 := foldPauli zero_lt_one (pgphase_1, fun _ => Pauli_X)

@[simp]
lemma pphase_XZ : pauli_pauli_phase zero_lt_one pgX pgZ = pgphase_n1 := by admit

@[simp]
lemma pphase_ZX : pauli_pauli_phase zero_lt_one pgZ pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XZ

@[simp]
lemma pphase_XY : pauli_pauli_phase zero_lt_one pgX pgY = pgphase_n1 := by admit

@[simp]
lemma pphase_YX : pauli_pauli_phase zero_lt_one pgY pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XY

@[simp]
lemma pphase_YZ : pauli_pauli_phase zero_lt_one pgY pgZ = pgphase_n1 := by admit

@[simp]
lemma pphase_ZY : pauli_pauli_phase zero_lt_one pgZ pgY = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_YZ

@[simp]
lemma pphase_id_right {U : PauliGroup zero_lt_one} :
  pauli_pauli_phase zero_lt_one pg1 U = pgphase_1 := by admit

@[simp]
lemma pphase_id_left (U : PauliGroup zero_lt_one) :
  pauli_pauli_phase zero_lt_one U pg1 = pgphase_1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_id_right
