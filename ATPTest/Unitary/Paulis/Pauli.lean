import ATPTest.Unitary.Basic
import ATPTest.States.Phase
import ATPTest.AI_Generated.ne0_unitary
import ATPTest.AI_Generated.scalar_mat_is_one
import ATPTest.AI_Generated.KronNonsense
import ATPTest.AI_Generated.PauliBruteForce
-- import ATPTest.AI_Generated.TediousLinearAlgebra
import ATPTest.Unitary.Paulis.Pauli1
import ATPTest.Unitary.Paulis.PauliFolding
import ATPTest.Unitary.Paulis.PauliMul

open Qubit
open Function

noncomputable section

-- variable {l : ℕ} (m_test : Fin l → Pauli)
variable {n : ℕ} (m : Fin n → Pauli)

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

lemma Pauli1_unfold : Pauli1 = foldPauli (pgphase_1, (fun (_ : Fin n) => Pauli_I)) := by
  unfold Pauli1; simp_rw [<- foldPauli1]
  simp [foldPauli, foldPauli_toFun, unfolded1]

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

def commute₁ (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

lemma commute₁_sym P P' :
  commute₁ P P' ↔ commute₁ P' P := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases P') with rfl | rfl | rfl | rfl
  all_goals simp [commute₁]
  all_goals tauto

lemma commute₁_xx P : commute₁ P P := by simp [commute₁]

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

lemma anticommuteₘ_sym (m₁ m₂ : Fin n -> Pauli) :
  anticommuteₘ m₁ m₂ = anticommuteₘ m₂ m₁ := by
  induction n with
  | zero => simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    rw [IH]
    suffices: commute₁ (m₁ 0) (m₂ 0) = commute₁ (m₂ 0) (m₁ 0)
    · rw [this]
    rw [Bool.eq_iff_iff]
    rw [commute₁_sym]

lemma anticommuteₘ_xx (m : Fin n -> Pauli) :
  anticommuteₘ m m = false := by
  induction n with
  | zero =>
    simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [IH]
    rw [commute₁_xx]

def anticommute (U₁ U₂ : PauliGroup n) :=
  anticommuteₘ (PauliGroup.map U₁) (PauliGroup.map U₂)

lemma map_kron_of_Pauli {n₁ n₂} -- (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (P₁ : PauliGroup n₁) (P₂ : PauliGroup n₂) :
  PauliGroup.map (kronOfPauli P₁ P₂) =
  cast_fin_append (PauliGroup.map P₂) (PauliGroup.map P₁) := by
  let P₁f := foldPauli.symm P₁
  let w₁ := P₁f.1
  let m₁ := P₁f.2
  let P₂f := foldPauli.symm P₂
  let w₂ := P₂f.1
  let m₂ := P₂f.2
  rw [kronOfPauli]
  simp_rw [kron_PaulisE]
  simp [factored_kron, PauliGroup.map]

lemma anticommute_kron {n₁ n₂}
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  anticommute (kronOfPauli U₁ U₂) (kronOfPauli U₁' U₂') =
  (anticommute U₁ U₁' ^^ anticommute U₂ U₂') := by
  unfold anticommute
  rw [map_kron_of_Pauli]
  rw [map_kron_of_Pauli]
  rw [anticommuteₘ_cat]
  rw [Bool.xor_comm]

lemma anticommute_sym (U₁ U₂ : PauliGroup n) :
  anticommute U₁ U₂ = anticommute U₂ U₁ := by
  unfold anticommute
  rw [anticommuteₘ_sym]

lemma anticommute_xx (P : PauliGroup n) :
  anticommute P P = false := by
  unfold anticommute
  rw [anticommuteₘ_xx]

def pauli_pauli_phase (U₁ U₂ : PauliGroup n) : pgroup_phases :=
  if anticommute U₁ U₂ then pgphase_n1 else pgphase_1

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ}
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  (pauli_pauli_phase U₁ U₁') * (pauli_pauli_phase U₂ U₂') =
  (pauli_pauli_phase
    (kronOfPauli U₁ U₂)) (kronOfPauli U₁' U₂') := by
  unfold pauli_pauli_phase
  rw [anticommute_kron]
  rcases (anticommute U₁ U₁') with Ht | Hf
  all_goals rcases (anticommute U₂ U₂') with Ht₂ | Hf₂
  all_goals simp

lemma pauli_pauli_phase_symm (P₁ P₂ : PauliGroup n) :
  pauli_pauli_phase P₁ P₂ = pauli_pauli_phase P₂ P₁ := by
  unfold pauli_pauli_phase
  rw [anticommute_sym]

lemma pauli_pauli_phase_self (U : PauliGroup n) :
  pauli_pauli_phase U U = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute_xx]

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

lemma pauli_mul' {n : ℕ} (U₁ U₂ : PauliGroup n) :
  U₁.val * U₂.val ∈ PauliGroup n := by
  rw [<- mul_Paulis_correct]
  aesop

lemma pauli_mul {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]}
 (hP₁ : U₁ ∈ PauliGroup n) (hP₂ : U₂ ∈ PauliGroup n) :
 U₁ * U₂ ∈ PauliGroup n := by
 apply (pauli_mul' ⟨U₁, hP₁⟩ ⟨U₂, hP₂⟩)

def factored_inv {n : ℕ} (U : factored_Pauli n) : factored_Pauli n :=
  (pgroup_phases.inv U.1, U.2)

lemma scale1_factored_Pauli {n} (P : factored_Pauli n) :
  scale_factored_Pauli pgphase_1 P = P := by
  rw [scale_factored_Pauli]
  have: pgphase_1 = 1 := by rfl
  rw [this]
  rw [PauliPhases.one_mul]

lemma mul_Pauli1_xx (P : Pauli) :
  mul_Pauli1 P P = (1, Pauli_I) := by
  rw [mul_Pauli1]
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals aesop

lemma eq_empty_tuples {t} (P Q : Fin 0 -> t) :
  P = Q := by convert rfl

lemma pointwise_mul_Paulis_xx {n} (P : Fin n -> Pauli) :
  pointwise_mul_Paulis P P = (λ _ => (1, Pauli_I)) := by
  unfold pointwise_mul_Paulis
  apply funext
  intro x
  apply mul_Pauli1_xx

lemma collect_phases_iter {n} (P : Fin (n + 1) -> (pgroup_phases × Pauli)) :
  collect_phases P =
  ((P 0).1 * (collect_phases (Fin.tail P)).1, λ i => (P i).2) := by
  rw [collect_phases, collect_phases]
  rfl

lemma mul_Pauli1_tuples_xx {n} (P : Fin n -> Pauli) :
  mul_Pauli1_tuples P P = unfolded1 := by
  rw [mul_Pauli1_tuples]
  rw [pointwise_mul_Paulis_xx]
  clear P
  induction n with
  | zero =>
    simp [collect_phases, fold_pgroup_phases]
    rfl
  | succ n₀ IH =>
    simp [collect_phases_iter]
    conv =>
      enter[1]
      enter[1]
      enter[1]
      enter[1]
      change (λ _ => (1, Pauli_I))
    rw [IH]
    rfl

lemma factored_inv_correct {n} (U : factored_Pauli n) :
  foldPauli (factored_inv U) = ((foldPauli U).val)⁻¹ := by
  symm; rw [DivisionMonoid.inv_eq_of_mul]
  rw [<-mul_Paulis_correct]
  simp [factored_inv, mul_Paulis]
  simp [mul_factored_Paulis]
  have: (U.1).val.z * ((pgroup_phases.inv U.1)).val.z = 1 := by
    suffices: U.1 * pgroup_phases.inv U.1 = 1
    · have H := congrArg (λx => x.val.z) this
      simp at H
      rw [H]
      rfl
    apply mul_inv_cancel
  simp_rw [this]
  conv =>
    enter[1]
    enter[1]
    enter[2]
    enter[1]
    change pgphase_1
  rw [scale1_factored_Pauli]
  rw [mul_Pauli1_tuples_xx]
  rw [unfolded1]
  rw [<- Pauli1_unfold]
  rfl

lemma pauli_inv' {n : ℕ} (U: PauliGroup n) :
  (U.val)⁻¹ ∈ PauliGroup n := by
  let FU := foldPauli.symm U
  have: U = foldPauli FU := by aesop
  rw [this]
  rw [<- factored_inv_correct]
  aesop

--maybe tedious proof?
lemma pauli_inv {n : ℕ} {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup n)
  : U⁻¹ ∈ PauliGroup n := by
  apply (pauli_inv' ⟨U, hU⟩)

-- TODO
lemma pauli_commute_or_anticommute' {n} (P Q : PauliGroup n) :
  P.val * Q.val = Q.val * P.val ∨
  P.val * Q.val = - Q.val * P.val := by
  sorry

--want to prove this one soon
lemma pauli_commute_or_anticommute {n : ℕ}{U₁ U₂ : 𝐔ₙ[n]}
  (hU₁ : U₁ ∈ PauliGroup n) (hU₂ : U₂ ∈ PauliGroup n) :
  U₁ * U₂ = U₂ * U₁ ∨ U₁ * U₂ = - U₂ * U₁ := by
  apply (pauli_commute_or_anticommute' ⟨U₁, hU₁⟩ ⟨U₂, hU₂⟩)
