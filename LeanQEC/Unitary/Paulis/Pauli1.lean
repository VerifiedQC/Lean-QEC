-- Single-qubit Paulis

import LeanQEC.Unitary.Basic


open Qubit
open Function
open Matrix

noncomputable section

abbrev pgroup_phases := Multiplicative (ZMod 4)

/- 1 = i ^ 0 -/
abbrev pgphase_1 : pgroup_phases := Multiplicative.ofAdd 0

/- -1 = i ^ 2 -/
abbrev pgphase_n1 : pgroup_phases := Multiplicative.ofAdd 2

/- i = i ^ 1 -/
abbrev pgphase_i : pgroup_phases := Multiplicative.ofAdd 1

/- -i = i ^ 3 -/
abbrev pgphase_ni : pgroup_phases := Multiplicative.ofAdd 3

lemma pgphase_cases (a : pgroup_phases) :
    a = 1 ∨ a = pgphase_n1 ∨ a = pgphase_i ∨ a = pgphase_ni := by
  revert a; decide

namespace pgroup_phases

def iCircle : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.2 (by simp)⟩

@[simp] lemma coe_iCircle : (iCircle : ℂ) = Complex.I := rfl

lemma iCircle_pow_four : iCircle ^ 4 = 1 := by
  ext; simp [iCircle]

/- Convert the exponent into an actual phase (element of the complex unit circle) -/
noncomputable def toCircle : pgroup_phases →* Circle where
  toFun z := iCircle ^ (Multiplicative.toAdd z).val
  map_one' := by simp
  map_mul' a b := by
    rw [← pow_add, toAdd_mul, ZMod.val_add, ← pow_mod_orderOf]
    conv_rhs => rw [← pow_mod_orderOf]
    have h4 : orderOf iCircle ∣ 4 := orderOf_dvd_of_pow_eq_one iCircle_pow_four
    rw [Nat.mod_mod_of_dvd _ h4]

@[simp] lemma toCircle_one : toCircle 1 = 1 := map_one _

lemma toCircle_apply (z : pgroup_phases) :
    toCircle z = iCircle ^ (Multiplicative.toAdd z).val := rfl

@[simp] lemma coe_toCircle_n1 : (toCircle pgphase_n1 : ℂ) = -1 := by
  rw [toCircle_apply, Circle.coe_pow, coe_iCircle]
  show Complex.I ^ 2 = -1
  simp

@[simp] lemma coe_toCircle_i : (toCircle pgphase_i : ℂ) = Complex.I := by
  rw [toCircle_apply, Circle.coe_pow, coe_iCircle]
  show Complex.I ^ 1 = Complex.I
  simp

@[simp] lemma coe_toCircle_ni : (toCircle pgphase_ni : ℂ) = -Complex.I := by
  rw [toCircle_apply, Circle.coe_pow, coe_iCircle]
  show Complex.I ^ 3 = -Complex.I
  simp [pow_succ]

lemma toCircle_injective : Injective toCircle := by
  intro a b h
  have h' := congrArg (fun z : Circle => (z : ℂ)) h
  rcases pgphase_cases a with rfl | rfl | rfl | rfl <;>
    rcases pgphase_cases b with rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso; simp [Complex.ext_iff] at h' <;> norm_num at h')

end pgroup_phases

def Pauli : Finset 𝐔[Qubit] := {1, X, Y, Z}

def Pauli_I : Pauli := ⟨1, by simp [Pauli]⟩
def Pauli_X : Pauli := ⟨X, by simp [Pauli]⟩
def Pauli_Y : Pauli := ⟨Y, by simp [Pauli]⟩
def Pauli_Z : Pauli := ⟨Z, by simp [Pauli]⟩

instance : Inhabited Pauli := ⟨Pauli_I⟩

abbrev pauliMat (p : Pauli) : Matrix Qubit Qubit ℂ := (p.val : Matrix Qubit Qubit ℂ)

@[simp] lemma Pauli_X_mat : pauliMat Pauli_X = !![0, 1; 1, 0] := rfl
@[simp] lemma Pauli_Y_mat : pauliMat Pauli_Y = !![0, -Complex.I; Complex.I, 0] := rfl
@[simp] lemma Pauli_Z_mat : pauliMat Pauli_Z = !![1, 0; 0, -1] := rfl
@[simp] lemma Pauli_I_mat : pauliMat Pauli_I = 1 := rfl

lemma pauliMat_injective {p q : Pauli} (h : pauliMat p = pauliMat q) : p = q :=
  Subtype.ext (Subtype.ext h)

@[simp] lemma pgXnepgI : Pauli_X ≠ Pauli_I := by
  intro h
  have := congrArg (fun p : Pauli => pauliMat p 0 0) h
  simp at this

@[simp] lemma pgInepgX : Pauli_I ≠ Pauli_X := pgXnepgI.symm

@[simp] lemma pgZnepgI : Pauli_Z ≠ Pauli_I := by
  intro h
  have := congrArg (fun p : Pauli => pauliMat p 1 1) h
  norm_num at this

@[simp] lemma pgInepgZ : Pauli_I ≠ Pauli_Z := pgZnepgI.symm

@[simp] lemma pgYnepgI : Pauli_Y ≠ Pauli_I := by
  intro h
  have := congrArg (fun p : Pauli => pauliMat p 0 0) h
  simp at this

@[simp] lemma pgInepgY : Pauli_I ≠ Pauli_Y := pgYnepgI.symm

@[simp] lemma pgXnepgZ : Pauli_X ≠ Pauli_Z := by
  intro h
  have := congrArg (fun p : Pauli => pauliMat p 0 0) h
  simp at this

@[simp] lemma pgZnepgX : Pauli_Z ≠ Pauli_X := pgXnepgZ.symm

@[simp] lemma pgXnepgY : Pauli_X ≠ Pauli_Y := by
  intro h
  have := congrArg (fun p : Pauli => (pauliMat p 1 0).im) h
  simp at this

@[simp] lemma pgYnepgX : Pauli_Y ≠ Pauli_X := pgXnepgY.symm

@[simp] lemma pgZnepgY : Pauli_Z ≠ Pauli_Y := by
  intro h
  have := congrArg (fun p : Pauli => pauliMat p 0 0) h
  simp at this

@[simp] lemma pgYnepgZ : Pauli_Y ≠ Pauli_Z := pgZnepgY.symm

lemma Pauli_cases (a : Pauli) :
    a = Pauli_X ∨ a = Pauli_Y ∨ a = Pauli_Z ∨ a = Pauli_I := by
  rcases a with ⟨u, hu⟩
  have : u = 1 ∨ u = X ∨ u = Y ∨ u = Z := by
    simpa [Pauli, Finset.mem_insert, Finset.mem_singleton] using hu
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

lemma pauli_herm (p : Pauli) : (pauliMat p).IsHermitian := by
  rcases Pauli_cases p with rfl | rfl | rfl | rfl <;>
    · ext i j
      fin_cases i <;> fin_cases j <;> simp

lemma trace_star_pauli_mul (p q : Pauli) :
    (star (pauliMat p) * pauliMat q).trace = if p = q then 2 else 0 := by
  rcases Pauli_cases p with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases q with rfl | rfl | rfl | rfl <;>
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.star_eq_conjTranspose] <;> norm_num

lemma trace_pauli_single (p : Pauli) :
    (pauliMat p).trace = if p = Pauli_I then (2 : ℂ) else 0 := by
  rcases Pauli_cases p with rfl | rfl | rfl | rfl <;>
    simp [Matrix.trace_fin_two]

/- Paulis are orthogonal so if two elements of the Pauli group equal each other, the phases and base operators are equal too -/
lemma pauli_smul_injective {z z' : Circle} {p p' : Pauli} (h : z • p.val = z' • p'.val) :
    z = z' ∧ p = p' := by
  have hm : (z : ℂ) • pauliMat p = (z' : ℂ) • pauliMat p' := by
    simpa using congrArg (fun U : 𝐔[Qubit] => (U : Matrix Qubit Qubit ℂ)) h
  have h' : (z : ℂ) • (star (pauliMat p) * pauliMat p) =
      (z' : ℂ) • (star (pauliMat p) * pauliMat p') := by
    rw [← mul_smul_comm, ← mul_smul_comm, hm]
  have ht := congrArg Matrix.trace h'
  simp only [trace_smul, trace_star_pauli_mul, smul_eq_mul] at ht
  by_cases hp : p = p'
  · subst hp
    refine ⟨Circle.ext ?_, rfl⟩
    simp only [if_true] at ht
    exact mul_right_cancel₀ (two_ne_zero) ht
  · simp only [if_neg hp, mul_zero, mul_eq_zero, Circle.coe_ne_zero, false_or] at ht
    norm_num at ht

lemma paulis_distinct {p p' : Pauli} (z : pgroup_phases) (H : p ≠ p') :
    pgroup_phases.toCircle z • p.val ≠ p'.val := by
  intro h
  rw [← one_smul Circle p'.val] at h
  exact H (pauli_smul_injective h).2

lemma uphase_injective (z z' : pgroup_phases) (p p' : Pauli)
    (eq : pgroup_phases.toCircle z • p.val = pgroup_phases.toCircle z' • p'.val) :
    z = z' ∧ p = p' := by
  obtain ⟨hz, hp⟩ := pauli_smul_injective eq
  exact ⟨pgroup_phases.toCircle_injective hz, hp⟩

end
