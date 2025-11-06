import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Group.Units.Defs
import ATPTest.Unitary.Basic
import ATPTest.Unitary.Pauli

noncomputable section

-- undergrad-level subgroup test
-- why is this not in the mathlib?

def subgroup_test {G} [Group G] (N : Set G) := (forall (a b : G), a ∈ N → b ∈ N → a * b⁻¹ ∈ N)

lemma mul_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) (x y : G) :
  x ∈ N → y ∈ N → x * y ∈ N :=
  by sorry

lemma one_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) : 1 ∈ N :=
  by sorry

lemma inv_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) (x : G) :
  x ∈ N → x⁻¹ ∈ N :=
  by sorry

def subgroup_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) : Subgroup G where
  carrier := N
  mul_mem' := by apply mul_mem_by_test; trivial
  one_mem' := by apply one_mem_by_test; trivial
  inv_mem' := by apply inv_mem_by_test; trivial

-- Now, the actually useful part

lemma IsUnitI : IsUnit Complex.I := by sorry

def iu := IsUnitI.unit
def μ₄ : Set ℂˣ := {1, -1, iu, -iu}

lemma sg_test_μ₄ : subgroup_test μ₄ := by sorry

instance μ₄_grp : Group μ₄ := (subgroup_by_test sg_test_μ₄).toGroup

-- Now, if we must use this funny phase thing...

/-
def pgphase_1 : pgroup_phases := ⟨⟨1, by norm_num⟩, by simp [pgroup_phases]⟩
def pgphase_n1 : pgroup_phases := ⟨⟨-1, by norm_num⟩, by simp [pgroup_phases]⟩
-/
def pgphase_i : pgroup_phases := ⟨⟨Complex.I, by norm_num⟩, by simp [pgroup_phases]⟩
def pgphase_ni : pgroup_phases := ⟨⟨-Complex.I, by norm_num⟩, by simp [pgroup_phases]⟩

def μ₄_1 : μ₄ := ⟨1, by rw [μ₄]; simp⟩
def μ₄_n1 : μ₄ := ⟨-1, by rw [μ₄]; simp⟩
def μ₄_i : μ₄ := ⟨iu, by rw [μ₄]; simp⟩
def μ₄_ni : μ₄ := ⟨-iu, by rw [μ₄]; simp⟩

def addPhase_toFun (ζ : μ₄) : pgroup_phases :=
  if ζ = μ₄_1 then pgphase_1
  else if ζ = μ₄_n1 then pgphase_n1
  else if ζ = μ₄_i then pgphase_i
  else pgphase_ni

def addPhase_invFun (p : pgroup_phases) : μ₄ :=
  let v := p.1.1
  if v = 1 then μ₄_1
  else if v = -1 then μ₄_n1
  else if v = Complex.I then μ₄_i
  else μ₄_ni

lemma addPhase_leftInv x : addPhase_invFun (addPhase_toFun x) = x := by
  sorry
lemma addPhase_rightInv x : addPhase_toFun (addPhase_invFun x) = x := by
  sorry

def addPhase [Group μ₄] : μ₄ ≃ pgroup_phases where
  toFun := addPhase_toFun
  invFun := addPhase_invFun
  left_inv := by apply addPhase_leftInv
  right_inv := by apply addPhase_rightInv

def phases_mul [Group μ₄] (x y : pgroup_phases) :=
  addPhase ((addPhase.symm x) * (addPhase.symm y))

def mul_ph : Mul pgroup_phases where
  mul := phases_mul

def inv_ph : Inv pgroup_phases where
  inv := (fun (x : pgroup_phases) => addPhase ((addPhase.symm x)⁻¹))

def one_ph : One pgroup_phases where
  one := addPhase 1

local instance : Mul pgroup_phases := mul_ph
local instance : Inv pgroup_phases := inv_ph
local instance : One pgroup_phases := one_ph

lemma phases_grp_mul_assoc [Mul pgroup_phases] (x y z : pgroup_phases) :
  x * y * z = x * (y * z) := by sorry

lemma phases_grp_one_mul [Mul pgroup_phases] [One pgroup_phases]
  (a : pgroup_phases) : 1 * a = a := by sorry

lemma phases_grp_left_inv
  [Mul pgroup_phases] [Inv pgroup_phases] [One pgroup_phases]
  (a : pgroup_phases) :
  a⁻¹ * a = 1 := by sorry

def phases_grp' [Group μ₄] : Group pgroup_phases := Group.ofLeftAxioms
  phases_grp_mul_assoc phases_grp_one_mul phases_grp_left_inv
