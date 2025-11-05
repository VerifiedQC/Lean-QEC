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

-- TODO
def addPhase_toFun (ζ : μ₄) : pgroup_phases := ⟨⟨1, by norm_num⟩, by sorry⟩
def addPhase_invFun (p : pgroup_phases) : μ₄ := ⟨1, by sorry⟩

lemma addPhase_leftInv x : addPhase_invFun (addPhase_toFun x) = x := by sorry
lemma addPhase_rightInv x : addPhase_toFun (addPhase_invFun x) = x := by sorry

def addPhase [Group μ₄] : μ₄ ≃ pgroup_phases where
  toFun := addPhase_toFun
  invFun := addPhase_invFun
  left_inv := by apply addPhase_leftInv
  right_inv := by apply addPhase_rightInv

def phases_grp [Group μ₄] : Group pgroup_phases where
  mul := (fun (x y : pgroup_phases) => addPhase ((addPhase.symm x) * (addPhase.symm x) ))
  mul_assoc := sorry
  one := addPhase 1
  one_mul := sorry
  mul_one := sorry
  inv := (fun (x : pgroup_phases) => addPhase ((addPhase.symm x)⁻¹))
  inv_mul_cancel := by
    sorry
  div_eq_mul_inv := by
    sorry
