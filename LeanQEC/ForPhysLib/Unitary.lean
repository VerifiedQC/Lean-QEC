module

public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import Mathlib.Analysis.Complex.Circle

@[expose] public section

noncomputable section

namespace Circle

theorem star_mul_self (z : Circle) : star (z : ℂ) * z = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe]
  simp

def negOne : Circle := ⟨-1, mem_sphere_zero_iff_norm.2 (by simp)⟩

@[simp]
theorem coe_negOne : (negOne : ℂ) = -1 :=
  rfl

end Circle

namespace Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]

theorem circle_smul_mem_unitaryGroup (z : Circle) (U : 𝐔[k]) :
    (z : ℂ) • (U : Matrix k k ℂ) ∈ 𝐔[k] := by
  rw [mem_unitaryGroup_iff']
  rw [star_smul, smul_mul_smul_comm, Circle.star_mul_self, one_smul]
  exact U.2.1

instance instSMulCircleUnitaryGroup : SMul Circle 𝐔[k] :=
  ⟨fun z U => ⟨_, circle_smul_mem_unitaryGroup z U⟩⟩

@[simp]
theorem coe_circle_smul (z : Circle) (U : 𝐔[k]) :
    ((z • U : 𝐔[k]) : Matrix k k ℂ) = (z : ℂ) • (U : Matrix k k ℂ) :=
  rfl

instance instMulActionCircleUnitaryGroup : MulAction Circle 𝐔[k] where
  one_smul U := Subtype.ext (by simp)
  mul_smul z w U := Subtype.ext (by simp [smul_smul])

instance instIsScalarTowerCircleUnitaryGroup : IsScalarTower Circle 𝐔[k] 𝐔[k] where
  smul_assoc z U V := Subtype.ext (by simp [smul_eq_mul])

instance instSMulCommClassCircleUnitaryGroup : SMulCommClass Circle 𝐔[k] 𝐔[k] where
  smul_comm z U V := Subtype.ext (by simp [smul_eq_mul])

instance instSMulCommClassUnitaryGroupCircle : SMulCommClass 𝐔[k] Circle 𝐔[k] :=
  SMulCommClass.symm _ _ _

theorem neg_eq_circle_negOne_smul (U : 𝐔[k]) : -U = Circle.negOne • U :=
  Subtype.ext (by simp)

theorem circle_smul_inj {z w : Circle} {U : 𝐔[k]} [Nonempty k] (h : z • U = w • U) : z = w := by
  have h' : ((z : ℂ) • (U : Matrix k k ℂ)) * star (U : Matrix k k ℂ) =
      ((w : ℂ) • (U : Matrix k k ℂ)) * star (U : Matrix k k ℂ) := by
    rw [← coe_circle_smul, ← coe_circle_smul, h]
  rw [smul_mul_assoc, smul_mul_assoc, U.2.2] at h'
  ext
  obtain ⟨i⟩ := ‹Nonempty k›
  simpa using congrFun (congrFun h' i) i

theorem reindex_mem_unitaryGroup {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (e : a ≃ b) (U : 𝐔[a]) : reindex e e (U : Matrix a a ℂ) ∈ 𝐔[b] := by
  rw [mem_unitaryGroup_iff']
  simp only [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix]
  rw [submatrix_mul_equiv, ← star_eq_conjTranspose, U.2.1]
  simp

def unitaryReindex {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) : 𝐔[a] ≃* 𝐔[b] where
  toFun U := ⟨_, reindex_mem_unitaryGroup e U⟩
  invFun U := ⟨_, reindex_mem_unitaryGroup e.symm U⟩
  left_inv U := Subtype.ext (by simp)
  right_inv U := Subtype.ext (by simp)
  map_mul' U V := Subtype.ext (by simp [submatrix_mul_equiv])

@[simp]
theorem unitaryReindex_val {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (U : 𝐔[a]) :
    (unitaryReindex e U : Matrix b b ℂ) = reindex e e (U : Matrix a a ℂ) :=
  rfl

theorem unitaryReindex_circle_smul {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (e : a ≃ b) (z : Circle) (U : 𝐔[a]) :
    unitaryReindex e (z • U) = z • unitaryReindex e U :=
  Subtype.ext (by simp [submatrix_smul])

theorem unitary_inner_preserve (v₁ v₂ : k → ℂ) (U : 𝐔[k]) :
    ∑ x : k, ((U : Matrix k k ℂ) *ᵥ v₁) x * starRingEnd ℂ (((U : Matrix k k ℂ) *ᵥ v₂) x) =
      ∑ x : k, v₁ x * starRingEnd ℂ (v₂ x) := by
  have h_unitary : (U : Matrix k k ℂ)ᴴ * (U : Matrix k k ℂ) = 1 := by
    rw [← star_eq_conjTranspose]
    exact U.2.1
  have h_inner : ∑ x : k, ((U : Matrix k k ℂ) *ᵥ v₁) x *
      starRingEnd ℂ (((U : Matrix k k ℂ) *ᵥ v₂) x) =
      ∑ x : k, ∑ y : k, v₁ y * starRingEnd ℂ (v₂ x) *
        ((U : Matrix k k ℂ)ᴴ * (U : Matrix k k ℂ)) x y := by
    simp +decide [Matrix.mulVec, dotProduct, mul_comm]
    simp +decide [Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _,
      Finset.sum_mul]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  rw [h_inner]
  simp_all [Matrix.one_apply]

end Matrix
