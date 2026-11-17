module

public import LeanQEC.ForPhysLib.KetMeasure
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace Ket

variable {d : Type*} [Fintype d]

def ofSphere (x : sphere (0 : EuclideanSpace ℂ d) 1) : Ket d where
  vec := fun i => (x : EuclideanSpace ℂ d) i
  normalized' := by
    have h := x.2
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    exact h

theorem continuous_vec_ofSphere :
    Continuous fun x : sphere (0 : EuclideanSpace ℂ d) 1 => (ofSphere x).vec :=
  (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

theorem measurable_ofSphere :
    Measurable (ofSphere : sphere (0 : EuclideanSpace ℂ d) 1 → Ket d) := by
  rintro s ⟨t, ht, rfl⟩
  exact continuous_vec_ofSphere.measurable ht

theorem exists_ofSphere (φ : Ket d) : ∃ x, ofSphere x = φ := by
  refine ⟨⟨WithLp.toLp 2 φ.vec, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    exact φ.normalized'
  · cases φ
    rfl

abbrev sphereMeasure (d : Type*) [Fintype d] : Measure (sphere (0 : EuclideanSpace ℂ d) 1) :=
  (volume : Measure (EuclideanSpace ℂ d)).toSphere

variable [Nonempty d]

instance : NeZero (sphereMeasure d) := ⟨by
  haveI : Nontrivial (EuclideanSpace ℂ d) := inferInstance
  exact Measure.toSphere_ne_zero _⟩

def uniform (d : Type*) [Fintype d] [Nonempty d] : ProbabilityMeasure (Ket d) :=
  ⟨(((sphereMeasure d) Set.univ)⁻¹ • sphereMeasure d).map ofSphere,
    Measure.isProbabilityMeasure_map measurable_ofSphere.aemeasurable⟩

end Ket

namespace Ket

variable {d : Type*} [Fintype d]

def FullSupport (p : ProbabilityMeasure (Ket d)) : Prop :=
  ∀ U : Set (d → ℂ), IsOpen U → (∃ φ : Ket d, φ.vec ∈ U) →
    (p : Measure (Ket d)) (Ket.vec ⁻¹' U) ≠ 0

theorem uniform_fullSupport [Nonempty d] : FullSupport (uniform d) := by
  intro U hU ⟨φ, hφ⟩
  obtain ⟨x, rfl⟩ := exists_ofSphere φ
  simp only [uniform, ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply measurable_ofSphere (measurable_vec hU.measurableSet),
    Measure.smul_apply, smul_eq_mul]
  refine mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) ?_
  exact (hU.preimage continuous_vec_ofSphere).measure_ne_zero _ ⟨x, hφ⟩

theorem eq_one_of_integral_eq_one {p : ProbabilityMeasure (Ket d)} (hp : FullSupport p)
    {F : (d → ℂ) → ℝ} (hF : Continuous F) (h0 : ∀ φ : Ket d, 0 ≤ F φ.vec)
    (h1 : ∀ φ : Ket d, F φ.vec ≤ 1) (hint : ∫ φ, F φ.vec ∂(p : Measure (Ket d)) = 1)
    (φ : Ket d) : F φ.vec = 1 := by
  by_contra hne
  have hmeas : Measurable fun φ : Ket d => F φ.vec := hF.measurable.comp measurable_vec
  have hint' : Integrable (fun φ : Ket d => F φ.vec) (p : Measure (Ket d)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ψ => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h0 ψ, h1 ψ]
  have hzero : ∫ ψ, (1 - F ψ.vec) ∂(p : Measure (Ket d)) = 0 := by
    rw [integral_sub (integrable_const _) hint', hint]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg (fun ψ => sub_nonneg.mpr (h1 ψ))
    ((integrable_const _).sub hint')).mp hzero
  have hU : IsOpen {v : d → ℂ | F v < 1} := isOpen_lt hF continuous_const
  apply hp _ hU ⟨φ, lt_of_le_of_ne (h1 φ) hne⟩
  rw [Filter.EventuallyEq, ae_iff] at hae
  refine measure_mono_null (fun ψ hψ => ?_) hae
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hψ ⊢
  simp only [Pi.zero_apply]
  linarith

end Ket
