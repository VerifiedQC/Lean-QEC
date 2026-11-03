module

public import QuantumInfo.States.Ensemble
public import QuantumInfo.Channels.CPTP

@[expose] public section

open Matrix MeasureTheory

noncomputable section

variable {d : Type*} [Fintype d]

instance Ket.instMeasurableSpace : MeasurableSpace (Ket d) :=
  MeasurableSpace.comap Ket.vec inferInstance

theorem Ket.measurable_vec : Measurable (Ket.vec : Ket d → d → ℂ) :=
  comap_measurable _

variable [DecidableEq d]

def PEnsemble.toProbabilityMeasure {α : Type*} [Fintype α] (e : PEnsemble d α) :
    ProbabilityMeasure (Ket d) :=
  ⟨∑ i, ENNReal.ofReal (e.distr i : ℝ) • Measure.dirac (e.states i), ⟨by
    simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (e.distr i).zero_le_coe)]
    simp⟩⟩

omit [DecidableEq d] in
theorem PEnsemble.integral_toProbabilityMeasure {α : Type*} [Fintype α] (e : PEnsemble d α)
    (f : Ket d → ℝ) (hf : Measurable f) :
    ∫ φ, f φ ∂(e.toProbabilityMeasure : Measure (Ket d)) =
      ∑ i, (e.distr i : ℝ) * f (e.states i) := by
  simp only [PEnsemble.toProbabilityMeasure, ProbabilityMeasure.coe_mk]
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable,
      ENNReal.toReal_ofReal (e.distr i).zero_le_coe, smul_eq_mul]
  · intro i _
    exact (integrable_dirac' hf.stronglyMeasurable enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

theorem MState.exp_val_pure_mem_Icc (ρ : MState d) (φ : Ket d) :
    ρ.exp_val (MState.pure φ).M ∈ Set.Icc (0 : ℝ) 1 :=
  ρ.exp_val_prob ⟨(MState.pure φ).nonneg, MState.le_one _⟩

theorem CPTPMap.exp_val_pure_eq_trace (Λ : CPTPMap d d) (φ : Ket d) :
    (Λ (MState.pure φ)).exp_val (MState.pure φ).M =
      (Matrix.trace (Λ.map (vecMulVec φ.vec (star φ.vec)) * vecMulVec φ.vec (star φ.vec))).re := by
  have hm : (MState.pure φ).m = vecMulVec φ.vec (star φ.vec) := by
    ext i j; simp [MState.pure_apply, vecMulVec_apply, Ket.apply]
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace]
  rw [← hm, ← CPTPMap.mat_coe_eq_apply_mat]
  rfl

theorem CPTPMap.measurable_exp_val_pure (Λ : CPTPMap d d) :
    Measurable fun φ : Ket d => (Λ (MState.pure φ)).exp_val (MState.pure φ).M := by
  have hL : Continuous (Λ.map : Matrix d d ℂ → Matrix d d ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have hc : Continuous fun v : d → ℂ =>
      (Matrix.trace (Λ.map (vecMulVec v (star v)) * vecMulVec v (star v))).re := by
    fun_prop
  have : (fun φ : Ket d => (Λ (MState.pure φ)).exp_val (MState.pure φ).M) =
      (fun v : d → ℂ => (Matrix.trace (Λ.map (vecMulVec v (star v)) * vecMulVec v (star v))).re) ∘
        Ket.vec := _root_.funext fun φ => Λ.exp_val_pure_eq_trace φ
  rw [this]
  exact hc.measurable.comp Ket.measurable_vec

theorem CPTPMap.integrable_exp_val_pure (Λ : CPTPMap d d) (p : ProbabilityMeasure (Ket d)) :
    Integrable (fun φ : Ket d => (Λ (MState.pure φ)).exp_val (MState.pure φ).M)
      (p : Measure (Ket d)) := by
  refine Integrable.of_bound Λ.measurable_exp_val_pure.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun φ => ?_)
  have := MState.exp_val_pure_mem_Icc (Λ (MState.pure φ)) φ
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

end
