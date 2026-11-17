import LeanQEC.Decoding.Basic

open Matrix MeasureTheory Kronecker
open scoped ComplexOrder

noncomputable section

variable {n k m : ℕ}

variable {C : StabCode n}

/- The probability that the correction `R` is the right one -/
def mldWeight (e : C.Encoder k) (G : C.Generators m) (P : ProbDistribution (PauliGroup_group n))
    (p : ProbabilityMeasure (Ket (Qubits k))) (s : Syndrome m) (R : PauliGroup_group n) : ℝ :=
  ∑ Err, (P Err : ℝ) * ∫ φ, errorIntegrand e G s R Err φ ∂(p : Measure _)

def mldDecoder (e : C.Encoder k) (G : C.Generators m) (P : ProbDistribution (PauliGroup_group n))
    (p : ProbabilityMeasure (Ket (Qubits k))) : Decoder n m :=
  fun s => Classical.choose (Finite.exists_max (mldWeight e G P p s))

theorem mldWeight_le_mldDecoder (e : C.Encoder k) (G : C.Generators m)
    (P : ProbDistribution (PauliGroup_group n)) (p : ProbabilityMeasure (Ket (Qubits k)))
    (s : Syndrome m) (R : PauliGroup_group n) :
    mldWeight e G P p s R ≤ mldWeight e G P p s (mldDecoder e G P p s) :=
  Classical.choose_spec (Finite.exists_max (mldWeight e G P p s)) R

/- For Pauli mixtures we can work with the easier mldWeight rather than the full syndromeTerm -/
theorem syndromeTerm_pauliErrorChannel (e : C.Encoder k) (G : C.Generators m)
    (P : ProbDistribution (PauliGroup_group n)) (p : ProbabilityMeasure (Ket (Qubits k)))
    (s : Syndrome m) (R : PauliGroup_group n) :
    syndromeTerm e G (pauliErrorChannel P) p s R = mldWeight e G P p s R := by
  unfold syndromeTerm mldWeight
  simp_rw [syndromeIntegrand_pauliErrorChannel]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro Err _
    refine (integrable_syndromeIntegrand e G (pauliErrorChannel P) p s R).mono
      ((measurable_errorIntegrand e G s R Err).const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun φ => ?_)
    have h0 : ∀ E', 0 ≤ (P E' : ℝ) * errorIntegrand e G s R E' φ := fun E' =>
      mul_nonneg (P E').zero_le_coe (errorIntegrand_nonneg ..)
    rw [syndromeIntegrand_pauliErrorChannel, Real.norm_of_nonneg (h0 Err),
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => h0 _)]
    exact Finset.single_le_sum (f := fun E' => (P E' : ℝ) * errorIntegrand e G s R E' φ)
      (fun _ _ => h0 _) (Finset.mem_univ Err)

/- Charactizing theorem of MLD -/
theorem gfidelity_le_gfidelity_mldDecoder (e : C.Encoder k) (G : C.Generators m)
    (P : ProbDistribution (PauliGroup_group n)) (p : ProbabilityMeasure (Ket (Qubits k)))
    (dec : Decoder n m) :
    gfidelity e G dec p (pauliErrorChannel P) ≤
      gfidelity e G (mldDecoder e G P p) p (pauliErrorChannel P) := by
  rw [gfidelity_eq_sum_syndromeTerm, gfidelity_eq_sum_syndromeTerm]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [syndromeTerm_pauliErrorChannel, syndromeTerm_pauliErrorChannel]
  exact mldWeight_le_mldDecoder e G P p s (dec s)

end
