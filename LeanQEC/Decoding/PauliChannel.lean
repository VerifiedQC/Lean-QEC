import LeanQEC.Decoding.Defs
import LeanQEC.Channels.Pauli_Channels

open Matrix MeasureTheory Kronecker
open scoped ComplexOrder

noncomputable section

variable {n k m : ℕ}

instance PauliGroup_group.instFintype (n : ℕ) : Fintype (PauliGroup_group n) :=
  Fintype.ofFinset (PauliGroup n) (fun _ => Iff.rfl)

/- Turn a distribution on Paulis into a channel -/
def pauliErrorChannel (P : ProbDistribution (PauliGroup_group n)) :
    CPTPMap (Qubits n) (Qubits n) :=
  mixedUnitaryChannel P (fun E => (E : 𝐔ₙ[n]))

abbrev pauliGroupMat (R : PauliGroup_group n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((R : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ)

abbrev ketProj {d : Type*} [Fintype d] (φ : Ket d) : Matrix d d ℂ :=
  vecMulVec φ.vec (star φ.vec)

namespace StabCode.Generators

variable {C : StabCode n} (G : C.Generators m)

def syndromeKraus (s : Syndrome m) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((G.syndromePOVM.mats s) ^ (1 / 2 : ℝ)).mat

end StabCode.Generators

theorem CPTPMap.compose_map_apply {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
    [DecidableEq d₁] [DecidableEq d₂] (Λ₂ : CPTPMap d₂ d₃) (Λ₁ : CPTPMap d₁ d₂)
    (X : Matrix d₁ d₁ ℂ) : (Λ₂ ∘ₘ Λ₁).map X = Λ₂.map (Λ₁.map X) :=
  rfl

namespace Decoder

theorem correction_map_kron_single (dec : Decoder n m) (B : Matrix (Qubits n) (Qubits n) ℂ)
    (s : Syndrome m) :
    dec.correction.map (B ⊗ₖ Matrix.single s s 1) =
      pauliGroupMat (dec s) * B * (pauliGroupMat (dec s))ᴴ := by
  have hk : B ⊗ₖ Matrix.single s s (1 : ℂ) = Matrix.blockDiagonal (Pi.single s B) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [kroneckerMap_apply, Matrix.single_apply, blockDiagonal_apply, Pi.single_apply]
    by_cases ha : a = s <;> by_cases hb : b = s <;> subst_vars <;> simp_all [eq_comm]
  change Matrix.traceRight ((dec.controlledCorrection : Matrix _ _ ℂ) *
    (B ⊗ₖ Matrix.single s s 1) * (dec.controlledCorrection : Matrix _ _ ℂ)ᴴ) = _
  rw [hk]
  simp only [Decoder.controlledCorrection, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  ext i j
  simp only [Matrix.traceRight, of_apply, blockDiagonal_apply, Pi.single_apply, if_true]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Decoder

variable {C : StabCode n}

theorem logicalChannel_map (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (E : CPTPMap (Qubits n) (Qubits n)) (X : Matrix (Qubits k) (Qubits k) ℂ) :
    (logicalChannel e G dec E).map X = ∑ s, e.unencode.map (pauliGroupMat (dec s) *
      G.syndromeKraus s * (E ∘ₘ e.encode).map X * G.syndromeKraus s * (pauliGroupMat (dec s))ᴴ) := by
  simp only [logicalChannel, CPTPMap.compose_map_apply, StabCode.Generators.syndromeMeasurement]
  rw [POVM.measurementMap_apply_matrix, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Decoder.correction_map_kron_single]
  simp only [StabCode.Generators.syndromeKraus, Matrix.mul_assoc]

def syndromeIntegrand (e : C.Encoder k) (G : C.Generators m) (E : CPTPMap (Qubits n) (Qubits n))
    (s : Syndrome m) (R : PauliGroup_group n) (φ : Ket (Qubits k)) : ℝ :=
  (trace (e.unencode.map (pauliGroupMat R * G.syndromeKraus s * (E ∘ₘ e.encode).map (ketProj φ) *
    G.syndromeKraus s * (pauliGroupMat R)ᴴ) * ketProj φ)).re

theorem exp_val_logicalChannel_eq_sum (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (E : CPTPMap (Qubits n) (Qubits n)) (φ : Ket (Qubits k)) :
    (logicalChannel e G dec E (MState.pure φ)).exp_val (MState.pure φ).M =
      ∑ s, syndromeIntegrand e G E s (dec s) φ := by
  rw [CPTPMap.exp_val_pure_eq_trace, logicalChannel_map, Finset.sum_mul, trace_sum, Complex.re_sum]
  rfl

theorem re_trace_map_conj_nonneg {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂]
    [DecidableEq d₂] (L : CPTPMap d₁ d₂) (K : Matrix d₁ d₁ ℂ) {Y : Matrix d₁ d₁ ℂ}
    (hY : Y.PosSemidef) (v : d₂ → ℂ) :
    0 ≤ (trace (L.map (K * Y * Kᴴ) * vecMulVec v (star v))).re :=
  (Complex.nonneg_iff.mp (PosSemidef.trace_mul_nonneg
    (L.cp.IsPositive (hY.mul_mul_conjTranspose_same K)) (posSemidef_vecMulVec_self_star v))).1

theorem syndromeIntegrand_nonneg (e : C.Encoder k) (G : C.Generators m)
    (E : CPTPMap (Qubits n) (Qubits n)) (s : Syndrome m) (R : PauliGroup_group n)
    (φ : Ket (Qubits k)) : 0 ≤ syndromeIntegrand e G E s R φ := by
  have hA : (G.syndromeKraus s)ᴴ = G.syndromeKraus s :=
    ((G.syndromePOVM.mats s) ^ (1 / 2 : ℝ)).H
  have hK : pauliGroupMat R * G.syndromeKraus s * (E ∘ₘ e.encode).map (ketProj φ) *
      G.syndromeKraus s * (pauliGroupMat R)ᴴ = (pauliGroupMat R * G.syndromeKraus s) *
      (E ∘ₘ e.encode).map (ketProj φ) * (pauliGroupMat R * G.syndromeKraus s)ᴴ := by
    rw [conjTranspose_mul, hA, Matrix.mul_assoc _ (G.syndromeKraus s)]
  unfold syndromeIntegrand
  rw [hK]
  exact re_trace_map_conj_nonneg _ _
    ((E ∘ₘ e.encode).cp.IsPositive (posSemidef_vecMulVec_self_star _)) _

theorem measurable_syndromeIntegrand (e : C.Encoder k) (G : C.Generators m)
    (E : CPTPMap (Qubits n) (Qubits n)) (s : Syndrome m) (R : PauliGroup_group n) :
    Measurable (syndromeIntegrand e G E s R) := by
  have hL : Continuous (e.unencode.map : Matrix (Qubits n) (Qubits n) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional _
  have hE : Continuous ((E ∘ₘ e.encode).map : Matrix (Qubits k) (Qubits k) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional _
  have hc : Continuous fun v : Qubits k → ℂ =>
      (trace (e.unencode.map (pauliGroupMat R * G.syndromeKraus s *
        (E ∘ₘ e.encode).map (vecMulVec v (star v)) * G.syndromeKraus s * (pauliGroupMat R)ᴴ) *
        vecMulVec v (star v))).re := by
    fun_prop
  exact hc.measurable.comp Ket.measurable_vec

theorem integrable_syndromeIntegrand (e : C.Encoder k) (G : C.Generators m)
    (E : CPTPMap (Qubits n) (Qubits n)) (p : ProbabilityMeasure (Ket (Qubits k)))
    (s : Syndrome m) (R : PauliGroup_group n) :
    Integrable (syndromeIntegrand e G E s R) (p : Measure (Ket (Qubits k))) := by
  refine (gfidelity_integrable e G (fun _ => R) p E).mono
    (measurable_syndromeIntegrand e G E s R).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [exp_val_logicalChannel_eq_sum, Real.norm_of_nonneg (syndromeIntegrand_nonneg ..),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => syndromeIntegrand_nonneg ..)]
  exact Finset.single_le_sum (f := fun t => syndromeIntegrand e G E t R φ)
    (fun _ _ => syndromeIntegrand_nonneg ..) (Finset.mem_univ s)

/- The (unnormalized) success probability contributed by the syndrome `s` when the decoder gives `R` on it, summed over the logical states -/
def syndromeTerm (e : C.Encoder k) (G : C.Generators m) (E : CPTPMap (Qubits n) (Qubits n))
    (p : ProbabilityMeasure (Ket (Qubits k))) (s : Syndrome m) (R : PauliGroup_group n) : ℝ :=
  ∫ φ, syndromeIntegrand e G E s R φ ∂(p : Measure _)

/- Discretize, allowing us to work over all the syndromes individually -/
theorem gfidelity_eq_sum_syndromeTerm (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) :
    gfidelity e G dec p E = ∑ s, syndromeTerm e G E p s (dec s) := by
  unfold gfidelity syndromeTerm
  simp_rw [exp_val_logicalChannel_eq_sum]
  exact integral_finsetSum _ fun s _ => integrable_syndromeIntegrand e G E p s (dec s)

def errorIntegrand (e : C.Encoder k) (G : C.Generators m) (s : Syndrome m)
    (R Err : PauliGroup_group n) (φ : Ket (Qubits k)) : ℝ :=
  (trace (e.unencode.map (pauliGroupMat R * G.syndromeKraus s *
    (pauliGroupMat Err * e.encode.map (ketProj φ) * (pauliGroupMat Err)ᴴ) *
    G.syndromeKraus s * (pauliGroupMat R)ᴴ) * ketProj φ)).re

theorem syndromeIntegrand_pauliErrorChannel (e : C.Encoder k) (G : C.Generators m)
    (P : ProbDistribution (PauliGroup_group n)) (s : Syndrome m) (R : PauliGroup_group n)
    (φ : Ket (Qubits k)) :
    syndromeIntegrand e G (pauliErrorChannel P) s R φ =
      ∑ Err, (P Err : ℝ) * errorIntegrand e G s R Err φ := by
  unfold syndromeIntegrand errorIntegrand
  rw [CPTPMap.compose_map_apply, pauliErrorChannel, mixedUnitaryChannel_map_apply,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mul, map_sum, Matrix.sum_mul,
    trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun Err _ => ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul]

theorem errorIntegrand_nonneg (e : C.Encoder k) (G : C.Generators m) (s : Syndrome m)
    (R Err : PauliGroup_group n) (φ : Ket (Qubits k)) : 0 ≤ errorIntegrand e G s R Err φ := by
  have hA : (G.syndromeKraus s)ᴴ = G.syndromeKraus s :=
    ((G.syndromePOVM.mats s) ^ (1 / 2 : ℝ)).H
  have hK : pauliGroupMat R * G.syndromeKraus s *
      (pauliGroupMat Err * e.encode.map (ketProj φ) * (pauliGroupMat Err)ᴴ) *
      G.syndromeKraus s * (pauliGroupMat R)ᴴ = (pauliGroupMat R * G.syndromeKraus s) *
      (pauliGroupMat Err * e.encode.map (ketProj φ) * (pauliGroupMat Err)ᴴ) *
      (pauliGroupMat R * G.syndromeKraus s)ᴴ := by
    rw [conjTranspose_mul, hA, Matrix.mul_assoc _ (G.syndromeKraus s)]
  unfold errorIntegrand
  rw [hK]
  exact re_trace_map_conj_nonneg _ _ ((e.encode.cp.IsPositive
    (posSemidef_vecMulVec_self_star _)).mul_mul_conjTranspose_same _) _

theorem measurable_errorIntegrand (e : C.Encoder k) (G : C.Generators m) (s : Syndrome m)
    (R Err : PauliGroup_group n) : Measurable (errorIntegrand e G s R Err) := by
  have hL : Continuous (e.unencode.map : Matrix (Qubits n) (Qubits n) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional _
  have hE : Continuous (e.encode.map : Matrix (Qubits k) (Qubits k) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional _
  have hc : Continuous fun v : Qubits k → ℂ =>
      (trace (e.unencode.map (pauliGroupMat R * G.syndromeKraus s *
        (pauliGroupMat Err * e.encode.map (vecMulVec v (star v)) * (pauliGroupMat Err)ᴴ) *
        G.syndromeKraus s * (pauliGroupMat R)ᴴ) * vecMulVec v (star v))).re := by
    fun_prop
  exact hc.measurable.comp Ket.measurable_vec

end
