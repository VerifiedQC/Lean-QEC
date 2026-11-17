import LeanQEC.Stabilizer.Basic
import QuantumInfo.Measurements.POVM
import LeanQEC.ForPhysLib.KetMeasure
import LeanQEC.ForPhysLib.MatrixMap

open Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

variable {n k m : ℕ}

/- It feels a little irrelevant to talk about encoders, ideally I would like to be able to ignore that detail. But encoders are nonunique so we have to deal with it. I wonder what restrictions we can place such that there is a unique choice of encoder for each code? May or may not be worth it though -/
structure StabCode.Encoder (C : StabCode n) (k : ℕ) where
  le : k ≤ n
  U : 𝐔ₙ[n]
  range_eq : LinearMap.range (Matrix.toLin' ((U : Matrix (Qubits n) (Qubits n) ℂ) *
    ancillaEmbedding le)) = C.space

def prepAncilla (k r : ℕ) : CPTPMap (Qubits k) (Qubits k × Qubits r) :=
  (CPTPMap.id ⊗ᶜᵖ CPTPMap.replacement (MState.pure (Ket.basis (0 : Qubits r)))) ∘ₘ
    (CPTPMap.ofEquiv (Equiv.prodPUnit (Qubits k)).symm : CPTPMap (Qubits k) (Qubits k × Unit))

namespace StabCode.Encoder

variable {C : StabCode n}

def encode (e : C.Encoder k) : CPTPMap (Qubits k) (Qubits n) :=
  CPTPMap.ofUnitary e.U ∘ₘ CPTPMap.ofEquiv (qubitsSplit e.le) ∘ₘ prepAncilla k (n - k)

def unencode (e : C.Encoder k) : CPTPMap (Qubits n) (Qubits k) :=
  CPTPMap.traceRight ∘ₘ CPTPMap.ofEquiv (qubitsSplit e.le).symm ∘ₘ CPTPMap.ofUnitary e.U⁻¹

end StabCode.Encoder

theorem traceRight_prepAncilla (k r : ℕ) (ρ : MState (Qubits k)) :
    (CPTPMap.traceRight : CPTPMap (Qubits k × Qubits r) (Qubits k)) (prepAncilla k r ρ) = ρ := by
  have h : (CPTPMap.ofEquiv (Equiv.prodPUnit (Qubits k)).symm :
      CPTPMap (Qubits k) (Qubits k × Unit)) ρ = ρ ⊗ᴹ MState.pure (Ket.basis ()) := by
    apply MState.ext_m
    ext ⟨i, u⟩ ⟨j, v⟩
    simp only [CPTPMap.ofEquiv_apply, Equiv.symm_symm, MState.relabel_m, Matrix.submatrix_apply,
      Equiv.prodPUnit_apply]
    change ρ.m i j = ρ.m i j * (MState.pure _).m u v
    simp [MState.pure_apply, Ket.apply, Ket.basis]
  simp only [prepAncilla, CPTPMap.compose_eq, h, CPTPMap.prod_apply_prod, CPTPMap.id_MState,
    CPTPMap.traceRight_eq_MState_traceRight, MState.traceRight_prod_eq]

theorem StabCode.Encoder.unencode_comp_encode {C : StabCode n} (e : C.Encoder k) :
    e.unencode ∘ₘ e.encode = CPTPMap.id := by
  apply CPTPMap.funext
  intro ρ
  simp only [StabCode.Encoder.unencode, StabCode.Encoder.encode, CPTPMap.compose_eq,
    CPTPMap.ofUnitary_inv_apply, CPTPMap.ofEquiv_symm_apply, traceRight_prepAncilla,
    CPTPMap.id_MState]

/- One bit per stabilizer generator -/
abbrev Syndrome (m : ℕ) := Fin m → ZMod 2

def syndromeSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

namespace StabCode.Generators

variable {C : StabCode n} (G : C.Generators m)

/-- The matrix of the `j`-th generator. -/
def mat (j : Fin m) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((G.gen j : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ)

/- Project onto the `(-1)^b`-eigenspace of the `j`th generator -/
def factor (j : Fin m) (b : ZMod 2) : Matrix (Qubits n) (Qubits n) ℂ :=
  (1 / 2 : ℂ) • (1 + syndromeSign b • G.mat j)

def syndromeProjector (s : Syndrome m) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun j => G.factor j (s j)).prod

lemma mat_mul_self (j : Fin m) : G.mat j * G.mat j = 1 := by
  have := congrArg (fun g : PauliGroup_group n => ((g : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ))
    (C.mul_self_of_mem (G.gen_mem j))
  simpa [mat] using this

lemma mat_commute (i j : Fin m) : Commute (G.mat i) (G.mat j) := by
  have := congrArg (fun g : PauliGroup_group n => ((g : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ))
    (C.commute_of_mem (G.gen_mem i) (G.gen_mem j))
  simpa [mat, Commute, SemiconjBy] using this

lemma mat_isSelfAdjoint (j : Fin m) : IsSelfAdjoint (G.mat j) := by
  have hu : star (G.mat j) * G.mat j = 1 := Unitary.star_mul_self_of_mem (G.gen j : 𝐔ₙ[n]).2
  show star (G.mat j) = G.mat j
  calc star (G.mat j) = star (G.mat j) * (G.mat j * G.mat j) := by rw [G.mat_mul_self, mul_one]
    _ = G.mat j := by rw [← mul_assoc, hu, one_mul]

omit G in
lemma syndromeSign_mul_self (b : ZMod 2) : syndromeSign b * syndromeSign b = 1 := by
  unfold syndromeSign; split_ifs <;> norm_num

omit G in
lemma star_syndromeSign (b : ZMod 2) : star (syndromeSign b) = syndromeSign b := by
  unfold syndromeSign; split_ifs <;> simp

lemma factor_isSelfAdjoint (j : Fin m) (b : ZMod 2) : IsSelfAdjoint (G.factor j b) := by
  have h := G.mat_isSelfAdjoint j
  simp only [IsSelfAdjoint, factor, star_smul, star_add, star_one, star_syndromeSign, h.star_eq]
  congr 1
  simp

lemma factor_idem (j : Fin m) (b : ZMod 2) : IsIdempotentElem (G.factor j b) := by
  unfold IsIdempotentElem factor
  have h1 := G.mat_mul_self j
  have h2 := syndromeSign_mul_self b
  simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, h1, h2, one_smul]
  module

lemma factor_add (j : Fin m) : G.factor j 0 + G.factor j 1 = 1 := by
  simp only [factor, syndromeSign]
  norm_num
  module

lemma factor_commute (i j : Fin m) (a b : ZMod 2) : Commute (G.factor i a) (G.factor j b) := by
  unfold factor
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.add_left (Commute.one_left _) (Commute.add_right (Commute.one_right _) ?_)
  exact ((G.mat_commute i j).smul_left _).smul_right _

theorem syndromeProjector_selfAdjoint_idem (s : Syndrome m) :
    IsSelfAdjoint (G.syndromeProjector s) ∧ IsIdempotentElem (G.syndromeProjector s) :=
  List.prod_ofFn_selfAdjoint_idem _ (fun j => G.factor_isSelfAdjoint j (s j))
    (fun j => G.factor_idem j (s j)) (fun i j => G.factor_commute i j _ _)

theorem syndromeProjector_isHermitian (s : Syndrome m) : (G.syndromeProjector s).IsHermitian :=
  (G.syndromeProjector_selfAdjoint_idem s).1

theorem syndromeProjector_posSemidef (s : Syndrome m) : (G.syndromeProjector s).PosSemidef := by
  obtain ⟨h1, h2⟩ := G.syndromeProjector_selfAdjoint_idem s
  have : (G.syndromeProjector s)ᴴ * G.syndromeProjector s = G.syndromeProjector s := by
    rw [← Matrix.star_eq_conjTranspose, h1.star_eq, h2.eq]
  rw [← this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sum_syndromeProjector : ∑ s, G.syndromeProjector s = 1 :=
  List.prod_ofFn_sum_eq_one _ G.factor_add

/- PhysLib packaging -/
def syndromePOVM : POVM (Syndrome m) (Qubits n) where
  mats s := ⟨G.syndromeProjector s, G.syndromeProjector_isHermitian s⟩
  nonneg s := HermitianMat.zero_le_iff.mpr (G.syndromeProjector_posSemidef s)
  normalized := by
    ext1
    simpa [HermitianMat.mat_finset_sum] using G.sum_syndromeProjector

def syndromeMeasurement : CPTPMap (Qubits n) (Qubits n × Syndrome m) :=
  G.syndromePOVM.measurementMap

end StabCode.Generators
def Decoder (n m : ℕ) := Syndrome m → PauliGroup_group n

namespace Decoder

/- We need classical control in the logical channel to read off the syndrome measurement and then use that to generate the correction from the decoder function -/
variable (dec : Decoder n m)
def controlledCorrection : 𝐔[Qubits n × Syndrome m] :=
  ⟨Matrix.blockDiagonal fun s => ((dec s : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_one]
    congr 1
    funext s
    exact Unitary.mul_star_self_of_mem (dec s : 𝐔ₙ[n]).2⟩

/- Reads off syndrome, applies the correction, cuts syndrome register -/
def correction : CPTPMap (Qubits n × Syndrome m) (Qubits n) :=
  CPTPMap.traceRight ∘ₘ CPTPMap.ofUnitary dec.controlledCorrection

end Decoder

variable {C : StabCode n}

/- Transform physical errors into logical errors -/
def logicalChannel (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (E : CPTPMap (Qubits n) (Qubits n)) : CPTPMap (Qubits k) (Qubits k) :=
  e.unencode ∘ₘ dec.correction ∘ₘ G.syndromeMeasurement ∘ₘ E ∘ₘ e.encode

/- Intended as a generalization of the usual definition of fidelity. The usual definition of fidelity is the average success rate -- take the observable that projects to the original logical state and read off the probability from it after applying the logical error channel. The key generalization is that we allow the measure on logical states to be arbitrary as opposed to uniform -/
def gfidelity (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) : ℝ :=
  ∫ φ, (logicalChannel e G dec E (MState.pure φ)).exp_val (MState.pure φ).M ∂(p : Measure _)

theorem gfidelity_nonneg (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) :
    0 ≤ gfidelity e G dec p E :=
  integral_nonneg fun φ => (MState.exp_val_pure_mem_Icc _ φ).1

theorem gfidelity_le_one (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) :
    gfidelity e G dec p E ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (p : Measure (Ket (Qubits k)))) (C := 1)
    (f := fun φ => (logicalChannel e G dec E (MState.pure φ)).exp_val (MState.pure φ).M)
    (Filter.Eventually.of_forall fun φ => by
      have := MState.exp_val_pure_mem_Icc (logicalChannel e G dec E (MState.pure φ)) φ
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [this.1, this.2])
  simp only [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)

/- The generalized fidelity is indeed a probability. -/
theorem gfidelity_mem_Icc (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) :
    gfidelity e G dec p E ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gfidelity_nonneg e G dec p E, gfidelity_le_one e G dec p E⟩

theorem gfidelity_integrable (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) :
    Integrable (fun φ => (logicalChannel e G dec E (MState.pure φ)).exp_val (MState.pure φ).M)
      (p : Measure (Ket (Qubits k))) :=
  (logicalChannel e G dec E).integrable_exp_val_pure p

/- Discrete case -/
theorem gfidelity_ensemble {α : Type*} [Fintype α] (e : C.Encoder k) (G : C.Generators m)
    (dec : Decoder n m) (ens : PEnsemble (Qubits k) α) (E : CPTPMap (Qubits n) (Qubits n)) :
    gfidelity e G dec ens.toProbabilityMeasure E =
      ∑ i, (ens.distr i : ℝ) * (logicalChannel e G dec E (MState.pure (ens.states i))).exp_val
        (MState.pure (ens.states i)).M :=
  ens.integral_toProbabilityMeasure _ (logicalChannel e G dec E).measurable_exp_val_pure

def gfidelityProb (e : C.Encoder k) (G : C.Generators m) (dec : Decoder n m)
    (p : ProbabilityMeasure (Ket (Qubits k))) (E : CPTPMap (Qubits n) (Qubits n)) : Prob :=
  ⟨gfidelity e G dec p E, gfidelity_mem_Icc e G dec p E⟩

end
