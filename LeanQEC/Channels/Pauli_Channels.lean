import QuantumInfo.Channels.CPTP
import QuantumInfo.ClassicalInfo.Distribution
import LeanQEC.Unitary.Basic
import LeanQEC.ForPhysLib.MatrixMap

open Matrix Kronecker Qubit

noncomputable section

variable {d κ : Type*} [Fintype d] [DecidableEq d] [Fintype κ]

/- We can construct a valid channel out of a classical distribution on unitaries (Kraus completeness condition) -/
theorem sum_sqrt_smul_unitary_kraus (p : ProbDistribution κ) (U : κ → 𝐔[d]) :
    ∑ k, ((Real.sqrt (p k) : ℂ) • (U k : Matrix d d ℂ))ᴴ * ((Real.sqrt (p k) : ℂ) • (U k : Matrix d d ℂ))
      = 1 := by
  have hU : ∀ k, (U k : Matrix d d ℂ)ᴴ * (U k : Matrix d d ℂ) = 1 := fun k => by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem (U k).2
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul]
  have hs : ∀ k, (Real.sqrt (p k) : ℂ) * star (Real.sqrt (p k) : ℂ) = ((p k : ℝ) : ℂ) := fun k => by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (p k).zero_le_coe]
  simp only [hs, ← Finset.sum_smul]
  rw [← Complex.ofReal_sum, p.normalized, Complex.ofReal_one, one_smul]

/- The aforementioned channel -/
def mixedUnitaryChannel (p : ProbDistribution κ) (U : κ → 𝐔[d]) : CPTPMap d d :=
  CPTPMap.of_kraus_CPTPMap (fun k => (Real.sqrt (p k) : ℂ) • (U k : Matrix d d ℂ))
    (sum_sqrt_smul_unitary_kraus p U)

theorem mixedUnitaryChannel_map_apply (p : ProbDistribution κ) (U : κ → 𝐔[d])
    (X : Matrix d d ℂ) :
    (mixedUnitaryChannel p U).map X =
      ∑ k, ((p k : ℝ) : ℂ) • ((U k : Matrix d d ℂ) * X * (U k : Matrix d d ℂ)ᴴ) := by
  change (MatrixMap.of_kraus (fun k => (Real.sqrt (p k) : ℂ) • (U k : Matrix d d ℂ))
    (fun k => (Real.sqrt (p k) : ℂ) • (U k : Matrix d d ℂ))) X = _
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : star (Real.sqrt (p k) : ℂ) * (Real.sqrt (p k) : ℂ) = ((p k : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (p k).zero_le_coe]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

def Prob.toDistribution₂ (p : Prob) : ProbDistribution (Fin 2) :=
  ProbDistribution.mk' ![1 - (p : ℝ), p]
    (by intro i; fin_cases i <;> simp [p.coe_le_one, p.zero_le_coe])
    (by simp)

def unitaryErrorChannel (U : 𝐔[d]) (p : Prob) : CPTPMap d d :=
  mixedUnitaryChannel p.toDistribution₂ ![1, U]

def bitFlipChannel (p : Prob) : CPTPMap Qubit Qubit := unitaryErrorChannel Qubit.X p

def dephasingChannel (p : Prob) : CPTPMap Qubit Qubit := unitaryErrorChannel Qubit.Z p

def pauliChannel (p : ProbDistribution (Fin 4)) : CPTPMap Qubit Qubit :=
  mixedUnitaryChannel p ![1, Qubit.X, Qubit.Y, Qubit.Z]

def Prob.depolarizingDistribution (p : Prob) : ProbDistribution (Fin 4) :=
  ProbDistribution.mk' ![1 - (p : ℝ), p / 3, p / 3, p / 3]
    (by have := p.zero_le_coe; intro i; fin_cases i <;> simp [p.coe_le_one] <;> positivity)
    (by simp [Fin.sum_univ_four]; ring)

def depolarizingChannel (p : Prob) : CPTPMap Qubit Qubit :=
  pauliChannel p.depolarizingDistribution

/- Useful for constructing errors that apply to subsystems independently -/
def iidChannel (n : ℕ) (Λ : CPTPMap d d) : CPTPMap (Fin n → d) (Fin n → d) :=
  CPTPMap.piProd (fun _ : Fin n => Λ)

abbrev iidBitFlip (n : ℕ) (p : Prob) := iidChannel n (bitFlipChannel p)

abbrev iidDepolarizing (n : ℕ) (p : Prob) := iidChannel n (depolarizingChannel p)

namespace CPTPMap

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

omit [Fintype dI₁] [Fintype dI₂] [DecidableEq dO₁] [DecidableEq dO₂] in
theorem kraus_prod_complete {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ) (M₂ : κ₂ → Matrix dO₂ dI₂ ℂ)
    (hM₁ : ∑ k, (M₁ k)ᴴ * M₁ k = 1) (hM₂ : ∑ k, (M₂ k)ᴴ * M₂ k = 1) :
    ∑ k : κ₁ × κ₂, (M₁ k.1 ⊗ₖ M₂ k.2)ᴴ * (M₁ k.1 ⊗ₖ M₂ k.2) = 1 := by
  simp only [conjTranspose_kronecker, ← mul_kronecker_mul, Fintype.sum_prod_type,
    ← kronecker_sum, ← sum_kronecker, hM₁, hM₂, one_kronecker_one]

/- Characterization of tensors of channels -/
theorem of_kraus_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ) (M₂ : κ₂ → Matrix dO₂ dI₂ ℂ)
    (hM₁ : ∑ k, (M₁ k)ᴴ * M₁ k = 1) (hM₂ : ∑ k, (M₂ k)ᴴ * M₂ k = 1) :
    of_kraus_CPTPMap M₁ hM₁ ⊗ᶜᵖ of_kraus_CPTPMap M₂ hM₂ =
      of_kraus_CPTPMap (fun k : κ₁ × κ₂ => M₁ k.1 ⊗ₖ M₂ k.2)
        (kraus_prod_complete M₁ M₂ hM₁ hM₂) := by
  apply CPTPMap.ext
  exact MatrixMap.of_kraus_kron M₁ M₁ M₂ M₂

end CPTPMap
