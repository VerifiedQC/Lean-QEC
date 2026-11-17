module

public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.CPTP

@[expose] public section

open Matrix Kronecker

namespace Matrix

variable {ι l m n p α : Type*} [Fintype ι] [NonUnitalNonAssocSemiring α]

theorem sum_kronecker (M : ι → Matrix l m α) (B : Matrix n p α) :
    (∑ i, M i) ⊗ₖ B = ∑ i, M i ⊗ₖ B := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum (A : Matrix l m α) (M : ι → Matrix n p α) :
    A ⊗ₖ (∑ i, M i) = ∑ i, A ⊗ₖ M i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

end Matrix

namespace MatrixMap

variable {A B C D R : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

theorem ext_kron [CommSemiring R] {M₁ M₂ : MatrixMap (A × C) (B × D) R}
    (h : ∀ (MA : Matrix A A R) (MC : Matrix C C R), M₁ (MA ⊗ₖ MC) = M₂ (MA ⊗ₖ MC)) :
    M₁ = M₂ := by
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun ⟨a₁, c₁⟩ _ => Finset.sum_congr rfl fun ⟨a₂, c₂⟩ _ => ?_
  rw [← mul_one (X (a₁, c₁) (a₂, c₂)), ← Matrix.single_kronecker_single, h]

variable [Fintype B] [Fintype D]

theorem of_kraus_kron [CommRing R] [StarRing R] {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (M₁ N₁ : κ₁ → Matrix B A R) (M₂ N₂ : κ₂ → Matrix D C R) :
    (of_kraus M₁ N₁) ⊗ₖₘ (of_kraus M₂ N₂) =
      of_kraus (fun i : κ₁ × κ₂ => M₁ i.1 ⊗ₖ M₂ i.2) (fun i : κ₁ × κ₂ => N₁ i.1 ⊗ₖ N₂ i.2) := by
  apply ext_kron
  intro MA MC
  rw [kron_map_of_kron_state]
  simp only [of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  rw [Matrix.sum_kronecker, Fintype.sum_prod_type]
  simp only [Matrix.kronecker_sum]

end MatrixMap

section ChannelInverse

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

theorem CPTPMap.ofUnitary_inv_apply (U : 𝐔[d]) (ρ : MState d) :
    CPTPMap.ofUnitary U⁻¹ (CPTPMap.ofUnitary U ρ) = ρ := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat, CPTPMap.mat_coe_eq_apply_mat]
  change (U⁻¹ : 𝐔[d]).val * ((U : Matrix d d ℂ) * ρ.m * (U : Matrix d d ℂ)ᴴ) *
    ((U⁻¹ : 𝐔[d]) : Matrix d d ℂ)ᴴ = ρ.m
  have h1 : (U⁻¹ : 𝐔[d]).val * (U : Matrix d d ℂ) = 1 := by
    rw [← Matrix.UnitaryGroup.mul_val, inv_mul_cancel]; rfl
  have h2 : (U : Matrix d d ℂ)ᴴ * ((U⁻¹ : 𝐔[d]) : Matrix d d ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [← mul_assoc, h1, one_mul]
  rw [mul_assoc, h2, mul_one]

theorem CPTPMap.ofEquiv_symm_apply (σ : d ≃ d₂) (ρ : MState d) :
    CPTPMap.ofEquiv σ.symm (CPTPMap.ofEquiv σ ρ) = ρ := by
  simp

end ChannelInverse
