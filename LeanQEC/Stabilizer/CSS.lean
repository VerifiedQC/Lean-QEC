import LeanQEC.Stabilizer.Basic
import LeanQEC.Stabilizer.LinAlg
import LeanQEC.Classical_EC.Basic


variable {n k₁ k₂ : ℕ}

def CSS_BSM (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : BinSympMatrix (k₁ + k₂) n where
    X := Fin.append (fun (_ : Fin k₁) => (fun _ => 0)) H₂
    Z := Fin.append H₁ (fun (_ : Fin k₂) => (fun _ => 0))

theorem CSS_BSM_is_comm {C₁ C₂ : CodeSpace n} (H_dual : (C₁.dualCode : Set (Fin n → ZMod 2)) ⊆ C₂) {H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} (hpc₁ : C₁.parityCheckMatrixOf H₁)
  (hpc₂ : C₂.parityCheckMatrixOf H₂) : (CSS_BSM H₁ H₂).isCommuting := by
  intros r₁ r₂
  unfold CSS_BSM BinSympMatrix.rowProd symplecticProd
  have h : ∀ x y, H₁ x ⬝ᵥ H₂ y = 0 := by
    intros x y
    have hy := C₂.pc_prod_mem_dual y hpc₂
    have hx : H₁ x ∈ C₂ := by
      apply H_dual
      apply C₁.pc_prod_mem_dual x hpc₁
    unfold CodeSpace.dualCode at hy
    rw [Submodule.mem_orthogonalBilin_iff] at hy
    apply hy _ hx
  refine Fin.addCases (fun x => ?_) (fun x => ?_) r₁ <;>
  refine Fin.addCases (fun y => ?_) (fun y => ?_) r₂ <;>
  simp [Fin.append, BinSympMatrix.row]
  · apply h x y
  rw [dotProduct_comm]
  apply h y x

structure CSS_pair (n k₁ k₂) where
  C₁ : CodeSpace n
  C₂ : CodeSpace n
  H_dual : (C₁.dualCode : Set (Fin n → ZMod 2)) ⊆ C₂
  H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)
  H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)
  hpc₁ : C₁.parityCheckMatrixOf H₁
  hpc₂ : C₂.parityCheckMatrixOf H₂
  nt₁ : 0 < k₁
  nt₂ : 0 < k₂


def CSS_pair.toBSM (C : CSS_pair n k₁ k₂) := CSS_BSM C.H₁ C.H₂

noncomputable def CSS_pair.dX (C : CSS_pair n k₁ k₂) := min_weight_ker_not_mem_rowspace C.H₂ C.H₁

noncomputable def CSS_pair.dZ (C : CSS_pair n k₁ k₂) := min_weight_ker_not_mem_rowspace C.H₁ C.H₂

theorem CSS.toBSM_dist_eq (C : CSS_pair n k₁ k₂) :
  C.toBSM.distance (Nat.add_pos_left C.nt₁ _) = min C.dX C.dZ := sorry

def Matrix.mutually_orth_rows {α β γ δ : Type*} [Fintype γ] [Mul δ] [AddCommMonoid δ]
  (M₁ : Matrix α γ δ) (M₂ : Matrix β γ δ) : Prop := ∀ a b, M₁ a ⬝ᵥ M₂ b = 0

lemma toCodeSpace_subset_dual_of_orth_gen {n k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h_orth : M₁.mutually_orth_rows M₂) :
  (M₁.toCodeSpace : Set (Fin n → ZMod 2)) ⊆ M₂.toCodeSpace.dualCode := by
  have htoRow₁ : M₁.toCodeSpace = M₁.rowSpace := by
      ext x
      simp [Matrix.toCodeSpace, Matrix.rowSpace, Matrix.row]
  have htoRow₂ : M₂.toCodeSpace = M₂.rowSpace := by
    ext x
    simp [Matrix.toCodeSpace, Matrix.rowSpace, Matrix.row]
  intro x hx
  rw [htoRow₁] at hx
  rw [htoRow₂]
  have hsubset : M₁.rowSpace ≤ CodeSpace.dualCode M₂.rowSpace := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨i, rfl⟩
    show M₁.row i ∈ M₂.rowSpace.orthogonalBilin (dotProductBilin _ _)
    rw [Submodule.mem_orthogonalBilin_iff]
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨j, rfl⟩
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply, dotProduct_comm]
      exact h_orth i j
    · simp [LinearMap.IsOrtho, dotProductBilin_apply_apply]
    · intro a b _ _ ha hb
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply] at ha hb ⊢
      rw [add_dotProduct, ha, hb, zero_add]
    · intro a b _ hb
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply] at hb ⊢
      rw [smul_dotProduct, hb, smul_zero]
  exact hsubset hx

def CSS_pair.of_matrices [NeZero k₁] [NeZero k₂] (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
(h_orth : H₁.mutually_orth_rows H₂) (H₁_ind : LinearIndependent (ZMod 2) (H₁.row)) (H₂_ind : LinearIndependent (ZMod 2) (H₂.row)) : CSS_pair n k₁ k₂ where
  C₁ := H₁.toCodeSpace.dualCode
  C₂ := H₂.toCodeSpace.dualCode
  H_dual := by
    rw [dual_dual_eq]
    apply toCodeSpace_subset_dual_of_orth_gen _ _ h_orth
  H₁ := H₁
  H₂ := H₂
  hpc₁ := by
    unfold CodeSpace.parityCheckMatrixOf
    rw [dual_dual_eq]
    apply CodeSpace.generatorMatrixOf_toCodeSpace H₁_ind
  hpc₂ := by
    unfold CodeSpace.parityCheckMatrixOf
    rw [dual_dual_eq]
    apply CodeSpace.generatorMatrixOf_toCodeSpace H₂_ind
  nt₁ := NeZero.pos _
  nt₂ := NeZero.pos _
