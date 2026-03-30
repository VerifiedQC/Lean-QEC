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

def CSS_pair.of_matrices [NeZero k₁] [NeZero k₂] (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
(h_dual : (CSS_BSM H₁ H₂).isCommuting) (H₁_ind : LinearIndependent (ZMod 2) (H₁.row)) (H₂_ind : LinearIndependent (ZMod 2) (H₂.row)) : CSS_pair n k₁ k₂ where
  C₁ := H₁.toCodeSpace.dualCode
  C₂ := H₂.toCodeSpace.dualCode
  H_dual := by
    have htoRow₁ : H₁.toCodeSpace = H₁.rowSpace := by
      ext x
      simp [Matrix.toCodeSpace, Matrix.rowSpace, Matrix.row]
    have htoRow₂ : H₂.toCodeSpace = H₂.rowSpace := by
      ext x
      simp [Matrix.toCodeSpace, Matrix.rowSpace, Matrix.row]
    have hkerdual : LinearMap.ker H₂.toLin' = CodeSpace.dualCode H₂.rowSpace := by
      ext z
      constructor
      · intro hz
        rw [CodeSpace.dualCode, Submodule.mem_orthogonalBilin_iff]
        intro y hy
        unfold Matrix.rowSpace at hy
        refine Submodule.span_induction
          (p := fun y _ => (dotProductBilin (ZMod 2) (ZMod 2)).IsOrtho y z) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          simpa [LinearMap.IsOrtho, dotProductBilin] using
            (mem_ker_iff_dotProd_rows_eq_zero H₂ z).1 hz i
        · simp [LinearMap.IsOrtho, dotProductBilin]
        · intro y₁ y₂ hy₁ hy₂ h₁ h₂
          have hy₁zero : y₁ ⬝ᵥ z = 0 := by
            simpa [LinearMap.IsOrtho, dotProductBilin] using h₁
          have hy₂zero : y₂ ⬝ᵥ z = 0 := by
            simpa [LinearMap.IsOrtho, dotProductBilin] using h₂
          simp [LinearMap.IsOrtho, dotProductBilin, dotProduct_add, hy₁zero, hy₂zero]
        · intro a y hy hyz
          fin_cases a <;> simpa [LinearMap.IsOrtho, dotProductBilin, hyz]
      · intro hz
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have hrow := hz (H₂.row i) Matrix.row_mem_rowSpace
        simpa [CodeSpace.dualCode, LinearMap.IsOrtho, dotProductBilin] using hrow
    have hrow_in_dual : ∀ r, H₁.row r ∈ CodeSpace.dualCode H₂.rowSpace := by
      intro r
      rw [← hkerdual, mem_ker_iff_dotProd_rows_eq_zero]
      intro i
      have hcomm := h_dual (Fin.castAdd k₂ r) (Fin.natAdd k₁ i)
      simpa [CSS_BSM, BinSympMatrix.rowProd, symplecticProd, BinSympMatrix.row, Fin.append, dotProduct_comm] using hcomm
    intro x hx
    have hxRow : x ∈ H₁.rowSpace := by
      have hx' : x ∈ (H₁.toCodeSpace.dualCode).dualCode := by
        simpa using hx
      have hx'' : x ∈ H₁.toCodeSpace := by
        rw [dual_dual_eq] at hx'
        exact hx'
      rw [htoRow₁] at hx''
      exact hx''
    rw [htoRow₂]
    exact Submodule.span_induction
      (p := fun y _ => y ∈ CodeSpace.dualCode H₂.rowSpace)
      (by
        rintro y ⟨r, rfl⟩
        exact hrow_in_dual r)
      (CodeSpace.dualCode H₂.rowSpace).zero_mem
      (by
        intro a b ha hb hdual_a hdual_b
        exact (CodeSpace.dualCode H₂.rowSpace).add_mem hdual_a hdual_b)
      (by
        intro c a ha hdual_a
        exact (CodeSpace.dualCode H₂.rowSpace).smul_mem c hdual_a)
      hxRow
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
