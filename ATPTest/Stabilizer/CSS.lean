import ATPTest.Stabilizer.Basic
import ATPTest.Classical_EC.Basic

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

variable {M : Matrix (Fin n) (Fin n) (ZMod 2)}

#check LinearMap.ker M.toLin'

lemma matrix_ker_sdiff_rowspace_nonempty {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
  ((LinearMap.ker M₁.toLin') \ (Submodule.span (ZMod 2) (Set.range M₂.row)) : Set (Fin n → (ZMod 2))).toFinset.Nonempty := sorry

noncomputable def CSS_pair.dX (C : CSS_pair n k₁ k₂) : ℕ := Finset.min' (Finset.image hammingNorm ((LinearMap.ker C.H₂.toLin') \ Submodule.span (ZMod 2) (Set.range C.H₁.row) : Set (Fin n → (ZMod 2))).toFinset)
 (Finset.image_nonempty.2 (matrix_ker_sdiff_rowspace_nonempty C.nt₂ C.nt₁ _ _))

noncomputable def CSS_pair.dZ (C : CSS_pair n k₁ k₂) : ℕ := Finset.min' (Finset.image hammingNorm ((LinearMap.ker C.H₁.toLin') \ Submodule.span (ZMod 2) (Set.range C.H₂.row) : Set (Fin n → (ZMod 2))).toFinset)
 (Finset.image_nonempty.2 (matrix_ker_sdiff_rowspace_nonempty C.nt₁ C.nt₂ _ _))



theorem CSS.toBSM_dist_eq (C : CSS_pair n k₁ k₂) :
  C.toBSM.distance (Nat.add_pos_left C.nt₁ _) = min C.dX C.dZ := sorry
