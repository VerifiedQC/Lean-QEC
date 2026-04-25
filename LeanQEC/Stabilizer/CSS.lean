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

private lemma finset_min_eq_of_forall_exists_le {s t : Finset ℕ}
    (hst : ∀ a ∈ s, ∃ b ∈ t, b ≤ a)
    (hts : ∀ b ∈ t, ∃ a ∈ s, a ≤ b) :
    s.min = t.min := by
  apply le_antisymm
  · rw [Finset.le_min_iff]
    intro b hb
    rcases hts b hb with ⟨a, ha, hab⟩
    exact (Finset.min_le ha).trans (WithTop.coe_le_coe.2 hab)
  · rw [Finset.le_min_iff]
    intro a ha
    rcases hst a ha with ⟨b, hb, hba⟩
    exact (Finset.min_le hb).trans (WithTop.coe_le_coe.2 hba)

private lemma min_with_fallback_union_eq_min {s t : Finset ℕ} {n : ℕ}
    (hs : ∀ a ∈ s, a ≤ n) (ht : ∀ a ∈ t, a ≤ n) :
    (match (s ∪ t).min with
      | ⊤ => n + 1
      | some a => a) =
    min
      (match s.min with
        | ⊤ => n + 1
        | some a => a)
      (match t.min with
        | ⊤ => n + 1
        | some a => a) := by
  rw [Finset.min_union]
  cases hsmin : s.min with
  | top =>
      cases htmin : t.min with
      | top => simp
      | coe b =>
          have hb_mem : b ∈ t := Finset.mem_of_min htmin
          have hb_le : b ≤ n := ht b hb_mem
          simp
          exact Nat.le_succ_of_le hb_le
  | coe a =>
      have ha_mem : a ∈ s := Finset.mem_of_min hsmin
      have ha_le : a ≤ n := hs a ha_mem
      cases htmin : t.min with
      | top =>
          simp
          exact Nat.le_succ_of_le ha_le
      | coe b =>
          simp

private lemma CSS_BSM_rowSpace_iff
    (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
    (x z : Fin n → ZMod 2) :
    (x, z) ∈ (CSS_BSM H₁ H₂).rowSpace ↔
      x ∈ H₂.rowSpace ∧ z ∈ H₁.rowSpace := by
  constructor
  · intro h
    let prodRows : Submodule (ZMod 2) (BinSympPauli n) :=
    {
      carrier := {bsp | bsp.1 ∈ H₂.rowSpace ∧ bsp.2 ∈ H₁.rowSpace}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      smul_mem' := by
        intro a b hb
        exact ⟨Submodule.smul_mem _ a hb.1, Submodule.smul_mem _ a hb.2⟩
    }
    have hle : (CSS_BSM H₁ H₂).rowSpace ≤ prodRows := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · constructor
        · change (Fin.append (fun (_ : Fin k₁) => (fun _ => 0)) H₂ (Fin.castAdd k₂ i₁)) ∈ H₂.rowSpace
          rw [Fin.append_left]
          exact Submodule.zero_mem _
        · simpa [CSS_BSM, BinSympMatrix.row, Matrix.row] using
            (Matrix.row_mem_rowSpace (M := H₁) (i := i₁))
      · constructor
        · simpa [CSS_BSM, BinSympMatrix.row, Matrix.row] using
            (Matrix.row_mem_rowSpace (M := H₂) (i := i₂))
        · change (Fin.append H₁ (fun (_ : Fin k₂) => (fun _ => 0)) (Fin.natAdd k₁ i₂)) ∈ H₁.rowSpace
          rw [Fin.append_right]
          exact Submodule.zero_mem _
    exact hle h
  · rintro ⟨hx, hz⟩
    have hx_pair : (x, 0) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (y, 0) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.natAdd k₁ i, ?_⟩
        ext j <;> simp [CSS_BSM, BinSympMatrix.row, Matrix.row]
      · exact Submodule.zero_mem ((CSS_BSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((CSS_BSM H₁ H₂).rowSpace) a hy
    have hz_pair : (0, z) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (0, y) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.castAdd k₂ i, ?_⟩
        ext j <;> simp [CSS_BSM, BinSympMatrix.row, Matrix.row]
      · exact Submodule.zero_mem ((CSS_BSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((CSS_BSM H₁ H₂).rowSpace) a hy
    simpa [Prod.ext_iff] using
      Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) hx_pair hz_pair

private lemma zmod2_val_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a.1 = 1 := by
  have hlt : a.1 < 2 := a.2
  have hne : a.1 ≠ 0 := by simpa using ha
  omega

private lemma zmod2_or_val_ge_left (a b : ZMod 2) : a.1 ≤ (ZMod2_or a b).1 := by
  by_cases ha : a = 0
  · simp [ha, ZMod2_or]
  · have h_or_ne : ZMod2_or a b ≠ 0 := by
      intro h_or
      exact ha ((ZMod2_or_eq_zero_iff a b).1 h_or).1
    rw [zmod2_val_eq_one_of_ne_zero a ha, zmod2_val_eq_one_of_ne_zero (ZMod2_or a b) h_or_ne]

private lemma zmod2_or_val_ge_right (a b : ZMod 2) : b.1 ≤ (ZMod2_or a b).1 := by
  by_cases hb : b = 0
  · simp [hb, ZMod2_or]
  · have h_or_ne : ZMod2_or a b ≠ 0 := by
      intro h_or
      exact hb ((ZMod2_or_eq_zero_iff a b).1 h_or).2
    rw [zmod2_val_eq_one_of_ne_zero b hb, zmod2_val_eq_one_of_ne_zero (ZMod2_or a b) h_or_ne]

private lemma hammingNorm_le_union_weight_left'
    (v₁ v₂ : Fin n → ZMod 2) :
    hammingNorm v₁ ≤ union_weight v₁ v₂ := by
  let v : Fin n → ZMod 2 := fun i => ZMod2_or (v₁ i) (v₂ i)
  have hv_eq : hammingNorm v = ∑ i, (v i).1 := by
    refine le_antisymm
      ((weight_le_disj (z := v) (k := ∑ i, (v i).1)).2 le_rfl)
      ((weight_le_disj (z := v) (k := hammingNorm v)).1 le_rfl)
  rw [weight_le_disj]
  rw [show union_weight v₁ v₂ = hammingNorm v by rfl, hv_eq]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact zmod2_or_val_ge_left (v₁ i) (v₂ i)

private lemma hammingNorm_le_union_weight_right'
    (v₁ v₂ : Fin n → ZMod 2) :
    hammingNorm v₂ ≤ union_weight v₁ v₂ := by
  let v : Fin n → ZMod 2 := fun i => ZMod2_or (v₁ i) (v₂ i)
  have hv_eq : hammingNorm v = ∑ i, (v i).1 := by
    refine le_antisymm
      ((weight_le_disj (z := v) (k := ∑ i, (v i).1)).2 le_rfl)
      ((weight_le_disj (z := v) (k := hammingNorm v)).1 le_rfl)
  rw [weight_le_disj]
  rw [show union_weight v₁ v₂ = hammingNorm v by rfl, hv_eq]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact zmod2_or_val_ge_right (v₁ i) (v₂ i)

set_option maxHeartbeats 0 in
theorem CSS.toBSM_dist_eq (C : CSS_pair n k₁ k₂) :
  C.toBSM.distance (Nat.add_pos_left C.nt₁ _) = min C.dX C.dZ := by
  let xWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace).toFinset)
  let zWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace).toFinset)
  let bsmWeights : Finset ℕ :=
    Finset.image BinSympPauli.weight C.toBSM.undetectable_set
  have hbsm_min : bsmWeights.min = (xWeights ∪ zWeights).min := by
    apply finset_min_eq_of_forall_exists_le
    · intro d hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : C.toBSM.undetectable bsp := by
        simpa [BinSympMatrix.undetectable_set] using hbsp
      rcases hbsp' with ⟨hcomm, hnot_row⟩
      have hx_ker : bsp.1 ∈ LinearMap.ker C.H₁.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.castAdd k₂ i)
        simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd, Matrix.row] using this
      have hz_ker : bsp.2 ∈ LinearMap.ker C.H₂.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.natAdd k₁ i)
        simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd, Matrix.row] using this
      have hnot_or : bsp.1 ∉ C.H₂.rowSpace ∨ bsp.2 ∉ C.H₁.rowSpace := by
        by_contra h
        simp only [not_or, not_not] at h
        apply hnot_row
        exact (CSS_BSM_rowSpace_iff C.H₁ C.H₂ bsp.1 bsp.2).2 ⟨h.1, h.2⟩
      rcases hnot_or with hx_not | hz_not
      · refine ⟨hammingNorm bsp.1, ?_, ?_⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨bsp.1, ?_, rfl⟩
          simp [hx_ker, hx_not]
        · simpa [BinSympPauli.weight] using hammingNorm_le_union_weight_left' bsp.1 bsp.2
      · refine ⟨hammingNorm bsp.2, ?_, ?_⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨bsp.2, ?_, rfl⟩
          simp [hz_ker, hz_not]
        · simpa [BinSympPauli.weight] using hammingNorm_le_union_weight_right' bsp.1 bsp.2
    · intro d hd
      rcases Finset.mem_union.1 hd with hd | hd
      · rcases Finset.mem_image.1 hd with ⟨z, hz, rfl⟩
        have hz_mem : z ∈ (LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace := by
          simpa using hz
        have hz_ker : z ∈ LinearMap.ker C.H₂.toLin' := hz_mem.1
        have hz_not : z ∉ C.H₁.rowSpace := by
          exact hz_mem.2
        refine ⟨BinSympPauli.weight ((0 : Fin n → ZMod 2), z), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨((0 : Fin n → ZMod 2), z), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable ((0 : Fin n → ZMod 2), z) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · simp [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd]
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₂ z).1 hz_ker i₂
                simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd] using this
            · intro hrow
              exact hz_not ((CSS_BSM_rowSpace_iff C.H₁ C.H₂ 0 z).1 hrow).2
          simpa [BinSympMatrix.undetectable_set] using hbsp
        · simpa [BinSympPauli.weight] using (union_weight_zero_left z).le
      · rcases Finset.mem_image.1 hd with ⟨x, hx, rfl⟩
        have hx_mem : x ∈ (LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace := by
          simpa using hx
        have hx_ker : x ∈ LinearMap.ker C.H₁.toLin' := hx_mem.1
        have hx_not : x ∉ C.H₂.rowSpace := by
          exact hx_mem.2
        refine ⟨BinSympPauli.weight (x, (0 : Fin n → ZMod 2)), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨(x, (0 : Fin n → ZMod 2)), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable (x, (0 : Fin n → ZMod 2)) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₁ x).1 hx_ker i₁
                simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd] using this
              · simp [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd]
            · intro hrow
              exact hx_not ((CSS_BSM_rowSpace_iff C.H₁ C.H₂ x 0).1 hrow).1
          simpa [BinSympMatrix.undetectable_set] using hbsp
        · simpa [BinSympPauli.weight] using (union_weight_zero_right x).le
  have hx_bound : ∀ d ∈ xWeights, d ≤ n := by
    intro d hd
    rcases Finset.mem_image.1 hd with ⟨z, _, rfl⟩
    simpa using (hammingNorm_le_card_fintype (x := z))
  have hz_bound : ∀ d ∈ zWeights, d ≤ n := by
    intro d hd
    rcases Finset.mem_image.1 hd with ⟨x, _, rfl⟩
    simpa using (hammingNorm_le_card_fintype (x := x))
  have hdist :
      C.toBSM.distance (Nat.add_pos_left C.nt₁ _) =
        (match bsmWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    rfl
  have hdx :
      C.dX =
        (match xWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    unfold CSS_pair.dX min_weight_ker_not_mem_rowspace
    rfl
  have hdz :
      C.dZ =
        (match zWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    unfold CSS_pair.dZ min_weight_ker_not_mem_rowspace
    rfl
  rw [hdist, hdx, hdz, hbsm_min]
  exact min_with_fallback_union_eq_min hx_bound hz_bound

theorem CSS.toBSM_undetectable_set_nonempty (C : CSS_pair n k₁ k₂)
    (h_dist : min C.dX C.dZ ≤ n) : C.toBSM.undetectable_set.Nonempty := by
  exact BinSympMatrix.undetectable_set_nonempty C.toBSM (Nat.add_pos_left C.nt₁ _) (by
    rwa [CSS.toBSM_dist_eq])

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
    · simp [LinearMap.IsOrtho]
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
