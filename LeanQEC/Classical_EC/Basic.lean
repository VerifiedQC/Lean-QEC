import LeanQEC.States.BitVec
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import LeanQEC.LinearAlgebra.RowspaceKernel

abbrev CodeSpace (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

variable {n : ℕ}

def codeFromGenerators (G : Finset (Fin n → ZMod 2)) : CodeSpace n :=
Submodule.span (ZMod 2) G

def Matrix.toCodeSpace {α : Type*} [Fintype α] (M : Matrix α (Fin n) (ZMod 2)) : CodeSpace n :=
  Submodule.span (ZMod 2) (Finset.univ.image (fun i => M i))

def CodeSpace.dualCode (C : CodeSpace n) : CodeSpace n := (C.orthogonalBilin (dotProductBilin _ _))

def zeroVec : Fin n → ZMod 2 := 0

noncomputable section


def CodeSpace.toFinset (C : CodeSpace n) : Finset (Fin n → ZMod 2) :=
  (C : Set (Fin n → ZMod 2)).toFinset

def CodeSpace.nonzero (C : CodeSpace n) : Finset (Fin n → ZMod 2) := (C.toFinset).filter (fun v => v != 0)

def CodeSpace.selfDual (C : CodeSpace n) : Prop := C.toFinset ⊆ C.dualCode.toFinset

def CodeSpace.nontrivial (C : CodeSpace n) : Prop := Finset.Nonempty C.nonzero

def CodeSpace.distance (C : CodeSpace n) (nt : C.nontrivial) : ℕ :=
  Finset.min' (C.nonzero.image hammingNorm) (Finset.image_nonempty.2 nt)

variable {α : Type*} [Fintype α]

--pass to aristotle later
lemma injective_of_linearIndependent {ι} {s : ι → (Fin n → ZMod 2)}
  (hlin : LinearIndependent (ZMod 2) s) : Function.Injective s := by
  apply (LinearIndependent.injective hlin)

def CodeSpace.generatorMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2))
  : Prop := (LinearIndependent (ZMod 2) G) ∧ Submodule.span (ZMod 2) (Finset.image (fun r => G r) Finset.univ) = C

lemma CodeSpace.generatorMatrixOf_span_map_eq {C : CodeSpace n} {G : Matrix α (Fin n) (ZMod 2)} (hgen : C.generatorMatrixOf G) :
  Submodule.span (ZMod 2) (Finset.map ⟨(fun r => G r), injective_of_linearIndependent hgen.1⟩ Finset.univ) = C := by
  convert hgen.2 using 3
  exact (Finset.map_eq_image _ _)

lemma CodeSpace.generatorMatrixOf_toCodeSpace {G : Matrix α (Fin n) (ZMod 2)} (hG : LinearIndependent (ZMod 2) (G.row)):
  G.toCodeSpace.generatorMatrixOf G := by
  unfold generatorMatrixOf
  refine' ⟨hG, rfl⟩




def CodeSpace.parityCheckMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2))
  : Prop := C.dualCode.generatorMatrixOf G

lemma CodeSpace.pc_prod_mem_dual (C : CodeSpace n) {H : Matrix α (Fin n) (ZMod 2)} (x : α) (hpc : C.parityCheckMatrixOf H) : H x ∈ C.dualCode := by
  unfold CodeSpace.parityCheckMatrixOf CodeSpace.generatorMatrixOf at hpc
  rw [←hpc.2]
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma CodeSpace.gm_prod_mem (C : CodeSpace n) {G : Matrix α (Fin n) (ZMod 2)} (x : α) (hgm : C.generatorMatrixOf G) : G x ∈ C := by
  unfold CodeSpace.generatorMatrixOf at hgm
  rw [←hgm.2]
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)


lemma Finset.mem_map_univ {ι τ : Type*} [Fintype ι] [DecidableEq τ] {a : ι} {f : ι ↪ τ} : f a ∈ Finset.map f Finset.univ := by
  rw [Finset.mem_map]
  exists a
  simp

theorem generatorMatrix_image_eq_CodeSpace (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2))
  (hgen : C.generatorMatrixOf G) (x : Fin n → ZMod 2) : x ∈ C ↔ ∃ v, G.transpose.mulVec v = x := by
  have hspan := CodeSpace.generatorMatrixOf_span_map_eq hgen
  let mmap : α ↪ (Fin n → ZMod 2) := ⟨(fun r => G r), injective_of_linearIndependent hgen.1⟩
  refine' ⟨fun h_mem => _, fun v => _⟩
  · rw [←hspan, Submodule.mem_span_finset] at h_mem
    obtain ⟨f, ⟨fsupp, hfx⟩⟩ := h_mem
    let v := fun (a : α) => f (G a)
    exists v
    convert hfx
    unfold v
    rw [Matrix.mulVec_eq_sum, Matrix.transpose_transpose,
    Finset.sum_map]
    congr --it just works
    simp
  rcases v with ⟨v, hv⟩
  rw [Matrix.mulVec_eq_sum, Matrix.transpose_transpose] at hv
  rw [←hspan, Submodule.mem_span_finset]
  let f := fun (w : Fin n → ZMod 2) => if hw : w ∈ ↑(Set.range ⇑mmap) then v (mmap.invOfMemRange ⟨w, hw⟩) else 0
  refine' ⟨f, ⟨_, _⟩⟩
  · unfold Function.support
    intro a ha
    simp only [ne_eq, Set.mem_setOf_eq] at ha
    by_cases arange: a ∈ Set.range ⇑mmap
    · rw [Set.mem_range] at arange
      obtain ⟨y, hy⟩ := arange
      simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
        Set.mem_range]
      exists y
    unfold f at ha
    simp [arange] at ha
  rw [←hv, Finset.sum_map]
  congr
  ext1 a
  simp only [Function.Embedding.coeFn_mk, op_smul_eq_smul]
  unfold f
  have hw : G a ∈ Set.range mmap := by
    use a
    rfl
  simp only [hw, ↓reduceDIte]
  congr
  have:= mmap.right_inv_of_invOfMemRange a
  convert this

theorem genMatrix_size_eq {k : ℕ} (C : CodeSpace n) (G : Matrix (Fin k) (Fin n) (ZMod 2))
  (hgen : C.generatorMatrixOf G) : Module.finrank (ZMod 2) C = k := by
  have:= hgen.2
  rw [←this]
  have:= (finrank_span_eq_card hgen.1) --just converting this got me something really weird
  rw [Fintype.card_fin] at this
  have h : Set.range G = (Finset.image G Finset.univ) := by simp
  rw [h] at this
  exact this

--horrible terrible aristotle proof that keeps breaking my build
lemma dual_finrank_eq {C : CodeSpace n} : Module.finrank (ZMod 2) C.dualCode = n - (Module.finrank (ZMod 2) C) := by
  let B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
    Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) (ZMod 2))
  have hdual : C.dualCode = B.orthogonal C := by
    ext x
    constructor
    · intro hx n₁ hn₁
      simpa [B, LinearMap.BilinForm.IsOrtho, Matrix.toBilin'_apply', dotProductBilin] using hx n₁ hn₁
    · intro hx n₁ hn₁
      simpa [B, LinearMap.BilinForm.IsOrtho, Matrix.toBilin'_apply', dotProductBilin] using hx n₁ hn₁
  have hB_refl : B.IsRefl := by
    intro x y hxy
    simpa [B, Matrix.toBilin'_apply', dotProduct_comm] using hxy
  have hB_nondeg : B.Nondegenerate := by
    simpa [B] using
      (Matrix.Nondegenerate.of_det_ne_zero
        (M := (1 : Matrix (Fin n) (Fin n) (ZMod 2)))
        (by simp)).toBilin'
  rw [hdual]
  simpa [Module.finrank_fin_fun] using LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nondeg hB_refl C
  /-
  -- By definition of dual code, we know that its dimension is equal to the dimension of the original code.
  have h_dual_dim : Module.finrank (ZMod 2) C.dualCode + Module.finrank (ZMod 2) C = n := by
    rw [ add_comm, CodeSpace.dualCode ];
    have := Submodule.finrank_quotient_add_finrank C;
    -- By definition of quotient space, we know that the dimension of the quotient space is equal to the dimension of the original space minus the dimension of the subspace.
    have h_quotient_dim : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ C) = Module.finrank (ZMod 2) (↥(Submodule.orthogonalBilin C (dotProductBilin (ZMod 2) (ZMod 2)))) := by
      have h_quotient_dim : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ C) = Module.finrank (ZMod 2) (↥(Submodule.dualAnnihilator C)) := by
        have h_quotient_dim : (C.dualAnnihilator ≃ₗ[ZMod 2] ((Fin n → ZMod 2) ⧸ C) →ₗ[ZMod 2] ZMod 2) := by
          exact (Submodule.dualQuotEquivDualAnnihilator C).symm;
        have := h_quotient_dim.finrank_eq; aesop;
      convert h_quotient_dim using 1;
      fapply LinearEquiv.finrank_eq;
      refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
      refine' { toFun := fun x => ⟨ _, _ ⟩, map_add' := _, map_smul' := _ };
      exact ( dotProductBilin ( ZMod 2 ) ( ZMod 2 ) ).flip x;
      all_goals simp_all +decide [ Function.Injective ];
      · exact fun w hw => by simpa [ dotProduct_comm ] using x.2 w hw;
      · intro a ha b hb hab; ext i; replace hab := congr_arg ( fun f => f ( Pi.single i 1 ) ) hab; aesop;
      · simp only [Function.Surjective, Subtype.exists, Submodule.mem_orthogonalBilin_iff,
        Subtype.forall, Submodule.mem_dualAnnihilator, Subtype.mk.injEq, exists_prop]
        intro a ha;
        -- By definition of dot product, we know that every linear functional can be represented as a dot product with some vector.
        obtain ⟨v, hv⟩ : ∃ v : Fin n → ZMod 2, ∀ w : Fin n → ZMod 2, a w = dotProduct w v := by
          use fun i => a ( Pi.single i 1 );
          intro w; rw [ show w = ∑ i, w i • Pi.single i 1 from by ext i; simp +decide [ Pi.single_apply ] ] ; simp +decide [ Finset.sum_apply, dotProduct ] ;
          simp +decide [ Pi.single_apply ];
        refine' ⟨ v, _, _ ⟩
        · intros n₁ hn₁
          unfold LinearMap.IsOrtho dotProductBilin
          simp only [LinearMap.coe_mk, AddHom.coe_mk]
          rw [← (hv n₁), (ha n₁ hn₁)]
        aesop
    rw [ add_comm, h_quotient_dim ] at this ; aesop;
  exact eq_tsub_of_add_eq h_dual_dim
  -/

theorem dual_dual_eq {C : CodeSpace n} : (C.dualCode).dualCode = C := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.le_orthogonalBilin_orthogonalBilin
    intros a b
    simp only [dotProductBilin_apply_apply, dotProduct_comm]
    exact fun x => x
  rw [dual_finrank_eq, dual_finrank_eq]
  have h_rank : Module.finrank (ZMod 2) C ≤ n := le_of_le_of_eq
    (Submodule.finrank_le _) (Module.finrank_fin_fun _)
  symm
  exact Nat.sub_sub_self h_rank

  theorem pc_size_eq {k : ℕ} (C : CodeSpace n) (H : Matrix (Fin k) (Fin n) (ZMod 2)) (hpc : C.parityCheckMatrixOf H)
   : k = n - Module.finrank (ZMod 2) C := by
   unfold CodeSpace.parityCheckMatrixOf at hpc
   rw [←genMatrix_size_eq C.dualCode H hpc]
   exact dual_finrank_eq

--PROVE DISTANCE IS MIN WT NONZERO VEC IN PARITY CHECK KERNEL
