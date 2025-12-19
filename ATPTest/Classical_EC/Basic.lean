import ATPTest.States.BitVec

abbrev CodeSpace (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

variable {n : ℕ}

def codeFromGenerators (G : Finset (Fin n → ZMod 2)) : CodeSpace n :=
Submodule.span (ZMod 2) G

def CodeSpace.dualCode (C : CodeSpace n) : CodeSpace n := (C.orthogonalBilin (dotProductBilin _ _))

def weight (w : Fin n → ZMod 2) : ℕ := hammingNorm w

def zeroVec : Fin n → ZMod 2 := 0

noncomputable section

instance CodeSpace_fintype (C : CodeSpace n) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance

def CodeSpace.toFinset (C : CodeSpace n) : Finset (Fin n → ZMod 2) :=
  (C : Set (Fin n → ZMod 2)).toFinset

def CodeSpace.nonzero (C : CodeSpace n) : Finset (Fin n → ZMod 2) := (C.toFinset).filter (fun v => v != 0)

def CodeSpace.selfDual (C : CodeSpace n) : Prop := C.toFinset ⊆ C.dualCode.toFinset

def CodeSpace.nontrivial (C : CodeSpace n) : Prop := Finset.Nonempty C.nonzero

def CodeSpace.distance (C : CodeSpace n) (nt : C.nontrivial) : ℕ :=
  Finset.min' (C.nonzero.image weight) (Finset.image_nonempty.2 nt)

variable {α : Type*} [Fintype α]

lemma injective_of_linearIndependent {ι} {s : ι → (Fin n → ZMod 2)} (hlin : LinearIndependent (ZMod 2) s) : Function.Injective s := sorry

def CodeSpace.generatorMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2))
  : Prop := (LinearIndependent (ZMod 2) (fun r => G r)) ∧ Submodule.span (ZMod 2) (Finset.image (fun r => G r) Finset.univ) = C

lemma CodeSpace.generatorMatrixOf_span_map_eq {C : CodeSpace n} {G : Matrix α (Fin n) (ZMod 2)} (hgen : C.generatorMatrixOf G) :
  Submodule.span (ZMod 2) (Finset.map ⟨(fun r => G r), injective_of_linearIndependent hgen.1⟩ Finset.univ) = C := by
  convert hgen.2 using 3
  exact (Finset.map_eq_image _ _)

def CodeSpace.parityCheckMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2))
  : Prop := C.dualCode.generatorMatrixOf G


lemma Finset.mem_map_univ {ι τ : Type*} [Fintype ι] [DecidableEq τ] {a : ι} {f : ι ↪ τ} : f a ∈ Finset.map f Finset.univ := sorry

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
    rw [Matrix.mulVec_eq_sum, Matrix.transpose_transpose]
    unfold v
    rw [Finset.sum_map]
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
  rw [←hv]
  rw [Finset.sum_map]
  congr
  ext1 a
  simp only [Function.Embedding.coeFn_mk, op_smul_eq_smul]
  unfold f
  have hw : G a ∈ Set.range mmap := by
    use a
    rfl
  simp [hw]
  congr
  have:= mmap.right_inv_of_invOfMemRange a
  convert this
