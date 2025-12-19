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
