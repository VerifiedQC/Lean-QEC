import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

noncomputable section

abbrev mat2 := Matrix (Fin 2) (Fin 2) ℂ

def rawI : mat2 := !![1, 0; 0, 1]
def rawX : mat2 := !![0, 1; 1, 0]
def rawY : mat2 := !![0, -Complex.I; Complex.I, 0]
def rawZ : mat2 := !![1, 0; 0, -1]

def raw_Paulis : Finset mat2 := {rawI, rawX, rawY, rawZ}

lemma raw_paulis_distinct {p1 p2 : raw_Paulis} (H: p1 ≠ p2) (z : ℂ) :
  z • p1.val ≠ p2 := by sorry
