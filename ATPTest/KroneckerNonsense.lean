import Mathlib.Data.BitVec
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix

local instance fin_bits (m : ℕ) : Fintype (BitVec m) :=
  Fintype.ofEquiv (Fin (2 ^ m)) ((BitVec.equivFin (m := m)).symm)

def bits_cat {w₁ w₂} : BitVec w₁ × BitVec w₂ ≃ BitVec (w₁ + w₂) where
  toFun := fun (s1, s2) => BitVec.cast (by rw [Nat.add_comm]) (s2 ++ s1)
  invFun := fun s => (BitVec.extractLsb' 0 w₁ s,
    BitVec.extractLsb' w₁ w₂ s)
  left_inv := by
    intro s
    cases s with | _ s1 s2 =>
    apply Prod.ext
    · ext i ltw1_i; simp
      have H: (s2 ++ s1).getLsbD i = (s2 ++ s1)[i] := rfl
      rw [H, BitVec.getElem_append]
      simp [ltw1_i]
    · ext i ltw2_i; simp
      have H: (s2 ++ s1).getLsbD (w₁ + i) = (s2 ++ s1)[w₁ + i] := rfl
      rw [H, BitVec.getElem_append]
      have hfalse : ¬ w₁ + i < w₁ :=
        Nat.not_lt.mpr (Nat.le_add_right _ _)
      simp [hfalse]
  right_inv := by
    intro s
    ext i rg_i; simp
    rw [BitVec.getElem_append]
    by_cases H : i < w₁
    · simp [H]
      rfl
    · simp [H]
      rw [<- Nat.add_sub_assoc]
      · simp; rfl
      · exact not_lt.mp H

abbrev normalize_mat {n₁ m₁ n₂ m₂} :
  Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ ≃
  Matrix (BitVec (n₁ + m₁)) (BitVec (n₂ + m₂)) ℂ :=
  Matrix.reindex bits_cat bits_cat

def normalized_kron {n₁ m₁ n₂ m₂}
  (U₁ : Matrix (BitVec m₁) (BitVec n₁) ℂ)
  (U₂ : Matrix (BitVec m₂) (BitVec n₂) ℂ) :=
  normalize_mat (Matrix.kronecker U₁ U₂)

lemma normalize_mul {n₁ m₁ n₂ m₂ n₃ m₃}
  (U : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ)
  (U' : Matrix (BitVec n₂ × BitVec m₂) (BitVec n₃ × BitVec m₃) ℂ) :
  normalize_mat (U * U') =
  normalize_mat U * normalize_mat U' := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  apply Matrix.submatrix_mul
  exact bits_cat.symm.bijective

def toMat {t} : (t → ℂ) ≃ (Matrix t (BitVec 0) ℂ) where
  toFun := fun (v n _) => v n
  invFun := fun (m i) => m i 0
  left_inv := by
    rw [Function.LeftInverse]
    intro m; funext i
    rfl
  right_inv := by
    rw [Function.RightInverse]
    intro m
    apply Matrix.ext; intro i j; simp
    have H : j = 0#0 := by
      apply Subsingleton.elim
    rewrite [H]
    rfl

-- Aristotle
lemma mulvec_toMat {t u} {fin_u : Fintype u} (U : Matrix t u ℂ) (v : u -> ℂ) :
  toMat (U *ᵥ v) = U * (toMat v) := by
    -- By definition of matrix multiplication and the definitions of `toMat` and `tm_inv`, we can show that the equality holds elementwise.
    ext n; simp [Matrix.mulVec, toMat];
    -- By definition of matrix multiplication, we have:
    simp [Matrix.mul_apply, dotProduct]

def ket_prod {n₁ n₂}
    (v1 : BitVec n₁ → ℂ)
    (v2 : BitVec n₂ → ℂ) :=
  toMat.symm (normalized_kron (toMat v1) (toMat v2))

lemma kron_prod {n₁ m₁ n₂ m₂}
    (U₁ : Matrix (BitVec m₁) (BitVec n₁) ℂ)
    (U₂ : Matrix (BitVec m₂) (BitVec n₂) ℂ)
    (v₁ : BitVec n₁ → ℂ)
    (v₂ : BitVec n₂ → ℂ) :
  ket_prod (U₁ *ᵥ v₁) (U₂ *ᵥ v₂) =
  (normalized_kron U₁ U₂) *ᵥ (ket_prod v₁ v₂) := by
  rw [ket_prod, mulvec_toMat, mulvec_toMat]
  rw [normalized_kron, kronecker, Matrix.mul_kronecker_mul]
  have H : kroneckerMap (fun x1 x2 ↦ x1 * x2) U₁ U₂ = kronecker U₁ U₂ :=
    by rfl
  rw [H]
  have H' : kroneckerMap (fun x1 x2 ↦ x1 * x2) (toMat v₁) (toMat v₂) =
    kronecker (toMat v₁) (toMat v₂) := by rfl
  rw [H']
  rw [normalize_mul]
  rw [toMat.symm_apply_eq, mulvec_toMat, ket_prod, toMat.apply_symm_apply]
  rfl
