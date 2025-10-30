import QuantumInfo.Finite.Unitary
import ATPTest.States.BitVec
import QuantumInfo.Finite.Qubit.Basic
open Matrix

section unitary

theorem reindex_unitary {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  (e : a ≃ b) (U : 𝐔[a]) : (reindex e e) U.1 ∈ unitaryGroup b ℂ := by
  have h_mem := U.2
  rw [mem_unitaryGroup_iff] at h_mem ⊢
  simp
  rw [star_eq_conjTranspose, conjTranspose_submatrix]
  simp [←star_eq_conjTranspose, h_mem]

def unitary_fin_equiv {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (h: a ≃ b) :(𝐔[a] ≃ 𝐔[b]) where
  toFun U := ⟨(reindex h h) U.1, reindex_unitary _ _⟩
  invFun U := ⟨(Matrix.reindex h.symm h.symm) U.1, reindex_unitary _ _⟩
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    simp

notation "𝐔ₙ[" n "]" => Matrix.unitaryGroup (BitVec n) ℂ

open Kronecker in
theorem nkron_unitary {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) : normalized_kron a.val b.val ∈ 𝐔ₙ[n₁ + n₂] := by
  rw [normalized_kron, normalize_mat]
  exact reindex_unitary bits_cat ⟨_, kron_unitary a b⟩

open Kronecker in
def unitary_nkron {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) : 𝐔ₙ[n₁ + n₂] := ⟨_, nkron_unitary a b⟩

notation a:60 " ⊗ₙ " b:60 => unitary_nkron a b

def unitary_n_nkron {n : ℕ} (hn : 0 < n) (m : Fin n → 𝐔ₙ[1]) : 𝐔ₙ[n] :=
match n with
| 0 => by contradiction
| 1 => (m 0)
| n₀+2 => (@unitary_nkron (n₀+1) 1 (unitary_n_nkron (by norm_num) (λ (x : Fin (n₀+1)) => m ⟨x.val + 1, by simp [x.isLt]⟩)) (m 0))
