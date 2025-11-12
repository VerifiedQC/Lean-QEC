import QuantumInfo.Finite.Unitary
import ATPTest.States.BitVec
import QuantumInfo.Finite.Qubit.Basic
import ATPTest.KroneckerLemmas
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

lemma normalize_dagger {a₁ b₁ a₂ b₂}
  (m : Matrix (BitVec a₁ × BitVec b₁) (BitVec a₂ × BitVec b₂) ℂ):
  (normalize_mat m)ᴴ = normalize_mat mᴴ := by
  rw [normalize_mat, normalize_mat]
  rw [conjTranspose_reindex]

--maybe unitary_nkron should have an underlying version using matrices?
lemma unitary_herm_of_kron_herm {n₁ n₂ : ℕ} {M₁ : 𝐔ₙ[n₁]} {M₂ : 𝐔ₙ[n₂]} (hM₁ : M₁.val.IsHermitian) (hM₂ : M₂.val.IsHermitian) :
  Matrix.IsHermitian (M₁ ⊗ₙ M₂).val := by
  simp [IsHermitian, unitary_nkron]
  rw [normalized_kron, kronecker, normalize_dagger]
  rw [Matrix.conjTranspose_kronecker]
  rw [hM₁, hM₂]

def herm_of_qubit_tensor_herm {n : ℕ} (hn : 0 < n) (m : Fin n → 𝐔ₙ[1]) (Hm : ∀ x, Matrix.IsHermitian (m x).1) :
  Matrix.IsHermitian (unitary_n_nkron hn m).1 := by
  induction n with
  | zero => contradiction
  | succ n ih => cases n
                 · simp [unitary_n_nkron, (Hm 0)]
                 · rw [unitary_n_nkron]
                   apply unitary_herm_of_kron_herm (ih _ _ _) (Hm 0)
                   exact fun x => (Hm ⟨x+1, by norm_num⟩)

noncomputable section

structure phase where
  z : ℂ
  z_norm : ‖z‖ = 1
deriving DecidableEq

instance : Coe phase ℂ where
  coe p := p.z

namespace Phase

def mul (p q : phase) : phase :=
  {
    z := p * q
    z_norm := by simp [p.z_norm, q.z_norm]
  }

instance : Mul phase where
  mul := mul

def phase_star (p : phase) : phase :=
  {
    z := star p
    z_norm := by simp [p.2]
  }


@[simp]
lemma phase_mul_eq {p q : phase} : p * q = ⟨p.1 * q.1, by simp [p.z_norm, q.z_norm]⟩ := by rfl

end Phase

def U_phase {n : ℕ} (U : 𝐔ₙ[n]) (z : phase) : 𝐔ₙ[n] := ⟨z.1 • U.val, by
  simp [unitary.mem_iff, smul_smul, mul_comm]
  rw [mul_comm, ←Complex.normSq_eq_conj_mul_self, Complex.coe_smul, Complex.normSq_eq_norm_sq, z.2]
  simp
⟩

@[simp]
def phase_id : phase :=
  {
    z := 1
    z_norm := by norm_num
  }

@[simp]
lemma U_phase_id {n : ℕ} {U : 𝐔ₙ[n]} : U_phase U phase_id = U := by
  simp [U_phase, phase_id]


def u_neg {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[n] := (U_phase U ⟨-1, by norm_num⟩)

def u_im {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[n] := (U_phase U ⟨Complex.I, by norm_num⟩)

def fin2prodbitvec_equiv {n : ℕ} : (Fin 2 × BitVec n) ≃ BitVec (1+n) := (beq.prodCongr (Equiv.refl _)).trans bits_cat

def n_controllize {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[1+n] := unitary_fin_equiv fin2prodbitvec_equiv (Qubit.controllize U)

notation "Cₙ[" g "]" => n_controllize g
