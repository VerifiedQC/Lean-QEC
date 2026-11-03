import QuantumInfo.States.Pure.Qubit
import LeanQEC.ForPhysLib.PiProd
import LeanQEC.ForPhysLib.Unitary

open Matrix

noncomputable section

abbrev Qubits (n : ℕ) := Fin n → Qubit

notation "𝐔ₙ[" n "]" => Matrix.unitaryGroup (Qubits n) ℂ

variable {n n₁ n₂ : ℕ}

abbrev qubitsAppend (n₁ n₂ : ℕ) : Qubits n₁ × Qubits n₂ ≃ Qubits (n₁ + n₂) :=
  Fin.appendEquiv n₁ n₂

def qubitsSplit {k : ℕ} (hk : k ≤ n) : Qubits k × Qubits (n - k) ≃ Qubits n :=
  (qubitsAppend k (n - k)).trans
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' hk)) (Equiv.refl Qubit))

def ancillaEmbedding {k : ℕ} (hk : k ≤ n) : Matrix (Qubits n) (Qubits k) ℂ :=
  fun x y => if (qubitsSplit hk).symm x = (y, 0) then 1 else 0

def unitary_nkron (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) : 𝐔ₙ[n₁ + n₂] :=
  unitaryReindex (qubitsAppend n₁ n₂) (a ⊗ᵤ b)

notation a:60 " ⊗ₙ " b:60 => unitary_nkron a b

lemma unitary_nkron_val (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) :
    ((a ⊗ₙ b : 𝐔ₙ[n₁ + n₂]) : Matrix (Qubits (n₁ + n₂)) (Qubits (n₁ + n₂)) ℂ) =
      reindex (qubitsAppend n₁ n₂) (qubitsAppend n₁ n₂)
        (kroneckerMap (· * ·) (a : Matrix _ _ ℂ) (b : Matrix _ _ ℂ)) :=
  rfl

lemma mul_nkrons (U₁ U₁' : 𝐔ₙ[n₁]) (U₂ U₂' : 𝐔ₙ[n₂]) :
    (U₁ ⊗ₙ U₂) * (U₁' ⊗ₙ U₂') = (U₁ * U₁') ⊗ₙ (U₂ * U₂') := by
  simp only [unitary_nkron, ← map_mul]
  congr 1
  ext1
  simp [unitary_kron, Matrix.mul_kronecker_mul]

@[simp]
lemma unitary_nkron_one_one : (1 : 𝐔ₙ[n₁]) ⊗ₙ (1 : 𝐔ₙ[n₂]) = 1 := by
  simp [unitary_nkron]

lemma circle_smul_nkron (z : Circle) (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) :
    (z • a) ⊗ₙ b = z • (a ⊗ₙ b) := by
  ext1
  simp [unitary_nkron_val, Matrix.smul_kronecker]

lemma nkron_circle_smul (z : Circle) (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) :
    a ⊗ₙ (z • b) = z • (a ⊗ₙ b) := by
  ext1
  simp [unitary_nkron_val, Matrix.kronecker_smul]

/- Allows us to collect all the tensors into an append, which is easier to work with -/
lemma unitaryPiProd_nkron (m₁ : Fin n₁ → 𝐔[Qubit]) (m₂ : Fin n₂ → 𝐔[Qubit]) :
    unitaryPiProd m₁ ⊗ₙ unitaryPiProd m₂ = unitaryPiProd (Fin.append m₁ m₂) := by
  ext1
  rw [unitary_nkron_val, unitaryPiProd_val, unitaryPiProd_val, unitaryPiProd_val, piProd_append]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

lemma herm_of_qubit_tensor_herm (m : Fin n → 𝐔[Qubit])
    (Hm : ∀ x, (m x : Matrix Qubit Qubit ℂ).IsHermitian) :
    (unitaryPiProd m : Matrix (Qubits n) (Qubits n) ℂ).IsHermitian :=
  IsHermitian.piProd Hm

def n_controllize (U : 𝐔ₙ[n]) : 𝐔ₙ[n + 1] :=
  unitaryReindex (Fin.consEquiv (fun _ => Qubit)) (Qubit.controllize U)

notation "Cₙ[" g "]" => n_controllize g

lemma n_controllize_mul (U V : 𝐔ₙ[n]) : Cₙ[U * V] = Cₙ[U] * Cₙ[V] := by
  simp only [n_controllize, ← Qubit.controllize_mul, map_mul]

end
