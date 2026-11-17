import LeanQEC.Unitary.Basic

open Matrix

section pstate

/- Unnormalized vectors in the `n`-qubit Hilbert space, as opposed to PhysLib's kets which are normalized -/
abbrev PState (n : ℕ) := Qubits n → ℂ

variable {n n₁ n₂ : ℕ}

noncomputable section

@[simp]
def PState.apply (ψ : PState n) (U : 𝐔ₙ[n]) : PState n := U.1.toLin' ψ

def PState.kron (ψ₁ : PState n₁) (ψ₂ : PState n₂) : PState (n₁ + n₂) :=
  fun s => ψ₁ ((qubitsAppend n₁ n₂).symm s).1 * ψ₂ ((qubitsAppend n₁ n₂).symm s).2

@[inherit_doc] notation a:60 " ⊗ₚ " b:60 => PState.kron a b

lemma PState.kron_val {ψ₁ : PState n₁} {ψ₂ : PState n₂} {x : Qubits (n₁ + n₂)} :
    (ψ₁ ⊗ₚ ψ₂) x = (ψ₁ ((qubitsAppend n₁ n₂).symm x).1) * (ψ₂ ((qubitsAppend n₁ n₂).symm x).2) :=
  rfl

@[simp]
lemma PState.kron_append (ψ₁ : PState n₁) (ψ₂ : PState n₂) (x : Qubits n₁) (y : Qubits n₂) :
    (ψ₁ ⊗ₚ ψ₂) (Fin.append x y) = ψ₁ x * ψ₂ y := by
  rw [PState.kron_val]
  have : (qubitsAppend n₁ n₂).symm (Fin.append x y) = (x, y) :=
    (qubitsAppend n₁ n₂).symm_apply_apply (x, y)
  rw [this]

theorem kron_mul_kron (ψ₁ : PState n₁) (ψ₂ : PState n₂) (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) :
    (ψ₁ ⊗ₚ ψ₂).apply (U₁ ⊗ₙ U₂) = (ψ₁.apply U₁) ⊗ₚ (ψ₂.apply U₂) := by
  ext s
  simp only [PState.apply, toLin'_apply, unitary_nkron_val, PState.kron_val, mulVec, dotProduct,
    reindex_apply, submatrix_apply, kroneckerMap_apply]
  rw [← (qubitsAppend n₁ n₂).sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply]
  ring

def PState.trivial : PState 0 := fun _ => 1

def pstate_n_kron (m : Fin n → Qubit → ℂ) : PState n :=
  fun s => ∏ i, m i (s i)

lemma pstate_n_kron_apply (um : Fin n → 𝐔[Qubit]) (km : Fin n → Qubit → ℂ) :
    (pstate_n_kron km).apply (unitaryPiProd um) =
      pstate_n_kron (fun i => (um i : Matrix Qubit Qubit ℂ) *ᵥ km i) := by
  simp only [PState.apply, toLin'_apply, unitaryPiProd_val]
  exact piProd_mulVec_prod _ _

lemma PState.kron_assoc {ψ₁ ψ₂ ψ₃ : PState 1} : (ψ₁ ⊗ₚ ψ₂) ⊗ₚ ψ₃ = ψ₁ ⊗ₚ (ψ₂ ⊗ₚ ψ₃) := by
  ext x
  simp only [PState.kron_val, qubitsAppend, Fin.appendEquiv, Equiv.coe_fn_symm_mk, mul_assoc]
  refine congrArg₂ (· * ·) (congrArg ψ₁ ?_) (congrArg₂ (· * ·) (congrArg ψ₂ ?_) (congrArg ψ₃ ?_)) <;>
    (funext i; congr 1; try (ext; simp))

open ComplexConjugate

@[simp]
def PState.dot (ψ₁ ψ₂ : PState n) : ℂ := ψ₁ ⬝ᵥ (conj ψ₂)

lemma PState.dot_star_symm (ψ₁ ψ₂ : PState n) : ψ₁.dot ψ₂ = conj (ψ₂.dot ψ₁) := by
  unfold PState.dot dotProduct
  simp_rw [starRingEnd_apply, star_sum, star_mul]
  simp

@[simp]
lemma starRingEnd_smul {R : Type u} [CommSemiring R] [StarRing R]
    {A : Type v} [CommSemiring A] [StarRing A] [SMul R A] [StarModule R A] (x : R) (y : A) :
    (starRingEnd A) (x • y) = ((starRingEnd R) x) • ((starRingEnd A) y) := by
  rw [starRingEnd_apply, star_smul, ← starRingEnd_apply, ← starRingEnd_apply]

@[simp]
def PState.orth (ψ₁ ψ₂ : PState n) : Prop := ψ₁.dot ψ₂ = 0

lemma PState.orth_symm {ψ₁ ψ₂ : PState n} :
    ψ₁.orth ψ₂ ↔ ψ₂.orth ψ₁ := by
  unfold PState.orth
  rw [PState.dot_star_symm]
  simp

@[simp]
lemma PState.dot_orth1 {ψ₁ ψ₂ : PState n} (h_orth : ψ₁.orth ψ₂) :
    ψ₁ ⬝ᵥ starRingEnd (Qubits n → ℂ) ψ₂ = 0 := h_orth

@[simp]
lemma PState.dot_orth2 {ψ₁ ψ₂ : PState n} (h_orth : ψ₁.orth ψ₂) :
    ψ₂ ⬝ᵥ starRingEnd (Qubits n → ℂ) ψ₁ = 0 := PState.orth_symm.1 h_orth

lemma PState.apply_eq {ψ : PState n} {U : 𝐔ₙ[n]} {i : Qubits n} :
    (ψ.apply U) i = (U.val.mulVec ψ) i := by rfl

lemma PState.apply_orth {ψ φ : PState n} (h_orth : ψ.orth φ) {U : 𝐔ₙ[n]} :
    (ψ.apply U).orth (φ.apply U) := by
  unfold PState.orth
  have h_dot : PState.dot (ψ.apply U) (φ.apply U) = PState.dot ψ φ := by
    unfold PState.dot dotProduct
    simp_rw [Pi.conj_apply, PState.apply_eq]
    exact unitary_inner_preserve _ _ _
  rw [h_dot]
  exact h_orth

@[simp]
lemma PState.apply_id {ψ : PState n} : ψ.apply 1 = ψ := by simp

lemma PState.apply_add (ψ φ : PState n) (U : 𝐔ₙ[n]) :
    (ψ + φ).apply U = ψ.apply U + φ.apply U := by
  simp [Matrix.mulVec_add]

lemma PState.apply_smul (a : ℂ) (ψ : PState n) (U : 𝐔ₙ[n]) :
    (a • ψ).apply U = a • (ψ.apply U) := by
  simp

end

end pstate
