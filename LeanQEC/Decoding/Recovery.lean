import LeanQEC.Decoding.PauliChannel

open Matrix MeasureTheory Kronecker
open scoped ComplexOrder

noncomputable section

section fidSum

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def nsq (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

def fidSum (w : ι × κ → ℂ) (φ : ι → ℂ) : ℝ := ∑ a, ‖∑ i, star (φ i) * w (i, a)‖ ^ 2

theorem nsq_nonneg (x : ι → ℂ) : 0 ≤ nsq x := Finset.sum_nonneg fun _ _ => by positivity

theorem dotProduct_star_self_eq_nsq (x : ι → ℂ) : star x ⬝ᵥ x = (nsq x : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem nsq_eq_re_dotProduct (x : ι → ℂ) : nsq x = (star x ⬝ᵥ x).re := by
  rw [dotProduct_star_self_eq_nsq, Complex.ofReal_re]

theorem nsq_mulVec_of_isometry [DecidableEq ι] {ι' : Type*} [Fintype ι'] {M : Matrix ι' ι ℂ}
    (hM : Mᴴ * M = 1) (x : ι → ℂ) : nsq (M *ᵥ x) = nsq x := by
  rw [nsq_eq_re_dotProduct, nsq_eq_re_dotProduct, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, hM, one_mulVec]

theorem nsq_smul (c : ℂ) (x : ι → ℂ) : nsq (c • x) = ‖c‖ ^ 2 * nsq x := by
  simp [nsq, mul_pow, Finset.mul_sum]

theorem nsq_eq_zero_iff (x : ι → ℂ) : nsq x = 0 ↔ x = 0 := by
  rw [nsq, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity]
  simp [funext_iff]

theorem fidSum_nonneg (w : ι × κ → ℂ) (φ : ι → ℂ) : 0 ≤ fidSum w φ :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem nsq_sub_proj (v φ : ι → ℂ) (hφ : nsq φ = 1) :
    nsq (v - (star φ ⬝ᵥ v) • φ) = nsq v - ‖star φ ⬝ᵥ v‖ ^ 2 := by
  have h1 : star φ ⬝ᵥ φ = 1 := by rw [dotProduct_star_self_eq_nsq, hφ]; simp
  obtain ⟨c, hc⟩ : ∃ c, star φ ⬝ᵥ v = c := ⟨_, rfl⟩
  have h2 : star v ⬝ᵥ φ = star c := by
    rw [← hc]
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul, star_star]
  have key : star (v - c • φ) ⬝ᵥ (v - c • φ) = star v ⬝ᵥ v - c * star c := by
    simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h1, h2, hc]
    ring
  rw [hc, nsq_eq_re_dotProduct, nsq_eq_re_dotProduct v, key, Complex.star_def, Complex.mul_conj,
    Complex.sub_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem nsq_sub_fidSum (w : ι × κ → ℂ) {φ : ι → ℂ} (hφ : nsq φ = 1) :
    nsq w - fidSum w φ =
      ∑ a, nsq ((fun i => w (i, a)) - (star φ ⬝ᵥ fun i => w (i, a)) • φ) := by
  simp only [nsq_sub_proj _ _ hφ, Finset.sum_sub_distrib]
  rw [nsq, Fintype.sum_prod_type_right]
  rfl

theorem fidSum_le (w : ι × κ → ℂ) {φ : ι → ℂ} (hφ : nsq φ = 1) : fidSum w φ ≤ nsq w := by
  have := nsq_sub_fidSum w hφ
  have h0 : 0 ≤ ∑ a, nsq ((fun i => w (i, a)) - (star φ ⬝ᵥ fun i => w (i, a)) • φ) :=
    Finset.sum_nonneg fun _ _ => nsq_nonneg _
  linarith

theorem fidSum_eq_iff (w : ι × κ → ℂ) {φ : ι → ℂ} (hφ : nsq φ = 1) :
    fidSum w φ = nsq w ↔ ∃ c : κ → ℂ, ∀ i a, w (i, a) = φ i * c a := by
  have hsum := nsq_sub_fidSum w hφ
  constructor
  · intro h
    rw [h, sub_self, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => nsq_nonneg _] at hsum
    refine ⟨fun a => star φ ⬝ᵥ fun i => w (i, a), fun i a => ?_⟩
    have := congrFun ((nsq_eq_zero_iff _).mp (hsum a (Finset.mem_univ a))) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
    rw [this, mul_comm]
  · rintro ⟨c, hc⟩
    have h1 : star φ ⬝ᵥ φ = 1 := by rw [dotProduct_star_self_eq_nsq, hφ]; simp
    have hz : ∀ a, (fun i => w (i, a)) - (star φ ⬝ᵥ fun i => w (i, a)) • φ = 0 := by
      intro a
      have hv : (fun i => w (i, a)) = c a • φ := funext fun i => by
        rw [hc, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [hv, dotProduct_smul, h1, smul_eq_mul, mul_one, sub_self]
    simp only [hz, (nsq_eq_zero_iff (0 : ι → ℂ)).mpr rfl, Finset.sum_const_zero] at hsum
    linarith

theorem re_trace_traceRight_vecMulVec (w : ι × κ → ℂ) (φ : ι → ℂ) :
    (trace (traceRight (vecMulVec w (star w)) * vecMulVec φ (star φ))).re = fidSum w φ := by
  have h : trace (traceRight (vecMulVec w (star w)) * vecMulVec φ (star φ)) =
      ∑ a, (∑ i, star (φ i) * w (i, a)) * star (∑ i, star (φ i) * w (i, a)) := by
    simp only [trace, diag, mul_apply, traceRight, of_apply, vecMulVec_apply, Pi.star_apply,
      star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h, fidSum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end fidSum

variable {n k m : ℕ} {C : StabCode n}

theorem prepAncilla_apply (k r : ℕ) (ρ : MState (Qubits k)) :
    prepAncilla k r ρ = ρ ⊗ᴹ MState.pure (Ket.basis (0 : Qubits r)) := by
  have h : (CPTPMap.ofEquiv (Equiv.prodPUnit (Qubits k)).symm :
      CPTPMap (Qubits k) (Qubits k × Unit)) ρ = ρ ⊗ᴹ MState.pure (Ket.basis ()) := by
    apply MState.ext_m
    ext ⟨i, u⟩ ⟨j, v⟩
    simp only [CPTPMap.ofEquiv_apply, Equiv.symm_symm, MState.relabel_m, Matrix.submatrix_apply,
      Equiv.prodPUnit_apply]
    change ρ.m i j = ρ.m i j * (MState.pure _).m u v
    simp [MState.pure_apply, Ket.apply, Ket.basis]
  simp only [prepAncilla, CPTPMap.compose_eq, h, CPTPMap.prod_apply_prod, CPTPMap.id_MState,
    CPTPMap.replacement_apply]

theorem conj_vecMulVec {ι ι' : Type*} [Fintype ι] (B : Matrix ι' ι ℂ) (v : ι → ℂ) :
    B * vecMulVec v (star v) * Bᴴ = vecMulVec (B *ᵥ v) (star (B *ᵥ v)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

theorem ancillaEmbedding_mulVec (hk : k ≤ n) (φ : Qubits k → ℂ) :
    ancillaEmbedding hk *ᵥ φ = (fun p : Qubits k × Qubits (n - k) => if p.2 = 0 then φ p.1 else 0) ∘
      (qubitsSplit hk).symm := by
  funext z
  simp only [mulVec, dotProduct, ancillaEmbedding, Function.comp_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ((qubitsSplit hk).symm z).1]
  · by_cases h : ((qubitsSplit hk).symm z).2 = 0 <;> simp [h, Prod.ext_iff]
  · intro b _ hb
    simp [Prod.ext_iff, Ne.symm hb]
  · simp

namespace StabCode.Encoder

/- The encoding isometry of an encoder. -/
def isom (e : C.Encoder k) : Matrix (Qubits n) (Qubits k) ℂ :=
  (e.U : Matrix (Qubits n) (Qubits n) ℂ) * ancillaEmbedding e.le

def amp (e : C.Encoder k) (y : Qubits n → ℂ) : Qubits k × Qubits (n - k) → ℂ :=
  fun ia => ((e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ *ᵥ y) (qubitsSplit e.le ia)

theorem U_isometry (e : C.Encoder k) :
    (e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * (e.U : Matrix (Qubits n) (Qubits n) ℂ) = 1 :=
  Unitary.star_mul_self_of_mem e.U.2

theorem U_coisometry (e : C.Encoder k) :
    (e.U : Matrix (Qubits n) (Qubits n) ℂ) * (e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = 1 :=
  Unitary.mul_star_self_of_mem e.U.2

theorem ancillaEmbedding_isometry (hk : k ≤ n) :
    (ancillaEmbedding hk)ᴴ * ancillaEmbedding hk = 1 := by
  ext y y'
  simp only [mul_apply, conjTranspose_apply, ancillaEmbedding, one_apply]
  rw [Fintype.sum_equiv (qubitsSplit hk).symm _ (fun p => star (if p = (y, 0) then (1 : ℂ) else 0) *
    if p = (y', 0) then 1 else 0) (fun x => rfl)]
  rw [Finset.sum_eq_single (y, 0)]
  · by_cases h : y = y' <;> simp [h, Prod.ext_iff]
  · intro b _ hb
    simp [hb]
  · simp

theorem isom_isometry (e : C.Encoder k) : e.isomᴴ * e.isom = 1 := by
  simp only [isom, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ, U_isometry, Matrix.one_mul,
    ancillaEmbedding_isometry]

theorem isom_mulVec_mem_space (e : C.Encoder k) (ψ : Qubits k → ℂ) : e.isom *ᵥ ψ ∈ C.space := by
  rw [← e.range_eq]
  exact ⟨ψ, by rw [Matrix.toLin'_apply]; rfl⟩

theorem exists_eq_isom_mulVec (e : C.Encoder k) {y : Qubits n → ℂ} (hy : y ∈ C.space) :
    ∃ ψ, y = e.isom *ᵥ ψ := by
  rw [← e.range_eq] at hy
  obtain ⟨ψ, rfl⟩ := hy
  exact ⟨ψ, by rw [Matrix.toLin'_apply]; rfl⟩

theorem isom_mulVec_conjTranspose_mulVec (e : C.Encoder k) {y : Qubits n → ℂ}
    (hy : y ∈ C.space) : e.isom *ᵥ (e.isomᴴ *ᵥ y) = y := by
  obtain ⟨ψ, rfl⟩ := e.exists_eq_isom_mulVec hy
  rw [mulVec_mulVec ψ e.isomᴴ e.isom, isom_isometry, one_mulVec]

theorem amp_isom_mulVec (e : C.Encoder k) (ψ : Qubits k → ℂ) :
    e.amp (e.isom *ᵥ ψ) = fun ia => if ia.2 = 0 then ψ ia.1 else 0 := by
  funext ia
  simp only [amp, isom, mulVec_mulVec, ← Matrix.mul_assoc, U_isometry, Matrix.one_mul]
  simp only [mulVec, dotProduct, ancillaEmbedding, Equiv.symm_apply_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_eq_single ia.1]
  · by_cases h : ia.2 = 0 <;> simp [h, Prod.ext_iff]
  · intro b _ hb
    simp [Prod.ext_iff, Ne.symm hb]
  · simp

theorem nsq_amp (e : C.Encoder k) (y : Qubits n → ℂ) : nsq (e.amp y) = nsq y := by
  have h : nsq (e.amp y) = nsq ((e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ *ᵥ y) :=
    (qubitsSplit e.le).sum_comp (fun x => ‖((e.U : Matrix _ _ ℂ)ᴴ *ᵥ y) x‖ ^ 2)
  rw [h, nsq_mulVec_of_isometry]
  rw [conjTranspose_conjTranspose, U_coisometry]

theorem amp_smul (e : C.Encoder k) (c : ℂ) (y : Qubits n → ℂ) : e.amp (c • y) = c • e.amp y := by
  funext ia
  simp [amp, mulVec_smul]

theorem encode_map_ketProj (e : C.Encoder k) (φ : Ket (Qubits k)) :
    e.encode.map (ketProj φ) = vecMulVec (e.isom *ᵥ φ.vec) (star (e.isom *ᵥ φ.vec)) := by
  have hm : ketProj φ = (MState.pure φ).m := by
    ext i j; simp [MState.pure_apply, vecMulVec_apply, Ket.apply]
  set v0 : Qubits k × Qubits (n - k) → ℂ := fun p => if p.2 = 0 then φ.vec p.1 else 0 with hv0
  have hk : (MState.pure φ ⊗ᴹ MState.pure (Ket.basis (0 : Qubits (n - k)))).m =
      vecMulVec v0 (star v0) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    change (MState.pure φ).m i j * (MState.pure (Ket.basis (0 : Qubits (n - k)))).m a b = _
    simp only [MState.pure_apply, vecMulVec_apply, hv0, Pi.star_apply]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, Ket.apply, Ket.basis, eq_comm]
  have hB : (e.U : Matrix (Qubits n) (Qubits n) ℂ) *ᵥ (v0 ∘ (qubitsSplit e.le).symm) =
      e.isom *ᵥ φ.vec := by
    rw [StabCode.Encoder.isom, ← mulVec_mulVec, ancillaEmbedding_mulVec]
  rw [hm, ← CPTPMap.mat_coe_eq_apply_mat]
  simp only [StabCode.Encoder.encode, CPTPMap.compose_eq, prepAncilla_apply, CPTPMap.ofEquiv_apply,
    CPTPMap.ofUnitary_eq_conj]
  change (e.U : Matrix _ _ ℂ) * ((MState.pure φ ⊗ᴹ MState.pure (Ket.basis 0)).m.submatrix
    (qubitsSplit e.le).symm (qubitsSplit e.le).symm) * (e.U : Matrix _ _ ℂ)ᴴ = _
  rw [hk, ← hB, ← conj_vecMulVec]
  rfl

theorem unencode_map (e : C.Encoder k) (Y : Matrix (Qubits n) (Qubits n) ℂ) :
    e.unencode.map Y = Matrix.traceRight (((e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * Y *
      (e.U : Matrix (Qubits n) (Qubits n) ℂ)).submatrix (qubitsSplit e.le) (qubitsSplit e.le)) := by
  change Matrix.traceRight ((((e.U⁻¹ : 𝐔ₙ[n]) : Matrix (Qubits n) (Qubits n) ℂ) * Y *
    ((e.U⁻¹ : 𝐔ₙ[n]) : Matrix _ _ ℂ)ᴴ).submatrix (qubitsSplit e.le) (qubitsSplit e.le)) = _
  simp only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
    conjTranspose_conjTranspose]

theorem re_trace_unencode_map (e : C.Encoder k) (y : Qubits n → ℂ) (φ : Qubits k → ℂ) :
    (trace (e.unencode.map (vecMulVec y (star y)) * vecMulVec φ (star φ))).re =
      fidSum (e.amp y) φ := by
  have h : (e.U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * vecMulVec y (star y) *
      (e.U : Matrix (Qubits n) (Qubits n) ℂ) =
      vecMulVec ((e.U : Matrix _ _ ℂ)ᴴ *ᵥ y) (star ((e.U : Matrix _ _ ℂ)ᴴ *ᵥ y)) := by
    rw [← conj_vecMulVec, conjTranspose_conjTranspose]
  rw [unencode_map, h, ← re_trace_traceRight_vecMulVec]
  rfl

def recoveryFid (e : C.Encoder k) (M : PauliGroup_group n) (ψ φ : Qubits k → ℂ) : ℝ :=
  fidSum (e.amp (pauliGroupMat M *ᵥ (e.isom *ᵥ ψ))) φ

theorem pauliGroupMat_isometry (M : PauliGroup_group n) :
    (pauliGroupMat M)ᴴ * pauliGroupMat M = 1 :=
  Unitary.star_mul_self_of_mem (M : 𝐔ₙ[n]).2

theorem nsq_amp_pauli_isom (e : C.Encoder k) (M : PauliGroup_group n) (ψ : Qubits k → ℂ) :
    nsq (e.amp (pauliGroupMat M *ᵥ (e.isom *ᵥ ψ))) = nsq ψ := by
  rw [nsq_amp, nsq_mulVec_of_isometry (pauliGroupMat_isometry M),
    nsq_mulVec_of_isometry e.isom_isometry]

theorem recoveryFid_nonneg (e : C.Encoder k) (M : PauliGroup_group n) (ψ φ : Qubits k → ℂ) :
    0 ≤ e.recoveryFid M ψ φ :=
  fidSum_nonneg _ _

theorem recoveryFid_le_one (e : C.Encoder k) (M : PauliGroup_group n) {ψ φ : Qubits k → ℂ}
    (hψ : nsq ψ = 1) (hφ : nsq φ = 1) : e.recoveryFid M ψ φ ≤ 1 := by
  have := fidSum_le (e.amp (pauliGroupMat M *ᵥ (e.isom *ᵥ ψ))) hφ
  rwa [nsq_amp_pauli_isom, hψ] at this

end StabCode.Encoder

end
