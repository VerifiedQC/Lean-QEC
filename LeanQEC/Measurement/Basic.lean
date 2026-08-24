import LeanQEC.States.PState
import LeanQEC.Unitary.Paulis.Basic
import LeanQEC.Unitary.Paulis.PauliTrace
import LeanQEC.Stabilizer.Basic

open Matrix

structure Observable (d : Type*) [Fintype d] [DecidableEq d] where
  mat : Matrix d d ℂ
  herm : mat.IsHermitian

namespace Observable

noncomputable def eigenspace {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : Submodule ℂ (d → ℂ) :=
  Module.End.eigenspace (Matrix.toLin' O.mat) (k : ℂ)

@[simp]
lemma mem_eigenspace_iff {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (v : d → ℂ) :
    v ∈ O.eigenspace k ↔ O.mat *ᵥ v = (k : ℂ) • v := by
  simp [eigenspace]

/- We use this later to classically define the actual projectors -/
def isProjectorOnto {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (P : Matrix d d ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ LinearMap.range (Matrix.toLin' P) = O.eigenspace k

noncomputable def eigU {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) : Matrix d d ℂ := O.herm.eigenvectorUnitary

noncomputable def eigval {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) : d → ℝ := O.herm.eigenvalues

lemma eigU_mem {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    O.eigU ∈ Matrix.unitaryGroup d ℂ :=
  O.herm.eigenvectorUnitary.2

lemma star_eigU_mem {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    star O.eigU ∈ Matrix.unitaryGroup d ℂ :=
  Unitary.star_mem O.eigU_mem

lemma eigU_mul_star {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    O.eigU * star O.eigU = 1 :=
  Unitary.mul_star_self_of_mem O.eigU_mem

lemma star_mul_eigU {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    star O.eigU * O.eigU = 1 :=
  Unitary.star_mul_self_of_mem O.eigU_mem

/- Wrapper for the spectral theorem in Mathlib -/
lemma spectral_decomp {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    O.mat = O.eigU * diagonal (fun i => (O.eigval i : ℂ)) * star O.eigU := by
  conv_lhs => rw [O.herm.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

noncomputable def coords {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (v : d → ℂ) : d → ℂ := star O.eigU *ᵥ v

lemma eigU_mulVec_coords {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (v : d → ℂ) : O.eigU *ᵥ O.coords v = v := by
  rw [coords, Matrix.mulVec_mulVec, O.eigU_mul_star, Matrix.one_mulVec]

lemma coords_eigU_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (y : d → ℂ) : O.coords (O.eigU *ᵥ y) = y := by
  rw [coords, Matrix.mulVec_mulVec, O.star_mul_eigU, Matrix.one_mulVec]

lemma coords_injective {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) {v w : d → ℂ} (h : O.coords v = O.coords w) : v = w := by
  rw [← O.eigU_mulVec_coords v, ← O.eigU_mulVec_coords w, h]

noncomputable def diagProj {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : Matrix d d ℂ :=
  diagonal (fun i => if O.eigval i = k then (1 : ℂ) else 0)

noncomputable def projMat {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : Matrix d d ℂ := O.eigU * O.diagProj k * star O.eigU

lemma coords_projMat_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (v : d → ℂ) :
    O.coords (O.projMat k *ᵥ v) = O.diagProj k *ᵥ O.coords v := by
  rw [projMat, coords, coords, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, O.star_mul_eigU, Matrix.one_mulVec]

lemma diagProj_mulVec_apply {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (y : d → ℂ) (i : d) :
    (O.diagProj k *ᵥ y) i = if O.eigval i = k then y i else 0 := by
  rw [diagProj, Matrix.mulVec_diagonal]
  split <;> simp

lemma coords_mat_mulVec {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (v : d → ℂ) (i : d) :
    O.coords (O.mat *ᵥ v) i = (O.eigval i : ℂ) * O.coords v i := by
  conv_lhs => rw [coords, spectral_decomp O]
  rw [Matrix.mulVec_mulVec]
  have h : star O.eigU * (O.eigU * diagonal (fun i => (O.eigval i : ℂ)) * star O.eigU)
      = diagonal (fun i => (O.eigval i : ℂ)) * star O.eigU := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, O.star_mul_eigU, Matrix.one_mul]
  rw [h, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  rfl

lemma coords_smul {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (c : ℂ) (v : d → ℂ) (i : d) :
    O.coords (c • v) i = c * O.coords v i := by
  simp [coords, Matrix.mulVec_smul]

lemma mem_eigenspace_iff_coords {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (v : d → ℂ) :
    v ∈ O.eigenspace k ↔ ∀ i, O.eigval i ≠ k → O.coords v i = 0 := by
  rw [mem_eigenspace_iff]
  constructor
  · intro h i hi
    have hc := congrArg (fun w => O.coords w i) h
    simp only [coords_mat_mulVec, coords_smul] at hc
    have hne : (O.eigval i : ℂ) - (k : ℂ) ≠ 0 := by
      simpa [sub_eq_zero, Complex.ofReal_inj] using hi
    have : ((O.eigval i : ℂ) - (k : ℂ)) * O.coords v i = 0 := by
      rw [sub_mul, hc, sub_self]
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hne
    · exact h'
  · intro h
    apply O.coords_injective
    funext i
    rw [coords_mat_mulVec, coords_smul]
    by_cases hi : O.eigval i = k
    · rw [hi]
    · rw [h i hi, mul_zero, mul_zero]

lemma star_diagProj {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    star (O.diagProj k) = O.diagProj k := by
  rw [diagProj, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : O.eigval i = k <;> simp [h]

lemma diagProj_mul_self {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    O.diagProj k * O.diagProj k = O.diagProj k := by
  rw [diagProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : O.eigval i = k <;> simp [h]

lemma projMat_hermitian {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    (O.projMat k).IsHermitian := by
  have h : star (O.projMat k) = O.projMat k := by
    rw [projMat, Matrix.star_mul, Matrix.star_mul, star_star, O.star_diagProj, Matrix.mul_assoc]
  simpa [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using h

lemma projMat_mul_self {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    O.projMat k * O.projMat k = O.projMat k := by
  simp only [projMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star O.eigU) O.eigU, O.star_mul_eigU, Matrix.one_mul,
    ← Matrix.mul_assoc (O.diagProj k) (O.diagProj k), O.diagProj_mul_self]

lemma projMat_mulVec_eq_self {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) {v : d → ℂ} (hv : v ∈ O.eigenspace k) :
    O.projMat k *ᵥ v = v := by
  rw [O.mem_eigenspace_iff_coords] at hv
  apply O.coords_injective
  funext i
  rw [O.coords_projMat_mulVec, O.diagProj_mulVec_apply]
  by_cases h : O.eigval i = k
  · simp [h]
  · simp [h, hv i h]

lemma projMat_isProjectorOnto {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : O.isProjectorOnto k (O.projMat k) := by
  refine ⟨O.projMat_hermitian k, O.projMat_mul_self k, ?_⟩
  apply Submodule.ext
  intro v
  simp only [LinearMap.mem_range, Matrix.toLin'_apply]
  constructor
  · rintro ⟨w, rfl⟩
    rw [O.mem_eigenspace_iff_coords]
    intro i hi
    rw [O.coords_projMat_mulVec, O.diagProj_mulVec_apply, if_neg hi]
  · intro hv
    exact ⟨v, O.projMat_mulVec_eq_self k hv⟩

lemma isProjectorOnto_unique {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) {P Q : Matrix d d ℂ}
    (hP : O.isProjectorOnto k P) (hQ : O.isProjectorOnto k Q) : P = Q := by
  obtain ⟨hPh, hPi, hPr⟩ := hP
  obtain ⟨hQh, hQi, hQr⟩ := hQ
  have key : ∀ (A B : Matrix d d ℂ), A * A = A → B * B = B →
      LinearMap.range (Matrix.toLin' A) = LinearMap.range (Matrix.toLin' B) → A * B = B := by
    intro A B hA hB hr
    have : Matrix.toLin' (A * B) = Matrix.toLin' B := by
      apply LinearMap.ext
      intro w
      have hmem : B *ᵥ w ∈ LinearMap.range (Matrix.toLin' A) := by
        rw [hr]
        exact ⟨w, by simp [Matrix.toLin'_apply]⟩
      obtain ⟨u, hu⟩ := hmem
      rw [Matrix.toLin'_apply] at hu
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hu,
        Matrix.mulVec_mulVec, hA]
    exact Matrix.toLin'.injective this
  have hPQ : P * Q = Q := key P Q hPi hQi (hPr.trans hQr.symm)
  have hQP : Q * P = P := key Q P hQi hPi (hQr.trans hPr.symm)
  have hstarP : star P = P := by simpa [Matrix.star_eq_conjTranspose] using hPh
  have hstarQ : star Q = Q := by simpa [Matrix.star_eq_conjTranspose] using hQh
  calc P = star (Q * P) := by rw [hQP, hstarP]
    _ = star P * star Q := Matrix.star_mul _ _
    _ = P * Q := by rw [hstarP, hstarQ]
    _ = Q := hPQ

theorem existsUnique_projector {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) :
    ∃! P : Matrix d d ℂ, O.isProjectorOnto k P :=
  ⟨O.projMat k, O.projMat_isProjectorOnto k,
    fun _ hP => O.isProjectorOnto_unique k hP (O.projMat_isProjectorOnto k)⟩

/- Classically get the projector due to existence and uniqueness (TODO(?): Make this computable instead? (is that possible?)) -/
noncomputable def projector {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : Matrix d d ℂ :=
  (O.existsUnique_projector k).choose

lemma projector_isProjectorOnto {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) : O.isProjectorOnto k (O.projector k) :=
  (O.existsUnique_projector k).choose_spec.1

lemma eq_projector {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) {P : Matrix d d ℂ} (hP : O.isProjectorOnto k P) :
    P = O.projector k :=
  (O.existsUnique_projector k).choose_spec.2 P hP

@[simp]
lemma projector_eq_projMat {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    O.projector k = O.projMat k :=
  (O.eq_projector k (O.projMat_isProjectorOnto k)).symm

lemma projector_hermitian {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    (O.projector k).IsHermitian :=
  (O.projector_isProjectorOnto k).1

lemma projector_idem {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    O.projector k * O.projector k = O.projector k :=
  (O.projector_isProjectorOnto k).2.1

lemma projector_mulVec_eq_self {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) {v : d → ℂ} (hv : v ∈ O.eigenspace k) :
    O.projector k *ᵥ v = v := by
  rw [O.projector_eq_projMat k]
  exact O.projMat_mulVec_eq_self k hv

/- Probability extraction of an observable -/
noncomputable def prob {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (ψ : Ket d) : ℝ :=
  ∑ x, ‖(O.projector k *ᵥ ψ.vec) x‖ ^ 2

lemma prob_eq_euclidean_norm_sq {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (ψ : Ket d) :
    O.prob k ψ = ‖(WithLp.equiv 2 (d → ℂ)).symm (O.projector k *ᵥ ψ.vec)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  rfl

/- The (finite) set of eigenvalues of an observable -/
noncomputable def spec {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) : Finset ℝ :=
  Finset.image O.eigval Finset.univ

lemma mem_spec_iff {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (k : ℝ) :
    k ∈ O.spec ↔ ∃ i, O.eigval i = k := by
  simp [spec]

/- Characterization of the spectrum -/
theorem mem_spec_iff_eigenspace_ne_bot {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) :
    k ∈ O.spec ↔ O.eigenspace k ≠ ⊥ := by
  rw [mem_spec_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨O.eigU *ᵥ (Pi.single i (1 : ℂ)), ?_, ?_⟩
    · rw [O.mem_eigenspace_iff_coords, O.coords_eigU_mulVec]
      intro j hj
      have : j ≠ i := by rintro rfl; exact hj hi
      simp [this]
    · intro hzero
      have h1 : O.coords (O.eigU *ᵥ (Pi.single i (1 : ℂ))) i = 1 := by
        rw [O.coords_eigU_mulVec]; simp
      rw [hzero] at h1
      simp [coords] at h1
  · rintro ⟨v, hv, hv0⟩
    rw [O.mem_eigenspace_iff_coords] at hv
    by_contra hc
    push_neg at hc
    apply hv0
    rw [← O.eigU_mulVec_coords v]
    have : O.coords v = 0 := by
      funext i
      by_cases hi : O.eigval i = k
      · exact absurd hi (hc i)
      · simp [hv i hi]
    rw [this]
    simp

lemma sum_smul_diagProj {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    ∑ k ∈ O.spec, (k : ℂ) • O.diagProj k = diagonal (fun i => (O.eigval i : ℂ)) := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    have : ∀ k ∈ O.spec, ((k : ℂ) • O.diagProj k) i i
        = if O.eigval i = k then (k : ℂ) else 0 := by
      intro k _
      rw [diagProj, Matrix.smul_apply, Matrix.diagonal_apply_eq]
      split <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq O.spec (O.eigval i) (fun k => (k : ℂ)),
      if_pos ((O.mem_spec_iff _).2 ⟨i, rfl⟩)]
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    rw [diagProj, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, smul_zero]

theorem spectral_theorem {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) :
    O.mat = ∑ k ∈ O.spec, (k : ℂ) • O.projector k := by
  have hsum : ∑ k ∈ O.spec, (k : ℂ) • O.projector k
      = O.eigU * (∑ k ∈ O.spec, (k : ℂ) • O.diagProj k) * star O.eigU := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [O.projector_eq_projMat, projMat, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, O.sum_smul_diagProj, ← spectral_decomp]

lemma sum_norm_sq_mulVec_unitary {d : Type*} [Fintype d] [DecidableEq d]
    {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (v : d → ℂ) : ∑ x, ‖(U *ᵥ v) x‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  have hc : ∀ (w : d → ℂ), ((∑ x, ‖w x‖ ^ 2 : ℝ) : ℂ) = ∑ x, w x * (starRingEnd ℂ) (w x) := by
    intro w
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.mul_conj]
    norm_cast
    exact (Complex.normSq_eq_norm_sq (w x)).symm
  have h := unitary_inner_preserve v v ⟨U, hU⟩
  have : ((∑ x, ‖(U *ᵥ v) x‖ ^ 2 : ℝ) : ℂ) = ((∑ x, ‖v x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hc, hc]
    exact h
  exact_mod_cast this

lemma prob_eq_sum_coords {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (ψ : Ket d) :
    O.prob k ψ = ∑ i ∈ Finset.univ.filter (fun i => O.eigval i = k), ‖O.coords ψ.vec i‖ ^ 2 := by
  have h1 : O.projector k *ᵥ ψ.vec = O.eigU *ᵥ (O.diagProj k *ᵥ O.coords ψ.vec) := by
    rw [← O.coords_projMat_mulVec, O.eigU_mulVec_coords, O.projector_eq_projMat]
  rw [prob, h1, sum_norm_sq_mulVec_unitary O.eigU_mem, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [O.diagProj_mulVec_apply]
  split <;> simp

lemma sum_coords_sq {d : Type*} [Fintype d] [DecidableEq d] (O : Observable d) (ψ : Ket d) :
    ∑ i, ‖O.coords ψ.vec i‖ ^ 2 = 1 := by
  rw [coords, sum_norm_sq_mulVec_unitary O.star_eigU_mem]
  exact ψ.normalized'

theorem prob_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (ψ : Ket d) : 0 ≤ O.prob k ψ := by
  rw [prob]
  positivity

theorem prob_le_one {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (k : ℝ) (ψ : Ket d) : O.prob k ψ ≤ 1 := by
  rw [O.prob_eq_sum_coords k ψ, ← O.sum_coords_sq ψ]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

theorem prob_eq_zero_of_not_mem_spec {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) {k : ℝ} (hk : k ∉ O.spec) (ψ : Ket d) :
    O.prob k ψ = 0 := by
  rw [O.prob_eq_sum_coords k ψ]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  exact absurd ((O.mem_spec_iff k).2 ⟨i, hi.2⟩) hk

theorem sum_prob_eq_one {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (ψ : Ket d) : ∑ k ∈ O.spec, O.prob k ψ = 1 := by
  simp only [O.prob_eq_sum_coords _ ψ]
  rw [Finset.sum_fiberwise_of_maps_to (fun i _ => (O.mem_spec_iff (O.eigval i)).2 ⟨i, rfl⟩)]
  exact O.sum_coords_sq ψ

/- Measuring an eigenvector determinisically gives the associated eigenvalue -/
theorem prob_eigenvector_self {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (l : ℝ) (ψ : Ket d) (h : O.mat *ᵥ ψ.vec = (l : ℂ) • ψ.vec) :
    O.prob l ψ = 1 := by
  have hmem : ∀ i, O.eigval i ≠ l → O.coords ψ.vec i = 0 :=
    (O.mem_eigenspace_iff_coords l ψ.vec).1 ((O.mem_eigenspace_iff l ψ.vec).2 h)
  rw [O.prob_eq_sum_coords l ψ, ← O.sum_coords_sq ψ]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro i _ hi
  rw [Finset.mem_filter] at hi
  push_neg at hi
  rw [hmem i (hi (Finset.mem_univ i))]
  simp

theorem prob_eigenvector_ne {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (l : ℝ) (ψ : Ket d) (h : O.mat *ᵥ ψ.vec = (l : ℂ) • ψ.vec)
    {k : ℝ} (hk : k ≠ l) : O.prob k ψ = 0 := by
  have hmem : ∀ i, O.eigval i ≠ l → O.coords ψ.vec i = 0 :=
    (O.mem_eigenspace_iff_coords l ψ.vec).1 ((O.mem_eigenspace_iff l ψ.vec).2 h)
  rw [O.prob_eq_sum_coords k ψ]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  have : O.eigval i ≠ l := by rw [hi.2]; exact hk
  rw [hmem i this]
  simp

lemma eigval_sq_eq_one {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (h : O.mat * O.mat = 1) (i : d) :
    O.eigval i ^ 2 = 1 := by
  have hy : O.coords (O.eigU *ᵥ (Pi.single i (1 : ℂ))) = Pi.single i 1 :=
    O.coords_eigU_mulVec _
  have h3 : O.mat *ᵥ (O.mat *ᵥ (O.eigU *ᵥ (Pi.single i (1 : ℂ))))
      = O.eigU *ᵥ (Pi.single i (1 : ℂ)) := by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h2 := O.coords_mat_mulVec (O.mat *ᵥ (O.eigU *ᵥ (Pi.single i (1 : ℂ)))) i
  rw [h3, O.coords_mat_mulVec, hy] at h2
  simp only [Pi.single_eq_same, mul_one] at h2
  have : ((O.eigval i ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    rw [pow_two, ← h2]
  exact_mod_cast this

lemma eigval_eq_one_or_neg_one {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (h : O.mat * O.mat = 1) (i : d) :
    O.eigval i = 1 ∨ O.eigval i = -1 := by
  have hsq := O.eigval_sq_eq_one h i
  have : (O.eigval i - 1) * (O.eigval i + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.1 this with h' | h'
  · left; linarith
  · right; linarith

lemma sum_eigval_eq_zero_of_trace_eq_zero {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) (htr : O.mat.trace = 0) :
    ∑ i, O.eigval i = 0 := by
  have h := O.herm.trace_eq_sum_eigenvalues
  rw [htr] at h
  have : ((∑ i, O.eigval i : ℝ) : ℂ) = 0 := by
    push_cast
    exact h.symm
  exact_mod_cast this

theorem spec_eq_of_sq_eq_one_of_trace_eq_zero {d : Type*} [Fintype d] [DecidableEq d]
    (O : Observable d) [Nonempty d]
    (hsq : O.mat * O.mat = 1) (htr : O.mat.trace = 0) : O.spec = {-1, 1} := by
  classical
  have hpm := O.eigval_eq_one_or_neg_one hsq
  have hsum := O.sum_eigval_eq_zero_of_trace_eq_zero htr
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset d)
      (fun i => O.eigval i = 1) O.eigval
  have hS1 : ∑ i ∈ Finset.univ.filter (fun i : d => O.eigval i = 1), O.eigval i
      = ((Finset.univ.filter (fun i : d => O.eigval i = 1)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hT1 : ∑ i ∈ Finset.univ.filter (fun i : d => ¬ O.eigval i = 1), O.eigval i
      = -((Finset.univ.filter (fun i : d => ¬ O.eigval i = 1)).card : ℝ) := by
    have hall : ∀ i ∈ Finset.univ.filter (fun i : d => ¬ O.eigval i = 1), O.eigval i = -1 := by
      intro i hi
      rcases hpm i with h1 | h1
      · exact absurd h1 (Finset.mem_filter.1 hi).2
      · exact h1
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
  have hcards := Finset.card_filter_add_card_filter_not
    (p := fun i : d => O.eigval i = 1) (s := (Finset.univ : Finset d))
  rw [hS1, hT1, hsum] at hsplit
  have hEqN : (Finset.univ.filter (fun i : d => O.eigval i = 1)).card
      = (Finset.univ.filter (fun i : d => ¬ O.eigval i = 1)).card := by
    have : ((Finset.univ.filter (fun i : d => O.eigval i = 1)).card : ℝ)
        = ((Finset.univ.filter (fun i : d => ¬ O.eigval i = 1)).card : ℝ) := by linarith
    exact_mod_cast this
  have hpos : 0 < (Finset.univ : Finset d).card := Finset.card_pos.2 Finset.univ_nonempty
  have hSpos : 0 < (Finset.univ.filter (fun i : d => O.eigval i = 1)).card := by omega
  have hTpos : 0 < (Finset.univ.filter (fun i : d => ¬ O.eigval i = 1)).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hSpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hTpos
  have hival : O.eigval i = 1 := (Finset.mem_filter.1 hi).2
  have hjval : O.eigval j = -1 := by
    rcases hpm j with h1 | h1
    · exact absurd h1 (Finset.mem_filter.1 hj).2
    · exact h1
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton, O.mem_spec_iff]
  constructor
  · rintro ⟨l, rfl⟩
    rcases hpm l with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · rintro (rfl | rfl)
    · exact ⟨j, hjval⟩
    · exact ⟨i, hival⟩

end Observable

noncomputable def BinSympPauli.pauliString {n : ℕ} (bs : BinSympPauli n) : Fin n → Pauli :=
  fun i => Z2Z2_Pauli_equiv (bs.1 i, bs.2 i)

noncomputable def pauliObservable {n : ℕ} (bs : BinSympPauli n) :
    Observable (BitVec n) :=
  ⟨(unitary_n_nkron (bs.pauliString : Fin n → 𝐔ₙ[1])).val,
    pauli_tensor_hermitian bs.pauliString⟩

lemma pauliObservable_mat {n : ℕ} (bs : BinSympPauli n) :
    (pauliObservable bs).mat
      = ((BinSympPauli_toPauli bs : 𝐔ₙ[n]) : Matrix (BitVec n) (BitVec n) ℂ) := by
  have h : (BinSympPauli_toPauli bs : 𝐔ₙ[n])
      = unitary_n_nkron (bs.pauliString : Fin n → 𝐔ₙ[1]) := by
    show (fold (pgphase_1, bs.pauliString) : 𝐔ₙ[n]) = _
    show fold_aux pgphase_1 bs.pauliString = _
    rw [fold_aux]
    exact U_phase_id
  rw [pauliObservable, h]

lemma BinSympPauli.pauliString_ne_all_I {n : ℕ} {bs : BinSympPauli n} (hbs : bs ≠ 0) :
    ¬ ∀ i, bs.pauliString i = Pauli_I := by
  intro hall
  apply hbs
  have h : ∀ i, (bs.1 i, bs.2 i) = ((0 : ZMod 2), (0 : ZMod 2)) := by
    intro i
    have := hall i
    rw [BinSympPauli.pauliString] at this
    have h0 : Z2Z2_Pauli_equiv (bs.1 i, bs.2 i) = Z2Z2_Pauli_equiv (0, 0) := by
      rw [this]; rfl
    exact Z2Z2_Pauli_equiv.injective h0
  ext i
  · exact congrArg Prod.fst (h i)
  · exact congrArg Prod.snd (h i)

lemma pauliObservable_sq {n : ℕ} (bs : BinSympPauli n) :
    (pauliObservable bs).mat * (pauliObservable bs).mat = 1 := by
  have hu : (pauliObservable bs).mat ∈ Matrix.unitaryGroup (BitVec n) ℂ :=
    (unitary_n_nkron (bs.pauliString : Fin n → 𝐔ₙ[1])).2
  have h1 : star (pauliObservable bs).mat * (pauliObservable bs).mat = 1 :=
    Unitary.star_mul_self_of_mem hu
  rwa [Matrix.star_eq_conjTranspose, (pauliObservable bs).herm] at h1

lemma pauliObservable_trace {n : ℕ} (bs : BinSympPauli n) (hbs : bs ≠ 0) :
    (pauliObservable bs).mat.trace = 0 := by
  have hfold : (fold (pgphase_1, bs.pauliString))
      = unitary_n_nkron (bs.pauliString : Fin n → 𝐔ₙ[1]) := by
    show fold_aux pgphase_1 bs.pauliString = _
    rw [fold_aux]
    exact U_phase_id
  have h := trace_fold_eq pgphase_1 bs.pauliString
  rw [hfold, if_neg (BinSympPauli.pauliString_ne_all_I hbs)] at h
  exact h

/- Paulis only have eigenvalues -1 and +1 -/
theorem pauliObservable_spec {n : ℕ} (bs : BinSympPauli n) (hbs : bs ≠ 0) :
    (pauliObservable bs).spec = {-1, 1} :=
  Observable.spec_eq_of_sq_eq_one_of_trace_eq_zero _ (pauliObservable_sq bs)
    (pauliObservable_trace bs hbs)
