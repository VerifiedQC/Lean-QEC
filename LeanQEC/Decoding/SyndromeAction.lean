import LeanQEC.Decoding.Recovery

open Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

variable {n k m : ℕ}

theorem list_prod_ofFn_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Fin m → Matrix ι ι ℂ) (c : Fin m → ℂ) (w : ι → ℂ) (h : ∀ j, A j *ᵥ w = c j • w) :
    (List.ofFn A).prod *ᵥ w = (∏ j, c j) • w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ← mulVec_mulVec,
      ih (fun j => A j.succ) (fun j => c j.succ) (fun j => h j.succ), mulVec_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm]

namespace StabCode.Generators

variable {C : StabCode n} (G : C.Generators m)

/- The `j`th syndrome bit is `1` iff `E` anticommutes with the
`j`th generator. -/
def pauliSyndrome (E : PauliGroup_group n) : Syndrome m :=
  fun j => symplecticProd (Pauli_toBinSympPauli (G.gen j)) (Pauli_toBinSympPauli E)

theorem pauliSyndrome_mul (E F : PauliGroup_group n) :
    G.pauliSyndrome (E * F) = G.pauliSyndrome E + G.pauliSyndrome F := by
  funext j
  simp only [pauliSyndrome, Pi.add_apply, Pauli_to_BinSymp_correct, ← BinSympPauli.form_apply,
    map_add]

theorem mem_normalizerGroup_iff_pauliSyndrome (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ G.pauliSyndrome E = 0 := by
  rw [C.mem_normalizerGroup_of_closure G.closure_eq, funext_iff]
  simp only [Set.forall_mem_range, pauliSyndrome, Pi.zero_apply]
  refine forall_congr' fun j => ?_
  rw [commute_iff_symplecticProd_zero, symplecticProd_comm]

theorem mat_mulVec_pauli (j : Fin m) (E : PauliGroup_group n) {v : Qubits n → ℂ}
    (hv : v ∈ C.space) :
    G.mat j *ᵥ (pauliGroupMat E *ᵥ v) = syndromeSign (G.pauliSyndrome E j) • (pauliGroupMat E *ᵥ v) := by
  have hgv : G.mat j *ᵥ v = v := stabilizes_apply' (hv _ (G.gen_mem j))
  rw [mulVec_mulVec]
  by_cases h : G.pauliSyndrome E j = 0
  · have hc : commute (G.gen j) E := (commute_iff_symplecticProd_zero _ _).mpr h
    have hm : G.mat j * pauliGroupMat E = pauliGroupMat E * G.mat j :=
      congrArg Subtype.val (commute_of_commute _ _ hc)
    rw [hm, ← mulVec_mulVec, hgv, h]
    simp [syndromeSign]
  · have ha : anticommute (G.gen j) E := by
      have : ¬ commute (G.gen j) E := fun hc => h ((commute_iff_symplecticProd_zero _ _).mp hc)
      simpa [commute] using this
    have hm : G.mat j * pauliGroupMat E = -(pauliGroupMat E * G.mat j) :=
      congrArg Subtype.val (anticommute_of_anticommute ha)
    rw [hm, neg_mulVec, ← mulVec_mulVec, hgv]
    simp [syndromeSign, h]

theorem factor_mulVec_pauli (j : Fin m) (b : ZMod 2) (E : PauliGroup_group n)
    {v : Qubits n → ℂ} (hv : v ∈ C.space) :
    G.factor j b *ᵥ (pauliGroupMat E *ᵥ v) =
      (if b = G.pauliSyndrome E j then 1 else 0 : ℂ) • (pauliGroupMat E *ᵥ v) := by
  have h := G.mat_mulVec_pauli j E hv
  simp only [factor, smul_mulVec, add_mulVec, one_mulVec, h, smul_smul]
  generalize G.pauliSyndrome E j = c
  generalize pauliGroupMat E *ᵥ v = w
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
    simp [syndromeSign] <;> module

theorem syndromeProjector_mulVec_pauli (s : Syndrome m) (E : PauliGroup_group n)
    {v : Qubits n → ℂ} (hv : v ∈ C.space) :
    G.syndromeProjector s *ᵥ (pauliGroupMat E *ᵥ v) =
      if s = G.pauliSyndrome E then pauliGroupMat E *ᵥ v else 0 := by
  rw [syndromeProjector, list_prod_ofFn_mulVec _ _ _ fun j => G.factor_mulVec_pauli j (s j) E hv,
    Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  by_cases hs : s = G.pauliSyndrome E
  · simp [hs]
  · have h' : ¬ ∀ j, s j = G.pauliSyndrome E j := fun h => hs (funext h)
    rw [if_neg h', if_neg hs, zero_smul]

theorem syndromeKraus_eq (s : Syndrome m) : G.syndromeKraus s = G.syndromeProjector s := by
  obtain ⟨h1, h2⟩ := G.syndromeProjector_selfAdjoint_idem s
  have hspec : spectrum ℝ (G.syndromeProjector s) ⊆ {0, 1} :=
    (isIdempotentElem_iff_spectrum_subset ℝ _ h1).mp h2
  simp only [syndromeKraus, HermitianMat.rpow_eq_cfc, HermitianMat.mat_cfc]
  change _root_.cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) (G.syndromeProjector s) = _
  rw [cfc_congr (g := id) fun x hx => ?_, cfc_id ℝ _ h1]
  rcases hspec hx with rfl | rfl <;> simp

end StabCode.Generators

variable {C : StabCode n}

theorem errorIntegrand_eq (e : C.Encoder k) (G : C.Generators m) (s : Syndrome m)
    (R E : PauliGroup_group n) (φ : Ket (Qubits k)) :
    errorIntegrand e G s R E φ =
      if s = G.pauliSyndrome E then e.recoveryFid (R * E) φ.vec φ.vec else 0 := by
  have hA : (G.syndromeProjector s)ᴴ = G.syndromeProjector s :=
    (G.syndromeProjector_isHermitian s).eq
  set v := e.isom *ᵥ φ.vec
  have hmat : pauliGroupMat R * G.syndromeKraus s *
      (pauliGroupMat E * e.encode.map (ketProj φ) * (pauliGroupMat E)ᴴ) *
      G.syndromeKraus s * (pauliGroupMat R)ᴴ =
      vecMulVec (pauliGroupMat R *ᵥ (G.syndromeProjector s *ᵥ (pauliGroupMat E *ᵥ v)))
        (star (pauliGroupMat R *ᵥ (G.syndromeProjector s *ᵥ (pauliGroupMat E *ᵥ v)))) := by
    rw [G.syndromeKraus_eq, e.encode_map_ketProj]
    have h3 : pauliGroupMat R * G.syndromeProjector s *
        (pauliGroupMat E * vecMulVec v (star v) * (pauliGroupMat E)ᴴ) *
        G.syndromeProjector s * (pauliGroupMat R)ᴴ =
        (pauliGroupMat R * G.syndromeProjector s * pauliGroupMat E) * vecMulVec v (star v) *
        (pauliGroupMat R * G.syndromeProjector s * pauliGroupMat E)ᴴ := by
      simp only [conjTranspose_mul, hA, Matrix.mul_assoc]
    rw [h3, conj_vecMulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  unfold errorIntegrand
  rw [hmat, G.syndromeProjector_mulVec_pauli s E (e.isom_mulVec_mem_space _)]
  split_ifs
  · rw [StabCode.Encoder.re_trace_unencode_map, StabCode.Encoder.recoveryFid, mulVec_mulVec]
    rfl
  · simp

end
