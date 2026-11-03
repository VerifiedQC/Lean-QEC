import LeanQEC.Unitary.Paulis.Pauli1Mul


open Qubit
open Function
open Matrix

noncomputable section

variable {n : ℕ}

def pauliString (m : Fin n → Pauli) : 𝐔ₙ[n] :=
  unitaryPiProd (fun i => (m i).val)

lemma pauliString_val (m : Fin n → Pauli) :
    (pauliString m : Matrix (Qubits n) (Qubits n) ℂ) = piProd (fun i => pauliMat (m i)) :=
  rfl

lemma pauli_tensor_hermitian (m : Fin n → Pauli) :
    (pauliString m : Matrix (Qubits n) (Qubits n) ℂ).IsHermitian :=
  IsHermitian.piProd (fun i => pauli_herm (m i))

lemma card_qubits (n : ℕ) : Fintype.card (Qubits n) = 2 ^ n := by
  simp [Qubits]

lemma trace_star_pauliString_mul (m m' : Fin n → Pauli) :
    (star (pauliString m : Matrix (Qubits n) (Qubits n) ℂ) * pauliString m').trace =
      ∏ i, if m i = m' i then (2 : ℂ) else 0 := by
  rw [pauliString_val, pauliString_val, star_piProd, ← piProd_mul, trace_piProd]
  simp [trace_star_pauli_mul]

def fold_aux (z : pgroup_phases) (m : Fin n → Pauli) : 𝐔ₙ[n] :=
  pgroup_phases.toCircle z • pauliString m

lemma fold_aux_val (z : pgroup_phases) (m : Fin n → Pauli) :
    (fold_aux z m : Matrix (Qubits n) (Qubits n) ℂ) =
      (pgroup_phases.toCircle z : ℂ) • piProd (fun i => pauliMat (m i)) :=
  rfl

lemma injective_fold_aux {z z' : pgroup_phases} {m m' : Fin n → Pauli} :
    fold_aux z m = fold_aux z' m' → z = z' ∧ m = m' := by
  intro H
  set P := (pauliString m : Matrix (Qubits n) (Qubits n) ℂ)
  set P' := (pauliString m' : Matrix (Qubits n) (Qubits n) ℂ)
  have hm : (pgroup_phases.toCircle z : ℂ) • P = (pgroup_phases.toCircle z' : ℂ) • P' :=
    congrArg Subtype.val H
  have h' : (pgroup_phases.toCircle z : ℂ) • (star P * P) =
      (pgroup_phases.toCircle z' : ℂ) • (star P * P') := by
    rw [← mul_smul_comm, ← mul_smul_comm, hm]
  have hunit : star P * P = 1 := (pauliString m).2.1
  rw [hunit] at h'
  have ht := congrArg Matrix.trace h'
  simp only [trace_smul, trace_one, card_qubits, trace_star_pauliString_mul, smul_eq_mul,
    P, P'] at ht
  have hprod : ∏ i, (if m i = m' i then (2 : ℂ) else 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_eq_zero] at ht
    rcases ht with h | h
    · exact Circle.coe_ne_zero _ h
    · norm_num at h
  have hmm : m = m' := funext fun i => by
    by_contra hne
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hne))
  subst hmm
  refine ⟨pgroup_phases.toCircle_injective (Circle.ext ?_), rfl⟩
  simp only [if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at ht
  push_cast at ht
  exact mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) ht

abbrev factored_Pauli (n : ℕ) := pgroup_phases × (Fin n → Pauli)

def fold : factored_Pauli n ↪ 𝐔ₙ[n] :=
  ⟨fun zm => fold_aux zm.1 zm.2, by
    rintro ⟨z, m⟩ ⟨z', m'⟩ h
    obtain ⟨rfl, rfl⟩ := injective_fold_aux h
    rfl⟩

lemma fold_apply (zm : factored_Pauli n) : fold zm = fold_aux zm.1 zm.2 := rfl

def factored_Pauli_univ : Finset (factored_Pauli n) := Finset.univ

def PauliGroup (n : ℕ) : Finset 𝐔ₙ[n] := (factored_Pauli_univ).map (@fold n)

lemma mem_fold (pm : factored_Pauli n) : fold pm ∈ PauliGroup n := by
  unfold PauliGroup
  simp [factored_Pauli_univ]

abbrev foldPauli_toFun (n : ℕ) (pm : factored_Pauli n) : PauliGroup n :=
  ⟨fold pm, mem_fold pm⟩

lemma inj_foldPauli : Injective (foldPauli_toFun n) := by
  intro a a' h
  exact fold.injective (congrArg Subtype.val h)

lemma surj_fold (p : PauliGroup n) :
    ∃ m z, (p : 𝐔ₙ[n]) = fold (z, m) := by
  rcases p with ⟨pval, mem_p⟩
  rw [PauliGroup, Finset.mem_map] at mem_p
  rcases mem_p with ⟨⟨z', m'⟩, _, h'⟩
  exact ⟨m', z', h'.symm⟩

lemma surj_foldPauli : Surjective (foldPauli_toFun n) := by
  intro p
  obtain ⟨m, z, h'⟩ := surj_fold p
  exact ⟨(z, m), Subtype.ext h'.symm⟩

def foldPauli : factored_Pauli n ≃ PauliGroup n :=
  Equiv.ofBijective (foldPauli_toFun n) ⟨inj_foldPauli, surj_foldPauli⟩

@[simp]
lemma foldPauli_val (pm : factored_Pauli n) : (foldPauli pm : 𝐔ₙ[n]) = fold pm :=
  rfl

lemma fold_pauli_mul (p p' : pgroup_phases) (m : Fin n → Pauli) :
    (foldPauli (p * p', m) : 𝐔ₙ[n]) = pgroup_phases.toCircle p' • (foldPauli (p, m)).1 := by
  simp [fold_apply, fold_aux, smul_smul, mul_comm]

def factored_kron {n₁ n₂} (p : factored_Pauli n₁) (p' : factored_Pauli n₂) :
    factored_Pauli (n₁ + n₂) :=
  (p.1 * p'.1, Fin.append p.2 p'.2)

lemma pauliString_nkron {n₁ n₂} (m : Fin n₁ → Pauli) (m' : Fin n₂ → Pauli) :
    pauliString m ⊗ₙ pauliString m' = pauliString (Fin.append m m') := by
  rw [pauliString, pauliString, unitaryPiProd_nkron, pauliString]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

lemma fold_nkron {n₁ n₂} (p : factored_Pauli n₁) (p' : factored_Pauli n₂) :
    fold p ⊗ₙ fold p' = fold (factored_kron p p') := by
  simp only [fold_apply, fold_aux, factored_kron, circle_smul_nkron, nkron_circle_smul,
    pauliString_nkron, smul_smul, map_mul, mul_comm]

lemma kron_PaulisE {n₁ n₂ : ℕ} (p : PauliGroup n₁) (p' : PauliGroup n₂) :
    p.1 ⊗ₙ p'.1 = (foldPauli (factored_kron (foldPauli.symm p) (foldPauli.symm p'))) := by
  have h1 : (p : 𝐔ₙ[n₁]) = fold (foldPauli.symm p) := by
    rw [← foldPauli_val, Equiv.apply_symm_apply]
  have h2 : (p' : 𝐔ₙ[n₂]) = fold (foldPauli.symm p') := by
    rw [← foldPauli_val, Equiv.apply_symm_apply]
  rw [h1, h2, fold_nkron, foldPauli_val]

lemma kron_mem_PauliGroup {n₁ n₂ : ℕ} (U : PauliGroup (n₁ + n₂)) :
    ∃ (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂), U.1 = U₁ ⊗ₙ U₂ := by
  set zm := foldPauli.symm U with hzm
  refine ⟨foldPauli (zm.1, fun i => zm.2 (Fin.castAdd n₂ i)),
    foldPauli (1, fun i => zm.2 (Fin.natAdd n₁ i)), ?_⟩
  rw [foldPauli_val, foldPauli_val, fold_nkron]
  simp only [factored_kron, mul_one, Fin.append_castAdd_natAdd]
  rw [Prod.mk.eta, ← foldPauli_val, hzm, Equiv.apply_symm_apply]

lemma PauliGroup_mem_kron {n₁ n₂ : ℕ} (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂) :
    U₁ ⊗ₙ U₂ ∈ PauliGroup (n₁ + n₂) := by
  rw [kron_PaulisE]
  exact (foldPauli _).2

def kronOfPauli {n₁ n₂ : ℕ} (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂) : PauliGroup (n₁ + n₂) :=
  ⟨U₁ ⊗ₙ U₂, PauliGroup_mem_kron U₁ U₂⟩

theorem kron_mem_PauliGroup_iff {n₁ n₂ : ℕ} (U : 𝐔ₙ[n₁ + n₂]) :
    (U ∈ PauliGroup (n₁ + n₂)) ↔
      (∃ (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂), U = U₁ ⊗ₙ U₂) := by
  constructor
  · intro H
    exact kron_mem_PauliGroup ⟨U, H⟩
  · rintro ⟨U1, U2, rfl⟩
    apply PauliGroup_mem_kron

def unfolded1 : factored_Pauli n := (1, (fun (_ : Fin n) => Pauli_I))

lemma pauliString_I : pauliString (fun (_ : Fin n) => Pauli_I) = 1 :=
  unitaryPiProd_one

lemma foldPauli1 : @fold n unfolded1 = 1 := by
  simp [fold_apply, fold_aux, unfolded1, pauliString_I]

lemma mem_PauliGroup_id : 1 ∈ PauliGroup n := by
  rw [← foldPauli1]
  exact mem_fold _

def Pauli1 : PauliGroup n := ⟨1, mem_PauliGroup_id⟩

lemma Pauli1_unfold : Pauli1 = foldPauli (1, (fun (_ : Fin n) => Pauli_I)) := by
  apply Subtype.ext
  simp only [Pauli1, foldPauli_val]
  exact foldPauli1.symm

def PauliGroup.map (P : PauliGroup n) : (Fin n → Pauli) :=
  (foldPauli.symm P).2

def PauliGroup.phase (P : PauliGroup n) : pgroup_phases :=
  (foldPauli.symm P).1

def PauliGroup.normalized (P : PauliGroup n) := PauliGroup.phase P = 1

lemma rep_unique (f₁ f₂ : factored_Pauli n) (H : foldPauli f₁ = foldPauli f₂) :
    f₁ = f₂ :=
  foldPauli.injective H

lemma map_kron_of_Pauli {n₁ n₂} (P₁ : PauliGroup n₁) (P₂ : PauliGroup n₂) :
    PauliGroup.map (kronOfPauli P₁ P₂) = Fin.append (PauliGroup.map P₁) (PauliGroup.map P₂) := by
  have : kronOfPauli P₁ P₂ = foldPauli (factored_kron (foldPauli.symm P₁) (foldPauli.symm P₂)) :=
    Subtype.ext (kron_PaulisE P₁ P₂)
  simp [PauliGroup.map, this, factored_kron]

lemma foldPauli_phase_map {n : ℕ} (P : PauliGroup n) :
    (foldPauli (PauliGroup.phase P, PauliGroup.map P) : PauliGroup n) = P := by
  unfold PauliGroup.phase PauliGroup.map
  simp

end
