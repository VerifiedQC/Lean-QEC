import LeanQEC.Unitary.Paulis.PauliFolding

open Matrix

noncomputable section

def pointwise_mul_Paulis {n} (P Q : Fin n → Pauli) (i : Fin n) :=
  mul_Pauli1 (P i) (Q i)

def fold_pgroup_phases {n} (lst : Fin n → pgroup_phases) : pgroup_phases :=
  match n with
  | 0 => 1
  | _ + 1 => lst 0 * fold_pgroup_phases (Fin.tail lst)

lemma fold_pgroup_phases_empty (lst : Fin 0 → pgroup_phases) :
    fold_pgroup_phases lst = 1 := by rfl

lemma fold_pgroup_phases_eq_prod {n} (lst : Fin n → pgroup_phases) :
    fold_pgroup_phases lst = ∏ i, lst i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fold_pgroup_phases, ih, Fin.prod_univ_succ]
    rfl

def collect_phases {n} (P : Fin n → (pgroup_phases × Pauli)) : factored_Pauli n :=
  (fold_pgroup_phases (fun i => (P i).1), (fun i => (P i).2))

lemma collect_phases_correct {n} (P : Fin n → (pgroup_phases × Pauli)) :
    (fold (collect_phases P) : Matrix (Qubits n) (Qubits n) ℂ) =
      piProd (fun i => (pgroup_phases.toCircle (P i).1 : ℂ) • pauliMat (P i).2) := by
  rw [piProd_smul, fold_apply, fold_aux_val]
  simp only [collect_phases, fold_pgroup_phases_eq_prod, map_prod]
  congr 1
  exact map_prod Circle.coeHom _ _

def mul_Pauli1_tuples {n} (P Q : Fin n → Pauli) : factored_Pauli n :=
  collect_phases (pointwise_mul_Paulis P Q)

lemma mul_Pauli1_tuples_correct {n} (P Q : Fin n → Pauli) :
    (foldPauli (mul_Pauli1_tuples P Q)).val = pauliString P * pauliString Q := by
  apply Subtype.ext
  rw [foldPauli_val, mul_Pauli1_tuples, collect_phases_correct]
  show _ = (pauliString P : Matrix (Qubits n) (Qubits n) ℂ) * pauliString Q
  rw [pauliString_val, pauliString_val, ← piProd_mul]
  congr 1
  funext i
  exact (mul_Pauli1_correct' (P i) (Q i)).symm

def scale_factored_Pauli {n} (c : pgroup_phases) (P : factored_Pauli n) : factored_Pauli n :=
  (c * P.1, P.2)

def mul_factored_Paulis {n} (P Q : factored_Pauli n) : factored_Pauli n :=
  scale_factored_Pauli (P.1 * Q.1) (mul_Pauli1_tuples P.2 Q.2)

lemma mul_factored_Paulis_correct {n} (P Q : factored_Pauli n) :
    foldPauli (mul_factored_Paulis P Q) = (foldPauli P).val * (foldPauli Q).val := by
  have h := mul_Pauli1_tuples_correct P.2 Q.2
  simp only [foldPauli_val, fold_apply, fold_aux] at h ⊢
  simp only [mul_factored_Paulis, scale_factored_Pauli, map_mul, mul_smul, h,
    smul_mul_smul_comm]

def mul_Paulis {n} (P Q : PauliGroup n) :=
  foldPauli (mul_factored_Paulis (foldPauli.symm P) (foldPauli.symm Q))

lemma mul_Paulis_correct {n} (P Q : PauliGroup n) :
    mul_Paulis P Q = P.val * Q.val := by
  rw [mul_Paulis, mul_factored_Paulis_correct, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma pointwise_mul_Paulis_xx {n} (P : Fin n → Pauli) :
    pointwise_mul_Paulis P P = (fun _ => (1, Pauli_I)) := by
  funext x
  exact mul_Pauli1_xx _

lemma collect_phases_iter {n} (P : Fin (n + 1) → (pgroup_phases × Pauli)) :
    collect_phases P =
      ((P 0).1 * (collect_phases (Fin.tail P)).1, fun i => (P i).2) := by
  rw [collect_phases, collect_phases]
  rfl

lemma mul_Pauli1_tuples_xx {n} (P : Fin n → Pauli) :
    mul_Pauli1_tuples P P = unfolded1 := by
  rw [mul_Pauli1_tuples, pointwise_mul_Paulis_xx, collect_phases, unfolded1,
    fold_pgroup_phases_eq_prod]
  simp

end
