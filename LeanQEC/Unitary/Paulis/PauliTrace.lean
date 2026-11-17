import LeanQEC.Unitary.Paulis.PauliFolding


open Matrix

noncomputable section

variable {n : ℕ}

lemma prod_if_pauli_I (m : Fin n → Pauli) :
    (∏ i, (if m i = Pauli_I then (2 : ℂ) else 0))
      = if (∀ i, m i = Pauli_I) then (2 : ℂ) ^ n else 0 := by
  split_ifs <;> simp_all +decide [Finset.prod_ite]

lemma trace_pauliString (m : Fin n → Pauli) :
    (pauliString m : Matrix (Qubits n) (Qubits n) ℂ).trace =
      ∏ i, (if m i = Pauli_I then (2 : ℂ) else 0) := by
  rw [pauliString_val, trace_piProd]
  simp [trace_pauli_single]

lemma trace_fold_prod (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = (pgroup_phases.toCircle z : ℂ) * ∏ i, (if m i = Pauli_I then (2 : ℂ) else 0) := by
  rw [fold_apply, fold_aux_val, trace_smul, ← pauliString_val, trace_pauliString, smul_eq_mul]

lemma trace_fold_eq (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = if (∀ i, m i = Pauli_I) then (pgroup_phases.toCircle z : ℂ) * (2 : ℂ) ^ n else 0 := by
  rw [trace_fold_prod, prod_if_pauli_I]
  split <;> simp

end
