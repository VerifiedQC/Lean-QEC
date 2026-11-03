import LeanQEC.Unitary.Paulis.Pauli1

open Matrix

noncomputable section

def mul_Pauli1 (P : Pauli) (Q : Pauli) : pgroup_phases × Pauli :=
  if P = Pauli_I then
    (1, Q)
  else if P = Pauli_X then
    if Q = Pauli_I then
      (1, Pauli_X)
    else if Q = Pauli_X then
      (1, Pauli_I)
    else if Q = Pauli_Y then
      (pgphase_i, Pauli_Z)
    else -- Q = Z
      (pgphase_ni, Pauli_Y)
  else if P = Pauli_Y then
    if Q = Pauli_I then
      (1, Pauli_Y)
    else if Q = Pauli_X then
      (pgphase_ni, Pauli_Z)
    else if Q = Pauli_Y then
      (1, Pauli_I)
    else -- Q = Z
      (pgphase_i, Pauli_X)
  else -- P = Z
    if Q = Pauli_I then
      (1, Pauli_Z)
    else if Q = Pauli_X then
      (pgphase_i, Pauli_Y)
    else if Q = Pauli_Y then
      (pgphase_ni, Pauli_X)
    else -- Q = Z
      (1, Pauli_I)

lemma mul_Pauli1_correct (P Q : Pauli) :
    let PQ := mul_Pauli1 P Q
    P.val * Q.val = pgroup_phases.toCircle PQ.1 • PQ.2.val := by
  intro PQ
  apply Subtype.ext
  change pauliMat P * pauliMat Q = (pgroup_phases.toCircle PQ.1 : ℂ) • pauliMat PQ.2
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    · simp only [PQ, mul_Pauli1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma mul_Pauli1_correct' (P Q : Pauli) :
    pauliMat P * pauliMat Q =
      (pgroup_phases.toCircle (mul_Pauli1 P Q).1 : ℂ) • pauliMat (mul_Pauli1 P Q).2 :=
  congrArg Subtype.val (mul_Pauli1_correct P Q)

/- Paulis square to the identity -/
lemma mul_Pauli1_xx (P : Pauli) :
    mul_Pauli1 P P = (1, Pauli_I) := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;> simp [mul_Pauli1]

end
