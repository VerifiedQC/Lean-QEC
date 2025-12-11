/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6110b4e9-98c2-4de7-8ad4-98fd279a5e54

The following was proved by Aristotle:

- @[simp] lemma neXI : (Pauli_X = Pauli_I) = false

- @[simp] lemma neXY : (Pauli_X = Pauli_Y) = false

- @[simp] lemma neXZ : (Pauli_X = Pauli_Z) = false

- @[simp] lemma neYI : (Pauli_Y = Pauli_I) = false

- @[simp] lemma neYX : (Pauli_Y = Pauli_X) = false

- @[simp] lemma neYZ : (Pauli_Y = Pauli_Z) = false

- @[simp] lemma neZI : (Pauli_Z = Pauli_I) = false

- @[simp] lemma neZX : (Pauli_Z = Pauli_X) = false

- @[simp] lemma neZY : (Pauli_Z = Pauli_Y) = false
-/

import ATPTest.Unitary.Paulis.Pauli1


@[simp] lemma neXI : (Pauli_X = Pauli_I) = false := by
  -- Since Pauli_X and Pauli_I are distinct elements in the Pauli set, their equality is false.
  simp [Pauli_X, Pauli_I];
  erw [ Subtype.mk.injEq ] at * ; aesop;
  have := congr_fun ( congr_fun a 1 ) 1; simp +decide at this;
  erw [ show ( beq.symm : BitVec 1 → Fin 2 ) 1#1 = 1 from rfl ] at this ; norm_num [ Qubit.X ] at this

@[simp] lemma neXY : (Pauli_X = Pauli_Y) = false := by
  -- By definition of Pauli_X and Pauli_Y, we know that they are not equal.
  simp [Pauli_X, Pauli_Y];
  -- By definition of $pX$ and $pY$, we know that $pX \neq pY$.
  simp [pX, pY];
  -- By definition of $X$ and $Y$, we know that $X \neq Y$ because their matrix representations are different.
  simp [Qubit.X, Qubit.Y];
  norm_num [ Complex.ext_iff ]

@[simp] lemma neXZ : (Pauli_X = Pauli_Z) = false := by
  simp +decide [ Pauli_X, Pauli_Z ];
  -- Since pX and pZ are different matrices, their corresponding unitaries are also different.
  simp [pX, pZ];
  simp +decide [ Qubit.X, Qubit.Z ]

@[simp] lemma neYI : (Pauli_Y = Pauli_I) = false := by
  -- By definition of Pauli matrices, we know that Pauli_Y is not equal to Pauli_I.
  simp [Pauli_Y, Pauli_I];
  -- By definition of Pauli-Y, we know that its (0,1) entry is -i, while the (0,1) entry of the identity matrix is 0.
  have h_entries : (pY : Matrix (BitVec 1) (BitVec 1) ℂ) 0 1 = -Complex.I ∧ (1 : Matrix (BitVec 1) (BitVec 1) ℂ) 0 1 = 0 := by
    bound;
  aesop

@[simp] lemma neYX : (Pauli_Y = Pauli_X) = false := by
  simp +decide [ Pauli_Y, Pauli_X ];
  -- By definition of $pX$ and $pY$, we know that $pX \neq pY$.
  simp [pX, pY];
  -- By comparing the entries of the matrices, we can see that Y and X are not equal.
  simp [Qubit.Y, Qubit.X];
  norm_num [ Complex.ext_iff ]

@[simp] lemma neYZ : (Pauli_Y = Pauli_Z) = false := by
  unfold Pauli_Y Pauli_Z;
  unfold pY pZ;
  -- By definition of Pauli matrices, we know that their corresponding matrices are different.
  simp [Qubit.Y, Qubit.Z]

@[simp] lemma neZI : (Pauli_Z = Pauli_I) = false := by
  -- Since the matrices are not equal, the equalities of the Pauli_Z and Pauli_I matrices cannot hold.
  simp [Pauli_Z, Pauli_I];
  -- Since pZ and the identity matrix are not equal, we can conclude that pZ ≠ 1.
  by_contra h_eq;
  -- The (0,0) entry of the Pauli Z matrix is 1, and the (0,0) entry of the identity matrix is also 1. So, the equality holds, but that doesn't help me. I need to look at another entry.
  have := congr_arg ( fun m => m 1 1 ) h_eq ; norm_num at this;
  -- The (1,1) entry of the Pauli Z matrix is -1, not 1.
  have h_pZ_11 : (pZ : Matrix (BitVec 1) (BitVec 1) ℂ) 1 1 = -1 := by
    exact?;
  norm_num [ h_pZ_11 ] at this

@[simp] lemma neZX : (Pauli_Z = Pauli_X) = false := by
  aesop;
  -- By definition of Pauli_X and Pauli_Z, we know that they are distinct.
  have h_distinct : Pauli_X ≠ Pauli_Z := by
    -- By definition of Pauli_X and Pauli_Z, we know that they are distinct because their matrices are different.
    simp [Pauli_X, Pauli_Z];
    unfold pX pZ;
    unfold Qubit.X Qubit.Z; aesop;
  -- Apply the distinctness hypothesis to obtain a contradiction.
  apply h_distinct; exact a.symm

@[simp] lemma neZY : (Pauli_Z = Pauli_Y) = false := by
  -- Since these two vectors are not equal, we conclude that the Pauli matrices are not equal.
  simp [Pauli_Y, Pauli_Z];
  -- By definition of Pauli matrices, we know that pZ ≠ pY.
  simp [pZ, pY];
  -- By definition of Pauli matrices, we know that Z and Y have different entries.
  simp [Qubit.Z, Qubit.Y]