# Quantum Error Correction in Lean

This project formalizes and verifies the theory of Quantum Error Correction in Lean in an end-to-end fashion, from basic Quantum theory to abstract properties. Some accomplishments include:
 * Formalizing basic quantum computing concepts such as Qubits, Quantum States, and the Pauli Group.
 * Verifying the link between the Pauli Group and the Binary Symplectic Representation.
 * Formalizing Stabilizer Codes and CSS codes, reasoning about their code properties.
 * A SAT-assisted computer algebra pipeline for the verification of Stabilizer Code properties like code distance.
 * Concrete distance verification for a number of codes such as large codes belonging to the Bivariate Bicycle family.

This project is built on top of Mathlib4.

 ## Distance Verification

The primary innovation of Lean-QEC is its set of tools for automatic verification of code properties such as code distance. This is accomplished through a novel code parameters-to-SAT translation fully verified in Lean, allowing for full confidence in values previously only known through opaque calculation.

 ## Major Theorems

 ```lean
theorem BinSympMatrix.distance_eq_distance {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm).distance = B.distance hk
```

This theorem proves the relationship between the binary symplectic formulation of distance and the stabilizer-theoretic notion.

 ```lean
theorem bitvec_sat_translation_correct
  {n k₁ k₂ xkersize zkersize : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xker : Matrix (Fin xkersize) (Fin n) (ZMod 2))
  (xker_correct : xker.is_ker_for css.H₂)
  (zker : Matrix (Fin zkersize) (Fin n) (ZMod 2))
  (zker_correct : zker.is_ker_for css.H₁)
  {dist : ℕ}
  (dist_le : dist ≤ n)
   :
  lt_dist_sat (flatten_matrix css.H₁) (flatten_matrix xker) (dist - 1) (Nat.clog 2 n) →
  lt_dist_sat (flatten_matrix css.H₂) (flatten_matrix zker) (dist - 1) (Nat.clog 2 n) →
  dist ≤ css.toBSM.distance (by apply NeZero.pos)
```

This theorem links the Binary Symplectic distance of a CSS code to the SAT formulation of the distance, allowing for automatic distance verification.

 ## Installing Lean-QEC
 - Clone this repository.
 - In a terminal in the top-level directory, run `lake exe cache get` to fetch Mathlib and dependencies.
 - Run `lake build` to build the project.
 - Open the directory in VSCode for infoview access to files.

 ## Future Directions
 - Formalization of codes with pen-and-paper-proof-based distance specifications like the Toric Code.
 - Including different error channels and proving the correctness of code distance under them.
 - Expansion to qudit codes.