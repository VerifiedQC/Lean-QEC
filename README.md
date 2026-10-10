# Quantum Error Correction in Lean

[![CI](https://github.com/VerifiedQC/Lean-QEC/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/VerifiedQC/Lean-QEC/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2605.16523-b31b1b.svg)](https://arxiv.org/abs/2605.16523)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc2-black.svg)](https://github.com/leanprover/lean4/releases/tag/v4.30.0-rc2)

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

```lean
theorem BB72_dist_6 : 6 ≤ BB72_css.toBSM.distance (by norm_num)
```

This theorem gives a lower bound for the distance of the 72-qubit bivariate bicycle code.

 ## Installing Lean-QEC

Install Lean through [elan](https://github.com/leanprover/elan) and install
[Git LFS](https://git-lfs.com/) for your platform (for example,
`brew install git-lfs` on macOS with Homebrew). The repository's `lean-toolchain`
file selects the Lean version.

The `.lrat` proof certificates are stored in Git LFS. Set up LFS before cloning,
then download the certificates and build from the repository root:

```sh
git lfs install
git clone https://github.com/VerifiedQC/Lean-QEC.git
cd Lean-QEC
git lfs pull
lake exe cache get
lake build
```

A clone with Git LFS configured normally downloads the certificates automatically;
`git lfs pull` also handles an existing checkout that still contains pointer files.
If you already cloned the repository, install Git LFS and run `git lfs install`
and `git lfs pull` from its root. `lake exe cache get` downloads Mathlib's cache,
not this repository's LFS certificates. See the
[Git LFS pull documentation](https://github.com/git-lfs/git-lfs/blob/main/docs/man/git-lfs-pull.adoc)
for download behavior.

Open the directory in VSCode for infoview access to files. To check the BB72
example explicitly, run:

```sh
lake build LeanQEC.Stabilizer.Examples.BB.BB72
```

The default build does not check every example. Examples using `bv_check` need
their actual LRAT files even if other lemmas use `bv_decide` to solve locally.

If a `.lrat` file contains text beginning with
`version https://git-lfs.github.com/spec/v1`, it is an LFS pointer, not a proof
certificate. Passing such a file to `bv_check` can report
`SAT solver produced invalid LRAT: offset 0: digit expected`; download the real
file with `git lfs pull` before retrying. A verification failure with a fully
downloaded certificate is a separate problem and is not necessarily fixed by
fetching LFS again.

 ## Future Directions
 - Figure out how far the framework currently scales, and where the bottlenecks are.
   Then, push further until we reach the $$[[144, 12, 12]]$$ BB code, or even $$[[288, 12, 18]]$$.
 - Formalization of codes with pen-and-paper-proof-based distance specifications like the Toric Code.
 - Including different error channels and proving the correctness of code distance under them.
 - Expansion to qudit codes.

 ## Citation

If you use Lean-QEC in your research, please cite the accompanying paper, [End-to-End Formalization of Quantum Error Correction](https://arxiv.org/abs/2605.16523) ([`CITATION.bib`](CITATION.bib)):

```bibtex
@article{ehatamm2026endtoend,
  title         = {End-to-End Formalization of Quantum Error Correction},
  author        = {Ehatamm, Mattias and Lee, Yi and Wu, Xiaodi and Tao, Runzhou},
  year          = {2026},
  eprint        = {2605.16523},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  journal       = {arXiv preprint arXiv:2605.16523}
}
```

 ## License

This project is licensed under the Apache License 2.0. See the [LICENSE](LICENSE) file for the full text and [NOTICE](NOTICE) for attribution.
