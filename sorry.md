# Sorry inventory

Last updated: 2026-05-15.

Scope: active `sorry`/`admit` occurrences under `LeanQEC/**/*.lean`, excluding line comments and block comments.

Current active unresolved count: 0.

## Notes

- The remaining textual matches from `rg "sorry|admit" LeanQEC` are inside block comments.
- In `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean`, the old runtime-indexed `row_bv_correct` / `mutually_orth_correct` path is commented out. The maintained distance examples use `mutually_orth_nat_correct`.
- In `LeanQEC/Channels/Pauli_Channels.lean`, the unfinished `of_kraus_prob_unitary` sketch is commented out because it is outside the maintained distance-theorem dependency path.
- The maintained symmetry proof uses the Nat-valued `symmetry_constraints_aux` bound to avoid overflow from encoding `2 ^ nlog` as a `BitVec nlog`.
