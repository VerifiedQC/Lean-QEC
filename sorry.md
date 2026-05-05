# Sorry inventory

Last updated: 2026-05-05.

Scope: active `sorry` occurrences under `LeanQEC/**/*.lean`, excluding line comments. The current active unresolved count is 15.

## Solved

These were proved during the recent sorry sweep.

| File | Line | Name / obligation | Commit |
| --- | ---: | --- | --- |
| `LeanQEC/Stabilizer/Basic.lean` | 642 | `BinSympMatrix.rowProduct_zero` | `950ec0f` |
| `LeanQEC/Stabilizer/Basic.lean` | 653 | `BinSympMatrix.rowProduct_single` | `950ec0f` |
| `LeanQEC/Stabilizer/Basic.lean` | 668 | `BinSympMatrix.rowProductSub_add` | `950ec0f` |
| `LeanQEC/Stabilizer/Basic.lean` | 724 | `BinSympMatrix.rowProduct_binaryImage` | `950ec0f` |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 68 | `vec_to_BitVec'_correct` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 171 | `loc_constraints_ith_jth_aux_correct` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 218 | `BitVec.ofNat_clog_eq_iff` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 232 | `loc_constraints_of_index`: final nonzero case | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 304 | `dot_product_correct` | `d7d62d7` |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 569 | `all_dot_zero_correct` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 745 | `mutually_orth_aux_descent` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 763 | `mutually_orth_aux_ascent` | working tree |
| `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean` | 853 | `inds_strict_mono_correct` | working tree |

## Not solved

Active unresolved proof obligations still in the tree:

| File | Line | Name / obligation |
| --- | ---: | --- |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 67 | `pivot_rank_correct` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 88 | `ker_from_non_pivot_correct` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 119 | `ker_from_rref_lin_indep` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 127 | `ker_from_rref_le_ker` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 138 | `ker_from_rref_correct` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 237 | `append_to_pivot`: `locs_increasing` field proof |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 252 | `rref_aux`: first proof argument to `append_to_pivot` |
| `LeanQEC/ComputerAlgebra/Basic.lean` | 252 | `rref_aux`: second proof argument to `append_to_pivot` |
| `LeanQEC/Stabilizer/BB.lean` | 29 | `BB_ind` |
| `LeanQEC/Stabilizer/Basic.lean` | 869 | `StabCode.undetectable_set_nonempty` |
| `LeanQEC/Stabilizer/Basic.lean` | 1031 | `BinSympMatrix.toStabCodeNontrivial_of_k_pos` |
| `LeanQEC/Stabilizer/Examples/BB72.lean` | 30 | `bb72_test_z` |
| `LeanQEC/Stabilizer/Examples/BB72.lean` | 36 | `bb72_test_x` |
| `LeanQEC/Stabilizer/Examples/Steane.lean` | 70 | `steane_ker_mat_correct`: rank lower bound for `steane_mat'` |
| `LeanQEC/Stabilizer/Examples/Steane.lean` | 71 | `steane_ker_mat_correct`: rank lower bound for `steane_ker'` |
