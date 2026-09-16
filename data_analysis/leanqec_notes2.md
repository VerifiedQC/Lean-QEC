# BB code distance verification — status, bottlenecks, optimizations

Companion to `leanqec_notes.txt`, which describes the encoding and the original measurements. This
file supersedes that document's performance figures: the timing tactic it relied on was wrong, and
the encoding it measured has since been changed.

Everything here was measured on one laptop (8 logical cores, 31.6 GB RAM, Lean 4.30.0-rc2, CaDiCaL
from the toolchain), with `set_option Elab.async false` so declarations elaborate one at a time and
wall-clock numbers are not distorted by concurrency.

---

## 1. What a distance proof consists of

`lt_dist_sat stabs ker k nlog` says no error vector of weight `≤ k` is both in the kernel of the
stabiliser matrix and outside its rowspace. Proving it for a concrete code goes through five stages:

| stage | what happens |
|---|---|
| preparation | a `simp only` unfolds the constraint definitions against the code's bitvector constants |
| normalization | `bv_decide`'s `bv_normalize` puts the goal in its `BitVec`/`Bool` fragment |
| AIG | the reflected `BVLogicalExpr` is bitblasted to an and-inverter graph |
| CNF | the AIG is converted to DIMACS and handed to CaDiCaL |
| checking | the returned LRAT certificate is compiled into Lean and run through the verified checker |

Preparation and normalization together are "formula generation" — they produce the CNF. Solving and
checking are what turn it into a theorem.

---

## 2. Current status

### Codes with complete distance proofs

`BB54`, `GB54`, `BB70`, `BB72`, `BB90` are `sorry`-free in `LeanQEC/Stabilizer/Examples/BB/`. They
close their rank and distance lemmas with `bv_check` against `.lrat` certificates committed next to
the source, so they replay without invoking a solver.

Optimization 4.1 invalidated their distance certificates, so all ten distance queries were re-solved
and the certificates replaced (see section 6). Their rank lemmas were unaffected throughout and
never needed regenerating. These five carry 4.1 only, not 4.2.

| code | re-solve (s) | Z cert | X cert | old Z cert | old X cert |
|---|---|---|---|---|---|
| BB54 | 58.2 | 1.34 MB | 1.33 MB | 1.39 MB | 1.38 MB |
| GB54 | 102.0 | 79.5 MB | 73.7 MB | 90.3 MB | 83.6 MB |
| BB70 | 95.6 | 51.5 MB | 56.7 MB | 57.8 MB | 59.7 MB |
| BB72 | 72.6 | 2.47 MB | 2.80 MB | 3.09 MB | 2.96 MB |
| BB90 | 147.3 | 93.6 MB | 102.8 MB | 105.0 MB | 104.6 MB |

Re-solve times are whole-module `lake build` wall clock, which includes normalization and
bitblasting as well as the two solver calls. Every new certificate is smaller than the one it
replaces — 4–18% — which is the encoding shrink showing up in the proof rather than any change in
solver configuration.

### Codes with incomplete proofs

| code | n | `sorry`s | missing |
|---|---|---|---|
| BB18 | 18 | 2 | — |
| BB108 | 108 | 4 | rank lemmas |
| BB144 | 144 | 2 | — |
| BB162 | 162 | 4 | rank lemmas |
| BB180 | 180 | 4 | rank lemmas |
| BB288 | 288 | 4 | rank lemmas |

BB144 was verified end to end previously (~30 min); BB162, BB180 and BB288 have never been.

### CNFs

All 22 distance queries (11 codes × X and Z) are in `bv_decide_queries/*_dist.cnf`, regenerated from
the current encoding by the modules in `LeanQEC/Stabilizer/Examples/Benchmarks/cnf_gen/`.

| code | n | Z query (vars / clauses) | X query | generation |
|---|---|---|---|---|
| BB18 | 18 | 658 / 1 678 | 658 / 1 678 | 28 s |
| BB54 | 54 | 3 178 / 6 550 | 3 094 / 6 091 | 30 s |
| GB54 | 54 | 4 990 / 9 667 | 4 990 / 9 667 | 38 s |
| BB70 | 70 | 6 876 / 13 093 | 7 038 / 13 120 | 37 s |
| BB72 | 72 | 4 310 / 9 530 | 4 841 / 9 575 | 33 s |
| BB90 | 90 | 9 434 / 17 086 | 8 522 / 16 456 | 38 s |
| BB108 | 108 | 14 648 / 19 831 | 13 127 / 19 372 | 42 s |
| BB144 | 144 | 19 023 / 31 695 | 23 562 / 32 568 | 64 s |
| BB162 | 162 | 32 897 / 41 213 | 29 915 / 39 215 | 83 s |
| BB180 | 180 | 52 311 / 52 087 | 40 014 / 47 182 | 94 s |
| BB288 | 288 | 78 905 / 92 317 | 113 750 / 93 253 | 273 s |

Generation time covers both queries for that code. BB162, BB180 and BB288 had no CNF before;
BB288 is the 288-qubit gross code.

**These files and the five in-tree proofs use different encodings.** The `cnf_gen` modules apply
both optimizations, 4.1 and 4.2. The `BB/*.lean` proofs apply only 4.1 — they still unfold
`loc_constraints` the slow way, because regenerating them was a repair of a break, not a rewrite.
The two are provably equivalent (`loc_constraints_iff_fast`) but are not the same CNF, so a
certificate from one does not check the other.

**Only BB72 has been confirmed UNSAT under this encoding.** The other 21 CNFs have never been
solved, so a semantic error at larger scale would not yet have surfaced.

The `*_rank.cnf` files were not regenerated, and do not need to be: the rank lemmas go through
`dot_col_aux`, a separate dot-product family that section 4 did not touch. Confirmed empirically —
BB72's two rank `bv_check`s still replay against their stored certificates.

---

## 3. Where the time actually goes

### The old timing tactic was wrong

`bv_decidet` logged six absolute timestamps and assigned them to columns positionally, but the third
was taken in `bvUnsatt` *before* `closeWithBVReflection` ran rather than after the solver returned.
Every column after `normalize` was shifted by one: the column labelled "solve" held the AIG-to-CNF
conversion time, and "end" lumped together the DIMACS write, the external solve, LRAT parsing and
trimming, certificate compilation and the LRAT check. `runExternal` had no instrumentation at all,
so the solve was never measured — which is why solve times looked implausibly small.

The rewritten tactic records elapsed times per stage rather than absolute timestamps, so a row
cannot desynchronise from its header, and inlines `runExternal` and `LratCert.toReflectionProof` to
expose eleven stages: `normalize, reflect, bitblast, cnf, dimacs, solve, lrat_read, expr_def,
cert_def, verify, assign`. Every invocation writes exactly one complete row, including the
early-exit paths, so a counterexample or a normalization-closed goal cannot corrupt the next row.

### Corrected phase breakdown (old encoding, ms)

| code | normalization | aig | cnf | solving | checking | total |
|---|---|---|---|---|---|---|
| BB72 | 20 020.5 (92%) | 45.3 | 10.0 | 571.2 (3%) | 998.3 (5%) | 21 687.8 |
| BB70 | 16 460.6 (45%) | 52.6 | 15.4 | 12 924.8 (36%) | 6 131.1 (17%) | 36 304.9 |
| BB90 | 27 628.2 (44%) | 65.6 | 15.8 | 22 613.7 (36%) | 10 495.4 (17%) | 62 167.0 |
| BB144 | 91 072.4 (21%) | 196.2 | 41.0 | 229 758.1 (53%) | 100 458.4 (23%) | 434 447.6 |

Solving is 36% of the tactic for BB70/BB90 and 53% for BB144, against the ~0.03% the broken logger
implied. BB144's solve was reported as 19 ms; it is 229.8 s.

Normalization dominates only for the smallest code. The trend matches the earlier observation that
formula preparation scales with code size while solve time scales with distance — extrapolating,
solve and check are what will dominate beyond BB144.

### Checking is driven by certificate size

| code | LRAT steps | certificate | `verify` stage |
|---|---|---|---|
| BB72 | 34 844 | 4.8 MB | 0.21 s |
| BB70 | 374 906 | 95 MB | 4.1 s |
| BB90 | 529 231 | 174 MB | 7.2 s |
| BB144 | 2 388 478 | 1.29 GB | 80.8 s |

Within checking, `verify` — compiling and running `verifyBVExpr` by native evaluation — is the
largest single component.

### Proof size vs. solve and check time

BB72's distance query was run 16 times on the *identical* CNF under different CaDiCaL
configurations. The original plan was to vary `--seed`, but that does nothing here: seeds 1 and 7
produce byte-identical LRAT proofs, and `--seed`, `--stabilize=false`, `--walk=false` and
`--target=0` all reproduce the default proof exactly. The solve is well under a second, so CaDiCaL's
randomised components never fire. (Earlier pysat seed experiments showed variance because those were
much longer solves.) Search parameters — `--reduceint`, `--restartint`, `--phase`, `--lucky`,
`--elim`, `--chrono`, `--bump` — do change the derivation.

Across the 16 configurations the LRAT file ranged 2.60–85.07 MiB and solve time 528 ms – 15.6 s.

| | all 16 | excluding `bump=false` (n=15) |
|---|---|---|
| solve vs. LRAT size | r = 1.000 | r = 0.821 |
| check vs. LRAT size | r = 0.999 | r = 0.696 |
| check vs. trimmed certificate | r = 0.999 | r = 0.837 |

The near-perfect correlations are carried by one extreme configuration. Over the other 15, which
span only 2.6–4.6 MiB, the relationship is much looser. Proof size predicts the *order of magnitude*
of both costs well, not small differences. Checking tracks the trimmed certificate better than the
raw LRAT file, which is expected — the trimmed certificate is what gets compiled and checked.

**Reducing unsatisfiable-core size therefore pays twice: once in solve time, again in the size of
the proof that has to be checked back in Lean.**

### The formula-generation bottleneck, before optimization

Profiling BB162's CNF generation under the old encoding (1 073 s of profiled work):

| step | calls | total |
|---|---|---|
| `simp` (includes `bv_normalize`'s own simp) | 345 | 535.6 s |
| **typeclass inference of `Decidable`** | 349 | **370.3 s** |
| process pre-definitions | 1 | 79.6 s |
| type checking | 1 | 53.7 s |
| share common exprs | 1 | 21.6 s |

A third of the total was `Decidable` instance synthesis, growing from 106 ms to 2.6 s per call. The
cause was `loc_constraints_ith`, which equates a `Bool` (`errs[i]!`) to a `Prop`, so every position
needed a `Decidable` instance for a term that grew with the recursion — quadratic.

---

## 4. Optimizations performed

Both changes shrink the Lean term, which is what `simp` and `bv_normalize` cost is proportional to.
Both leave the verified translation intact: no existing proof changed except two `unfold` sites, and
the `sorry` count in `BitVecCorrectness.lean` is unchanged at 5, all pre-existing.

### 4.1 `BitVec.dot_product` — XOR chain to logarithmic fold

`dot_product_aux` expanded to one `x[c] && y[c]` leaf per bit per matrix row:
`(stabdim + kerdim) * n` leaves — 26 892 for BB162, **84 672 for BB288**.

It is now the parity of the bitwise AND, computed by a halving XOR fold: `⌈log₂ n⌉` operations per
row instead of `n`. Using *increasing* shifts (1, 2, 4, …) rather than decreasing makes the fold
invariant a contiguous bit range, which is what kept the correctness proof short.

The old chain survives as `dot_product_aux`, and `BitVec.dot_product_eq_aux` proves the two agree,
so `dot_product_correct` keeps its original proof after a single rewrite. Supporting lemmas:
`BitVec.xorRange_add`, `BitVec.xorRange_of_width_le`, `BitVec.getLsbD_xorFold`,
`dot_product_aux_eq_xorRange`.

The fold depth is `Nat.clog 2 n`, so the definition stays generic with no width side-condition.
Plain `simp` cannot evaluate `Nat.clog`, so **every call site must have
`have hclog : Nat.clog 2 n = d := by norm_num` in scope and must list `hclog` and `BitVec.xorFold`
in its simp set.** This is not optional cosmetics — see section 6, it is the difference between a
proof and a silent wrong answer.

### 4.2 `loc_constraints` — one-hot union

`loc_constraints` compared every index slot against every position: `n * k` comparisons (4 896 for
BB288), each equating a `Bool` to a `Prop`.

`loc_constraints_fast` shifts each slot into place and ORs the results — `k` terms, as one plain
bitvector equation. `loc_constraints_iff_fast` proves equivalence, given `n ≤ 2 ^ nlog` (enough index
bits to name every position without wrapping); this is discharged by `norm_num` at each call site and
holds for every code in the repository. Supporting lemmas: `getLsbD_loc_slot`,
`getLsbD_loc_union_aux`.

Because the result is a plain `BitVec` equation rather than `Bool = Prop`, this also eliminates the
`Decidable` synthesis that was a third of generation time.

### 4.3 Measured effect

BB72, one query, three encodings:

| step | chain | + fold | + one-hot |
|---|---|---|---|
| `simp` total | 24.3 s | 7.23 s | — |
| typeclass inference | 14.4 s | 0.75 s | — |
| `bv_normalize` | 19.56 s | 6.85 s | **2.35 s** |
| type checking | 6.42 s | 0.002 s | — |
| process pre-definitions | 5.46 s | 0.002 s | — |
| share common exprs | 2.03 s | 0.0002 s | — |
| wall clock | 84.6 s | 36.1 s | — |
| CNF (vars / clauses) | 7 113 / 18 621 | 4 742 / 10 538 | 4 310 / 9 530 |

BB162, one query:

| | chain | + fold | + one-hot |
|---|---|---|---|
| `simp` total | 535.6 s | 52.9 s | — |
| `Decidable` inference | 370.3 s | 11.8 s | — |
| `bv_normalize` | 153.8 s | 50.1 s | **10.1 s** |
| wall clock | ~960 s | 95.7 s | **54 s** |
| CNF clauses | 87 248 | 43 481 | 41 213 |

BB162 generation went from ~16 minutes to 54 seconds (~18×). BB144's two queries went from a
34-minute module build to 64 s. BB288, previously never attempted and projected to risk exhausting
31.6 GB, completes in 126 s for the Z query.

### 4.4 Optimizations considered and not done

After 4.1 and 4.2 the measurement moved: `bv_normalize` is now 10.1 s of BB162's ~11 s of tactic
work, and the preparation `simp` is a rounding error. Three further ideas were therefore dropped as
targeting costs that had already shrunk:

- **Tagging the constraint definitions `@[bv_normalize]`** to skip the separate preparation pass
  would move ~1 s of work *into* the 10 s stage — plausibly a wash or a regression.
- **Storing matrix rows as separate constants** instead of extracting them from one giant literal
  targets the same shrunken preparation cost, and would need the data files regenerated.
- **`Elab.async`** is a no-op: the real `BB*.lean` files never set it; only the measurement modules
  do, where serialising is what we want.

Making `parity_constraints` and `rowspace_constraints` uniformly `Bool` was also left alone. They use
`∧`/`∨` over `Bool` coercions, which are `x = true` and need no `Decidable` search, so the change
would be cosmetic rather than a speedup.

---

## 5. Current bottlenecks

1. **`bv_normalize`** is now ~95% of formula generation. It is inside `bv_decide` rather than our
   code, so improving it means either shrinking the term further or changing the tactic itself.
2. **Solving**, for anything past BB90. Unmeasured for the new CNFs — a BB162 solve attempt was
   abandoned after 10 minutes.
3. **Checking**, which scales with certificate size and reached 1.29 GB / 80.8 s of `verify` for
   BB144 under the old encoding. Not yet re-measured.

The lever that helps 2 and 3 together is unsatisfiable-core size, per section 3.

---

## 6. Known problems

- **An incomplete simp set silently turns the distance goal satisfiable. Fixed, but the failure
  mode is the dangerous one.** `BitVec.dot_product` now unfolds to `xorFold (Nat.clog 2 n)`. A simp
  set that can neither evaluate `Nat.clog` nor unfold `BitVec.xorFold` leaves an opaque term in the
  goal, and `bv_decide` abstracts that term as a *fresh free variable* rather than rejecting it. The
  formula it then hands the solver is a weaker one that happens to be SAT, and the tactic reports
  "The prover found a potentially spurious counterexample" — which reads like a `bv_decide`
  incompleteness message, not like "your encoding did not unfold". Observed on `BB54` during
  regeneration. The fix is the `hclog` + `BitVec.xorFold` requirement in section 4.1, now applied to
  all five complete proofs and all eleven `cnf_gen` modules.

  The reason this is worth calling out: the symptom was *not* a failed proof. Had the goal been
  stated the other way round, or had the abstracted formula come out UNSAT for an unrelated reason,
  this would have produced a certificate that verifies and proves nothing. Any future change to
  `dot_product`'s definition needs every call site's simp set audited in the same pass.

- **The distance certificates were stale after the encoding change — now regenerated.** Changing
  `dot_product` and `loc_constraints` changes the CNF, so the committed certificates no longer
  matched the formula. `BB72` failed at both distance lemmas with "The LRAT certificate could not be
  verified"; all five codes were re-solved and their certificates replaced (table in section 2). The
  tactic lines moved from `bv_check ...-120-2.lrat` / `-131-2.lrat` to `-121-2.lrat` / `-133-2.lrat`
  because the inserted `hclog` line shifts the tactic down one line, and `bv_decide?` names
  certificates by source position.

- **The 22 CNF files have not been validated by solving the files themselves.** The regeneration
  above established that the ten distance queries of `BB54`, `GB54`, `BB70`, `BB72` and `BB90` are
  UNSAT *under optimization 4.1*, which is what those proofs use. It did not touch the files in
  `bv_decide_queries/`, which additionally carry 4.2 (see section 2). That is strong evidence for
  those ten files, since 4.2 is proved equivalent to the slow path, but it is not a check of them.
  The twelve queries of `BB18`, `BB108`, `BB144`, `BB162`, `BB180` and `BB288` have not been solved
  at all under the current encoding; `BB162`, `BB180` and `BB288` have never been solved at any
  encoding. Running all 22 on a cluster is the outstanding task.
- **`loc_constraints_iff_fast` needs `n ≤ 2 ^ nlog`.** It holds for every code here, but the rewrite
  would silently fail to apply for a code declared with too few index bits, falling back to the slow
  path rather than erroring.

---

## 7. Reproducing

```bash
# regenerate one code's CNFs (expected to FAIL: the solver wrapper returns no result)
lake build LeanQEC.Stabilizer.Examples.Benchmarks.cnf_gen.BB288_cnf

# per-stage timings land in cnf_gen_times.csv; roll them up into the five phases
python data_analysis/bvd_stage_rollup.py cnf_gen_times.csv
```

`cnf_loggers/<CODE>_<z|x>.bat` is the `sat.solver` wrapper: it copies the DIMACS file into
`bv_decide_queries/` and exits without printing a result, so `bv_decidet` fails *after* the CNF is
written. The row it logs carries status `error`, which is the expected outcome for these modules.

To re-solve a distance lemma whose certificate has gone stale, swap the `bv_check "…"` line for
`bv_decide? (timeout := 9999) (maxSteps := 9999999)` and build the module. The tactic solves, writes
a fresh `.lrat` next to the source, and prints the exact `bv_check` line to paste back — including
the filename, which encodes the tactic's line and column, so it changes whenever the lemma body
shifts. Delete the certificate the old line referred to; nothing else will.
