# LU and pivoting audit for the dense factorization sprint

Inspected 2026-11-24 at `/home/ubuntu/nlalib`, HEAD `7cbea9d1`. This is a planning audit; proposed names and signatures below are not existing or checked declarations. No library or registry files were changed.

## What already exists

The exact mathematics is much further along than the executable factorization layer.

| File | Reusable declarations | Meaning and limitation |
|---|---|---|
| `NLAlib/Matrix/Factorizations/LU.lean` | `IsLU`, `IsLU.unique`, `IsLU.mulVec_eq_iff`, `luLower`, `luUpper`, `eq_luLower_mul_luUpper`, `isLU_luLower_luUpper` | Unit lower / upper triangular factorization; total elimination recurrence; realization under nonzero pivots or zero-column compatibility. These are mathematical functions, not builder execution certificates. |
| Same | `exists_perm_forall_weight_gaussState_le`, `exists_perm_isLU`, `exists_perm_isLU_norm_le` | An existential row permutation can make each pivot maximal for a chosen real weight. It does not construct a stored-word scan or execute swaps. |
| `NLAlib/Matrix/Factorizations/LUGeneral.lean` | `isLU_luLower_luUpper_of_forall_eq_zero`, `isLU_luLower_luUpper_of_forall_norm_le`, `norm_luLower_apply_le_one`, `norm_luUpper_apply_le`, `exists_perm_isLU_luLower_luUpper_norm_le` | Includes singular matrices: zero pivot with zero column below it is valid. Partial pivoting multipliers are bounded by one; upper row i grows by at most `2^i` times an entry bound. |
| `NLAlib/Matrix/Factorizations/GaussState.lean` | `gaussState`, `eq_gaussState_add_sum`, `gaussState_submatrix_left`, `gaussState_submatrix` | Exact elimination telescoping; row reindexing or simultaneous row/column reindexing commutes with an already eliminated prefix when earlier pivots are fixed. Useful for dynamic pivot invariants. |
| `NLAlib/Computation/BLAS/Triangular.lean` | `exec_trsvLower`, `IsArithErrSem.exec_trsvLower`, `IsRelErrSem.exec_trsvLower_add_mulVec_eq` | Real executable lower triangular solve, success and componentwise backward error. No upper triangular builder/solve found. |
| `NLAlib/Computation/RoutineFrames.lean`, `ScalarFrames.lean` | `ReadsDecoded`, `Writable`, `IsBlockRoutine`, `Store.writeBlocks_eq_some_of_read`, `executionComposable_single`, `exec_scalar_copy`, etc. | Shared execution/frame infrastructure; reuse rather than adding local copies. |

Searches of Mathlib matrix files found no LU/PLU decomposition API. Mathlib supplies `Matrix.swap`, `Equiv.swap`, permutation matrices and swap multiplication lemmas (`Mathlib/LinearAlgebra/Matrix/Swap.lean`, `Permutation.lean`), and pure selector lemmas `List.argmax`, `List.argmax_eq_some_iff`, `List.le_of_mem_argmax`, `List.index_of_argmax` (`Data/List/MinMax.lean`). These can justify pure selectors and deterministic first-tie behavior; they do not certify an imperative scan.

Searches found no LU/PLU routine certificate, no factorization builder, no LU rounding trace, no componentwise LU error contract, and no stored pivot scanner/swap kernel. Searches also found no complete, rook, threshold or scaled-partial executable pivoting implementations.

## Model constraints that should drive the design

1. Use existing `IsLU (A.submatrix σ id) L U` for row-pivoted exact output, and `IsLU (A.submatrix σ τ) L U` for two-sided pivoting. Do not add a competing factorization predicate merely to spell `PLU`.
2. Pick and document the permutation direction. Existing statements use `A.submatrix σ id = L * U`. A stored pivot log must be decoded by the same convention; do not silently exchange σ with its inverse.
3. `IExp` cannot depend directly on a Lean scalar value. Store the selected index using `litIdx`, then recover it with the existing bounded `bindIdx`. A scan using this route needs `IsIndexExactSem dec B I.sem`, with B covering all written index literals. `IsRelErrSem` alone does not make index literals or conversions exact.
4. `IsRelErrSem.cmp_eq`, `.cmp_lt`, `.cmp_le` are exact on decoded real values. Exact negation plus comparison with an exactly decoded zero permits an absolute-value scan without a new primitive. Complex norm comparisons would require an explicitly analyzed word representation/norm routine; start scalar-word executable routines over real decodings while keeping pure theory general over `RCLike`.
5. Real partial pivoting must compare absolute values of the actual rounded active column, not an ideal `gaussState A`. An exact specialization can connect them afterward. Squaring values to compare them introduces rounding and range issues; use sign and exact negation instead.
6. A zero maximal pivot means the active column is all zero. Skip its divisions and updates; do not fail or falsely require invertibility. A no-pivot variant may instead return explicit breakdown status when a zero pivot has nonzero entries below it. Guard division on the actual decoded pivot.
7. In an in-place packed LU matrix, later row swaps must swap the already stored multiplier prefix as well as the active matrix. Swapping only the trailing block yields the wrong global L. A two-output L/U design must explicitly swap earlier columns of L.
8. Copies/swaps need no rounding arithmetic contract, only initialized reads, writable capacity, scoped scratch and explicit alias cases. This makes them the most robust first executable work.
9. Full successful rounded LU cannot assume only that the exact input is nonsingular. Rounded pivots can vanish. Prove an actual-run trace with status first, then derive all-success under a suitable explicit perturbation/conditioning regime. Do not assume the desired factorization residual as an execution precondition.
10. Certificates contain composition, success and exact block writes, with a typed decoded guarantee. Counts and peak memory remain separate. New compiled `<spec>Prog` trees and cost targets require maintainer registration, forbidden to agents by `AGENTS.md` §2; prepare concrete target proposals without modifying the registry.

## Suggested shared interfaces

Keep the exact output relation as existing `IsLU`; introduce only genuinely missing decoded numerical guarantees. Prefer one two-sided factorization error guarantee so row-only and unpivoted cases specialize permutations to identity. Proposed mathematical content:

```lean
-- Schematic proposed interface, pending design review.
structure IsLUErr {n : Type*} [Fintype n] [LinearOrder n]
    (ε : ℝ) (A L U : Matrix n n ℝ) (σ τ : Equiv.Perm n) : Prop where
  lower : IsUnitLowerTriangular L
  upper : U.IsUpperTriangular
  residual : ∀ i j,
    |(A.submatrix σ τ - L * U) i j| ≤
      ε * ∑ k, |L i k| * |U k j|
```

The zero-error bridge concludes existing `IsLU (A.submatrix σ τ) L U`; monotonicity needs nonnegativity assumptions on the parameter comparison, as appropriate. Pure math can later generalize entrywise magnitude beyond real decodings. To avoid falsely promising full factorization on breakdown, the output guarantee must distinguish a complete result from a prefix/status result. Do not simply make an uninhabited certificate whose `run` demands full factorization for every input.

An actual execution theorem for the first swap primitive should have the form:

```lean
-- Schematic statement; names and complete binder list to be designed.
theorem exec_swapRows
    (I : Interp P ι K C) (st : St P K C)
    (hA : Holds ... A) (hrow : r < n) (hs : s < n) :
    ∃ out, exec I (swapRows tag n A_buffer offset r s).run st = some out ∧
      out.store = ... ∧
      Holds ... (A.submatrix (Equiv.swap r s) id)
```

The final version should expose `writeBlock`/`writeBlocks`, not just `Holds`, handle `r = s`, nonzero offsets and empty column ranges, and be computable. This is a run lemma about a builder, not a new registered program or published cost result.

## Parallel work packages and dependencies

| ID | Package and owner boundary | Depends on | 48h priority / completion criterion |
|---|---|---|---|
| LU0 | Shared design: packed column-major storage, permutation direction, first-tie rule, status, real decoding | Existing model | Must do first. Freeze small interfaces before agents code. |
| LU1 | Copy-based row and column swaps with scoped scalar scratch; exact block frames; same-row/column cases | LU0 | High. Kernel/run lemmas complete and checked. Most useful first slice. |
| LU2 | Absolute-value argmax scan over a strided column, then active submatrix; index-literal/binder round trip | LU0 | High. Success under arithmetic + index contracts; output in range; first-tie maximum of actual words; store frame. |
| LU3 | One no-pivot elimination step and packed prefix invariant; zero-pivot guard/status | LU0 | High. Do not wait for scanner. Actual rounded trace theorem, exact specialization to existing elimination. |
| LU4 | Full no-pivot LU recurrence, realization/certificate and zero-error specialization | LU3 | High but larger. Success/status theorem at every size; full factorization in admissible exact case. |
| LU5 | Partial-pivoted LU driver, permutation log decoding and multiplier-prefix swaps | LU1, LU2, LU3 | High stretch. Exact realization first; actual rounded pivot maximality separately. |
| LU6 | Componentwise backward-error analysis from actual traces; normwise consumer | LU3 + reviewed `IsLUErr` | High parallel math track. Explicit named rounding parameter and zero-error bridge; no floating-point growth claim borrowed from exact recurrence. |
| LU7 | Complete pivoting: active-submatrix scan and both permutation logs | LU1, LU2, LU3, LU5 invariant experience | Stretch. Reuse LU error relation; certify policy separately from correctness. |
| LU8 | Scaled partial / threshold pivot policies | LU2, scale convention and zero-scale handling | Stretch. Initial vs updated row scales must be fixed. Rounded quotient comparisons do not equal exact ratios without analysis. |
| LU9 | Rook pivot policy | LU1, LU2, proven termination/tie convention | Defer implementation unless earlier work completes. `whileFuel` requires a proved bound; arbitrary fuel is not a termination argument. |
| LU10 | Upper triangular solve + LU solve consumer | Existing lower solve, LU1, error interface | Useful parallel track. Upper solve can be derived via reversed indices but builder/run/alias proof is still necessary. |
| LU11 | Cost proofs and registry proposal | Concrete trees/interfaces | Separate integration step with maintainer-owned target registration. |

For available four-agent concurrency, run shared infrastructure, no-pivot LU, Cholesky, and integration/error-contract review concurrently; rotate the infrastructure agent onto partial-pivoted LU after swaps/scans land. Avoid assigning a whole independent algorithm to each agent before freezing storage and status conventions.

## Recommended first 48h gates

* Hours 0–4: freeze LU0 plus error/status relation; identify module closures touched by registered targets before editing existing definitions. Prepare target proposals early, but do not let registration prevent development of ordinary routine/run proof infrastructure.
* Hours 4–16: LU1 swaps, LU2 scanner, LU3 actual one-step trace and exact bridge in parallel with Cholesky. Deliver at least one success-and-write frame for a nontrivial actual builder.
* Hours 16–30: complete no-pivot recurrence; integrate row-pivoted driver; prove local-to-global residual analysis independently.
* Hours 30–40: certify implemented complete routines and integrate a solve consumer. Complete pivoting is stretch; scaled/rook/threshold work can finish as precise reviewed designs rather than unsupported implementation claims.
* Hours 40–48: stop changing interfaces, run targeted checks then isolated `stage_check.sh`; resolve defects and report theorem-by-theorem readbacks, remaining blockers and target proposals.

Acceptance means actual `exec` success and exact store frame plus decoded guarantee for concrete instruction builders, with no assumed local-error trace or existential permutation substituted for execution. A design note, pure existence result, and executable certificate are three distinct deliverables.

## Validation and provenance

Read repository agent/contributor contract, complete rules digest, Matrix/Computation rules and design/program/statement/vocabulary guides. This audit changes only this external Markdown report; it introduces no Lean declarations and does not claim a library check passed. Repository stage checks belong to the integration work after any library changes.

## First implementation wave

After root reviewed the design, implemented two files in `/home/ubuntu/work/nlalib-dense-factorizations`:

* `NLAlib/Matrix/Perturbation/LUErr.lean`: generalized `IsLUErr` over `RCLike` and arbitrary finite ordered index types. Same triangular field names as `IsLU`, zero-error bridges in both directions, monotonicity, and a componentwise solve-residual consumer combining factorization error with arbitrary upper/lower solve residuals. Exact-solve specialization follows. `lake lean` and source rules pass without warnings.
* `NLAlib/Matrix/Computation/RowSwap.lean`: actual rectangular column-major row-exchange builder with one scoped scratch word, composability and successful execution with a single net packed block write plus final `Holds` of the exchanged matrix. Arbitrary word carrier and scalar semantics; same-row swaps, empty column ranges and arbitrary offsets supported. `lake lean` passes without warnings. Source checker reports B1 because its suffix regex mistakes builder name `swapRows` for a numerical bound ending in `Rows`; reported to root without changing checks or allowlists. Naming review pending.

These are concrete first slices, not complete LU/PLU factorization programs or their certified floating-point instances. Full repository validation is the root integration task.
