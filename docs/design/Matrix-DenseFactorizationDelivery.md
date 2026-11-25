# Dense factorization implementation and validation

Base `7cbea9d1`; branch `design/dense-factorization-routines`; worktree
`/home/ubuntu/work/nlalib-dense-factorizations`. The maintainer approved the seven cost targets
and requested commit/push on 2026-11-25. The original checkout's
user-owned target approval and `.claude/` directory remain preserved. Four agent slots support
three parallel implementation/review lanes and one integration lead in successive waves.

This report supersedes the [historical six-wave checkpoint](dense-factorization-audits/six-wave-delivery.md).
The [execution plan](Matrix-DenseFactorizationRoutines.md) remains the design history; this
report records the implemented scope. Resource publication has a separate
[approved target review](Matrix-DenseFactorizationTargetProposal.md).

## Implemented algorithms and certificates

| Family | Actual stored execution and guarantee | Domain or qualification |
|---|---|---|
| Unpivoted LU | Canonical lower/upper factors, two original output writes, zero-error `IsLURoutine` | Nonzero canonical elimination pivots |
| Partial PLU | Actual row log, singular-capable factorization, multiplier bound one, `IsPLURoutine` | All exact real square inputs, including zero and empty |
| Complete PLUQ | Independent actual row/column logs, earlier upper-column swaps, four original writes, `IsPLUQRoutine` | All exact real inputs; both axes are explicit |
| Fixed-scale PLU | Computes original row infinity norms once, swaps scales with rows, full factor driver and certificate | Singular-capable; exact division-free ratio comparisons; no multiplier-one assertion |
| Rook PLUQ | Alternating active-row/column search, strict-growth termination, mutual maximum, full driver/certificate | All exact real inputs; local maximum does not mean complete maximum |
| Threshold PLU/PLUQ | Rational threshold policy, exact acceptance/column quality, full drivers/certificates | `0 < τ ≤ 1`, multiplier bound `1/τ`; stored threshold comparisons are exact |
| SPD Cholesky | Full canonical factor, one original factor write, zero-error `IsCholeskyRoutine` | Exact real positive definite input; source/output overlap |
| Semidefinite Cholesky | Zero-safe columns and updates, full canonical Gram factor, nonnegative diagonal; exact typed routine certificate | Exact PSD input, including rank deficiency and zero matrices |
| Pivoted PSD Cholesky | Stable active-diagonal choice, symmetric swaps, actual single log, canonical jointly permuted Gram factor, exact typed routine certificate | Singular PSD inputs, source/output overlap, zero-safe arithmetic and handle-free empty execution |
| Scalar-pivot LDL | Actual LU followed by diagonal extraction, full `IsLDL` and original output writes | Hermitian input with nonzero 1×1 canonical pivots; indefinite inputs permitted |
| Blocked LU | Clipped panels, two actual packed GER rectangles per pivot, one packed GEMM trailing update per panel | Positive block width and exact panel count; nonzero canonical pivots |
| Blocked Cholesky | Actual blocked LU plus canonical diagonal square roots, explicit upper zeros and lower-column scaling | SPD input; exact zero-error certificate; source/output overlap |
| Factor then solve | Cholesky/LU/PLU/PLUQ factorization followed by actual triangular solves, exact original-system solution | Nonsingular input for LU/pivoted solves, SPD for Cholesky; RHS-only net write |

Singular PSD factors use their exact nonnegative-diagonal contract, rather than the existing
strict-positive `IsCholesky`/`IsCholeskyErr` predicates. These existing predicates are unchanged.

The common pivot-policy verifier is reused by complete, rook and threshold drivers. Its
contract records actual writes, active indices, quantitative column quality and the fixed-column
promise; it does not assume factorization success. The original complete-pivot runtime tree is
preserved by `rfl`, and unchanged rounded complete-pivot consumers were rechecked against it.
Scaled pivoting retains its distinct fixed-scale invariant.

Permutation convention: factorization is of `A.submatrix σ τ`, where the actual swap logs map
current positions to original positions. Row-only factorization uses `τ = id`. Pivoted solves
apply the row permutation to the RHS and the inverse column permutation to the solution.
Independent executable checks reconstruct these logs, including different three-cycles.

`LDLMathlib.lean` proves a bridge to Mathlib's actual ordered-finite LDL construction. Its
lower factor is unit triangular and its diagonal real; on SPD `Fin N` inputs its lower factor
and diagonal agree with the executable algorithm's canonical LU data. This is separate from a
Bunch–Kaufman or 2×2 indefinite pivoting algorithm, which is not implemented here.

## Rounded and finite-range guarantees

The unchanged full partial- and complete-pivoted LU drivers have successful execution and
footprint proofs for generic stored words under the relative-error and exact-index contracts.
They preserve exact triangular zeros/unit lower diagonal and have componentwise `IsLUErr`
allowance `roundingFactor (N+4) u` when `u < 1`. Here
`roundingFactor n u = (1-u)^(-n)-1`; it is not the classical `nu/(1-nu)` notation.
The negative literal, coefficient division, both GER multiplications and lower division are
accounted for. No exact elimination trajectory or assumed successful run replaces the rounded run.

Full rounded Cholesky derives nonbreakdown from an original spectral band
`0 < μ`, `μ I ≤ A`, `‖A‖ ≤ B`, `u ≤ 1/10`, and an explicit Schur-error recurrence below `μ/2`.
With its proved uniform factor-entry allowance e, the absolute spectral residual budget is
`(N*e) * (2*sqrt(B) + N*e)`. The complete actual saved-row/column Schur update is covered,
including retired entries and exact upper-factor zeros. These are conservative,
conditioning-dependent estimates, not sharp condition-independent backward stability.

The finite-range extension uses mixed relative/additive errors and explicit
`CholeskyRangeConditions` depending only on order and numeric input parameters. It proves
root/divisor margins and exact-result range before each actual instruction. The concrete
`BinaryCholesky` theorems instantiate these laws for the library's mathematical bounded binary
quantizer, including its underflow allowance and maximum finite value. That quantizer rejects
exact results outside its finite interval and has no signed-zero/NaN/native-IEEE linkage.
Native Float regression tests do not prove that missing backend accuracy theorem.

Rounded factor-then-solve composition is supported by the error interfaces and triangular-solve
certificates. Concrete full pivoted factor-and-solve drivers currently have exact zero-error
instances; no complete rounded pivoted-solve driver theorem is claimed.

## Storage, blocking and resources

Generic-word block gathers/scatters support leading dimensions, offsets and complete gap frames
without adding a fictitious scalar zero. Their positive-area distinct-buffer condition is
explicit. Block Schur updates compute the full product before overwriting C, permitting factor/C
aliasing. Trailing updates gather actual strided views, run GEMM, scatter only the trailing square,
and retain the exterior. Empty dimensions, zero panel width, remainders and oversized blocks
are covered. The GEMM is the existing reference scalar IR kernel; this is not native BLAS dispatch
or a hardware/cache-speedup claim. Blocked drivers are exact and unpivoted.

Seven fixed actual symbolic trees have successful-run static count, cell and bit bounds.
Closed additional-live-word bounds are: LU/Cholesky `N²+2N+3`, semidefinite Cholesky
`N²+2N+4`, LDL `2N²+2N+3`, PLU/PLUQ `N²+2N+7`, scaled PLU `N²+3N+7`.
Caller buffers and hidden scalar implementation memory are excluded from these scratch bounds.
All seven trees have zero additional workspace at other tags. The library counts/bits are
structural summaries. The seven approved targets use independent cubic count formulas,
not a definition through the program’s own static analysis.

The library resource lemmas are conditional on successful execution. The seven approved
access/cost targets combine actual numerical success with explicit independent allowances of
`1024*(N+1)^3` per operation kind, with 23 possible kinds for Unit tags and no oracle/kernel
names, and the closed caller-plus-scratch memory envelopes. The proof of each target has no
assumed-run hypothesis. Nonvacuity witnesses provide identity inputs at every lower order bound.
The singular PSD domain also includes zero matrices.

Published definitions live in
[`DenseFactorizationTargets.lean`](../../NLAlib/Matrix/Computation/DenseFactorizationTargets.lean),
with proofs in
[`DenseFactorizationTargetProofs.lean`](../../NLAlib/Matrix/Computation/DenseFactorizationTargetProofs.lean)
and independent comparisons in
[`DenseFactorizationCounts.lean`](../../NLAlib/Matrix/Computation/DenseFactorizationCounts.lean).
The [review packet](dense-factorization-audits/target-proof-review/README.md) preserves the
approved prepublication sources and their 21-obligation standard-foundation audit. A separate
kernel check confirms all seven published targets and all seven nonvacuity propositions are
definitionally identical to that approved packet. The earlier tree-derived budget draft is
superseded; target count, memory and postcondition definitions use no static analysis.

## Verification checkpoints

Final publication checkpoint: `TMPDIR=/tmp/nlalib-publication-final-stage bash scripts/stage_check.sh`
exits **0**, without exclusions; log `/tmp/nlalib-publication-final-stage/stage.log`.
The normal warnings-fatal `NLAlib NLAlibTools` build passes all **4,561 jobs**, including the
**574 dense runtime guards** against the canonical Float backend. There are **147 new library
modules** and **22 new tool modules**, including the shared Float index adapter.

The stage builds all **892 proved modules** (4,523 jobs) with zero warnings and no unfinished
modules. The axiom/unsafe/partial audit passes for **27,368 declarations**. All 14 environment
linters pass for 13,377 user and 13,991 generated declarations. Generated imports and all
4,561 freshness checks pass. Strict kernel replay passes for **28,238 constants across 922
modules**, with zero violations or non-strict findings; all eight replay fixtures pass.

Program analysis passes for 163 programs, kernels and trees, with zero violations and no
allocation-scope warnings. The registry accepts **21 targets**, **19 program trees** and four
model pins, and all 22 access-model fixtures pass. The seven new registrations preserve all
14 existing target entries, existing trees, model entries and build pins exactly. The final
registry approval records the maintainer's explicit 2026-11-25 authorization.

All **109 extracted rules** pass with zero new errors; 73 ratcheted baseline findings and
1,574 reviewed/pre-existing warnings remain. The first publication stage found one guide
reference treating tactic syntax as a declaration; its wording was corrected, the full rule
check passed, and the complete stage was rerun. No Lean source or target changed in that fix.
The duplicate report covers 10,840 theorems and nine private-only classes; no private/public
or public/public duplicates are present.

References, 83 registered constants and LaTeX pass: 13,542 docstrings, 689 value markers on
667 spans and 43,039 math spans checked. All **85 Python regression tests** and **14 LaTeX
regression tests** pass. The B1 checker fix recognizes explicitly Builder-returning executable
definitions while retaining numerical definitions with Builder arguments or bodies; matching
regression coverage and contributor documentation are included. Existing optional NumPy
differential tests are skipped because NumPy is absent.

All seven target proofs, seven nonvacuity witnesses and seven count comparisons have separate
strict compilation and standard-foundation axiom audits. The approved-to-published statement
comparison also passes against the canonical build. Independent publication review is recorded
in [the target publication audit](dense-factorization-audits/target-publication-review.md).
No allowlist, ratchet, build-pin or stage-script exception was introduced. The original
checkout's user-owned approval-file change and `.claude/` directory remain preserved.

After the stage passed, three Lean files had trailing spaces removed and two archived proof
files had excess final blank lines removed. A token-preservation check confirmed these were
whitespace-only changes, archive hashes were refreshed, and a final warnings-fatal rebuild,
freshness check and full extracted-rule check passed before committing.

Independent reviews are recorded in
[the factorization interface audit](dense-factorization-audits/expanded-interface-review.md) and
[the resource/block audit](dense-factorization-audits/resource-block-review.md). All fifteen placement findings across the expanded and private-signature reviews were
corrected through proper ForMathlib generalization, shared finite-score lemmas and existing
Mathlib/library arithmetic facts. Private suffix-index signatures now use explicit bound
parameters. Identical LU entry/prefix proofs and the empty PLU body proof are shared by their
exact and rounded consumers. No allowlist or ratchet change was used.

## Remaining boundaries

Tolerance stopping, randomized Cholesky, 2×2 indefinite LDL, blocked pivoted/rounded variants,
optimized native BLAS kernels and a verified native IEEE backend remain separate extensions.
Additional cost targets require their own review. The approval and publication here cover
exactly the seven concrete statements in the linked target review.
