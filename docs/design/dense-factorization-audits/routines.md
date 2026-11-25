# Dense factorization routine architecture audit

Inspected `/home/ubuntu/nlalib` at `7cbea9d1`, 2026-11-24. No library changes made during this audit.

## Existing infrastructure

* `Computation/RoutineFrames.lean`: `ReadsDecoded`, `Writable`, `WritableBlocks`, `IsFramed`, the exact `Store.writeBlock`/`writeBlocks` footprint API, scoped allocation success, one word per loop iteration, and `IsBlockRoutine.bind`.
* `Matrix/Computation/OrthRoutine.lean` and `Computation/MatvecRoutine.lean`: approved two-field certificate pattern, `composable` and `run`. The latter concludes execution success, existential word outputs, exact net store writes and a mathematical decoded guarantee. Certificates impose no resource bound.
* `Matrix/Computation/MatvecRoutine.lean`: short actual scalar-loop implementation certificate, useful as a template. It uses `IsRelErrSem`, `AddsZeroExactly` and a block-write conversion.
* `Computation/BLAS.lean`: scalar builders for dot, axpy, scaling, reciprocal scaling, copy, norm, gemv, ger, gemm and lower triangular solve. BLAS entries are packed column-major, `offset + i + rows*j`.
* `Computation/BLAS/Triangular.lean`: exact execution, arbitrary arithmetic-error relation execution with range-safety hypotheses, and actual lower solve backward error. `IsRelErrSem.exec_trsvLower_add_mulVec_eq` proves success and one net block write, then a componentwise nearby-system relation.
* `Computation/BLAS/Traces.lean`: store-free dot and lower substitution trace predicates and nearby-system proof. Extend these patterns before deriving factorization error bounds.
* `Computation/BLAS/RoundingErrors.lean`: actual rounded dot, axpy, reciprocal scaling, gemv and gemm executions. The gemm entrywise error is `roundingFactor innerDimension u * (abs(A) * abs(B))`.
* `Computation/Contract.lean`: `IsRelErrSem` already gives exact comparisons on decoded words, exact negation, rounded division and square root with success clauses. `IsIndexExactSem` adds exact index literals up to a bound and exact decoded conversion to natural indices.
* `Computation/Syntax.lean` and `IndexBinder.lean`: data-dependent indices are available via `litIdx`, stored scalar copies and `bindIdx`; bounded loops, fuel-bounded while loops and comparisons suffice for pivot search. No new instruction primitive is needed for partial or complete pivoting.

Mathlib searches found matrix swap/permutation/echelon mathematics, including `Mathlib/LinearAlgebra/Matrix/Swap.lean`; no competing store execution, rounding semantics or certified-routine API. NLAlib searches found no existing triangular-solve error certificate or dense Cholesky/LU execution certificate.

## Shared decisions to fix before broad implementation

1. Real scalar words first. Existing exact matrix factorization results generalize over fields/RCLike, but routine decoding and standard scalar rounding contracts are real-valued. Complex routines require interleaved pairs and componentwise real proofs; preserve generality in pure mathematics rather than claim an immediate complex runtime.
2. Initially preserve the input matrix and write separate packed factors. This is easier to frame and compose than an in-place packed LU output with implicit unit diagonal. Optimize to in-place after an actual consumer exists.
3. Use existing `IsLU` on the appropriately reindexed matrix and `IsCholesky` where applicable. Do not introduce parallel exact factorization vocabulary.
4. Separate successful mathematical factorization from a completed algorithm reporting breakdown. A Cholesky routine promising a factor needs a quantitative no-breakdown premise in rounded arithmetic; SPD in exact arithmetic alone does not guarantee it. A guarded outer routine can always return status plus partial factors.
5. Fix permutation direction once. Interpret a stored pivot history by a product of swaps, then prove the bridge to the factorization's permutation convention. Do not silently choose a fresh existential permutation unrelated to stored pivots.
6. Pivot comparisons apply to the current rounded state, not to exact `gaussState A`. Exact comparisons on rounded entries are already contractual, but they do not imply the exact arithmetic pivot order.
7. Tie-breaking must be deterministic. A strict-improvement scan preserves the first maximum; prove its range and maximality. Complete pivoting scans a rectangular active region. Rook pivoting needs a bounded-progress theorem or an explicit timeout/fallback.

## Largest blockers

**Packed layout versus trailing blocks.** Current gemm/trsv builders bake the matrix dimension into column stride. A trailing block of an `N × N` matrix still has leading dimension `N`, so passing the smaller active dimension to packed gemm/trsv is incorrect. The first unblocked factorization can use explicit scalar indexing at stride `N`; blocked factorizations should either pack panels or introduce a measured leading-dimension API with bridges. Do not change the interpreter to solve a layout problem.

**No upper solve implementation certificate.** Pure `backSubst` mathematics already exists in `Matrix/Factorizations/Triangular.lean`, but the BLAS runtime only exposes lower solve. A factor-then-solve consumer needs an upper loop, or a proved reversal/copy transformation.

**No rounded ger run contract found.** Exact ger exists, but a Schur rank-one update needs actual rounded multiplication/subtraction traces. Reuse axpy per column or prove a ger rounded trace lemma. Stating a rounded Schur update axiom would bypass the requested model.

**Index and pivot buffers are scalar words.** Runtime permutation entries must be written by exact `litIdx` and converted by `bindIdx`. Ordinary rounded rational literals cannot be assumed to store arbitrary natural indices exactly. Require index exactness through at least `N` (or the largest encoded sentinel).

**Floating point range.** Existing first certificates often use `safe := True`; this is the standard unbounded relative-error model. Finite-range Float proofs need range hypotheses on every execution prefix, as the generic triangular theorem already demonstrates. State this limit plainly.

**Cost targets.** Certificates are proof infrastructure and introduce no registry obligation. A new `<spec>Prog`, fixed compiled tree or published exact cost theorem triggers target review. AGENTS forbids agents from editing `*Targets.lean`, `docs/targets.toml` and `docs/targets.approved`; prepare concrete proposed target statements for maintainer review after routines exist.

## First independent implementation slice

Wrap the already proved lower triangular runtime as a typed certified routine. This validates the exact architecture needed by factorization consumers without adding a new program or a new target.

Reviewed mathematical guarantee:

```lean
structure IsLinearSolveErr {n : Type*} [Fintype n]
    (η : ℝ) (T : Matrix n n ℝ) (b x : n → ℝ) : Prop where
  backward : ∃ ΔT : Matrix n n ℝ,
    (∀ i j, |ΔT i j| ≤ η * |T i j|) ∧ (T + ΔT) *ᵥ x = b
```

The same guarantee can serve upper and lower solve, with shape hypotheses on implementation instances. Add parameter monotonicity, exact solution construction and zero-parameter extraction. The reviewed name `IsLinearSolveErr` makes its matrix-shape independence explicit; root approved this name on 2026-11-24.

Certificate signature:

```lean
structure IsLinearSolveRoutine (I : Interp P ι K C)
    (dec : P → K → ℝ) (tag : P)
    (T : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (pre : Store P K → Prop) (xb : ℕ) (xo : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ st b, pre st.store → ReadsDecoded st.store dec tag xb xo.eval b →
    Writable st.store tag xb xo.eval N →
    ∃ out W, exec I routine.run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store ∧
      IsLinearSolveErr η T b (fun i => dec tag (W i))
```

The instance uses fixed `T` lower triangular with nonzero diagonal, `IsRelErrSem` at `safe := True`, `u tag < 1`, disjoint matrix/vector blocks and `pre := HoldsDecoded ... T`. Its parameter is exactly `roundingFactor N (u tag)`. Derive `.toBlockRoutine` and `.mono`. Own files `Matrix/Perturbation/LinearSolveErr.lean` and `Matrix/Computation/LinearSolveRoutine.lean`; vocabulary documentation and root imports are integration-owned.

## Dependency-ordered 48-hour architecture stream

| Window | Concrete deliverable | Acceptance |
|---|---|---|
| 0–4h | API/design choices and lower-solve certificate | actual existing scalar-loop success theorem becomes typed certificate; empty dimension and same-buffer disjoint blocks covered |
| 4–12h | runtime row/column swap + pivot argmax scan frames | exact net writes, decoded scan maximality/range, deterministic tie handling |
| 4–16h | Schur update trace/range lemmas | scalar loops produce the claimed trace and retain unrelated cells |
| 12–24h | first LU or Cholesky panel loop invariant | connects stored state to actual factors, not just an existential factorization |
| 24–36h | complete one unblocked routine and one pivoted routine | success/no-breakdown or explicit status, exact factorization bridge, backward error only where fully proved |
| 36–44h | factor-then-solve consumer | accepts certificates and composes actual footprints; requires upper solve workstream |
| 44–48h | integration, rules/build/audit, target proposals | no axiom/sorry, no changed checks/target registry; stage check exit 0 before declaring completion |

Parallelize mathematical traces, runtime memory frames, pivot scanning and algorithm-specific invariants. Keep a single owner for each shared API, vocabulary document, root import list and build integration. Certificates alone are useful completed work, but are not evidence that every full dense algorithm has been implemented.

## Implemented first slices (2026-11-24)

The isolated worktree `/home/ubuntu/work/nlalib-dense-factorizations` now contains:

* `Matrix/Perturbation/LinearSolveErr.lean`: reviewed componentwise backward-error predicate, generalized over `RCLike` and arbitrary finite indices; exact-solution, zero-allowance and monotonicity bridges. Root added the residual-bound consumer lemma.
* `Matrix/Computation/LinearSolveRoutine.lean`: typed successful in-place solve certificate, error monotonicity, block footprint projection and actual scalar-loop lower-solve instance. Same-buffer disjoint matrix/vector blocks and the zero dimension are supported.
* `Matrix/Computation/PivotScan.lean`: executable sign/negation magnitude copying, strict stable maximum update, initialized workspace scan, and a scoped `argmaxAbs` implementation. Its actual execution theorem proves success, exact selected index, maximal absolute current decoded entry, first-max tie handling and exactly one net output block write. Three scratch cells are released; composability is exposed. It requires a nonempty input and separate input/output buffer handles. It does not select according to an ideal exact elimination state, and does not claim a pivoted factorization or its complexity.

These are completed execution and mathematical building blocks for the larger plan, not a claim that complete LU or Cholesky programs already exist. No target registry, check or build-pin edit was made.
