# Cholesky, LDL and pivoted Cholesky: dense routine audit

Audit of `/home/ubuntu/nlalib` at `7cbea9d1`, 2026-11-24. Planning artifact only; no library declarations changed or claimed checked. Read repository contributor contract, agent rules, rules digest, Matrix and Computation topic rules, and design/programs/statements/proofs guidance. This note's proposed Lean shapes are design sketches, not compiled declarations.

## Existing mathematical coverage

- `NLAlib/Matrix/Factorizations/Cholesky.lean:46`: `IsCholesky A L` already owns the exact interface: lower triangular, positive diagonal, `A = L * Lᴴ`. Do not introduce a competing exact predicate.
- Same file `:154`: `choleskyLower` is **noncomputable**, read from `gaussState` and real square roots. It is a mathematical specification, not a runnable program.
- Same file `:276`, `:284`: PSD factorization and `Matrix.PosDef.isCholesky_choleskyLower`. `:59`, `:73`, `:126`, `:134`: invertibility, uniqueness, determinant and solve characterization.
- Same file `:420`: `Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose` gives a symmetric permutation, nonnegative triangular factor, positive first rank-many pivots, zero remaining columns. The supporting largest-diagonal permutation proof is existential (`exists_perm_choleskyLower` is private), not executable pivot scanning or comparison analysis.
- `NLAlib/Matrix/Factorizations/GaussState.lean`: total elimination recurrence, nonzero/positive pivot results, determinant products and permutation transport. `gaussState` is ordinary pure matrix recursion; this still does not constitute stored-buffer execution.
- `NLAlib/Matrix/Factorizations/Elimination.lean`: PSD preservation, zero-pivot column behavior, Schur complement and rank reduction.
- `NLAlib/Matrix/Factorizations/Nystrom.lean:143`: a PSD sequence of elimination pivots equals the Nyström residual; `:200` onwards: one-step randomly pivoted Cholesky expected residual/trace. No stored randomized pivot sampler/routine found.
- Pinned Mathlib **does have** `.lake/packages/mathlib/Mathlib/Analysis/Matrix/LDL.lean`: `Matrix.LDL.lowerInv`, `lower`, `diagEntries`, `diag` are noncomputable SPD Gram–Schmidt constructions. `lower_conj_diag` proves `L * D * Lᴴ = A`; `lowerInv_triangular` exists, while its module TODO explicitly leaves proving `lower` triangular. A new LDL interface must bridge this and record any deviation. This is not an indefinite 1x1/2x2 pivoted LDL algorithm.

## Existing computation coverage and reusable infrastructure

No Cholesky/LDL stored executable, execution-success theorem, typed routine certificate, or rounded factorization theorem found in `NLAlib/Matrix/Computation`, `NLAlib/Matrix/Perturbation`, or target registry.

- `NLAlib/Computation/BLAS.lean:103,128,141,151`: `copyv`, `ger`, `gemm`, `trsvLower`; raw arithmetic instructions support sqrt, divide and comparisons. Reuse these rather than new semantic primitives.
- `NLAlib/Computation/BLAS/Triangular.lean:280`: `exec_trsvLower` proves success, exact solution, full store frame and count; later `IsArithErrSem.exec_trsvLower` and `IsRelErrSem.exec_trsvLower_add_mulVec_eq` give rounded solve and componentwise backward error. Its core loop proof is private; factorization must either use the exported kernel theorem or develop its own factorization invariant. Existing solve supports lower/no-transpose only: Cholesky solve still needs an adjoint solve or explicit transpose-copy.
- `NLAlib/Computation/RoutineFrames.lean:325,554`: `Writable`, `WritableBlocks`, `IsFramed`, block-write frame conversions, loop writes, `IsBlockRoutine`, and `.bind` composition.
- `NLAlib/Matrix/Computation/OrthRoutine.lean`: exact certificate template, two fields `composable`/`run`, existential output words, typed decoded guarantee, `.mono`, `.toBlockRoutine`.
- `NLAlib/Computation/Contract.lean:105`: `IsRelErrSem` has success plus error clauses. `sqrt_ok` needs a nonnegative decoded operand; division needs nonzero decoded divisor; arithmetic requires `safe` exact results. Comparisons are exact on decoded words. The range-aware model has additional sqrt safety (`:267`).
- `NLAlib/Computation/Rounding.lean`: rounding products and `roundingFactor n u`; reuse rather than second gamma vocabulary.

## Recommended architecture and precise candidate shapes

Start with real stored arithmetic. Preserve general `[RCLike]` mathematical interfaces. Complex executable arithmetic needs the established interleaved pair kernels and is a separate work package.

Prefer an out-of-place certificate initially: source block A stays readable, output block L is full column-major n*n words, upper triangle explicitly zero, scratch scoped. Later add packed/in-place variants by refining the layout, not by ambiguous treatment of the unused triangle.

A useful mathematical guarantee should express a nearby SPD matrix, without falsely saying the computed factor exactly factors A:

```lean
structure IsCholeskyErr {n : Type*} [Fintype n] [LinearOrder n]
    (ε : ℝ) (A L : Matrix n n ℝ) : Prop where
  isLowerTriangular : L.IsLowerTriangular
  apply_self_pos : ∀ i, 0 < L i i
  residual : specNorm (A - L * Lᴴ) ≤ ε * specNorm A
```

This is a **candidate design choice**, not permission to add a second standalone contract without reviewing normwise versus componentwise requirements. If the owner selects componentwise backward error (usually more useful for LU/Cholesky), use that as the primary guarantee and derive this only when an actual consumer needs it. The current exact interface supplies a direct bridge by constructing `IsCholesky (L * Lᴴ) L` and by `IsCholesky A L → IsCholeskyErr 0 A L`. Named derived constants go into `docs/constants.toml`.

The corresponding execution-certificate field shape should be:

```lean
structure IsCholeskyRoutine (I : Interp P ι K C)
    (dec : P → K → ℝ) (tag : P) (n : ℕ) (ε : ℝ)
    (pre : Store P K → Prop) (Ab Lb : ℕ) (ao lo : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ (st : St P K C) (A : Matrix (Fin n) (Fin n) ℝ),
    pre st.store → HoldsDecoded st.store dec tag Ab ao.eval A →
    Writable st.store tag Lb lo.eval (n * n) →
    blockDisjoint (Ab, ao.eval, n * n) (Lb, lo.eval, n * n) = true →
    ∃ (out : St P K C) (Lw : Matrix (Fin n) (Fin n) K),
      exec I routine.run st = some out ∧
      st.store.writeBlock tag Lb lo.eval (packColumnMajor Lw) = some out.store ∧
      IsCholeskyErr ε A (Lw.map (dec tag))
```

`packColumnMajor` above is deliberately schematic: first find and reuse existing matrix encoding; do not invent another flattening order. The admissible-input condition belongs in a named reviewed interface/precondition. A certificate that quantifies over every A with only arbitrary `pre` must have an instance whose pre actually ensures the admitted A is suitable. Empty n=0 cases need no positive-size or valid-handle assumptions for empty writes.

Exact endpoint: a theorem quantifying over an exact interpretation, readable SPD A and writable disjoint L storage, concluding successful execution, final block write of the mathematical `choleskyLower A`, and hence `IsCholesky A L`. Count and peak proofs stay separate from the routine certificate.

Rounded endpoint: `IsRelErrSem … I.sem` plus explicit `0 ≤ u tag`, `u tag < 1`, range safety and **quantitative SPD margin** imply `IsCholeskyRoutine …`. Exact `A.PosDef` alone is insufficient: rounding can destroy a tiny positive Schur pivot. Do not replace success with a hypothesis that the whole run already succeeded. A first rounded theorem can instead certify an algorithm which returns either a valid factor or a declared breakdown flag, if the status/output format is designed explicitly.

## Work packages and 48-hour ordering

| Priority / wave | Work package | Own files / output | Done criterion |
|---|---|---|---|
| P0, hours 0–4 | Agree guarantees, buffer encoding, success/breakdown and range contract | proposed `docs/design/Matrix-DenseFactorizationRoutines.md` | Exact signatures, consumer examples, no duplicated interfaces; reviewed before proof code |
| P0, hours 4–16 | Scalar-loop Cholesky body and exact loop invariant | proposed `Matrix/Computation/Cholesky.lean` | Stored operations correspond to one Schur step; full frame; no noncomputable implementation |
| P0, hours 16–28 | Exact SPD success and certificate bridge | proposed `Matrix/Computation/CholeskyRoutine.lean` and preceding implementation | Success from input SPD, equality with `choleskyLower`; footprint projection; zero/one dimensional cases |
| P1, independent after P0 design | Rounded guarantee API, monotonicity, exact-zero bridge | proposed `Matrix/Perturbation/CholeskyErr.lean` | Checked contract/API useful to later solve consumers; not counted as certified implementation |
| P1, hours 20–36 | Local rounded column/update estimate | implementation-adjacent rounding file only if needed | Explicit factor-dependent/componentwise backward error; no unjustified SPD nonbreakdown |
| P1, hours 28–40 | Count/scratch analysis | adjacent proof topic | Static operation expression and scoped O(n*n) memory; published exact cost target only after maintainer registration |
| P2, hours 28–40 | Largest-diagonal symmetric pivot scan | shared pivot owner + Cholesky instance | Deterministic ties and swaps update previous factor columns; checked selection property |
| P2 | LDL exact bridge/recurrence | proposed `Matrix/Factorizations/LDL.lean`, if approved | Reuse Mathlib factorization and prove required triangular/unit properties; executable LDL remains separate |
| P3 | Pivoted PSD/rank truncation and randomized sampler | follow-up design | Explicit tolerance/status and tape obligations; not compressed into generic SPD certificate |
| P3 | Indefinite Bunch–Kaufman/rook LDL | follow-up design | 1x1/2x2 block pivots, permutation and block solve interfaces; cannot inherit plain diagonal positivity |
| Gate, hours 40–48 | Independent review and full checks | reports | check_rules + stage_check; reserve integration time; report unproved pieces honestly |

48h committed target should be **one real exact SPD end-to-end stored Cholesky routine plus its typed certificate**, shared rounding/interface API, and a well-specified pivoted extension. Full rounded nonbreakdown, pivoted PSD rank reveal, complex storage and indefinite block LDL are stretch tracks with independent acceptance criteria. Broad interface coverage alone is not algorithm completion.

## Coordination and constraints

A Cholesky implementer can exclusively own new `Matrix/Computation/Cholesky*.lean` files; rounding owner can own `Matrix/Perturbation/CholeskyErr.lean`; shared pivot owner owns scan/swap. Root integration owns `NLAlib.lean`, docs tables and any approved registry interaction. Avoid shared edits to BLAS/RoutineFrames: request precise reusable lemmas centrally.

Do not change `*Targets.lean`, targets registry/approval, checks, build pins, or ratchets. New `<spec>Prog` definitions require registered targets under E4, so start with an ordinary composable Builder routine; do not use a new `...Prog` family or claim a published exact cost result before maintainer review. Rounded program theorem exception does not erase the registered-tree requirements for `<spec>Prog`.

This audit writes only this external planning artifact; no library build or stage-check was run, and no library completion is asserted.

## Reviewed implementation choice (supersedes relative-A sketch above)

Root reviewed the interface before code and selected **absolute spectral budget**:
`IsCholeskyErr ε A L` retains `isLowerTriangular`, `apply_self_pos`, and
`residual : specNorm (A - L * Lᴴ) ≤ ε`. The earlier relative-A candidate is outdated and is not
being implemented. This avoids committing the shared decoded certificate to input-relative
scaling; a future componentwise or factor-scaled algorithm theorem can imply an absolute budget.
The design owner records this in `docs/design/Matrix-DenseFactorizationRoutines.md`.

Approved API slice: exact-to-zero bridge, budget monotonicity, nearby exact `IsCholesky`,
zero-error equivalence, and a two-solve residual bound
`‖b-Ax‖ ≤ ε‖x‖ + specNorm L * ‖y-Lᴴx‖ + ‖b-Ly‖`, with exact-solve corollary.
Implementation is isolated to `Matrix/Perturbation/CholeskyErr.lean` in the worktree
`/home/ubuntu/work/nlalib-dense-factorizations`; vocabulary/design/integration belong to root.

## Delivered initial executable slice

Root reviewed the next executable slice before implementation. Added
`NLAlib/Matrix/Computation/Cholesky.lean` with:

- `choleskyColumn`: scoped scalar square root of a Schur pivot into a diagonal cell, followed by
  existing `rscl` on the residual column below it; no allocation, new primitives or target.
- `executionComposable_choleskyColumn`: composability for arbitrary interpretations.
- `exec_choleskyColumn`: under exact real semantics and unit operation charges, a positive stored
  pivot, readable lower vector, writable diagonal and disjoint output blocks imply success.
  The final store is exactly two block writes: singleton square root, then the divided vector.
  Tape and all current/peak memory fields are unchanged; count is one sqrt plus n divisions.
  Offsets are arbitrary; outputs may share a buffer when disjoint; empty lower vector and
  pivot aliases are included. No assumption of whole-run success occurs.

This is one executable Cholesky column normalization, not the trailing Schur update or a full
factorization. It is exact-real only; rounded nonbreakdown still requires a separate proof.

Validation: `lake build NLAlib.Matrix.Perturbation.CholeskyErr` and
`lake build NLAlib.Matrix.Computation.Cholesky` both pass without warnings. `check_rules.py
--files` passes with zero errors/warnings for each file; extraction/name rules require the
integrator's full extraction. Root owns the full `stage_check.sh` gate and root imports.
