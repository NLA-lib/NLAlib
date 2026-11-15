# Rounded stored-matrix execution

The stored dense leaf executes its existing fixed scalar tree under a supplied `Machine`.
Its word recurrence records every rounded multiply and addition, including initialization.
The numerical bridge derives its error from `StdModel`; no successful-run assumption is added.

## Interfaces and consumers

`StoredDense.rowWord M m n raw xs i` is the `ScalarProducts.sumWord` recurrence on the
column-major row. `writes_apply_word` and `writes_impl_word` return the actual row words with
the existing footprint, tape position and one-cell workspace. Existing exact theorems are
specializations, so the storage proof has one implementation.

The local kernel error theorem has the shape

```lean
StdModel u id M → 0 ≤ u →
  ‖WithLp.toLp 2 (StoredOperator.denseMatrix m n raw *ᵥ decv id n xs -
    decv id m ((List.range m).map (StoredDense.rowWord M m n raw xs)))‖ ≤
  (ScalarProducts.roundoff u n * Real.sqrt n *
    specNorm (StoredOperator.denseMatrix m n raw)) * ‖WithLp.toLp 2 (decv id n xs)‖
```

This uses the actual raw matrix words. The spectral factor is proved in the numerical Matrix
layer through `norm_toLp_map_abs_mulVec_abs_le`, found in `Matrix/Norms/Compare.lean`.
Ops remains independent of the Matrix layer: its context call rule consumes a local pure
kernel bound, and Krylov consumers discharge it with the proved scalar-to-matvec theorem.
That local rule is not exposed as an arbitrary algorithm-correctness premise.

## Files and shared machinery

- `Ops/Profiles/StoredDense.lean`: generic word recurrence and total execution; existing exact
  API remains a specialization. The established row fill, frame and allocation rules handle
  all storage bookkeeping.
- `Ops/Profiles/StoredDenseRounded.lean`: per-row standard scalar error via the streamed
  product result, without another execution proof.
- `Matrix/FinitePrecision/StoredDense.lean`: the normwise matvec consequence, using the existing
  matrix comparison theorem and Mathlib Euclidean norm monotonicity.
- `Ops/Profiles/ContextDenseRounded.lean`: forwarding and protected data for the same actual
  scalar leaf; caller supplies only the local numerical kernel theorem.
- `Ops/Profiles/ContextLinearRounded.lean`: exhaustive rounded source primitive contracts and
  proof-only guarded interpretation, shared by CG and Lanczos.

The CG and Lanczos total word proofs supply termination and numerical recurrences. Canonical
instrumentation is applied to each final transformed tree; complete scalar, BLAS, frame,
addressing and control counts belong to that same execution. A subsequent BLAS table lowering
can remove the remaining BLAS names using the existing proved sequential profile.

The standard relative model is kept distinct from finite-format mixed-error models. This
integration makes no all-range IEEE relative-error claim. Ordinary and two-pass reorthogonalized Lanczos both have rounded stored scalar-only
endpoints. PCG initialization and active-step contracts are separate checked local results;
a full rounded PCG continuation proof and rounded reorthogonalized CG remain separate.

## Checked scope

The rounded stored carried-CG and both Lanczos scalar-only algorithms are checked. The CG
example `Rounded.Stored.Examples.algorithm` has dimension one, cap one, actual raw matrix
and RHS words, and strictly positive unit roundoff; `mul_one_ne_one` verifies its scalar
multiplication differs from exact arithmetic.

Rounded PCG has checked initialization, local active-step counts/footprints, spectral guard
derivation and an actual one-step `PCGRun` extraction. Its arbitrary-cap continuation and
stopping theorem are not claimed. The ordinary fixed-horizon PCG tree can continue after
exact convergence; SPD alone does not justify those later divisions. Rounded residual
reorthogonalization for CG is also distinct from the completed two-pass Lanczos integration.

## Remaining mathematical boundaries

For PCG, an exact coercive nonlinear preconditioner is compatible with the standard recurrence:
the residual/direction pairing equals the numerator, and the next residual is orthogonal to
the old direction. Rounded continuation needs a quantitative version of this pairing invariant,
together with a stopping implementation. A bound on each primitive alone does not establish
that every later search direction is nonzero.

Residual-reorthogonalized CG performs one sequential projection pass against unnormalized
archived residuals, including division by recomputed self-dots. Lanczos reorthogonalization
performs two classical passes against its normalized basis. Their numerical constants and
run models are distinct. The CG bridge needs the sequential projection coefficient/error
invariant and control of its total correction in the residual-gap recurrence; the exact
archive-orthogonality proof does not provide those rounded estimates.

## Two rounded PCG operator capabilities

`Krylov/CG/HSPCG/FinitePrecision/StoredContext.lean` uses the existing two-slot
`HSPCG.StoredContext.table`: the system and inverse-preconditioner are separate actual raw
inputs, and both compile to `ContextDense.impl`. Ordinary scalar and BLAS calls are retained
for the subsequent `RoundedScalarBlas.table` lowering.

The system `IsMatvec` allowance is
`ScalarProducts.roundoff u n * Real.sqrt n * specNorm decodedA`, proved directly by
`StdModel.norm_mulVec_sub_rowWord_le`. The preconditioner's `MatvecOracle` has reference
`StoredOperator.denseMatrix n n rawP`, action `ContextDenseRounded.wordKernel M n rawP`,
and relative error `ScalarProducts.roundoff u n * Real.sqrt n`. The action is the actual
row-word recurrence and need not be linear; the reference matrix is where SPD is required.
No oracle-correctness or solver-correctness callback is a public constructor premise.

Shared additions in `Ops/Profiles/ContextDenseRounded.lean` belong with context refinement:
`wordKernel` exposes the actual row action; `output_eq_ofFn_wordKernel`
identifies its actual list output; `wp_source_fn` and `callS_source_fn` supply the total
functional local contract using the existing dense execution and frame rules. Searched
`ContextDense` and `StoredDense`: the execution rule was present but its functional vector
contract was absent. `List.ext_getElem` and the existing `decv_ofFn` handle list/vector
round trips without introducing another representation. `Ops.ofFn_decv` belongs in
`Ops/Catalog/Operator.lean` beside the existing vector codec round trip `decv_ofFn`; both
the stored backend and deterministic dot proofs consume this generic real-word lemma.

Functional preconditioner contracts admit `MatvecOperands n n`, including separate input
and output capabilities. A contract with unrestricted `AnyOperands` would also promise
aliasing unsupported by the actual stored kernel. The proof-side fallback uses the same
word action; it is absent from the executed tree. Recomputed dot functionality uses the
actual `dotSeqFn` contract under `OutApart`, obtained after scalar BLAS lowering.

`HSPCG/FinitePrecision/StoredCertificate.lean` supplies the corresponding raw problem and
final scalar tree. The raw admission is symmetry plus independent spectral windows for the
two actual decoded matrices. Precision and positive lower endpoints are theorem parameters,
not hidden input preprocessing. `Problem.withContext` reuses the existing five-vector raw
buffer problem and adds both matrix blocks; initial payload is exactly `2*n*n + 5*n`.
The actual `Rounded.zeroStart` initializes the iterate and owns a scoped stopping cache.
The final program is linked through `RoundedScalarBlas.table`; its budget, scratch, work,
span and memory are recomputed on that scalar syntax.

The output specification retains physical buffers X,R,Z,P and an initialized `RunPrefix`
with its actual raw matrices, actual preconditioner action, original RHS and common error.
Its length is at most the requested cap; a strict early stop has zero residual. A length-zero
prefix is explicit and does not assert that an existing positive-length `PCGRun` exists.
The scalar-only certificate is direct: the coarser rounded BLAS model supplies numerical
relations but does not promise the deterministic dot functionality required by PCG.
