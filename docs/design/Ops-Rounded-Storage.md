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
