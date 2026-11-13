# Rounded stored Lanczos in Ops

The ordinary and fully reorthogonalized Lanczos programs read their dense matrix from the
first supplied buffer. Matrix applications execute fixed scalar loops. The rounded stored
certificates connect those loops to the existing Lanczos numerical output relations and
certify full canonical resources on the same execution. The scalar-only certificates also
expand every vector operation, with a target signature containing `ScalarOp` alone.

## Objects and contracts

The pure numerical analysis remains in `Lanczos.Rounded` and `Lanczos.Reorth.Rounded`.
No additional numerical run interface, error allowance or success condition is introduced.
The actual dense matrix is `StoredOperator.denseMatrix n n raw`, using the column-major words
in the declared input. The output relations are the existing `Rounded.Output` definitions;
they tie every packed basis and coefficient word to the executed numerical history.

`ContextLinearRounded.relation` indexes the existing scalar machine functions, rounded BLAS
relations and normwise matvec relation by the standard closed operation signature. Its
`admissible` family carries the existing separation/in-place conditions. These are local
primitive interfaces, with no claim about the result of an enclosing algorithm.
`RoundedBlas.model` jointly realizes the scalar and sequential rounded BLAS contracts by
executing the existing proved BLAS implementation over the specified machine.

The proof-side guarded interpreter protects the immutable raw matrix snapshot. Its fallback
forwards scalar and vector calls to their globally valid target interpretation and supplies
an exact matrix product only outside the protected regime. The runtime tree contains neither
that guard nor a fallback product. `Wp.linkContext_of_guarded` transfers the total source
numerical proof to the actual context-linked tree.

The shared theorem `StdModel.norm_mulVec_sub_rowWord_le` derives the dense product's absolute
operator allowance from standard scalar rounding:

```lean
ScalarProducts.roundoff u n * Real.sqrt n * specNorm A
```

The streamed scalar-product envelope is `(1 + u) ^ (2 * n) - 1`, accounting for the actual
multiplication and addition at every position, including addition to the initial zero.
The matrix norm comparison handles absolute entries without assuming cancellation is benign.

## Canonical statements

In each namespace `Lanczos.Stored.Rounded` and `Lanczos.Stored.Reorth.Rounded`, the public
endpoint has the following shape:

```lean
scalarAlgorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
  (E : (Fin 2 → ℕ) → ℝ)
  (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
    (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0))
    u (E d) (Blas.seq.err u) (d 0)) :
  Algorithm (RoundedScalarBlas.model (problem domain admitted) M)
    (scalarSpecification M ... E)
```

The reorthogonalized output additionally records `u` in its numerical history, so its
specification takes that argument explicitly. A BLAS-level `algorithm` retains vector
primitives while implementing the dense product; it accepts the chosen vector costing.

The problem has four supplied buffers: raw matrix, raw right-hand side, uninitialized basis
capacity, and uninitialized coefficient capacity. Symmetry is an explicit admission on the
actual raw matrix. Every size and cap in the caller's nonempty domain is admitted subject to
the explicit precision condition. No full-rank, nonzero RHS, future nonbreakdown, successful
execution or desired-output premise is assumed. Zero-dimensional data, zero cap and early
breakdown remain covered. The ordinary coefficient capacity is `2 * cap + 2`; the fully
reorthogonalized capacity is `3 * cap + 2`, retaining saved raw residual norms.

Each specification reads the actual returned basis and coefficient buffers. Its full count is
`staticCost` of its actual fixed tree. Work, sequential span, scratch and initial-plus-scratch
payload use that same tree and the selected resource model. Supplied raw matrix storage
contributes its full quadratic payload. Scalar lowering recomputes every count and scratch
bound rather than reusing the BLAS-level manifest. The scalar target model has no vector or
matrix operation names, and the erasure-independence theorem ensures that no arbitrary vector
fallback affects the lowered tree.

## Files and reuse

* `Ops/Profiles/ContextLinearRounded.lean`: exhaustive local rounded source contracts,
  fallback realization and guarded matrix-context transfer.
* `Ops/Profiles/RoundedBlas.lean`: jointly realized rounded scalar/vector model.
* `Krylov/Lanczos/RoundedStoredWords.lean`: total ordinary and reorthogonalized word theorems
  consuming the shared local dense/context contracts.
* `Krylov/Lanczos/RoundedStoredCertificate.lean`: ordinary canonical endpoints.
* `Krylov/Lanczos/Reorth/RoundedStoredCertificate.lean`: reorthogonalized canonical endpoints.

Shared machinery is `Wp.linkContext_of_guarded`, `Mem.ContextSnapshot`, the dense row-loop
word theorem and rounding bound, `Rounded.solve_writes`, `Algorithm.ofWp` and `Algorithm.link`.
No algorithm-local alternative to these core mechanisms is needed. The shared scalar-only
lowering lives in `Ops/Profiles/RoundedScalarBlas.lean`; dense numerical analysis lives in
`Matrix/FinitePrecision/StoredDense.lean`, above the self-contained operation core.

Mathlib was searched for stored-program, rounded machine and guarded context interfaces;
none exist there. Existing Mathlib matrices, symmetry and norms are reused through the
library's established bridges, without a parallel mathematical object. Existing `StoredWords`
and `StoredCertificate` supply layout/context and resource proof material; `RoundedSolve`
owns the numerical execution reasoning. Downstream Ritz and backward-error theorems consume
the existing rounded output directly, preserving its tie to the actual stored values.
