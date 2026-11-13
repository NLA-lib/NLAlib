# Rounded streamed scalar products

The dense stored matrix implementation streams one scalar multiplication and addition per
entry, starting from literal zero. Its proof previously specialized immediately to the exact
RCLike machine. The same fixed syntax now has a word-level theorem for an arbitrary Machine:
`ScalarProducts.sumWord M xs ys 0 = M.lit 0` and each successor is the actual rounded addition
of the previous accumulator and the actual rounded multiplication.

`ScalarProducts.writes_step_word` and `writes_sum_word` expose this output with the existing
spatial footprint, stride, liveness and capacity assumptions. The exact theorems specialize
these shared proofs; no second memory proof or execution premise is introduced.

`ScalarProductsRounded.lean` connects the word recurrence to the existing `IsDotTrace` model.
For `StdModel u dec M`, nonnegative u and n products, the theorem
`StdModel.abs_sum_mul_sub_sumWord_le` bounds exact-minus-computed error by
`ScalarProducts.roundoff u n * sum(abs(decoded products))`, where the roundoff envelope is
`(1+u)^(2*n)-1`. This includes n rounded additions, including the first addition to zero.
The empty row is exact. No smallness condition is required for this conservative bound.

The numerical proof reuses `IsDotTrace.abs_sum_mul_sub_le_of_absRelErr`, with zero absolute
allowance, rather than recreating summation error analysis. Mathlib was searched for an actual
Ops-machine recurrence theorem; none exists because this is a library-specific interface.
No new hypothesis interface or Mathlib alternative is introduced. The raw local trace is proved
from the scalar machine law, and is never a public solver's success assumption.

The consumers are rounded stored dense matrix-vector contracts, then the common stored CG and
Lanczos contexts. Their conversion from rowwise bounds to a matrix norm allowance remains in
that matrix-level layer. The exact API remains source-compatible.

The continuation lives in `Ops/Profiles/StoredDenseRounded.lean`: the streamed per-row bound
uses the decoded actual dense matrix and actual computed output list. `Matrix/FinitePrecision/
StoredDense.lean` converts that componentwise bound to the normwise allowance
`roundoff u n * sqrt n * specNorm A`, using the existing
`norm_toLp_map_abs_mulVec_abs_le` and `EuclideanSpace.norm_toLp_le_norm_toLp`.
The matrix comparison is deliberately outside Ops so the operation core remains self-contained.
The resulting `Ops.StdModel.norm_mulVec_sub_rowWord_le` is consumed by rounded stored-model
constructors, rather than asking their users for a matvec accuracy callback.

`Ops/Profiles/RoundedScalarBlas.lean` removes vector primitive names altogether. Its computable
`table` composes the existing level-one and sequential-sum tables, then erases the unused vector
names. `table_independent` proves that arbitrary assignments to those unused names give the
same scalar trees, so there is no active fallback primitive. `laws` derives sequential rounded
BLAS contracts from the target's scalar law using `Blas.seq_certifies` and composition.
The target `model` declares only the supplied scalar machine's functions, exact comparisons,
unit scalar work and zero primitive workspace. `contracts_link` supplies the rounded BLAS
model contracts for the induced interpreter. Solver certificates can therefore link their
complete program to actual ScalarOp syntax and recompute full counted resources there.

`Ops/Blas/DotFunction.lean` packages the existing `wp_dotSum_seq` word-execution proof as a
functional primitive contract. `dotSeqFn M` returns the sequential sum of actual machine
products. `isFn_dot_seq`, then `RoundedScalarBlas.isFn_dot`, establish that contract from scalar
functionality alone, independently of any numerical rounding law. PCG uses it when the previous
iteration's numerator is recomputed at the next iteration: the identical input words must
produce the identical scalar, rather than merely another word in the same error interval.
The broad BLAS error interface remains unchanged; determinism follows from this concrete
implementation and is supplied separately where the algorithm needs it.
