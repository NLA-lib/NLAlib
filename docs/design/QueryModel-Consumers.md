# Existing algorithms in the query model

This addition connects existing numerical linear algebra objects with `QueryAlgorithm`.
The interfaces are `QueryAlgorithm.IsMeasurableFamily`, `IsNonAdaptive`, and
`IsPassStructured`; no alternative oracle or algorithm interface is introduced.

The seed of power iteration is its start vector. Each response is the next query, so the
query matrix is exactly `krylovMatrix`, and its range is `krylovSpace`. Returning the last
response computes the power vector in q rounds. The Rayleigh estimator takes q+1 rounds:
the extra product is essential to evaluate the quadratic form. Its mathematical guarantee
is obtained from the existing gapped power theorem by exact execution equality. A separate
certificate shows that at least two power rounds are genuinely response-dependent.

The other seed consists of two sketch matrices, one for each side, with no probabilistic
independence assumption. A two-sided sketch queries right probe columns and then left probe
columns, with every query fixed before any response. The output is the two sampled matrices.
Postprocessing these responses and the seed gives the existing generalized Nyström routine.
Separate right and left budgets count nonzero probes; the sum of the sketch widths bounds
the total rounds. All these queries belong to one pass. The algorithm has access to the
matrix and its adjoint only through `twoSidedMulVec`; it is not asserted to fit a one-sided
oracle model.

Shared bookkeeping is exposed once as the seeded two-sided sketch algorithm: transcript
decoding, exact run, measurability, passes and side budgets. The generalized Nyström bridge
consumes this sampler and the existing low-rank exactness theorem. No arithmetic-operation,
memory or finite-precision cost is asserted; no new registered program target is needed.
