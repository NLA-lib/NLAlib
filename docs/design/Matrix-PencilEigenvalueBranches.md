# Analytic branches of Hermitian matrix pencils

For the trace-exponential representation the scalar pencil has complex spectral parameters
even when the input matrices are Hermitian. A diagonal direction with distinct real values
labels the eigenvalue branches near infinity. Reflection in the real axis identifies the
matching conjugate branches, and reciprocal affine pencils select roots in the upper
half-plane. Every trace consumer uses only the entire family and its local analytic expansion.

The spectral root bounds use the existing spectral norm. The implicit branch is obtained by a
Schur complement with a one-dimensional isolated coordinate and a nonsingular trailing block.
The current eigenvalue listing and deflation results supply the block split for the diagonal
input. The companion split for a perturbation uses the same coordinate reindexing.

The files `Matrix/Perturbation/PencilRoots`, `SimpleEigenvalueBranch`,
`ExteriorEigenvalueBranches`, and `InversePencilBranches` follow the order of the proof.
`SimpleSpectrum` supplies a spectral listing when a pencil has a full family of distinct roots;
the globalization and upper root sums use the analytic root cluster API. The real conjugation
and half-plane extension arguments use the complex-analysis layer. The only material taken
from the original pencil development is what the branch construction and its trace-exponential
consumer call. The sources are Horn and Johnson, *Matrix Analysis*, Theorem 6.3.12, and
Stahl's proof of the BMV conjecture, §§2–5.

## Public interfaces

For an injective complex diagonal `d` and any complex matrix `A`,
`exists_analytic_eigenvalue_branch_diagonal_expansion` labels the branch at `d i` near zero.
It returns analytic functions `φ, g` such that locally
`φ(t) = d i + t A[i,i] + t² g(t)` and `φ(t)` is an eigenvalue of `diag(d) + tA`.
`exists_exterior_eigenvalue_branches_of_diagonal` uses the same labels at infinity for
`A + z diag(d)`, where the correction to `z d i` converges to `A[i,i]`.

For Hermitian `A, D` with `D` invertible,
`Matrix.IsHermitian.analyticAt_inversePencilUpperRootSum` gives analyticity at each nonreal
parameter, allowing collisions within the selected cluster. In
`Matrix.IsHermitian.exists_inversePencilUpperRootSum_extension`, distinct slopes around a
threshold select the exterior inverse branches; the sum extends to the union of the exterior
and both open half-planes. The theorem retains nonnegative imaginary part in the upper
half-plane, conjugation symmetry, and the explicit global linear growth bound used by Stahl.
