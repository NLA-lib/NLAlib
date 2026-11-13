# Positive measure for the trace exponential

For real or complex Hermitian matrices `A` and `H`, the trace of the exponential
of `A + t • H` is the Laplace transform of a finite positive measure. The endpoints
are the infimum and supremum of the real spectrum of `H`. Repeated eigenvalues,
noncommuting matrices and a zero-dimensional index type are all allowed.

Apply `NLAlib.exists_isCompactExpRepresentation_re_trace_exp` to the matrices and
their Hermitian hypotheses. The resulting `MeasureTheory.IsCompactExpRepresentation`
gives the support interval and the identity at every real parameter. Its
`coe_mass_eq` gives the mass, `iteratedDeriv_eq_integral` gives tilted
moments of every order, and `exp_mul_iteratedDeriv_even_zero_le` and
`iteratedDeriv_even_le_exp_mul_zero` give the two spectral endpoint bounds.

## Proof and interfaces

- `TraceExponentialContour` computes the Laplace integral of the contour density.
  `TraceExponentialDensity` proves its positivity between adjacent slopes using the
  analytic branches of a Hermitian pencil. Combining this density with the atoms
  constructs the representing measure when the direction has simple spectrum.
- `TraceExponentialApproximation` diagonalizes the Hermitian direction, approximates
  repeated slopes by simple ones, and takes limits of finite measures on a common
  compact interval. The commuting case also follows directly from an atomic measure.
- `TraceExponentialMeasure` transfers the complex result through the existing
  complexification API to real or complex matrices. The measure statements are
  scalar results reusable directly for another compact Laplace transform.

The density construction follows [Stahl, Theorems 1 and 2](https://doi.org/10.1007/s11511-013-0104-z).
The contour, compactness and positivity proofs are adapted from the
[original atlas formalization at 77514ce](https://github.com/tchen-research/NLAlib/blob/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Functions/TraceExponentialRepresentation.lean).
