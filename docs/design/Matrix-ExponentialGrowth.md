# Exponential semigroup growth

`Matrix/Functions/ExponentialGrowth.lean` uses Mathlib's algebra exponential,
the existing spectral norm and the existing Hermitian part. For finite indices
and either scalar field the operator statement is

```lean
(∀ t : ℝ, 0 ≤ t → specNorm (NormedSpace.exp (t • A)) ≤ Real.exp (t * c)) ↔
  hermitianPart A ≤ c • 1
```

Choosing c = 0 characterizes contraction. In nonempty dimension the least such
c is `eigenvalue (hermitianPart A) 0`. The order formulation remains meaningful
in empty dimension. This is a stability bound for nonnormal generators as well
as normal ones. No new definition is required. The proof differentiates the
squared norm of a vector orbit, and takes its one-sided slope at zero for the
converse. The native order comparison of real quadratic forms supplies both
directions without choosing individual eigenvectors. Mathlib already provides
the radial derivative of the exponential and the required scalar comparison
results. Source: Higham, *What Is the Logarithmic Norm?*, Theorems 3 and 6,
and the original atlas's energy derivation.
