# Newton–Schulz inverse refinement

The square matrix iteration is total on its input pair. Its right residual is
the natural observable when the starting estimate does not commute with the
matrix. The error uses the library convention, exact inverse minus computed
iterate. No new assumption on the starting estimate is needed.

In `Matrix/Functions/InverseRefinement.lean` the interface for real and complex
square matrices of arbitrary finite dimension is

```lean
1 - A * inverseSchulzIterate A X k = (1 - A * X) ^ (2 ^ k)
specRadius (1 - A * X) < 1 → Tendsto (inverseSchulzIterate A X) atTop (𝓝 A⁻¹)
IsUnit A → specNorm (A⁻¹ - inverseSchulzIterate A X k) ≤
  specNorm A⁻¹ * specNorm (1 - A * X) ^ (2 ^ k)
```

The explicit norm estimate holds even when the initial residual has norm at
least one. In applications with residual norm below one it gives a quantitative
stopping bound. The residual power identity is just ring algebra. The inverse
and convergence proofs use the existing `PowerBounds` and spectral norm API;
the iteration is the only new vocabulary. Mathlib's Neumann series estimates
are about powers, not successive inverse estimates. Source: Higham,
*Functions of Matrices*, §5.3. The original atlas's proof at 77514ce is the
starting point for the residual calculation.
