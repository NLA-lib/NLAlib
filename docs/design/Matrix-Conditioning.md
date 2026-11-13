# Conditioning of a matrix and a differentiable map

The classical spectral condition number has codomain `ℝ≥0∞`. A singular
matrix has infinite condition number even when its pseudoinverse is bounded.
The definition `spectralConditionNumber` in `Matrix/Pseudoinverse/ConditionNumber.lean`
extends the existing finite `pseudoConditionNumber` on invertible square matrices.
The defining test is Mathlib's `IsUnit`, also valid for the empty matrix.
The two public rewrites needed for the atlas are

```lean
spectralConditionNumber A = ⊤ ↔ ¬ IsUnit A
spectralConditionNumber A = ENNReal.ofReal (pseudoConditionNumber A) -- if IsUnit A
```

The second rewrite transports the existing extremal singular-value formula and
attained distance to singularity without repeating their proofs.

For the conditioning of a differentiable map between Euclidean spaces,
`Matrix/Perturbation/MapConditioning.lean` uses Mathlib's Fréchet derivative,
Euclidean coordinate matrices and continuous linear maps. Scalars can be real
or complex, the dimensions need not agree, and division uses the field's total
inverse. The relative interpretation requires nonzero reference scales.
Absolute conditioning uses the derivative operator norm. Normwise relative
conditioning scales that norm by the ratio of input and output norms. The
componentwise condition uses the spectral norm of the matrix with entries
`(f x i)⁻¹ * (fderiv 𝕜 f x (EuclideanSpace.single j 1)) i * x j`.
The matrix also represents the derivative at zero when the input and output
are measured in relative coordinates.

The bounds used by perturbation analyses are

```lean
normwiseRelativeCondition 𝕜 (Matrix.toEuclideanCLM (𝕜 := 𝕜) A) x ≤ pseudoConditionNumber A
specNorm (componentwiseJacobian f x) ≤
  specNorm (Matrix.diagonal fun i => (f x i)⁻¹) * ‖fderiv 𝕜 f x‖ *
    specNorm (Matrix.diagonal fun j => x j)
```

The linear bound assumes invertibility. Scalar derivative formulas are valid
in one dimension. Matrix multiplication and Mathlib's chain rule handle the
two diagonal maps, and the library's spectral norm API handles all norm bounds.
The definitions and distinctions follow Gautschi (2004), Definitions 2.3–2.6, and the
two condition-number cards in the original atlas.

## Relative distance at singular inputs

A nonzero singular matrix is itself the nearest singular matrix. The minimum relative
perturbation is therefore zero. Measuring a square matrix by its extended spectral
condition number gives the same reciprocal-distance formula in the singular and
invertible cases. The existing finite theorem proves the invertible case.

```lean
theorem isLeast_specNorm_div_not_isUnit_add_of_ne_zero [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A ≠ 0) :
    IsLeast ((fun E : Matrix n n 𝕜 => specNorm E / specNorm A) '' {E | ¬ IsUnit (A + E)})
      ((spectralConditionNumber A)⁻¹).toReal
```

The nonzero assumption gives the relative error a nonzero scale. An application
with a rank-deficient reference matrix can use the same statement without supplying
invertibility. Rectangular least-squares and Kaczmarz estimates continue to use the finite
pseudo-condition number. The underlying atlas card `condition-number-of-map-def` also
collects three distinct results about a map: the relative-coordinate derivative,
the diagonal-scaling bound, and the normwise bound for a linear system. Their
explorer IDs are `componentwise-perturbation-derivative`, `componentwise-condition-bound`
and `linear-map-relative-condition-bound`, respectively. The absolute Jacobian norm
retains the original card ID.
