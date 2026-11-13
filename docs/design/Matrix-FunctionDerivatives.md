# Derivatives of matrix functions

The exponential uses Mathlib's `NormedSpace.exp` on the full matrix space. Its difference and
derivative are interval integrals of left and right matrix multiplication. No normality or
commutation is assumed. A scalar-line differentiation and the fundamental theorem of calculus
support both formulas.

For the Hermitian functional calculus, `dslope f x y` supplies each entry of the Löwner matrix,
including repeated eigenvalues. A supplied unitary diagonalization identifies the derivative
in any such basis. The real derivative is taken within the Hermitian matrices or on Mathlib's
self-adjoint submodule. Finite Hermite interpolation and Weyl's perturbation inequality transfer
the polynomial derivative to a function differentiable on the spectrum. The all-orders Löwner
criterion then tests positivity of the divided-difference matrix on all finite lists of nodes.

For rational functions, the data are two polynomials and a nonsingular evaluated denominator.
The off-diagonal blocks of two- and three-block triangular matrices give rectangular first and
ordered second differences. At coincident diagonal blocks the first difference is the Fréchet
derivative. The Hessian adds the two orders of the direction matrices. The resolvent instance
retains the ordered product, including for noncommuting directions.

The original proofs and statement inventory are in the atlas at commit `77514ce` in
`NLAlib/Matrix/Functions`. Shared mathematical ingredients include Mathlib's interval integrals,
noncommutative polynomial evaluation, Fréchet derivatives and block matrix operations.

## Native signatures

In these excerpts `n` is an arbitrary finite index type, `𝕜` is an `RCLike` field and `M`
denotes `Matrix n n 𝕜`. The real Löwner criterion uses all matrix dimensions simultaneously.
The rational block maps also evaluate between distinct finite index types.

```lean
theorem fderiv_exp_apply (A E : Matrix n n 𝕜) :
    fderiv 𝕜 exp A E =
      ∫ s : ℝ in 0..1, exp ((1 - s) • A) * E * exp (s • A)
```

```lean
theorem hasFDerivAt_cfc_subtype
    (A : selfAdjoint.submodule ℝ (Matrix n n 𝕜)) {f : ℝ → ℝ}
    (hf : ∀ x ∈ spectrum ℝ (A : Matrix n n 𝕜), DifferentiableAt ℝ f x)
    (ev : n → ℝ) (U : unitary (Matrix n n 𝕜))
    (hdiag : (A : Matrix n n 𝕜) = (U : Matrix n n 𝕜) * diagonal (fun i => (ev i : 𝕜)) *
      (U : Matrix n n 𝕜)ᴴ) :
    HasFDerivAt (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) => cfc f (B : Matrix n n 𝕜))
      ((loewnerDerivative f ev U).comp (selfAdjoint.submodule ℝ (Matrix n n 𝕜)).subtypeL) A
```

```lean
theorem operatorMonotoneOn_iff_posSemidef_loewnerMatrix {I : Set ℝ} {f : ℝ → ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I) (hf : DifferentiableOn ℝ f I) :
    OperatorMonotoneOn I f ↔ ∀ (d : ℕ) (ev : Fin d → ℝ),
      (∀ i, ev i ∈ I) → (loewnerMatrix f ev).PosSemidef
```

```lean
theorem sub_rationalMatrixEval (P Q : 𝕜[X]) (A B : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    rationalMatrixEval P Q A - rationalMatrixEval P Q B =
      rationalBlockDifference P Q A B (A - B)

theorem sub_rationalBlockDifference_left (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A C H - rationalBlockDifference P Q B C H =
      rationalSecondBlockDifference P Q A B C (A - B) H

theorem sub_rationalBlockDifference_right (P Q : 𝕜[X]) (A B C H : Matrix n n 𝕜)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    rationalBlockDifference P Q A B H - rationalBlockDifference P Q A C H =
      rationalSecondBlockDifference P Q A B C H (B - C)
```

```lean
theorem fderiv_fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A G H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B) A G H =
      rationalSecondBlockDifference P Q A A A G H +
        rationalSecondBlockDifference P Q A A A H G
```

## Placement and consumers

`ForMathlib/Analysis/Calculus/FDeriv/Polynomial.lean` gives the insertion-sum derivative
`Polynomial.aevalFDeriv`. Both the Hermitian and rational calculi consume it.
`ForMathlib/Analysis/Calculus/FDeriv/Secant.lean` identifies a derivative from an exact
increment and a continuous linear secant. Rational differentiation applies that criterion
twice. The existing polynomial intertwining theorem in `Matrix/Functions/Polynomial.lean`
only needs a commutative semiring of matrix entries, so both the algebraic and analytic
parts use one theorem. The real operator-norm algebra is supplied explicitly by
`Matrix.l2OpNormedAlgebraReal` where integral calculus requires it.

The Löwner criterion consumes the Hermitian derivative. The exponential insertion integral
serves perturbations of nonnormal matrices. The rational Hessian gives both ordered terms
for resolvent comparison. See Higham, *Functions of Matrices*, §3.2 and Chapter 10; Tropp,
*Matrix Analysis*, Theorems 14.5 and 14.13; and [Tropp (2026), §§4.2–4.4](https://arxiv.org/html/2603.05803v2).
