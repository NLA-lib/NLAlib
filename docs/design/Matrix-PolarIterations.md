# Iterations for the rectangular polar factor

The target on arbitrary finite real or complex matrices is the existing `polarFactor A`;
a full-rank input gives its polar isometry. The proofs use the current `IsSVD A U σ V`
relation, `pinv`, `HasOrthonormalCols`, `specNorm`, and Mathlib polynomial evaluation.
Newton averaging fixes the singular directions. For a positive singular value s write
c=(s−1)/(s+1). Its kth coefficient is (1+c^(2^k))/(1−c^(2^k)).
The inverse-free cubic iteration admits the broader initial domain ‖A‖₂<√3. Its
defect bounds begin at the first step, when every retained coefficient lies in (0,1].
An arbitrary odd polynomial acts on these directions as s p(s²). Composition of
greedy odd minimax updates gives the worst-case scalar bound and a Horner realization.

~~~lean
Tendsto (polarNewtonIterate A) atTop (𝓝 (polarFactor A))
specNorm A < Real.sqrt 3 → Tendsto (polarSchulzIterate A) atTop (𝓝 (polarFactor A))
~~~

The matrix statements belong to the matrix-functions layer, and scalar approximation
arguments belong with the library's polynomial approximation results. The sources are
Higham (1986), §3, Higham and Schreiber (1990), §3, and the polar-iteration files in the
[original atlas](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Functions).

## Horner evaluation and the operation target

The mathematical implementation `gramHorner` handles degree zero and one directly.
Each further degree appends exactly one left multiplication by the Gram matrix.
`oddMatrixIterate` forms that Gram matrix once and applies the resulting polynomial once
per update. Thus evaluating the displayed recursion uses at most $(q+1)k$ matrix products
for $q≥1$ in $k$ stages, counting a Gram product as one full matrix product.

For a positive Gram degree $q$ and $k$ stages, the compiled program reads the
$m$ by $n$ input in column-major order and the supplied real coefficients in
stage order, with each polynomial’s coefficients in ascending order. Each
stage uses one Gram product, $q-1$ square products and one final rectangular
product. This gives exactly $(q+1)k$ calls, including when a matrix dimension
is zero. Zero stages copy the input and use no product calls.

In the [standalone target proposal](../../proposals/polar/Final.lean),
`Proposal.Polar.storedEntriesHorner` proves that execution succeeds under exact
real or complex arithmetic and returns `oddMatrixIterate q c A k`. It proves
the count for the executed program and the peak bound
$3mn+3n^2+k(q+1)$ words, including the inputs and ROM. The native library
provides the minimax error and the exact polynomial identity for this output.

Publishing the executable target under E3 and E4 requires maintainer admission
of the stored-entry access model with exact matrix multiplication, its tree,
and the target. The proposal includes a nonvacuity witness for its inputs.

## From supplied coefficients to Mathlib polynomials

The input buffer stores the coefficients numbered zero through q. Mathlib’s
`Polynomial.ofFn (q + 1) (fun i => c i)` is the polynomial represented by
those entries. For a polynomial `p : ℝ[X]` with `p.natDegree ≤ q`, its padded
coefficients recover `p` by `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`.

```lean
oddScalarUpdate q p.coeff x = x * p.eval (x ^ 2)
gramHorner q p.coeff A = Polynomial.aeval A p
```

The arbitrary-input versions use `ofFn` on the right and need no degree or tail
condition. The scalar Taylor competitor uses the first identity. The fixed-frame
SVD calculation uses both arbitrary-input identities. This also relates the
coefficient layout of the executable Horner proposal to a caller’s polynomial.

## Hypotheses for the inverse-free iteration

The signed singular-value filter sends the interval from −2 to 2 into the closed
unit interval in absolute value. Consequently, after one step the Gram defect
is positive semidefinite and bounded above by the identity for every input of
spectral norm at most two, including rank-deficient rectangular inputs. Squaring
the defect recurrence then gives a non-strict norm rate. A zero singular value
keeps defect one, so a strict defect bound still needs injectivity. For the
error relative to the original polar factor, nonnegative signed coefficients
are sufficient and hold up to and including the initial norm threshold √3.

```lean
(specNorm A ≤ 2) → (columnGramDefect (polarSchulzIterate A (k + 1))).PosSemidef
(specNorm A ≤ 2) → specNorm (columnGramDefect (polarSchulzIterate A (k + 2))) ≤
  specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ^ 2
(specNorm A ≤ 2) → specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ≤
  specNorm (columnGramDefect (polarSchulzIterate A 1)) ^ (2 ^ k)
(specNorm A ≤ Real.sqrt 3) → specNorm (polarFactor A - polarSchulzIterate A (k + 1)) ≤
  specNorm (columnGramDefect (polarSchulzIterate A (k + 1)))
```

The rate at arbitrary iteration counts consumes the one-step rate. Positivity
uses the existing scalar theorem `abs_newtonSchulz_le_one` through compact
singular frames and the Gram-matrix characterization of the operator norm.
At a singular value of 2 the first signed coefficient is −1. At √3 it is zero
and stays zero, although the original polar coefficient is one. These examples
explain the different endpoint hypotheses for the Gram defect, polar error,
and convergence.

## Applying error bounds at a computed iterate

A local rounding-error analysis starts from the matrix $X$ that was actually
computed. Its next exact update can be compared to a rounded update even when
the preceding updates include rounding errors. For rectangular matrices over
`RCLike`, the matrix-functions layer provides

~~~lean
specNorm_polarSchulzStep_le_one {X : Matrix m n 𝕜} (hX : specNorm X ≤ 2) :
  specNorm (polarSchulzStep X) ≤ 1
posSemidef_columnGramDefect_of_specNorm_le_one {X : Matrix m n 𝕜} (hX : specNorm X ≤ 1) :
  (columnGramDefect X).PosSemidef
specNorm_columnGramDefect_polarSchulzStep_le {X : Matrix m n 𝕜} (hX : specNorm X ≤ 1) :
  specNorm (columnGramDefect (polarSchulzStep X)) ≤ specNorm (columnGramDefect X) ^ 2
rank_polarSchulzIterate (A : Matrix m n 𝕜) (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
  (polarSchulzIterate A k).rank = A.rank
~~~

The existing exact-trajectory inequalities consume the one-step estimates.
Rank preservation also covers deficient inputs and gives the full-column-rank
statement through `mulVec_injective_iff_rank_eq`. The scalar tools live beside
`newtonSchulz` in `Polynomial/Approximation/NewtonSchulz.lean`. Its existing
`one_sub_newtonSchulz_sq` and `abs_newtonSchulz_le_one` yield the iterated
defect bound for initial modulus at most two. Nonnegative starting values
whose square is at most three admit the error comparison; convergence to one
requires strict positivity and square strictly below three.

The inverse-averaging Newton iteration uses the initial Cayley modulus
`polarNewtonCayleyNorm A`, the sup norm of the Cayley coefficients of the
positive singular values, zero for the empty compact SVD. The two results are
independently applicable:

~~~lean
polarNewtonCayleyNorm_lt_one (A : Matrix m n 𝕜) : polarNewtonCayleyNorm A < 1
specNorm_polarFactor_sub_polarNewtonIterate_le (A : Matrix m n 𝕜) (k : ℕ) :
  specNorm (polarFactor A - polarNewtonIterate A k) ≤
    2 * polarNewtonCayleyNorm A ^ (2 ^ k) / (1 - polarNewtonCayleyNorm A ^ (2 ^ k))
~~~

For `h : IsGreedyOddMinimax q a c l u`, the existing actual-interval bound
and `h.one_sub_le_pow` compose directly. If $0<a\le1$, the positive singular
values of $A$ lie in $[a,1]$, and $1\le T$, then

~~~lean
specNorm (polarFactor A - oddMatrixIterate q c A T) ≤ (1 - a ^ 2) ^ ((q + 1) ^ T)
~~~

The convergence theorem uses this bound without inspecting the attained
endpoints. Search of pinned Mathlib found the ordinary finite-function norm and
iteration primitives used here, and no matching polar or minimax bounds.
