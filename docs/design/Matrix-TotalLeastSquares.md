# Total least squares

For augmented data $C=[A\ b]$, a correction $D=[E\ f]$ is consistent at $x$ when
$(C+D)(x,-1)=0$, equivalently $(A+E)x=b+f$. The domain index `n ⊕ Unit` distinguishes the
right-hand side. The coefficient and observation index types are arbitrary finite types,
and the scalar field is `RCLike`.

The set `totalLeastSquaresCosts C` contains the squared Frobenius norms of corrections
consistent at some finite solution. The predicate `IsTotalLeastSquaresSolution A b x` says
that a correction consistent at this particular vector attains the least cost. A caller
with separate coefficient and right-hand-side perturbations can rewrite the two-block
constraint with `fromCols_add_mulVec_eq_zero_iff`.

The infimum equals the last eigenvalue of $C^*C$, indexed by `Fintype.card n`. This
domain-side convention retains zero eigenvalues in wide problems. Equality in the
Rayleigh lower bound identifies the full minimizing eigenspace. Each unit vector $v$
in that eigenspace with nonzero last coordinate gives both a finite solution and the
optimal correction $-(Cv)v^*$. This correction is zero when $Cv=0$. When all minimizing
vectors have last coordinate zero, approximation by vectors with nonzero last coordinate
gives the same infimum.

For a strict gap between the augmented minimum $\mu$ and the least eigenvalue of
$A^*A$, the shifted Gram matrix is positive definite. The first block of the eigenvector
equation gives the unique solution $(A^*A-\mu I)^{-1} A^* b$. This is the statement an
application with a spectral gap can use directly.

The module `NLAlib.Matrix.Pseudoinverse.TotalLeastSquares` uses the existing `eigenvalue`,
`frobNorm`, Rayleigh estimates, and Mathlib's outer products, Euclidean normalization,
`IsGLB`, and `IsLeast`. The resulting public theorems share the atlas id
`total-least-squares-svd`. Their arguments adapt the [original atlas development](https://github.com/tchen-research/NLAlib/blob/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Basic/TotalLeastSquares.lean).
The printed source is Golub and Van Loan, [*Matrix Computations*, fourth edition, §6.3](https://www.press.jhu.edu/books/title/10678/matrix-computations).

The solution predicate takes `A b x` in the same order as ordinary least squares.
For an assembled matrix the projections `C.toCols₁` and `C.col (.inr ())`
recover these inputs. A bridge identifies the split-data predicate with minimum
correction cost on `C`. The generic formula uses the existing last singular
value of the augmented matrix via `singularValues_sq`, so its right-hand side
can be rewritten directly. Unit eigenvectors use the spectral interface in
the statement guide, an eigenvector equation and Euclidean norm one. Pinned
Mathlib's `HasEigenvector` would still require separate normalization.

## Public signatures

The observation and coefficient types `m` and `n` are finite, and `𝕜` is an `RCLike` field.

```lean
theorem isGLB_totalLeastSquaresCosts (C : Matrix m (n ⊕ Unit) 𝕜) :
    IsGLB (totalLeastSquaresCosts C) (eigenvalue (Cᴴ * C) (Fintype.card n))

theorem isTotalLeastSquaresSolution_iff_exists (C : Matrix m (n ⊕ Unit) 𝕜) (x : n → 𝕜) :
    IsTotalLeastSquaresSolution C.toCols₁ (C.col (.inr ())) x ↔
      ∃ v : n ⊕ Unit → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ v (.inr ()) ≠ 0 ∧
        (Cᴴ * C) *ᵥ v = eigenvalue (Cᴴ * C) (Fintype.card n) • v ∧
        x = fun i => -v (.inl i) / v (.inr ())

theorem isLeast_totalLeastSquaresCosts_of_mulVec_eq (C : Matrix m (n ⊕ Unit) 𝕜)
    {v : n ⊕ Unit → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1) (hl : v (.inr ()) ≠ 0)
    (he : (Cᴴ * C) *ᵥ v = eigenvalue (Cᴴ * C) (Fintype.card n) • v) :
    IsLeast (totalLeastSquaresCosts C) (frobNorm (-vecMulVec (C *ᵥ v) (star v)) ^ 2)

theorem isTotalLeastSquaresSolution_iff_eq_of_lt_singularValues [DecidableEq n]
    (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hgap : singularValues (fromCols A (replicateCol Unit b)) (Fintype.card n) <
      singularValues A k) :
    IsTotalLeastSquaresSolution A b x ↔ x =
      (Aᴴ * A - singularValues (fromCols A (replicateCol Unit b)) (Fintype.card n) ^ 2 • 1)⁻¹ *ᵥ
        (Aᴴ *ᵥ b)
```
