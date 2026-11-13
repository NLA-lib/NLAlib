# Direct factorizations

The [original atlas](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730)
groups triangular solves, pivoted elimination, orthogonal factorizations, matrix pencils
and polar factors under *Factorizations and direct algorithms*. This migration completes
the seven cards identified in the earlier comparison of the nineteen proved entries.
Shifted QR rapid decoupling is a separate open atlas item.

## Objects, interfaces and shared proofs

Partial pivoting for LU and diagonal pivoting for Cholesky use the same algorithm on
finite permutations. At position `j`, swap the first maximizer of a score over the
remaining positions into position `j`. The score can depend on the current permutation.
Both algorithms compute a pivot ordering with `Fin.greedyPerm`. The earlier
existence API `Fin.exists_perm_forall_le_apply_self` uses this same recursion. Mathlib's `List.argmax` supplies the
first maximizer. Its permutation API supplies the swap and composition. The proof that
earlier pivots remain maximal belongs with the recursion in `ForMathlib/GroupTheory/Perm/Fin`.

The matrix-level algorithms reuse `gaussState`, `choleskyLower`, `luLower` and `luUpper`.
The Cholesky rank certificate is a statement about columns of the computed factor.
It applies to singular positive semidefinite matrices and to the empty matrix.
LU with singular or zero pivots also needs an existence criterion expressed directly
on prefix row or column spans. The sharp growth example is specified for the same
pivot tie convention as the algorithm.

For a generalized Schur factorization, downstream eigenvalue calculations consume
the diagonal entries of the two triangular factors. Determinant and polynomial
identities therefore belong beside the existing simultaneous equivalence in
`Spectral/Congruence`. For an upper Hessenberg reduction, converses about the resulting
Krylov basis belong beside `IsGradedKrylovBasis` and `arnoldiMatrix` in the Krylov layer.

## Singular LU and partial pivoting

The row-inclusion card uses the span of earlier rows restricted to earlier columns.
Transposition gives the unit-upper convention. Both statements work over a commutative
ring. The other two LU cards concern the result of partial pivoting itself. The
existing multiplier and growth estimates apply by substituting the computed ordering
in the maximal-pivot hypothesis. Wilkinson’s matrix of order one also attains the
bound. In the signatures below, the labels `ι` form a finite linear order and `𝕜` is
real or complex.

```lean
theorem exists_isLU_iff_forall_mem_span (A : Matrix ι ι R) :
    (∃ L U, IsLU A L U) ↔ ∀ i : ι, (fun k : {k // k < i} => A i k) ∈
      Submodule.span R (Set.range fun j : {j // j < i} => fun k : {k // k < i} => A j k)

theorem exists_isLowerTriangular_isUnitUpperTriangular_iff_forall_mem_span (A : Matrix ι ι R) :
    (∃ L U : Matrix ι ι R, L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U) ↔
      ∀ i : ι, (fun k : {k // k < i} => A k i) ∈
        Submodule.span R (Set.range fun j : {j // j < i} => fun k : {k // k < i} => A k j)

theorem forall_luUpper_apply_self_ne_zero_iff_isUnit_det (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∀ i, luUpper (A.submatrix (luPartialPivotPerm A) id) i i ≠ 0) ↔ IsUnit A.det

theorem exists_norm_luUpper_apply_last_eq_two_pow (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜, (∀ i j, ‖A i j‖ ≤ 1) ∧
      ‖luUpper (A.submatrix (luPartialPivotPerm A) id) (Fin.last n) (Fin.last n)‖ = 2 ^ n
```

## Diagonal pivoting for Cholesky

A caller permutes both indices with `choleskyPivotPerm A` and factors the permuted
matrix with `choleskyLower`. The same computed factor satisfies reconstruction by
`Matrix.PosSemidef.eq_choleskyLower_mul_conjTranspose`. Its positive diagonal prefix
certifies the rank, and all its later columns vanish, even for a zero matrix.

```lean
theorem Matrix.PosSemidef.choleskyLower_choleskyPivotPerm_apply_self_pos_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) (i : Fin n) :
    0 < choleskyLower (A.submatrix (choleskyPivotPerm A) (choleskyPivotPerm A)) i i ↔
      (i : ℕ) < A.rank

theorem Matrix.PosSemidef.choleskyLower_choleskyPivotPerm_apply_eq_zero_of_rank_le
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) (i j : Fin n) (hj : A.rank ≤ (j : ℕ)) :
    choleskyLower (A.submatrix (choleskyPivotPerm A) (choleskyPivotPerm A)) i j = 0
```

## Modified Gram–Schmidt

The MGS update measures a coefficient against the partially reduced column. At stage
`k`, orthogonality to the earlier vectors makes this coefficient equal to the classical
one. The result accepts a zero vector at a dependent column. The full-sweep proof
uses the coefficient lemma at each step. The specialization below takes the actual
columns of `gramSchmidtQ A` and gives the entry of `gramSchmidtR A` read by a caller.
The program in `Factorizations/GramSchmidtProgram` imports the same residual identity
from the mathematical module to justify its normalization step.

```lean
theorem dotProduct_mgsSweep_eq {V : ℕ → m → 𝕜} {x : m → 𝕜} {k : ℕ}
    (h : ∀ i < k, star x ⬝ᵥ V i = 0) (w : m → 𝕜) :
    star x ⬝ᵥ mgsSweep V w k = star x ⬝ᵥ w

theorem dotProduct_mgsSweep_gramSchmidtQ_col {k : ℕ} (A : Matrix m (Fin k) 𝕜) (i j : Fin k) :
    star ((gramSchmidtQ A).col i) ⬝ᵥ
      mgsSweep (fun l a => if h : l < k then gramSchmidtQ A a ⟨l, h⟩ else 0) (A.col j) i =
        gramSchmidtR A i j
```

## Householder Hessenberg reduction

The public `householderTailReflector` in `Factorizations/Householder` forms the
reflector used in `hessenbergState`. The terminal pair `hessenbergReduction` supplies
the unitary and reduced matrix after `n - 2` steps (zero steps for dimensions up to
two). The first column stays fixed in positive dimension. The same state proves the
existing existence result, so the two APIs share the proof of correctness.

```lean
theorem hessenbergReduction_snd_eq_conjTranspose_mul_mul (A : Matrix (Fin n) (Fin n) 𝕜) :
    (hessenbergReduction A).2 = (hessenbergReduction A).1ᴴ * A * (hessenbergReduction A).1

theorem isUpperHessenberg_hessenbergReduction_snd (A : Matrix (Fin n) (Fin n) 𝕜) :
    IsUpperHessenberg (hessenbergReduction A).2
```

## Hessenberg reduction and the Arnoldi basis

In `Factorizations/Hessenberg`, the structure
`IsUnreducedHessenberg H` combines `IsUpperHessenberg H` with nonvanishing
of each entry immediately below the diagonal. The raw constructor uses adjacent
row and column indices, including rectangular shapes. For square matrices of
positive dimension, `isUnreducedHessenberg_iff` tests the usual
`H i.succ i.castSucc` entries. Shifted QR uses the equivalence between a reduced
Hessenberg matrix and `IsDecoupled 0 H` in its existing QR-iteration file.
There is no matching Hessenberg predicate in the pinned Mathlib.

The subdiagonal being nonzero gives the graded Krylov property. Its being positive
also fixes the phases and identifies the reducing basis with the actual Arnoldi
matrix. Both statements use the existing starting vector, graded-basis and Arnoldi
interfaces.

```lean
theorem HasOrthonormalCols.isGradedKrylovBasis_of_isUnreducedHessenberg
    (hQ : HasOrthonormalCols Q) (hH : IsUnreducedHessenberg (Qᴴ * A * Q)) :
    IsGradedKrylovBasis A (Q.col 0) Q

theorem HasOrthonormalCols.eq_arnoldiMatrix_of_isUpperHessenberg (hQ : HasOrthonormalCols Q)
    (hH : IsUpperHessenberg (Qᴴ * A * Q))
    (hpos : ∀ i : Fin k, 0 < (Qᴴ * A * Q) i.succ i.castSucc) :
    Q = arnoldiMatrix A (Q.col 0) (k + 1)
```

## Determinants of generalized Schur pencils

In `Spectral/Congruence`, `IsQZ A B Q Z` bundles the two orthonormal
column conditions and the upper triangularity of both transformed matrices.
Its constructor and projections use `HasOrthonormalCols` and
`Matrix.IsUpperTriangular` directly. The pinned Mathlib has no QZ predicate.
The existence proof supplies these factors through

```lean
theorem exists_isQZ [LinearOrder n] (A B : Matrix n n ℂ) :
    ∃ Q Z : Matrix n n ℂ, IsQZ A B Q Z
```

The homogeneous and affine polynomial calculations consume the same witness. Once
the factors are given, the determinant formulas work over either real or complex
scalars. Singular second matrices require no special case. The homogeneous formula
also handles infinite eigenvalues, and the affine polynomial tests regularity even
when some diagonal pairs vanish. Here `n` is a finite ordered type, `C` is the
constant-polynomial map and `X` is the polynomial indeterminate.

```lean
theorem IsQZ.det_smul_sub_smul (h : IsQZ A B Q Z) (α β : 𝕜) :
    (β • A - α • B).det = Q.det * Zᴴ.det *
      ∏ i, (β * (Qᴴ * A * Z) i i - α * (Qᴴ * B * Z) i i)

theorem IsQZ.det_smul_sub_smul_eq_zero_iff (h : IsQZ A B Q Z) (α β : 𝕜) :
    (β • A - α • B).det = 0 ↔ ∃ i, β * (Qᴴ * A * Z) i i = α * (Qᴴ * B * Z) i i

theorem IsQZ.det_sub_X_smul (h : IsQZ A B Q Z) :
    (A.map C - (X : 𝕜[X]) • B.map C).det = C (Q.det * Zᴴ.det) *
      ∏ i, (C ((Qᴴ * A * Z) i i) - X * C ((Qᴴ * B * Z) i i))

theorem IsQZ.det_sub_X_smul_ne_zero_iff (h : IsQZ A B Q Z) :
    (A.map C - (X : 𝕜[X]) • B.map C).det ≠ 0 ↔
      ∀ i, (Qᴴ * A * Z) i i ≠ 0 ∨ (Qᴴ * B * Z) i i ≠ 0
```

The audit used the original card IDs `lu-row-inclusion`, `lu-growth-factor`,
`lu-partial-pivoting`, `cholesky-algorithm`, `gram-schmidt`, `hessenberg-reduction`
and `generalized-schur-qz`. These statements extend existing matrix and Krylov topics.
The program target registry and its approved interfaces need no changes.

The explorer groups the existence and computation of a Hessenberg reduction under
`hessenberg-reduction`. Its Krylov-space and Arnoldi-basis characterizations, which
take an unreduced Hessenberg form as input, use `unreduced-hessenberg-krylov-basis`.
For matrix pencils, `qz` identifies existence of a generalized Schur form.
`generalized-schur-pencil-determinant` identifies the homogeneous and affine
determinant formulas and their zero and regularity criteria for given factors.
