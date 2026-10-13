# Design note: Matrix stage M9, factorizations and algorithms

Status: written 2026-10-14 by the orchestrator while M6 and M7 were being proved, reviewed by a
Fable agent the same day (§8); to be implemented without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(eleven files) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

Triangular matrices and triangular solves; Gaussian elimination; LU (predicate, uniqueness,
existence through leading principal minors, partial pivoting); Cholesky (predicate, uniqueness,
existence exactly for positive definite matrices, the pivoted factorization of a positive
semidefinite matrix); QR (predicate, existence, uniqueness, what `R` knows about `A`, least
squares through QR); Gram–Schmidt; Householder reflectors and Householder QR; Givens rotations;
Hessenberg and tridiagonal reduction, the QR iteration step, the implicit Q theorem; the polar
decomposition, the nearest isometry and Procrustes problems; rank-revealing column selection
(maximum volume, strong rank-revealing QR).

Owed to this stage by earlier ones, and paid here: least squares through QR (M4); leading
principal minors (M7, spelled with `principalMinor`); the polar frame of the subspace stage (M5);
the prototype's `Basic/SchurComplement` pivot step and `Basic/LeadingMinor`.

Not here: Schur triangularisation and Sylvester's criterion (M10); bidiagonalisation and the
Golub–Kahan process, Lanczos and Arnoldi (the Krylov layer, which will follow the algorithm
convention of §2); rounding error analysis of any of these algorithms (a later layer); LDLᵀ
(Mathlib's `LDL`).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| triangular matrix | Mathlib's `Matrix.IsUpperTriangular`, `Matrix.IsLowerTriangular` on `[LinearOrder n]` | `Matrix.BlockTriangular` |
| unit triangular | `IsUnitLowerTriangular L`, `IsUnitUpperTriangular U` (structures) | — |
| upper trapezoidal, Hessenberg, tridiagonal | `IsUpperTrapezoidal`, `IsUpperHessenberg`, `IsTridiagonal`, for matrices indexed by `Fin` | — |
| leading principal minor | `principalMinor A (Finset.Iic i)` (M7's `principalMinor`) | — |
| full column rank | `Function.Injective A.mulVec` (as in M4) | `mulVec_injective_iff_rank_eq` |
| one elimination step | `eliminationStep A t`, any index type, any field | — |
| elimination in the natural order | `gaussState A k` for `A : Matrix (Fin n) (Fin n) K` | — |
| elimination along a list of pivots | `l.foldl eliminationStep A` | — |
| LU | `IsLU A L U`; computed factors `luLower A`, `luUpper A` | — |
| Cholesky | `IsCholesky A L`; computed factor `choleskyLower A` | — |
| thin QR | `IsQR A Q R` (`Q` with orthonormal columns, `R` square upper triangular) | — |
| full QR | a square `Q` with `HasOrthonormalCols Q` and `IsUpperTrapezoidal R`; no predicate | — |
| Gram–Schmidt | `gramSchmidtQ A`, `gramSchmidtR A` | `InnerProductSpace.gramSchmidtNormed` |
| Householder reflector | `householder v`, `householderVector x i₀`; `householderQ A`, `householderR A` | — |
| Givens rotation | `givens i j c s` with `c s : 𝕜` | — |
| polar factor | `polarFactor A = A * pinv (CFC.sqrt (Aᴴ * A))` | — |
| column selection | `A.submatrix id e`, `e : p → n`; coefficients `pinv C * A`; residual `(1 - rangeProjector C) * A` | — |
| rank-revealing certificate | `IsLocalMaxVolume A e f` (structure) | — |

Not ported as names: `pivotSchur`, `borderedMatrix`, `borderedUpper`, `leadingSubmatrix`,
`leadingMinor`, `IsFullQR`, `IsPLU`, `IsPivotedCholesky`, `IsHessenbergForm`,
`IsUnreducedHessenberg`, `IsGradedColumnBasis`, `HasRowInclusion`, `HasColumnInclusion`,
`GramSchmidtSucceeds`, `LUSucceeds`, `CholeskySucceeds`, `LUPartialPivotSucceeds`, the pivoted
recursions `luPartialPivot`, `choleskyPivoted`, the Givens QR recursion, modified Gram–Schmidt,
`householderSign`, `givensCos`, `givensSin`, `givensRotation`, `polarFrame`,
`choleskyPivotProbability`, the canonical QR frame of the subspace stage.

## 2. Interfaces

**The algorithm convention** (the brief's question). An algorithm is

1. a *factorization predicate* (`IsLU`, `IsCholesky`, `IsQR`), a `Prop` structure on the factors,
   with uniqueness and consequences proved from the predicate alone;
2. a *total recursion* indexed by the step count, on matrices of fixed size: `gaussState A k`,
   `householderState A k`, `forwardSubstState L b k`. No recursion on the dimension, so no
   bordered matrices and no casts between `Fin (n + 1)` and `Fin n`; a step past the end does
   nothing;
3. *breakdown as a value, not a predicate*: a zero pivot makes the step the identity (the field
   inverse of zero is zero), and the factors are defined for every input. The prototype's
   `…Succeeds` predicates are replaced by hypotheses on the computed diagonal
   (`∀ i, luUpper A i i ≠ 0`), and each is characterised by a mathematical condition
   (`forall_luUpper_apply_self_ne_zero_iff`: leading principal minors nonzero;
   `forall_choleskyLower_apply_self_pos_iff`: positive definite;
   `forall_gramSchmidtR_apply_self_ne_zero_iff`: full column rank);
4. a *realisation theorem*: under the no-breakdown hypothesis the computed factors satisfy the
   predicate (`isLU_luLower_luUpper`, `Matrix.PosDef.isCholesky_choleskyLower`,
   `isQR_gramSchmidt`, `isQR_householder`).

Elimination and substitution are over a field `K`, so they compute over `ℚ`. Cholesky,
Gram–Schmidt and Householder need square roots and are over `𝕜`, noncomputable. A Krylov process
will be the same four items with the state sequence indexed by the iteration and breakdown a zero
norm.

**One elimination step serves LU, Cholesky and their pivoted and random variants.**
`eliminationStep A t = A - (A t t)⁻¹ • (column t)(row t)` is defined for any index type. Its rank
drop, its Schur-complement determinant and positive-definiteness statements, and its
monotonicity on positive semidefinite matrices are proved once. LU reads its factors off
`gaussState`: row `i` of `U` is the pivot row of step `i`, column `j` of `L` the multipliers of
step `j`; Cholesky is the pivot column divided by the square root of the pivot. Pivoted variants
are existence theorems about a permuted matrix (`exists_perm_isLU_norm_le`,
`Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose`), not further recursions. Elimination along
an arbitrary list of pivots is `l.foldl eliminationStep A`; for a positive semidefinite matrix it
is the Nyström residual of the pivot set (`Matrix.PosSemidef.foldl_eliminationStep_eq_sub`),
which with `trace_eliminationStep` and the expected step
`Matrix.PosSemidef.sum_smul_eliminationStep` is what the analysis of randomly pivoted Cholesky
rewrites with.

**Leading principal minors are `principalMinor A (Finset.Iic i)`**, and statements about them
hold for every lower set of indices (`IsLU.principalMinor_eq_prod`). The proper leading minors,
whose nonvanishing gives an LU factorization, are `principalMinor A (Finset.Iio i)`.

**QR is the thin factorization over `𝕜`**, on any row index type and any linearly ordered column
index type. Positive diagonal means `0 < R i i` in the order of `𝕜`, which forces a real
diagonal. The full factorization appears only for `Fin`-indexed matrices, as an existence theorem
and as the output of Householder QR; a thin factorization extends to a full one by M1's frame
completion.

**Gram–Schmidt is Mathlib's**, applied to the columns: this gives the span statements for free
and closes the bridge lemma the prototype left unproved. Modified Gram–Schmidt coincides with it
in exact arithmetic and is not defined; it will be defined with the rounding model that
distinguishes them.

**Householder and Givens are over `𝕜`.** The Householder vector carries the phase of the pivot
entry; a Givens rotation has `c s : 𝕜` and acts by `[[c, s], [-s̄, c̄]]`.

**The polar factor is one total function**, the partial isometry `A |A|⁺ = U Vᴴ`, for every shape
and rank. It replaces the prototype's `polarFrame` (full column rank only) and the tall and wide
existence statements. The absolute value is `CFC.sqrt (Aᴴ * A)` as in M8.

**Rank-revealing means a column selection with three bounded quantities** (the brief's
question): the selected columns `C = A.submatrix id e`, the interpolation coefficients
`pinv C * A`, and the residual `(1 - rangeProjector C) * A`. The certificate is the predicate
`IsLocalMaxVolume A e f` (independent columns, and no single exchange increases the volume by
more than `f²`); its consequences are stated with no QR factorization in sight, so that CUR,
interpolative decompositions and column subset selection consume them directly, including the
residual against the best rank-`k` error in every unitarily invariant norm. The QR form is a
thin QR of `C`; a row selection is a column selection of `Aᴴ`.

## 3. Statement shapes

`Triangular.lean`: conjugate transposes; `submatrix_of_strictMono`;
`eq_diagonal_of_isLowerTriangular_of_isUpperTriangular`; diagonals of products;
`Matrix.IsLowerTriangular.submatrix_mul_of_isLowerSet` and
`Matrix.IsUpperTriangular.submatrix_mul_of_isLowerSet` (leading blocks of a product on a lower
set; one triangular factor suffices); `isUnit_det_iff`, `inv`, `inv_apply_self`; the unit
triangular structures with `one`,
`mul`, `inv`, `det_eq_one`, transposes; `IsUpperTrapezoidal`; `forwardSubst`, `backSubst` with
`mulVec_forwardSubst`, `forwardSubst_eq_inv_mulVec` and the two for back substitution.

`Elimination.lean`: `eliminationStep` with its entry, zero-pivot, pivot-row and pivot-column
lemmas, `eliminationStep_mulVec`, `rank_eliminationStep_add_one`,
`det_eq_apply_self_mul_det_eliminationStep`; on Hermitian and positive semidefinite matrices
`Matrix.PosSemidef.eliminationStep`, `eliminationStep_le`, `posDef_iff_eliminationStep`,
`Matrix.PosSemidef.sum_smul_eliminationStep`; `gaussState` with the zero pattern, the rank, and
`principalMinor_Iic_eq_prod_gaussState`, `forall_gaussState_ne_zero_iff`.

`LU.lean`: `IsLU`; `det_eq_prod`, `isUnit_det_iff`, `principalMinor_eq_prod`,
`submatrix_of_isLowerSet`, `submatrix_orderIso`, `unique`;
`exists_isLU_iff_forall_principalMinor_ne_zero` (nonsingular `A`),
`exists_isLU_of_forall_principalMinor_ne_zero`,
`exists_isLU_of_forall_principalMinor_ne_zero_of_le_rank`; `exists_perm_isLU`,
`exists_perm_isLU_norm_le` (growth `2 ^ (n - 1)`); `luLower`, `luUpper`,
`isLU_luLower_luUpper`, `forall_luUpper_apply_self_ne_zero_iff`.

`Cholesky.lean`: `IsCholesky`; `posDef`, `unique`, `det_eq_prod`;
`exists_isCholesky_iff_posDef`, `Matrix.PosDef.existsUnique_isCholesky`;
`Matrix.PosSemidef.exists_eq_mul_conjTranspose_of_isLowerTriangular`,
`Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose` (pivoted, with the rank pattern);
`choleskyLower` and its realisation.

`QR.lean`: `IsQR`; `conjTranspose_mul_eq`, `conjTranspose_mul_self`, `singularValues_eq`,
`rank_eq`, `conditionNumber_eq`, `norm_det_sq`; at full column rank `injective_mulVec_iff`,
`apply_self_pos`, `pinv_eq`, `mul_conjTranspose_eq_rangeProjector`, `span_col_image_Iic`,
`isLeastSquaresSolution_iff`, `isCholesky`; `mul_diagonal`, `submatrix_rows`, `mul_left`,
`unique`; `exists_isQR`, `exists_isQR_of_injective`, `existsUnique_isQR_of_injective`,
`exists_hasOrthonormalCols_mul_isUpperTrapezoidal`, `isQR_submatrix_castLE`;
`IsQR.mul_eq_conjTranspose_mul_mul`, `IsQR.isHermitian_mul`.

`GramSchmidt.lean`: `gramSchmidtQ`, `gramSchmidtR`; `gramSchmidtQ_mul_gramSchmidtR` (always),
triangularity, nonnegative diagonal, the recursion `gramSchmidtR_apply_self_smul_col`, the Gram
matrix of `Q`, the two characterisations of breakdown, the span statement, `isQR_gramSchmidt`,
equivariance under a unitary factor on the left.

`Householder.lean`: `householder` with `isHermitian_householder`, `householder_mul_self`,
`hasOrthonormalCols_householder`, its action, `det_householder`; `householderVector` with
`householder_mulVec_householderVector`; `householderStep`, `householderState`, `householderQ`,
`householderR` with unitarity, `householderQ_mul_householderR`,
`isUpperTrapezoidal_householderR`, `isQR_householder`.

`Givens.lean`: `givens` with its action on vectors and on rows and columns of a matrix,
`conjTranspose_givens`, unitarity, determinant, `exists_givens_mulVec_apply_eq_zero`.

`Hessenberg.lean`: `IsUpperHessenberg` (rectangular), `IsTridiagonal`; closure lemmas;
`exists_isUpperHessenberg_conjTranspose_mul_mul`,
`Matrix.IsHermitian.exists_isTridiagonal_conjTranspose_mul_mul` (both fixing the first coordinate
vector); `IsUpperHessenberg.exists_isQR` (a QR factorization with Hessenberg `Q`, no rank
assumption), `IsQR.isUpperHessenberg_mul`, `IsQR.isTridiagonal_mul` (which needs no tridiagonal
hypothesis: `H` Hermitian and `Q` upper Hessenberg suffice); the implicit Q theorem
`exists_eq_mul_diagonal_of_isUpperHessenberg`.

`Polar.lean`: `polarFactor` with `polarFactor_mul_sqrt`, `sqrt_mul_polarFactor`, the two
projector identities, `IsSVD.polarFactor_eq`, `hasOrthonormalCols_polarFactor_iff`,
`mul_polarFactor_eq_polarFactor_mul`; `exists_hasOrthonormalCols_mul_sqrt_eq`,
`eq_sqrt_of_hasOrthonormalCols_mul_eq`, `eq_polarFactor_of_mul_sqrt_eq`,
`forall_eq_of_mul_sqrt_eq_iff`; nearest and farthest isometry in every `Φ.matrixNorm`;
`trace_eq_nuclearNorm_iff_posSemidef`; `isLeast_frobNorm_sub_mul_sq` (Procrustes), the two-sided
problem, the nearest scaled unitary matrix.

`RankRevealing.lean`: `re_det_conjTranspose_mul_self_updateCol`; bounds from a budget in block
form (`frobNorm_sq_add_frobNorm_pinv_sq_mul_le`, `singularValues_fromCols_le_sqrt_mul`,
`singularValues_le_sqrt_mul_singularValues_fromCols`); `IsLocalMaxVolume` with `one_le`, `mono`,
`isLocalMaxVolume_one_of_forall_re_det_le`, `submatrix_pinv_mul`, `norm_pinv_mul_apply_le`,
`singularValues_le_sqrt_mul`, `singularValues_one_sub_rangeProjector_mul_le`,
`matrixNorm_one_sub_rangeProjector_mul_le`; `exists_embedding_forall_re_det_le`,
`exists_embedding_isLocalMaxVolume`, `exists_embedding_eq_mul_pinv_mul`.

## 4. Consumers

- **Direct solvers and their error analysis** (later layer): the predicates, the recursions, the
  growth bound of partial pivoting.
- **Least squares**: `IsQR.isLeastSquaresSolution_iff`, `IsQR.pinv_eq`,
  `IsQR.conditionNumber_eq`; Cholesky of the normal equations through `IsQR.isCholesky`.
- **Eigenvalue algorithms**: Hessenberg and tridiagonal reduction, invariance under the QR step,
  the implicit Q theorem (shifted QR, and uniqueness of Lanczos and Arnoldi bases).
- **Randomized algorithms**: `Matrix.PosSemidef.sum_smul_eliminationStep` and
  `Matrix.PosSemidef.eliminationStep_le` (randomly pivoted Cholesky),
  `rank_eliminationStep_add_one`; `exists_embedding_rank_revealing` and
  `exists_embedding_eq_mul_pinv_mul` (interpolative decomposition, CUR, column subset selection);
  orthonormalisation of a sketch by `gramSchmidtQ` or thin QR, with `IsQR.span_col_image_Iic` and
  `IsQR.mul_conjTranspose_eq_rangeProjector`.
- **Subspace methods and manifold optimisation**: `polarFactor` as a retraction, the Procrustes
  problems (alignment of frames, M5's frame alignment), the nearest isometry.
- **M10**: Sylvester's criterion from `posDef_iff_eliminationStep` and
  `forall_gaussState_ne_zero_iff`; inertia through elimination.

## 5. Files

Under `NLAlib/Matrix/Factorizations/`:

1. `Triangular.lean` (Mathlib only).
2. `Elimination.lean` (imports 1, M7 `Determinant`, M2 `Loewner`).
3. `LU.lean` (imports 2).
4. `Cholesky.lean` (imports 2).
5. `QR.lean` (imports 4, M4 `ConditionNumber`, `LeastSquares`).
6. `GramSchmidt.lean` (imports 5).
7. `Householder.lean` (imports 5).
8. `Givens.lean` (imports 5).
9. `Hessenberg.lean` (imports 7, 8).
10. `Polar.lean` (imports M8 `AbsoluteValue`, M3b `UnitarilyInvariant`, M3a `TraceInequalities`).
11. `RankRevealing.lean` (imports 5, M3 `SingularValueInequalities`).

Order for proving: 1; then 2; then 3, 4; then 5; then 6, 7, 8 and 10, 11; then 9.

Amendment, 2026-10-14 (files added or split while the stage was proved):

- `GaussState.lean` (imports 2): `gaussState` and everything about elimination in the natural
  order, split from `Elimination.lean`; `LU.lean` and `Cholesky.lean` import it.
- `Nystrom.lean` (imports 2, M4 `GeneralizedSchur`): the Nyström residual along a selection
  (positive semidefinite, below `A`, vanishing columns, maximality),
  `Matrix.PosSemidef.foldl_eliminationStep_eq_sub`, `Matrix.PosSemidef.sum_smul_eliminationStep`
  and its trace `Matrix.PosSemidef.sum_mul_re_trace_eliminationStep`, split from
  `Elimination.lean`.
- `LUGeneral.lean` (imports 3): `isLU_luLower_luUpper_of_forall_eq_zero` (elimination factors
  the matrix when every zero pivot has zeros below it) and partial pivoting row by row
  (`norm_luUpper_apply_le`, `exists_perm_isLU_luLower_luUpper_norm_le`, growth `2 ^ i` in row
  `i`).
- `ColumnVolume.lean` (imports 5, M3b `UnitarilyInvariant`): the Gram determinant under a column
  exchange and the bounds from a budget, split from `RankRevealing.lean`, which imports it.
- `Procrustes.lean` (imports 10): `frobNorm_sub_mul_sq_of_mul_sqrt_eq`,
  `isLeast_frobNorm_sub_mul_sq`, `isLeast_frobNorm_sub_mul_mul_sq`, split from `Polar.lean`.

## 6. Material

Prototype `Matrix/Factorizations/*` (34 modules, 388 declarations), `Matrix/Basic/SchurComplement`
(pivot step), `Matrix/Basic/LeadingMinor`, `Matrix/Structured/Hessenberg`,
`Matrix/Subspaces/{PolarFrame,CanonicalQR}`. The prototype is real throughout and recurses on the
dimension; the proofs of the realisation theorems will be new (telescoping over `gaussState`
rather than induction through bordered matrices), while the predicate-level facts, the QR
consequences, the polar and Procrustes results, and the maximum-volume argument port with a
change of field.

Unproved in the prototype, and stated here: the rank pattern of pivoted Cholesky (2), Hessenberg
reduction and the implicit Q theorem (4), Hessenberg structure of the Givens QR factors (4), the
bridge from the hand recursion to Mathlib's Gram–Schmidt (1, dissolved by the definition). These
are proved or go to `NLAlibScaffold`.

## 7. Decisions taken without approval

1. The algorithm convention of §2: step-indexed total recursions on fixed-size matrices, no
   `…Succeeds` predicates, breakdown characterised by theorems.
2. `eliminationStep` and `gaussState` as the shared engine of LU and Cholesky; the factors read
   off the state rather than assembled recursively.
3. Leading minors through `principalMinor` on `Finset.Iic i`; no `leadingMinor`.
4. Pivoted factorizations as existence theorems, without recursions.
5. Gram–Schmidt through Mathlib; no modified Gram–Schmidt.
6. Householder and Givens over `𝕜`; the Givens QR recursion replaced by
   `IsUpperHessenberg.exists_isQR`.
7. `IsUpperHessenberg` rectangular and `Fin`-indexed; unreducedness as a hypothesis, not a
   predicate; no `IsHessenbergForm`.
8. `polarFactor` as a total partial isometry.
9. Rank-revealing as a column selection with certificate; the QR-block statements of the
   prototype are not ported in block form.
10. Not ported: the row and column inclusion characterisation of LU for singular matrices
    (the classical leading-minors-through-the-rank theorem is kept), the first-column
    characterisation lemmas of Cholesky, `choleskyPivotProbability` (its identity is stated with
    the ratio written out), the canonical QR frame on the Stiefel manifold and its measurability.

## 8. Review (Fable, 2026-10-14) and what changed

The review checked every statement, with hand examples for the recursions (2×2 and 3×3 LU,
Cholesky at zero and negative pivots, Householder QR for the three shapes, the complex Householder
vector), and found the definitions and the realisation hypotheses right. Findings and their
resolution:

1. **False statement.** The coefficient bound of the rank-revealing certificate had no `0 ≤ f`
   (a maximum-volume selection satisfies the hypothesis for `f = -1`). The certificate is now the
   structure `IsLocalMaxVolume A e f`, which carries `0 ≤ f` and full column rank; it had been a
   raw hypothesis repeated in five statements.
2. Elimination along a list of pivots was missing, so randomly pivoted Cholesky, the consumer
   named in §4, could not be stated. Added `Matrix.PosSemidef.foldl_eliminationStep_eq_sub` (the
   Nyström residual), `Matrix.PosSemidef.foldl_eliminationStep`, `trace_eliminationStep`,
   `gaussState_eq_foldl`.
3. Added the two identities every realisation proof and M10 would otherwise re-derive: the
   telescoping identity `eq_gaussState_add_sum` (no pivot hypothesis) and the pivot as a ratio of
   leading minors, `gaussState_apply_self_mul_principalMinor_Iio`.
4. Dot notation: `Matrix.IsHermitian.posDef_iff_eliminationStep`,
   `Matrix.IsHermitian.forall_choleskyLower_apply_self_pos_iff`.
5. General forms first: `IsQR.pinv_eq : pinv A = pinv R * Qᴴ` with no rank hypothesis (the
   inverse form is `IsQR.pinv_eq_inv_mul`); `IsQR.span_col_image_Iic` needs the diagonal nonzero
   only up to the index.
6. Conjunctions split (`gramSchmidtQ_mul_left`/`gramSchmidtR_mul_left`,
   `IsUpperTrapezoidal.apply_eq_zero_of_le`,
   `Matrix.IsHermitian.choleskyLower_apply_self_nonneg`, `gramSchmidtR_apply_self_pos`); a proof
   term removed from the Hessenberg reduction statements; `[WellFoundedLT n]` dropped (it follows
   from `Fintype`); `exists_eq_mul_diagonal_of_isUpperHessenberg` renamed.
7. Added for the consumers: `IsLU.mulVec_eq_iff`, `IsCholesky.mulVec_eq_iff`,
   `IsQR.isLeastSquaresSolution_backSubst`, the shifted QR step `IsQR.mul_add_smul_one_eq`,
   `polarFactor_eq_pinv_sqrt_mul`, `IsLocalMaxVolume.submatrix_pinv_mul`,
   `IsLocalMaxVolume.matrixNorm_one_sub_rangeProjector_mul_le`.
8. Removed as dead weight: `IsQR.norm_det_sq`, `givens_one_zero`, `IsUpperHessenberg.add` and
   `.smul`, `exists_isHermitian_mulVec_eq_smul_single`, the two `submatrix_orderIso` lemmas, the
   farthest-isometry half of Fan–Hoffman, the nearest scaled unitary matrix,
   `Matrix.PosSemidef.gaussState`, one of the two transpose twins for unit triangular matrices.
9. Mathlib supplies the proofs of several triangular and Gram–Schmidt statements
   (`Matrix.det_of_isUpperTriangular`, `Matrix.blockTriangular_inv_of_blockTriangular`,
   `InnerProductSpace.span_gramSchmidtNormed`, `Matrix.rank_mul_eq_right_of_isUpperTriangular`);
   they stay as statements in the vocabulary of the factorizations. Mathlib's `LDL` gives
   `exists_isCholesky_iff_posDef`.
10. Not taken: a row-selection twin of the certificate (apply the column statements to `Aᴴ`).
