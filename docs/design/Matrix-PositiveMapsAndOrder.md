# Positive maps and matrix order

Use Mathlib's bundled positive linear maps and the existing matrix perspective. The spectral projection weights of a single Hermitian input turn operator Jensen for a normalized finite Kraus sum into Jensen for a merely positive unital map. The square and inverse inequalities are its two atlas applications. Russo–Dye uses complex scalars: an arbitrary complex contraction is an average of two unitaries, and each unitary admits a spectral resolution whose positive images sum to the image of the identity. No invertibility or normalization of that image is needed.

For positive definite `A`, the geometric mean is exactly `matrixPerspective Real.sqrt A B`. Normalize the positive block by the inverse square root of its first diagonal block, apply the square-root order inequality, and conjugate back. This gives the greatest Hermitian off-diagonal completion, including when `B` is singular.

Use the same finite complex-matrix quantifier as `OperatorConvexOn` for matrix monotonicity on a scalar set. Transport it once along complexification and reindexing for arbitrary real or complex matrices. On the nonnegative half-line continuity and matrix monotonicity imply scalar concavity. Comparing the two PSD inputs against scalar translates then bounds the spectral norm of their functional-calculus difference.

Consumers are matrix concentration, Schur-complement bounds, matrix means, and perturbation estimates for positive matrices. Matrix order and the spectral norm retain their library spellings. Sources: Tropp (2022), Theorems 12.16–12.22 and Chapter 14; Bhatia (1997), Chapters V and X.

## Interfaces and consumers

| Module | Public statement |
| --- | --- |
| `Matrix/Functions/PositiveMaps.lean` | For `Φ : Matrix n n 𝕜 →ₚ[𝕜] Matrix m m 𝕜` with `Φ 1 = 1`, `(Φ A) ^ 2 ≤ Φ (A ^ 2)` if `A.IsHermitian`, and `(Φ A)⁻¹ ≤ Φ A⁻¹` if `A.PosDef`. Both are specializations of `OperatorConvexOn.cfc_map_le`. For a complex positive linear map, `IsGreatest ((fun A => specNorm (Φ A)) '' {A | specNorm A ≤ 1}) (specNorm (Φ 1))` without unitality. |
| `Matrix/Functions/Perspective.lean` | For `A.PosDef` and `B.PosSemidef`, `IsGreatest {X : Matrix n n 𝕜 \| X.IsHermitian ∧ (Matrix.fromBlocks A X X B).PosSemidef} (matrixPerspective Real.sqrt A B)`. |
| `Matrix/Functions/MatrixMonotone.lean` | `OperatorMonotoneOn s f` tests CFC order preservation on all finite complex matrix sizes. The bridge `OperatorMonotoneOn.cfc_le_cfc` applies on finite real or complex matrices indexed by arbitrary types. The derivative criterion and modulus theorem share the predicate. |
| `Matrix/Functions/MonotoneModulus.lean` | Given `OperatorMonotoneOn (Ici 0) f`, `ContinuousOn f (Ici 0)`, and `∀ t, 0 ≤ t → 0 ≤ f t`, positive semidefinite `A B : Matrix n n 𝕜` satisfy `specNorm (cfc f A - cfc f B) ≤ f (specNorm (A - B))`. |

Here `[RCLike 𝕜]` and both matrix index types are finite. Mathlib already supplies positive linear maps, CFC on Hermitian matrices, the square-root order theorem, and the Schur-complement equivalence; the library already supplies the matrix perspective, finite operator Jensen and spectral norm. Search found no existing positive-map norm-attainment result or operator-monotone modulus in these interfaces. The direct atlas statements therefore share a single positive-map Jensen argument and the existing perspective, with spectral projection and block-rotation steps kept local.

## Fractional powers as monotone functions

For `r ∈ Set.Icc (0 : ℝ) 1`, the witness consumed by the matrix modulus theorem is

```lean
operatorMonotoneOn_rpow (hr : r ∈ Set.Icc (0 : ℝ) 1) :
  OperatorMonotoneOn (Set.Ici 0) (fun t : ℝ => t ^ r)
operatorMonotoneOn_sqrt : OperatorMonotoneOn (Set.Ici 0) Real.sqrt
```

The pinned `CFC.rpow_le_rpow` proves the complex-matrix inequality. The existing
`OperatorMonotoneOn.cfc_le_cfc` transports it across scalar fields for
`Matrix.PosSemidef.rpow_le_rpow`. The square-root witness uses
`Real.sqrt_eq_rpow`. Both witnesses can be passed directly to
`OperatorMonotoneOn.specNorm_cfc_sub_le`.

The fractional-power perturbation estimate is the matrix consumer of this
interface. For finite real or complex matrices its statement is

```lean
Matrix.PosSemidef.specNorm_rpow_sub_rpow_le (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    specNorm (A ^ r - B ^ r) ≤ specNorm (A - B) ^ r
```

It combines the existing general modulus theorem with the fractional-power
witness and Mathlib’s CFC representation of positive semidefinite powers.

## Spectral decompositions and contractions used by positive maps

The public spectral resolution in `HermitianCalculus` takes a supplied
orthonormal diagonalization with eigenvalues `d`. Its conclusion expands
`cfc f A` as a sum of `f (d i)` times the rank-one column projections.
It works for any finite labeling of the eigenspaces, including repeated values.
It specializes `HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`.
The operator Jensen proof consumes this expansion.

`Inequalities/Block` supplies the spectral-norm bound for the off-diagonal
block of a positive semidefinite matrix with two equal diagonal blocks:
`(fromBlocks S B Bᴴ S).PosSemidef → specNorm B ≤ specNorm S`.
`Factorizations/PolarFrames` supplies two complex unitary factors whose
arithmetic mean is any square contraction, by combining a full SVD with
two conjugate unit phases per singular value. These are the separate inputs
to the existing Russo–Dye norm-attainment theorem.

The modulus theorem needs only `0 ≤ f 0`. The scalar-order bridge
`OperatorMonotoneOn.monotoneOn : OperatorMonotoneOn s f → MonotoneOn f s`
is obtained from order preservation on one-dimensional scalar matrices; it
supplies nonnegativity at every norm appearing in the proof.
