# Design note: Matrix stage M5, subspaces

Status: written 2026-10-14 by the orchestrator while M3a and M3b were being proved; to be
implemented without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(five files) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

Pairs of orthogonal projectors and the gap between them; principal angles with their cosines,
sines and tangents; frames of a subspace (change of frame, equal Gram matrices, completion,
compactness of the set of frames); the CS decomposition; oblique projections.

M1 already has `rangeProjector`, `IsStarProjection`, orthonormal completion and Pythagoras; M2 has
the norm bounds for one projector; M4 has least squares. This stage is about two subspaces.

Not here: the polar frame `Y (Yᴴ Y)^(-1/2)` and the canonical QR frame with its measurability
(M9, with the polar decomposition and QR); the `Stiefel n k` subtype with its group action (it
returns with Haar measure on frames, above the Matrix layer); fourth-moment contraction sums of a
frame (same).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| a subspace of `𝕜ⁿ` | its orthogonal projector `P` with `IsStarProjection P`; for a frame `U`, `U * Uᴴ`; for any matrix, `rangeProjector X` | M1 |
| distance from the range of `P` to the range of `Q` | the matrix `(1 - Q) * P`, in a norm: `specNorm ((1 - Q) * P)`, `frobNorm ((1 - Q) * P)`, `Φ.matrixNorm ((1 - Q) * P)` | — |
| principal angles | `principalAngle X Y k : ℝ`, `k : ℕ`, non-decreasing, for the column spaces of any two matrices | cosines are `singularValues (Uᴴ * V) k` for frames |
| tangent of the angles between a frame `U` and a basis `Y` | `tangentMatrix U Y := (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹`, in a norm; `0` when `Uᴴ * Y` is singular | — |
| oblique projector | `P` with `IsIdempotentElem P`; from two bases, `X * (Yᴴ * X)⁻¹ * Yᴴ` | Mathlib's `IsIdempotentElem` |
| CS canonical matrix | `csMatrix 𝕜 c s e` | — |

## 2. Interfaces

**The subspace-distance interface (the brief's question).** One notion, the principal angles, and
one way to state a distance: a matrix whose singular values are the sines, in a norm. The
prototype's `directedSubspaceGap`, `projResidual`, `sinePrincipalAngles`, `overlapTangentNorm`,
`tanThetaMax`, `subspaceTangent`, `vectorTangentToFrame` are not reproduced.

- A theorem that bounds how far one subspace is from another bounds `(1 - Q) * P` in a norm, where
  `P` and `Q` are the two orthogonal projectors. This is the form Davis–Kahan and Wedin take
  (`‖(1 - Q) P‖ ≤ ‖(1 - Q) E P‖ / δ`), it needs no choice of basis, it works when the two
  subspaces have different dimensions, and it works in every unitarily invariant norm.
- This file layer proves that every other spelling has the same singular values, so a consumer
  moves between them by rewriting: `(1 - U * Uᴴ) * V` for frames
  (`HasOrthonormalCols.singularValues_mul_conjTranspose_right`), `Wᴴ * V` for a complement frame
  `W` (`singularValues_conjTranspose_mul_eq_of_mul_conjTranspose_add_eq_one`), and, when the
  ranks agree, the reverse direction `(1 - P) * Q` and the difference `P - Q`
  (`IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`,
  `IsStarProjection.specNorm_sub_eq_of_rank_eq`).
- `principalAngle X Y k` names the angles: `cos` is a singular value of the product of the
  projectors, `sin` is a singular value of `(1 - P_X) * P_Y`, `tan` is a singular value of the
  tangent matrix in the acute case. Index conventions: angles are non-decreasing in `k`; singular
  values are non-increasing; so sines and tangents come in reverse order, stated with
  `i + j + 1 = rank` equations.
- Tangents (subspace iteration, randomized range finders) are stated with
  `tangentMatrix U Y = (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹` for a frame `U` and any basis `Y` with the
  same number of columns; the acute hypothesis is `IsUnit (Uᴴ * Y)`. This is the one named
  matrix: the four-factor expression is carried through inductions on `A ^ k * X`, and
  `tangentMatrix_mul_right` makes its independence of the basis a simp lemma.

**Projectors are hypotheses, frames are data.** Statements about two subspaces take
`hP : IsStarProjection P`, `hQ : IsStarProjection Q`; statements that need coordinates in the
subspace take frames with `HasOrthonormalCols`. `rangeProjector` converts.

**Oblique projectors** are `IsIdempotentElem P`. The angle that controls `‖P‖₂` is
`principalAngle P Pᴴ j`, between the range and the orthogonal complement of the kernel.

## 3. Statement shapes

```lean
theorem sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one {A : Matrix m p 𝕜}
    {B : Matrix n p 𝕜} (h : Aᴴ * A + Bᴴ * B = 1) {i j : ℕ} (hij : i + j + 1 = Fintype.card p) :
    singularValues B i ^ 2 = 1 - singularValues A j ^ 2
theorem IsStarProjection.sq_singularValues_one_sub_mul {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {i j : ℕ} (hij : i + j + 1 = P.rank) :
    singularValues ((1 - Q) * P) i ^ 2 = 1 - singularValues (Q * P) j ^ 2
theorem IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    singularValues ((1 - Q) * P) = singularValues ((1 - P) * Q)
theorem IsStarProjection.specNorm_sub_eq_max {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) :
    specNorm (P - Q) = max (specNorm ((1 - Q) * P)) (specNorm ((1 - P) * Q))
theorem IsStarProjection.specNorm_one_sub_mul_lt_one_iff {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    specNorm ((1 - Q) * P) < 1 ↔ (Q * P).rank = P.rank
theorem IsStarProjection.specNorm_one_sub_mul_le_add {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    specNorm ((1 - P) * R) ≤ specNorm ((1 - P) * Q) + specNorm ((1 - Q) * R)

noncomputable def principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) : ℝ :=
  Real.arccos (singularValues (rangeProjector X * rangeProjector Y) k)
theorem HasOrthonormalCols.cos_principalAngle {U : Matrix n p 𝕜} {V : Matrix n q 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (k : ℕ) :
    Real.cos (principalAngle U V k) = singularValues (Uᴴ * V) k
theorem singularValues_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) {i j : ℕ} (hij : i + j + 1 = Y.rank) :
    singularValues ((1 - rangeProjector X) * rangeProjector Y) i = Real.sin (principalAngle X Y j)
theorem specNorm_rangeProjector_sub_rangeProjector {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm (rangeProjector X - rangeProjector Y) = Real.sin (principalAngle X Y j)
theorem HasOrthonormalCols.isUnit_conjTranspose_mul_iff {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n p 𝕜) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsUnit (Uᴴ * Y) ↔ principalAngle U Y j < Real.pi / 2
noncomputable def tangentMatrix (U Y : Matrix n p 𝕜) : Matrix n p 𝕜 :=
  (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹
theorem HasOrthonormalCols.singularValues_tangentMatrix {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {Y : Matrix n p 𝕜} (hY : IsUnit (Uᴴ * Y)) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues (tangentMatrix U Y) i = Real.tan (principalAngle U Y j)
theorem IsStarProjection.matrixNorm_one_sub_mul_le_add (Φ : SymmetricGauge) {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    Φ.matrixNorm ((1 - P) * R) ≤ Φ.matrixNorm ((1 - P) * Q) + Φ.matrixNorm ((1 - Q) * R)
theorem IsStarProjection.matrixNorm_one_sub_mul_le_of_le (Φ : SymmetricGauge) {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P ≤ Q) (A : Matrix n m 𝕜) :
    Φ.matrixNorm ((1 - Q) * A) ≤ Φ.matrixNorm ((1 - P) * A)
theorem HasOrthonormalCols.exists_frobNorm_sub_mul_sq_le {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧
      frobNorm (U - V * T) ^ 2 ≤ 2 * frobNorm ((1 - V * Vᴴ) * U) ^ 2

theorem conjTranspose_mul_self_eq_iff_exists_mul {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
    (hcard : Fintype.card p ≤ Fintype.card m) :
    Aᴴ * A = Bᴴ * B ↔ ∃ W : Matrix m p 𝕜, HasOrthonormalCols W ∧ A = W * B
theorem isCompact_setOf_hasOrthonormalCols : IsCompact {Q : Matrix n p 𝕜 | HasOrthonormalCols Q}

theorem exists_cs_decomposition {U : Matrix (p ⊕ q) (p ⊕ q) 𝕜} (hU : HasOrthonormalCols U)
    (e : p ↪ q) :
    ∃ (V₁ W₁ : Matrix p p 𝕜) (V₂ W₂ : Matrix q q 𝕜) (c s : p → ℝ),
      HasOrthonormalCols V₁ ∧ HasOrthonormalCols W₁ ∧ HasOrthonormalCols V₂ ∧
      HasOrthonormalCols W₂ ∧ (∀ i, 0 ≤ c i) ∧ (∀ i, 0 ≤ s i) ∧ (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      U = Matrix.fromBlocks V₁ 0 0 V₂ * csMatrix 𝕜 c s e * (Matrix.fromBlocks W₁ 0 0 W₂)ᴴ

theorem IsIdempotentElem.isStarProjection_iff_specNorm_le_one {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) : IsStarProjection P ↔ specNorm P ≤ 1
theorem IsIdempotentElem.specNorm_one_sub {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) (h1 : P ≠ 1) : specNorm (1 - P) = specNorm P
theorem IsIdempotentElem.specNorm_mul_cos_principalAngle {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {j : ℕ} (hj : j + 1 = P.rank) :
    specNorm P * Real.cos (principalAngle P Pᴴ j) = 1
theorem HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    specNorm (U * (Vᴴ * U)⁻¹ * Vᴴ) = specNorm (Vᴴ * U)⁻¹
```

## 4. Consumers

| Item | Consumed by |
|---|---|
| `(1 - Q) * P` and its singular values, equal-rank symmetry, gap formulas | M6 Davis–Kahan and Wedin (statements and the passage between `sin Θ` forms); subspace iteration and Lanczos convergence; randomized range finders |
| triangle inequality for gaps | chaining a perturbation bound with an approximation bound |
| `principalAngle`, sines, tangents, the acute criterion | M6 `tan Θ` theorems; convergence of subspace iteration (`tan θ` contraction); canonical correlations |
| leverage scores as the diagonal of a projector | row sampling and coherence in the sketching layer |
| change of frame, equal Gram matrices | uniqueness of QR and polar factors (M9); invariance arguments in randomized algorithms |
| compactness of the set of frames | existence of optimal subspaces (PCA, Procrustes, M9) |
| oblique projector norm, `‖1 - P‖ = ‖P‖` | interpolative and CUR decompositions, Petrov–Galerkin and oblique Krylov methods, sketched Rayleigh–Ritz |
| CS decomposition | M6 (a route to `sin Θ`/`tan Θ` identities); generalized SVD |

## 5. Files

Under `NLAlib/Matrix/Subspaces/`:

1. `ProjectorPair.lean` (imports M2 `Projector`, M3b `UnitarilyInvariant`).
2. `PrincipalAngles.lean` (imports 1, M3 `SVD`).
3. `Frames.lean` (imports M1 `OrthonormalBasis`, M2 `Spectral`).
4. `Oblique.lean` (imports 2).
5. `CSDecomposition.lean` (imports 1, 3, M3 `SVD`).

Independent for proving: 1 and 3; then 2 and 5; then 4.

## 6. Material

Read: prototype `Matrix/Subspaces/*` (53 modules).

Reused: the equal-rank symmetry and gap formulas (already over `𝕜`), the principal-angle
identities (real, to be redone over `𝕜`), the CS decomposition (real and complex versions, to be
unified), the oblique projection norm theory (real and complex versions, to be unified).

Not reproduced: the seven distance notions listed in §2; `principalAnglesFintype` with `Fin`
indices and the diagonal matrices `sinePrincipalAngles`, `tangentPrincipalAngles`; the `Complex*`
duplicates; the canonical form of an idempotent with its parameters `t i` (the secant formula and
`‖1 - P‖ = ‖P‖` are stated directly); bundled toolkit theorems.

## 7. Decisions taken without approval

1. **The distance between subspaces is the matrix `(1 - Q) * P` of two orthogonal projectors, in
   a norm.** No named gap or residual function; one named matrix, `tangentMatrix`.
2. **`principalAngle X Y k` is defined for the column spaces of arbitrary matrices**, through
   `rangeProjector`, ℕ-indexed, non-decreasing, `π / 2` beyond the smaller dimension.
3. **Tangents are stated for a frame and a basis with the same number of columns** with
   `tangentMatrix U Y`; no pseudoinverse-based general tangent, which would not be a quantity of
   the subspace.
4. **One CS decomposition over `𝕜`**, in the prototype's form with an embedding `e : p ↪ q`, and
   a small definition `csMatrix` for the canonical matrix.
5. **`Stiefel`, the polar frame, the canonical QR frame and frame moment sums leave this stage**
   (M9 and the random-matrix layer).

## 8. Review (Fable, 2026-10-14) and what changed

The review wrote out Davis–Kahan, Wedin, the tangent contraction of subspace iteration and the
range-finder bound under this interface and confirmed decision 1 (no named distance), the
cosine-ordered `principalAngle` through `rangeProjector` (a sine-ordered definition would break
symmetry when the ranks differ), and decision 3 (no pseudoinverse tangent: `Ω₂ Ω₁⁺` of
Halko–Martinsson–Tropp is the `F` of the graph lemma after the reduction `Z = Ω * pinv Ω₁`). It
checked the degenerate cases of the listed statements and found none false. Folded in:

1. `tangentMatrix U Y` is a definition, because subspace iteration carries the four-factor
   expression through an induction; the tangent lemmas are stated with it.
2. The inequalities between projectors are stated for `Φ.matrixNorm` first (triangle inequality,
   equal-rank symmetry), with spectral and Frobenius corollaries; `ProjectorPair.lean` therefore
   imports M3b.
3. Added for M6 and the range-finder analysis: `IsStarProjection.rank_eq_of_specNorm_sub_lt_one`,
   residual monotonicity `IsStarProjection.matrixNorm_one_sub_mul_le_of_le`, and the alignment of
   two frames `HasOrthonormalCols.exists_frobNorm_sub_mul_sq_le` (with a spectral twin).
4. The CS decomposition records that its cosines are the singular values of the leading block.
