# Design note: Matrix stage M1, foundations

Status: written 2026-10-14 by the orchestrator. Implemented without a maintainer approval stop, by
the standing instruction recorded in `docs/port/status.md`. Every choice a maintainer would have
been asked about is in §7 with the option taken.

Every Lean signature in this note has been elaborated against the pinned Mathlib.

## 0. What this stage is for

M1 supplies the objects every later stage states its hypotheses in: orthonormal columns, the
orthogonal projector onto a column space, quadratic forms, Gram matrices, and the block and rank
facts that the spectral, least-squares and factorization stages lean on. It has no norms (M2) and
no eigenvalues (M3). Statements here that involve a length use the Euclidean vector norm
`‖WithLp.toLp 2 x‖` only.

## 1. Objects

New definitions, each a §5.3 row.

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| orthonormal columns | `HasOrthonormalCols Q := Qᴴ * Q = 1` (already a row) | `hasOrthonormalCols_iff_orthonormal`, `hasOrthonormalCols_iff_mem_unitaryGroup` |
| projector onto a column space | `rangeProjector A : Matrix m m 𝕜`, every shape and rank | `toEuclideanLin_rangeProjector` to `Submodule.starProjection` |
| projection residual | no definition; spelled `(1 - rangeProjector Y) * A` | `one_sub_rangeProjector_mul` expands it |
| full column rank | `Function.Injective A.mulVec`, as a hypothesis | Mathlib's; `isUnit_conjTranspose_mul_self_iff`, `…_iff_rank` |
| column space | no definition; Mathlib's `LinearMap.range A.mulVecLin` | Mathlib's |
| range containment | `LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin` | Mathlib's |
| quadratic form | `quadForm A z := star z ⬝ᵥ (A *ᵥ z) : 𝕜` (already a row) | `quadForm_def`, `posSemidef_iff_quadForm_nonneg` |
| Rayleigh quotient | `rayleighQuotient A x : ℝ := re (quadForm A x) / ‖toLp 2 x‖ ^ 2` | `rayleighQuotient_eq_toEuclideanCLM` to `ContinuousLinearMap.rayleighQuotient` |
| Gram matrix | no definition; spelled `Aᴴ * A` | `conjTranspose_mul_self_eq_gram` to `Matrix.gram` |
| Schur complement | no definition; Mathlib's `D - C * A⁻¹ * B` | Mathlib's |
| column selection | `selectionMatrix s : Matrix n p 𝕜` for `s : p → n` | `mul_selectionMatrix` to `Matrix.submatrix` |
| Hermitian dilation | `dilation A : Matrix (m ⊕ n) (m ⊕ n) 𝕜` | `rfl` to `Matrix.fromBlocks 0 A Aᴴ 0` |
| plane rotation | `planeRotation u v c s : Matrix n n 𝕜`, `c s : ℝ` | — |
| compound matrix | `Matrix.compound k A` (in `ForMathlib`), indexed by Mathlib's `Set.powersetCard` | — |

Mathlib objects used directly, with no NLAlib counterpart: `Matrix.rank`, `Matrix.PosSemidef`,
`Matrix.PosDef`, `Matrix.IsHermitian`, `IsStarProjection`, `Matrix.unitaryGroup`,
`Matrix.fromBlocks`, `Matrix.submatrix`, `Matrix.det`, `Orthonormal`, `Matrix.toEuclideanLin`.

## 2. Interfaces

**`HasOrthonormalCols Q`.** One predicate. It is a `def` unfolding to `Qᴴ * Q = 1`, as
`Matrix.IsHermitian` unfolds to `Aᴴ = A`, so a raw equation elaborates against it and
`hQ.conjTranspose_mul_self` rewrites with it.

- Isometries (tall `Q`): the predicate itself.
- Orthonormal rows: `HasOrthonormalCols Qᴴ`. There is no `HasOrthonormalRows`.
- Unitaries: a square `Q` with `HasOrthonormalCols Q`. `hQ.mul_conjTranspose_self` gives the other
  equation and `hasOrthonormalCols_iff_mem_unitaryGroup` is the bridge. Statements take
  `HasOrthonormalCols Q` with `Q : Matrix n n 𝕜`, never `Q ∈ unitaryGroup n 𝕜`, so that one lemma
  about isometries serves both. Mathlib's `unitaryGroup` is used only where its group structure is
  wanted.
- Partial isometries are not given a predicate in this stage. No consumer in M1 to M6 needs one
  that `HasOrthonormalCols` on a factor does not cover.

**`IsStarProjection P`** (Mathlib, `Mathlib.Algebra.Star.StarProjection`) is the interface for
"`P` is an orthogonal projector": idempotent and self-adjoint. NLAlib does not define its own.
This stage adds the matrix API Mathlib lacks: `Matrix.isStarProjection_iff`,
`IsStarProjection.isHermitian`, `.posSemidef`, `.eq_of_range_eq`, `.mul_eq_self_iff`.
Mathlib already has `IsStarProjection.one_sub`, `.mul_one_sub_self`, `.add`, `.mul`.

**`rangeProjector A`** is the one way to name the orthogonal projector onto `range A`. It is
defined for every matrix, so a theorem about a range finder is stated for the sketch
`Y = A * Ω` itself, `specNorm ((1 - rangeProjector Y) * A) ≤ …`, with no orthonormal basis chosen.
The prototype stated these for a chosen frame `Q` (a `gaussianRangeFrame`) and then had to carry
its measurability. With an orthonormal `Q` in hand the user rewrites with
`hQ.rangeProjector_eq : rangeProjector Q = Q * Qᴴ`; with two matrices of equal range,
`rangeProjector_inj`.

**Range containment** is `LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin`. The two
equivalent matrix forms are lemmas, not hypotheses: `rangeProjector_mul_eq_self_iff`
(`rangeProjector B * Y = Y`) and `range_mulVecLin_le_iff_exists_mul` (`∃ C, Y = B * C`).

## 3. Statement shapes

Variables: `{𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]`,
`DecidableEq` added per declaration where Mathlib needs it.

### Orthonormal columns

```lean
def HasOrthonormalCols [DecidableEq n] (Q : Matrix m n 𝕜) : Prop := Qᴴ * Q = 1

theorem hasOrthonormalCols_iff_orthonormal [DecidableEq n] {Q : Matrix m n 𝕜} :
    HasOrthonormalCols Q ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j)

theorem hasOrthonormalCols_iff_mem_unitaryGroup [DecidableEq n] {Q : Matrix n n 𝕜} :
    HasOrthonormalCols Q ↔ Q ∈ Matrix.unitaryGroup n 𝕜

theorem HasOrthonormalCols.norm_toLp_mulVec [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ = ‖WithLp.toLp 2 x‖

theorem HasOrthonormalCols.mul_conjTranspose_self_of_card_eq [DecidableEq m] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (h : Fintype.card m = Fintype.card n) :
    Q * Qᴴ = 1
```

API around these: `hasOrthonormalCols_one`, `.mul`, `.submatrix` (row equivalence, injective
column map), `hasOrthonormalCols_fromCols_iff`, the cancellation lemmas
`.conjTranspose_mul_cancel_left : Qᴴ * (Q * A) = A`, `.mul_conjTranspose_mul_self : Q * Qᴴ * Q = Q`,
`.conjTranspose_mul_mul : (Q * A)ᴴ * (Q * B) = Aᴴ * B`, `.mul_right_inj : Q * A = Q * B ↔ A = B`,
`.mulVec_injective`, `.star_mulVec_dotProduct_mulVec`, `.card_le`, `.rank_eq`, `.rank_mul`, and for
square `Q`: `.mul_conjTranspose_self`, `.conjTranspose`, `.isUnit`, `.inv_eq`.

### Projectors

```lean
noncomputable def rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) : Matrix m m 𝕜
  -- the matrix of `Submodule.starProjection` of the column space, transported along `WithLp`

theorem isStarProjection_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    IsStarProjection (rangeProjector A)

theorem rangeProjector_mul_self [DecidableEq m] (A : Matrix m n 𝕜) : rangeProjector A * A = A

theorem range_mulVecLin_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    LinearMap.range (rangeProjector A).mulVecLin = LinearMap.range A.mulVecLin

theorem rangeProjector_mul_eq_self_iff [DecidableEq m] {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜} :
    rangeProjector B * Y = Y ↔ LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin

theorem HasOrthonormalCols.rangeProjector_eq [DecidableEq m] [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : rangeProjector Q = Q * Qᴴ

theorem _root_.IsStarProjection.eq_rangeProjector [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {A : Matrix m n 𝕜}
    (h : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) : P = rangeProjector A

theorem exists_hasOrthonormalCols_range_eq [DecidableEq p] (A : Matrix m n 𝕜)
    (h : Fintype.card p = A.rank) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range Q.mulVecLin = LinearMap.range A.mulVecLin

theorem exists_hasOrthonormalCols_range_le [DecidableEq p] (A : Matrix m n 𝕜)
    (h : A.rank ≤ Fintype.card p) (hp : Fintype.card p ≤ Fintype.card m) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range A.mulVecLin ≤ LinearMap.range Q.mulVecLin

theorem HasOrthonormalCols.exists_fromCols [DecidableEq n] [DecidableEq p] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card n + Fintype.card p = Fintype.card m) :
    ∃ Q' : Matrix m p 𝕜, HasOrthonormalCols (Matrix.fromCols Q Q')

theorem range_mulVecLin_one_sub_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    LinearMap.range (1 - rangeProjector A).mulVecLin = LinearMap.ker Aᴴ.mulVecLin

theorem rangeProjector_eq_mul_inv_mul_conjTranspose [DecidableEq m] [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : IsUnit (Aᴴ * A)) :
    rangeProjector A = A * (Aᴴ * A)⁻¹ * Aᴴ

theorem norm_one_sub_rangeProjector_mulVec_le [DecidableEq m] (B : Matrix m n 𝕜) (x : m → 𝕜)
    (y : n → 𝕜) :
    ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (x - B *ᵥ y)‖
```

The existence theorems take the column index type `p` and a cardinality hypothesis, not
`Fin A.rank`: for a random `A` the type `Fin (A ω).rank` depends on `ω` and no downstream statement
could hold the basis. `exists_hasOrthonormalCols_range_le` is the literature's "`k`-column frame
containing the range". `HasOrthonormalCols.exists_fromCols` is orthonormal completion, concluded
in the interface form: the completed matrix `fromCols Q Q'` has orthonormal columns, and since it
is square up to a bijection `hQ.mul_conjTranspose_self_of_card_eq` gives `Q Qᴴ + Q' Q'ᴴ = 1`. The
last statement names the orthogonal complement of a range without leaving `m → 𝕜`.

`rangeProjector` itself takes no `DecidableEq m`: the definition uses a classical instance
internally and every API lemma is stated without unfolding it, so a consumer's own instance on `m`
(needed only where `1` appears) never has to match it.
API: `rangeProjector_zero`, `_one`, `_of_isUnit`, `_smul`, `rangeProjector_inj`,
`rangeProjector_mul_rangeProjector_of_range_le` and its mirror, `rangeProjector_mono` (Loewner),
`rangeProjector_mul_eq_zero_iff : rangeProjector B * Y = 0 ↔ Bᴴ * Y = 0`,
`conjTranspose_mul_one_sub_rangeProjector : Bᴴ * (1 - rangeProjector B) = 0`,
`conjTranspose_mul_rangeProjector : Aᴴ * rangeProjector A = Aᴴ`, the `@[simp]` pair
`rangeProjector_mul_rangeProjector` and `conjTranspose_rangeProjector`, the vector forms
`rangeProjector_mulVec_eq_self_iff : rangeProjector B *ᵥ x = x ↔ x ∈ LinearMap.range B.mulVecLin`
and `rangeProjector_mulVec_mulVec`,
`rank_rangeProjector`, `IsStarProjection.rangeProjector_eq : rangeProjector P = P`,
`IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq`, and the expansion
`one_sub_rangeProjector_mul : (1 - rangeProjector Y) * A = A - rangeProjector Y * A` for the
proofs that want the difference.

The matrix best-approximation and Pythagoras statements in Frobenius and spectral norm are M2's.
M4 adds `mul_pinv : A * pinv A = rangeProjector A`.

### Quadratic forms

```lean
def quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : 𝕜 := star z ⬝ᵥ (A *ᵥ z)

noncomputable def rayleighQuotient (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (quadForm A x) / ‖WithLp.toLp 2 x‖ ^ 2

theorem _root_.Matrix.PosSemidef.quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (z : n → 𝕜) : 0 ≤ quadForm A z

theorem posSemidef_iff_quadForm_nonneg {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ z, 0 ≤ quadForm A z

theorem re_quadForm_le_re_quadForm_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (z : n → 𝕜) :
    RCLike.re (quadForm A z) ≤ RCLike.re (quadForm B z)
```

`quadForm` is `𝕜`-valued, Mathlib's `PosSemidef` form. Real consumers take `RCLike.re`; for
Hermitian `A`, `hA.coe_re_quadForm` and `hA.im_quadForm` say nothing is lost. `0 ≤ quadForm A z`
over `𝕜` uses `ComplexOrder`, which the file opens. API: linearity in `A`
(`quadForm_add_left`, `_smul_left`, `_sub_left`, `_neg_left`, `_zero_left`), `quadForm_zero_right`,
`quadForm_smul_right`, the polar expansion `quadForm_add_right`, `star_quadForm`,
`quadForm_one`, `quadForm_diagonal`, `quadForm_vecMulVec_star`, `quadForm_conjTranspose_mul_mul`,
`quadForm_conjTranspose_mul_self`, `quadForm_eq_sum`, `Matrix.PosDef.quadForm_pos`,
`Matrix.IsHermitian.ext_quadForm`, `rayleighQuotient_smul`, `rayleighQuotient_of_mulVec_eq_smul`.

### Gram matrices

```lean
theorem isUnit_conjTranspose_mul_self_iff [DecidableEq n] {A : Matrix m n 𝕜} :
    IsUnit (Aᴴ * A) ↔ Function.Injective A.mulVec

theorem isUnit_conjTranspose_mul_self_iff_rank [DecidableEq n] {A : Matrix m n 𝕜} :
    IsUnit (Aᴴ * A) ↔ A.rank = Fintype.card n
```

"Full column rank" is therefore `Function.Injective A.mulVec` (Mathlib's hypothesis in
`Matrix.PosDef.conjTranspose_mul_self`), with the rank and `IsUnit` forms as equivalents.
Mathlib already has PSD, rank and kernel of `Aᴴ * A`; they are not restated.

### Schur complements

```lean
theorem posSemidef_fromBlocks_iff_exists {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ ∃ X : Matrix m n 𝕜, A * X = B ∧ (C - Xᴴ * A * X).PosSemidef

theorem quadForm_fromBlocks_eq_add {A : Matrix m m 𝕜} {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hX : A * X = B) (y : m → 𝕜) (x : n → 𝕜) :
    quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x) =
      quadForm A (y + X *ᵥ x) + quadForm (C - Xᴴ * A * X) x

theorem posDef_fromBlocks_iff [DecidableEq m] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ A.PosDef ∧ (C - Bᴴ * A⁻¹ * B).PosDef
```

The first is Albert's criterion with the pseudoinverse eliminated: any solution `X` of `A X = B`
gives the same `C - Xᴴ A X`. M4 specialises `X := A⁺ B` and introduces the named generalized
Schur complement there, where the pseudoinverse exists. Mathlib has the invertible-`A` PSD
criterion, the determinant and the inverse.

### Rank (ForMathlib, over a field `K`)

```lean
theorem Matrix.rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank

theorem Matrix.rank_add_rank_le_card_add_rank_mul (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank ≤ Fintype.card n + (A * B).rank

theorem Matrix.rank_mul_add_rank_mul_le (A : Matrix l m K) (B : Matrix m n K) (C : Matrix n p K) :
    (A * B).rank + (B * C).rank ≤ B.rank + (A * B * C).rank

theorem Matrix.rank_fromBlocks₁₁ [DecidableEq m] (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix l m K) (D : Matrix l n K) [Invertible A] :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * ⅟A * B).rank
```

Sylvester's and Frobenius's inequalities are stated additively. The prototype's
`A.rank + B.rank - card n ≤ (A * B).rank` uses truncated subtraction and cannot be used with
`omega` or `linarith` without a case split.

## 4. Consumers

| Item | Consumed by |
|---|---|
| `HasOrthonormalCols` | every later stage; M2 invariance of norms; M3 `IsSVD`, compressions; M5 principal angles; Krylov bases; sketch-and-solve |
| `rangeProjector`, `IsStarProjection` | M2 best approximation; M4 `A A⁺`; M5 projector gaps and subspace distance; M6 Davis–Kahan, Wedin; range finders, subspace iteration, Nyström |
| `exists_hasOrthonormalCols_range_eq` | every "choose an orthonormal basis of the range" step |
| `quadForm` | M3 Courant–Fischer and Rayleigh forms; M7; trace estimators; Krylov energy norms |
| `rayleighQuotient` | M3; power method and Ritz values (Krylov) |
| Gram invertibility | M4 full-rank pseudoinverse formulas; least squares; sketching `(SA)⁺` |
| `posSemidef_fromBlocks_iff_exists` | M4 generalized Schur complement; M7 block inequalities; M8 operator convexity |
| rank inequalities | M3 rank and singular values; M4; M9 rank-revealing factorizations |
| `selectionMatrix` | M3 interlacing for principal submatrices as compressions; M9; column sampling sketches |
| `dilation` | M3 singular values through eigenvalues; rectangular matrix concentration |
| `planeRotation` | M7 Schur–Horn; M9 Givens |
| Cauchy–Binet | M7 determinant inequalities; M9 maximum volume; volume sampling |
| PSD closedness, PD dense in PSD | M7 Hadamard power series and determinant boundary cases; M8 limits of matrix functions |

## 5. Files

In build order. `ForMathlib` files hold statements with no NLAlib vocabulary and are declared in
namespace `Matrix`.

1. `NLAlib/ForMathlib/LinearAlgebra/Matrix/Rank.lean`: `rank_eq_zero`, `rank_add_le`,
   `rank_sub_le`, Sylvester, Frobenius, `rank_fromBlocks_zero₁₂_zero₂₁`, `rank_fromBlocks₁₁`,
   `rank_fromCols_replicateCol_eq_iff`, the complementary nullity theorem.
2. `NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean`: zero diagonal entry forces zero row and
   column, entry bounds, real trace, trace pairing of two PSD matrices (nonnegative, zero iff
   product zero, monotone, characterises PSD), closedness of the PSD set, PD dense in PSD.
3. `NLAlib/ForMathlib/LinearAlgebra/Matrix/Adjugate.lean`: single-entry update of a
   determinant, cofactor locality, determinant under two different reindexings.
4. `NLAlib/ForMathlib/LinearAlgebra/Matrix/SchurComplement.lean` (imports 3): Jacobi's
   complementary minor formula.
5. `NLAlib/ForMathlib/LinearAlgebra/Matrix/CauchyBinet.lean`: Cauchy–Binet, the Gram determinant
   as a sum over row selections, compound matrices and their multiplicativity.
6. `NLAlib/Matrix/Basic/Orthonormal.lean`
7. `NLAlib/Matrix/Basic/QuadForm.lean`
8. `NLAlib/Matrix/Basic/Gram.lean`
9. `NLAlib/Matrix/Basic/Projector.lean` (imports 6 and 8)
10. `NLAlib/Matrix/Basic/SchurComplement.lean` (imports 7 and 9)
11. `NLAlib/Matrix/Basic/Selection.lean` (imports 6)
12. `NLAlib/Matrix/Basic/Dilation.lean`
13. `NLAlib/Matrix/Basic/PlaneRotation.lean` (imports 6)

Independent for proving, so two agents may run: the `ForMathlib` files 1, 2, 5 and the pair 3 → 4
are independent of each other and of the `Matrix/Basic` files; 7, 8, 11, 12, 13 are independent of
each other once 6 is done.

## 6. Material

Read: prototype `Matrix/Basic/*` (33 files) and `Matrix/Subspaces/{Projections, RangeProjector,
OrthonormalBasisMatrix}`, through `atlas/declarations.json` and the source of the definitions.

Reused as mathematics and proof material: the orthonormality lemmas; `rangeProjector` API (the
prototype proves it through `B B⁺`, here it is proved through `Submodule.starProjection`);
`QuadForm`; rank inequalities; Schur complement PSD criterion (`GeneralizedSchurComplement`,
restated without the pseudoinverse); Cauchy–Binet; determinant updates; Jacobi minors; PSD entry,
trace and limit lemmas; selection, dilation, plane rotation.

Not reproduced:

- `projResidual Q A = A - Q (Qᴴ A)`, used in 41 prototype files. It is a projection residual only
  when `Q` is orthonormal and is junk otherwise, and it forces a chosen basis into every range
  finder statement. Replaced by `A - rangeProjector Y * A`.
- `columnSpace` as a submodule of `EuclideanSpace`, with `toEuclideanSubmodule` and
  `toCoordinateSubmodule` transports, and `orthonormalBasisMatrix` as a definition. Replaced by
  Mathlib's `LinearMap.range A.mulVecLin` and an existence theorem.
- Bundles: `cauchy_binet_properties`, `complementary_nullities_properties`, `rank_mul_bounds`,
  `psd_trace_pairing_characterizations`. Their conjuncts are separate theorems.
- Real-only statements (`Gram`, `SchurRank`, `PlaneRotation`, `Selection`, determinant updates,
  PSD series): restated over `𝕜` or over a field or commutative ring.
- `quadForm_reindex`, `leadingSubmatrix_fin`, `leadingMinor_fin`: transport lemmas.

Moved to the stage that consumes them, recorded in the ledger as deferred: Moore–Penrose,
pseudoinverse, least squares, `generalizedSchurComplement` (M4); `IsBestFrobRankApprox` and every
`frobSq`/`specNorm` statement about projectors (M2, M3); unitary completion and complement (M5);
`pivotSchur`, `borderedMatrix`, `leadingSubmatrix`, `leadingMinor` (M9, where the elimination
recursion that uses them is designed); `matrixOf_curry_update_eq_add_single` (a Gaussian
integration-by-parts helper; it moves with its consumer in `RandomMatrix`).

## 7. Decisions taken without approval

1. **The projector is the primitive, not the residual.** `rangeProjector A` for every matrix;
   the residual has no name and one spelling, the product `(1 - rangeProjector Y) * A`.
   Alternative: keep `projResidual` as a definition. Not taken: a definition that only abbreviates
   a short expression costs an unfold at every use. The product form is the spelling because
   every consumer (range finders, Davis–Kahan, Wedin, contractivity in M2) has a star projection
   times something, so `IsStarProjection.one_sub` and submultiplicativity apply with no rewrite.
   `dilation` is also a `rfl` abbreviation and is kept as a definition, for the opposite reason:
   it carries its own API (`IsHermitian`, additivity, later its spectrum and norm), and
   `fromBlocks 0 A Aᴴ 0` is too long to be a spelling.
2. **`IsStarProjection` from Mathlib is the projector interface.** Alternative: an NLAlib
   `IsOrthProjector`. Not taken: Mathlib has the predicate and its algebra.
3. **Column space is `LinearMap.range A.mulVecLin`**, in `m → 𝕜`, not a submodule of
   `EuclideanSpace 𝕜 m`. Orthogonality is expressed through matrices (`Bᴴ * Y = 0`) or through
   `rangeProjector`; the Euclidean submodule appears only in the bridge lemma.
4. **Unitaries are square `HasOrthonormalCols`**, with a bridge to `unitaryGroup`.
5. **`quadForm` stays `𝕜`-valued**, as §5.3 already says; `rayleighQuotient` is real-valued and
   is a new §5.3 row.
6. **No Gram or Schur-complement definitions**; Mathlib's raw spellings are the vocabulary.
7. **Gap-filling facts about Mathlib objects go to `ForMathlib`** (rank, determinant, PSD
   entries, Cauchy–Binet). Topic developments that happen to use only Mathlib vocabulary (Gram
   invertibility, the PSD block criterion) stay in `NLAlib/Matrix/Basic/`.
8. **Leading minors and the pivot Schur step move to M9**, plane rotations stay in M1 because M7
   needs them before M9.
9. **Cauchy–Binet is stated without choosing enumerations.** The term for a subset `s` is
   `det (A.submatrix id val * B.submatrix val id)`, the two rectangular selections indexed by `s`
   itself, summed over Mathlib's `Finset.powersetCard`. No order on the index types is needed and
   the Gram case reads `det (Aᴴ A) = ∑ s, det (A_sᴴ A_s)`, which is the form volume sampling
   consumes. The prototype's `SizedSubset` and its chosen `sizedSubsetIndex` are not reproduced.
   Compound matrices do need a sign convention; they are indexed by Mathlib's
   `Set.powersetCard` and take `[LinearOrder]` on the index types, with minors in increasing
   order, which is where Mathlib's exterior-power files are heading.

## 8. Design review (Fable, 2026-10-14)

Eleven comments; none asked for a decision in §7 to be reversed. Folded in:

- Residual spelling changed from `A - rangeProjector Y * A` to the product
  `(1 - rangeProjector Y) * A` (the one MUST).
- Orthonormal completion (`HasOrthonormalCols.exists_fromCols`) and
  `range_mulVecLin_one_sub_rangeProjector` moved from M5 into `Projector.lean`: M3's full SVD and
  M6's complements need them first.
- Existence of orthonormal bases restated over an arbitrary column type with a cardinality
  hypothesis, plus the "frame containing the range" form.
- Vector-level and `@[simp]` projector lemmas added to the API list.
- "Full column rank" added as a §5.3 row; `selectionMatrix` ships its `rfl` bridge to
  `Matrix.submatrix`; `rangeProjector` takes no `DecidableEq`; consumers named for PSD closedness.

Checked and kept: `posDef_fromBlocks_iff`. Mathlib has `PosSemidef.fromBlocks₁₁`, which assumes
`A.PosDef` and concludes semidefiniteness of the block matrix; it has no positive definite
criterion.

## 9. Stage report (2026-10-14)

**Outcome.** Fifteen files, all proved; nothing in `NLAlibScaffold`. Thirteen were in §5; two were
added during the stage: `ForMathlib/Analysis/InnerProductSpace/PiL2.lean` (the bridges between
`‖WithLp.toLp 2 x‖` and `star x ⬝ᵥ x`, which three files needed) and
`Matrix/Basic/OrthonormalBasis.lean` (split from `Projector.lean` when it reached 610 lines).
Proofs were written by Opus agents, one or two small files per agent, two agents at a time; each
agent took between three and eleven minutes.

**What changed from the design, and why.**

- *Residual spelling.* The design review changed it from `A - rangeProjector Y * A` to the product
  `(1 - rangeProjector Y) * A` before any proof was written (§8).
- *`rangeProjector` takes no `DecidableEq`.* Its definition uses a classical instance internally;
  no API lemma exposes it.
- *Cauchy–Binet* is stated with each term as `det (A_s * B_s)`, indexed by the subset itself, and
  compound matrices are indexed by Mathlib's `Set.powersetCard` with linear orders on the index
  types (§7.9, rewritten when the skeleton was typed).
- *Typeclass arguments* were minimised per declaration by the linters. Several statements hold for
  an arbitrary (not finite) row type: `rank_add_le`, the PSD entry lemmas, closedness of the PSD
  cone.
- *Jacobi's formula* is proved by multiplying by a block triangular matrix and taking
  determinants, with no rank argument and no case split on a singular block; the prototype's proof
  needed both. The argument works over a commutative ring. The field statement was kept; the ring
  form `M.det * M⁻¹.toBlocks₂₂.det = M.toBlocks₁₁.det` is the better upstream statement.
- *`dilation_smul_real`* is stated with the real scalar action `c • A`, matching the convention
  M2 fixes for scalar multiples of the identity.
- *Promoted after review:* `HasOrthonormalCols.exists_fromCols_of_card_le` (completion by any
  number of columns that fits), `rank_one_sub_rangeProjector_add_rank`,
  `rangeProjector_mulVec_eq_zero_iff`, `Matrix.rank_neg`, `conjTranspose_dilation`.

**Mathlib overlap found while proving** (kept as one-line API on the interfaces):
`hasOrthonormalCols_iff_mem_unitaryGroup` is `Matrix.mem_unitaryGroup_iff'`;
`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` is `Matrix.mul_eq_one_comm_of_card_eq`;
`Matrix.isStarProjection_iff` is `isStarProjection_iff`; `Matrix.IsHermitian.im_quadForm` is
`Matrix.IsHermitian.im_star_dotProduct_mulVec_self`; `mul_selectionMatrix` is
`Matrix.mul_submatrix_one`. Mathlib has no Cauchy–Binet formula, no compound matrix, no closedness
of the PSD cone, no `OrderClosedTopology` on matrices, no positive definite block criterion.

**Deferred, with the stage that will account for them in the ledger.** Moore–Penrose, the
full-rank pseudoinverse formulas, least squares, `generalizedSchurComplement` (M4); every
`frobSq`/`specNorm` statement about projectors and `IsBestFrobRankApprox` (M2, M3);
`leadingSubmatrix`, `leadingMinor`, `pivotSchur`, `borderedMatrix` (M9).

**For the next stages.**

- M2 should state orthonormal invariance in the `HasOrthonormalCols` namespace and projector
  bounds on `IsStarProjection`, as its note already does; `PiL2.lean` has the norm bridges it
  needs.
- M3 can take `HasOrthonormalCols.exists_fromCols` for the full SVD and
  `exists_hasOrthonormalCols_range_eq` for thin factors. Eigenvalue bounds on the quadratic form
  (`re_quadForm_mem_Icc`) and eigenvalues of compressions were left for M3.
- M4 gets `rangeProjector A = A * A⁺` as a lemma, the generalized Schur complement as a
  definition, and the `IsLeast` form of the Schur complement minimum if a consumer wants it.
- Two general facts in `ForMathlib/LinearAlgebra/Matrix/Rank.lean` are private and deserve to be
  public upstream lemmas: rank–nullity restricted to a submodule
  (`finrank (map f S) + finrank (S ⊓ ker f) = finrank S`) and the dimension of a product of
  submodules.
- Process: skeletons must be checked with `lake lean`, not `lake env lean`. Proof agents handle a
  file of forty short lemmas in under ten minutes; grouping two or three small files per agent
  worked and saved orchestration time.
