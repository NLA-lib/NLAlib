# Generalized singular value decomposition of a rectangular pair

Design dated 2026-11-01. The coverage target is the original atlas card
`gsvd-normalized-pair`, in `matrix-factorizations` under **Matrix analysis toolkit**.
Formal source: `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Factorizations/GeneralizedSVD.lean` and its normalized PSD-pair dependency.
The source supplies proof material; the interfaces below follow this library.

## Objects and interfaces

Introduce only `IsGSVD A B X c s`, a predicate for normalized common right coordinates.
It uses arbitrary finite row types `m`, `p`, a common finite column type `n`, and `RCLike`.
It records `IsUnit X`, the two Gram congruences, nonnegative real `c`, `s`, and
`c i ^ 2 + s i ^ 2 = 0 ∨ c i ^ 2 + s i ^ 2 = 1`. No rank, nonempty-type, or relative
row-dimension hypothesis is added. In particular, `X` need not be unitary.
The structure constructor is the raw-condition constructor. Mathlib was searched for GSVD;
none was found. Existing Mathlib matrices, Gram products, ranks, kernels and spans are used
directly, with NLAlib's `HasOrthonormalCols` for the normalized columns.

`IsGSVD.swap` exchanges the two matrices and coordinate sequences. One column-normalization
theorem and one zero-column theorem then serve both sides; no left/right theorem twins or
real/complex copies are introduced. No generalized-value quotient is defined: a zero denominator
on an active coordinate and a common-kernel coordinate must not be conflated by total division.

## Statement shapes

The existing `Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal` is strengthened in
place, retaining its name and determinant-unit convention and adding the final normalization
clause. This exposes information already available in its proof, rather than adding a second
PSD-pair development. The statement change is recorded in the rename map.

```lean
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

theorem _root_.Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal
    {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    ∃ (X : Matrix n n 𝕜) (a b : n → ℝ), IsUnit X.det ∧
      Xᴴ * P * X = Matrix.diagonal (fun i => (a i : 𝕜)) ∧
      Xᴴ * Q * X = Matrix.diagonal (fun i => (b i : 𝕜)) ∧
      (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      ∀ i, a i + b i = 0 ∨ a i + b i = 1

structure IsGSVD (A : Matrix m n 𝕜) (B : Matrix p n 𝕜)
    (X : Matrix n n 𝕜) (c s : n → ℝ) : Prop where
  isUnit : IsUnit X
  conjTranspose_mul_mul_left :
    Xᴴ * (Aᴴ * A) * X = Matrix.diagonal (fun i => ((c i ^ 2 : ℝ) : 𝕜))
  conjTranspose_mul_mul_right :
    Xᴴ * (Bᴴ * B) * X = Matrix.diagonal (fun i => ((s i ^ 2 : ℝ) : 𝕜))
  nonneg_left : ∀ i, 0 ≤ c i
  nonneg_right : ∀ i, 0 ≤ s i
  normalized : ∀ i, c i ^ 2 + s i ^ 2 = 0 ∨ c i ^ 2 + s i ^ 2 = 1

theorem exists_isGSVD (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    ∃ X c s, IsGSVD A B X c s

variable {A : Matrix m n 𝕜} {B : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

theorem IsGSVD.swap (h : IsGSVD A B X c s) : IsGSVD B A X s c

theorem IsGSVD.rank_fromRows (h : IsGSVD A B X c s) :
    (Matrix.fromRows A B).rank = Fintype.card {i // c i ^ 2 + s i ^ 2 = 1}

theorem IsGSVD.mulVec_eq_zero_iff (h : IsGSVD A B X c s) (y : n → 𝕜) :
    (Matrix.fromRows A B) *ᵥ (X *ᵥ y) = 0 ↔
      ∀ i, c i ^ 2 + s i ^ 2 = 1 → y i = 0

theorem IsGSVD.hasOrthonormalCols_div (h : IsGSVD A B X c s) :
    HasOrthonormalCols (Matrix.of (fun i (j : {j // 0 < c j}) =>
      (A * X) i j / (c j : 𝕜)))

theorem IsGSVD.col_mul_eq_zero (h : IsGSVD A B X c s) (i : n) (hi : c i = 0) :
    (A * X).col i = 0

theorem IsGSVD.ker_inf_ker_eq_span (h : IsGSVD A B X c s) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin =
      Submodule.span 𝕜 (X.col '' {i | c i ^ 2 + s i ^ 2 = 0})
end NLAlib
```

Supporting Gram rewrite lemmas stay in the predicate namespace:
`IsGSVD.conjTranspose_mul_self_mul` identifies `(A * X)ᴴ * (A * X)` with the diagonal of
`c i ^ 2`, and `IsGSVD.conjTranspose_mul_mul_fromRows` identifies the congruence of the stacked
Gram matrix with the diagonal of `c i ^ 2 + s i ^ 2`. Both follow by associativity and the
structure fields; the right Gram statement follows by `swap`. The positive-column
subtype in the orthonormality statement permits empty subtypes. Common-kernel coordinates are
indexed by a set rather than reordered to the end of a `Fin` type; the rank count and span
equality give the same mathematical content without dimension subtraction or a chosen ordering.

## Consumers and coverage

The immediate consumer of normalized PSD congruence is `exists_isGSVD` on `Aᴴ * A`, `Bᴴ * B`.
GSVD coordinates provide the deterministic foundation for general-form Tikhonov filters and
common-nullspace uniqueness criteria; those consumer theorems are a separate card and are not
included here. The source-card clauses are covered individually by existence, stacked rank,
the common-kernel coordinate equivalence, normalized columns, zero columns, and the span theorem.
An invertible `X` makes its columns independent, so the inactive columns are a basis of that
common kernel. Active coordinates may be reordered first without changing the assertions.

## Files, reuse and attribution

- `Matrix/Spectral/Congruence.lean`: strengthen the existing semidefinite-pair theorem;
  preserve its whitening and commuting-Hermitian proof, with no copied normalization theory.
- `Matrix/Factorizations/GeneralizedSVD.lean`: the predicate, existence and its small API.
- Existing basic column API may be extended only if a shared lemma removes duplicate SVD/GSVD
  arguments; any such change will be listed as an amendment here.
- `CONTRIBUTING.md` receives the predicate's vocabulary row. No parallel Mathlib object exists.
- `docs/references.bib` receives Paige--Saunders (1981), DOI `10.1137/0718026`; the normalized Gram
  formulation and its relation to the block GSVD are stated explicitly in the documentation.
- `NLAlib.lean` is regenerated, and a rename map records the strengthened existing statement.

Mathlib reuse includes `Matrix.posSemidef_conjTranspose_mul_self`,
`Matrix.rank_conjTranspose_mul_self`, `Matrix.rank_diagonal`,
`Matrix.conjTranspose_mul_self_mulVec_eq_zero`, unit-multiplication rank invariance and
`Matrix.fromRows`. No matching normalized PSD-pair theorem or GSVD predicate was found in the
pinned Mathlib. The existing library congruence theorem is reused instead.

The source's `NormalizedPSDPair`, `CommutingHermitian` and `GramVanishing` files are not imported
or copied wholesale. Ordered block packing, a chosen GSVD algorithm, numerical implementation,
regularization limits, numerical-range and resolvent theories are outside this batch.

## Review and validation

The design was independently reviewed against the pinned card before implementation on
2026-11-01. The unordered-coordinate convention, empty dimensions and common kernel were
checked explicitly.

Amendment approved before implementation, 2026-11-01: share the following two elementary
column facts between ordinary SVD and GSVD in `Matrix/Basic/Orthonormal.lean`. The existing
SVD private zero-column helper and normalization subproof are replaced by these calls; this
is removal of duplicate mathematics, not a new factorization theory. The column API belongs
with the existing orthonormal-column and Gram-matrix API.

```lean
theorem col_eq_zero_of_conjTranspose_mul_self_apply_eq_zero
    (B : Matrix m n 𝕜) {i : n} (hi : (Bᴴ * B) i i = 0) : B.col i = 0

theorem hasOrthonormalCols_div_of_conjTranspose_mul_self_eq_diagonal
    {B : Matrix m n 𝕜} {s : n → ℝ}
    (hB : Bᴴ * B = Matrix.diagonal (fun i => ((s i ^ 2 : ℝ) : 𝕜)))
    {r : Type*} [DecidableEq r]
    (e : r → n) (he : Function.Injective e) (hs : ∀ i, s (e i) ≠ 0) :
    HasOrthonormalCols (Matrix.of (fun j i => B j (e i) / (s (e i) : 𝕜)))
```

The zero-column proof reuses Mathlib's `dotProduct_star_self_eq_zero`; normalization reuses
the matrix Gram identity and injective selection. The GSVD applies the latter to positive
coordinates; ordinary SVD applies it to nonzero coordinates. No extra scalar positivity
hypothesis is imposed on this shared fact.
The final shared normalization signature omits `Fintype r`: Gram products sum over rows,
so that instance was unnecessary. This changes no proof or application.

Review this design before library edits, then read every theorem back independently against the
card. Validate zero matrices, empty row/column types, a nontrivial common kernel, and active
coordinates with one generalized singular value zero. Run the unmodified full repository checks,
duplicate/reuse reports, and explorer extraction/rendering on the final tree. No build pins,
checks, target registry, approvals or rule baselines are changed.
