# Where NLAlib deviates from Mathlib, and why

Rule (maintainer, 2026-10-14): wherever the library states things differently from Mathlib, the
deviation is recorded here with its justification, its cost and the lemma that bridges back to
Mathlib. A new deviation gets an entry in the same commit that introduces it. "Deviation" means
that Mathlib has a notion and statements in NLAlib are written with another one. Notions Mathlib
does not have (the pseudoinverse, majorization, the condition number, Schatten norms) are
additions, not deviations; they are listed at the end.

None of these was approved by the maintainer when it was made. Status is given per entry.

## 1. Eigenvalues of a Hermitian matrix

- **Mathlib.** `hA.eigenvalues₀ : Fin (Fintype.card n) → ℝ` (sorted, non-increasing) and
  `hA.eigenvalues : n → ℝ` (unsorted), both taking the proof `hA : A.IsHermitian`.
- **NLAlib.** `eigenvalue A k : ℝ` with `k : ℕ` and no proof argument. For Hermitian `A` and
  `k < Fintype.card n` it is `hA.eigenvalues₀ ⟨k, _⟩`. It is `0` for `k ≥ Fintype.card n`, and
  `0` for every `k` when `A` is not Hermitian.
- **Bridge.** `Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀`,
  `Matrix.IsHermitian.exists_equiv_eigenvalue_eq` (to the unsorted `hA.eigenvalues`).
- **Why the index is `ℕ`.** The bound `k < card n` is usually trivial to prove; the difficulty
  is that with `Fin` the proof is part of the index term, so two indices that are the same number
  are different terms.
  - Index arithmetic: Weyl's inequality needs the index `i + j`, the eigenvalues of `-A` need
    `card n - 1 - k`, interlacing needs `i + (card n - card p)`. Each is a new `Fin` term with a
    bound proof built in, and `rw`, `simp` and `omega` do not see that `⟨i + j, h⟩` and
    `⟨j + i, h'⟩` are equal without an explicit `Fin.ext`.
  - Matrices of different sizes: interlacing and Poincaré separation compare a compression
    indexed by `p` with a matrix indexed by `n`. Their indices live in `Fin (card p)` and
    `Fin (card n)`, two types, so every statement carries `Fin.castLE` and composing two such
    statements means lining the casts up.
  - The type itself moves: `Fin (card (m ⊕ n))` and `Fin (card m + card n)` are different types,
    and rewriting a cardinality inside a type fails with "motive is not type correct".
  - Sums: `∑ i ∈ Finset.range k, eigenvalue A i` against a sum over a subtype of `Fin (card n)`;
    Hoffman–Wielandt and Lidskii are stated over any `S : Finset ℕ`, which uses the zero padding.
  - Mathlib made the same choice, for the same stated reasons, for singular values
    (`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`, implementation notes), and
    eigenvalues and singular values share one indexing here.
- **Why no proof argument.** With `hA.eigenvalues₀` the proof is inside the term. A statement
  about `A + B`, `Uᴴ * A * U` or `A - t • 1` has to build the Hermitian proof of the compound
  matrix inline, and rewriting the matrix under that proof needs a congruence lemma (the
  prototype had `eigenvalues₀_congr` for this). A function of the matrix alone rewrites with
  `rw`. This is a convenience, and a smaller one than the index.
- **Cost.** The hypotheses do not disappear, they move from the term to the theorem:
  statements carry `hA : A.IsHermitian` and, where the value matters, `hk : k < card n`. If one
  is forgotten the statement is either false (the proof fails: this happened once,
  `eigenvalue_le_of_forall_mem`) or true for a trivial reason, which no proof catches and only
  review does. `eigenvalue A 0` for a non-Hermitian `A` type-checks and means nothing; the name
  does not warn. Statements to be upstreamed have to be translated to `eigenvalues₀`.
- **Status: kept (maintainer, 2026-10-14).** The alternative `hA.eigenvalue k`, taking the
  proof, was considered and not taken: building the Hermitian proof at every use is a recurring
  cost in proofs, while the junk value costs nothing as long as statements are right, since Lean
  will not accept a proof of a false one. What has to be checked is therefore the statements.
  Checked on 2026-10-14: of the 193 statements that mention `eigenvalue`, 27 carry no
  Hermitian-type hypothesis, and each of those is intended. Either the argument is Hermitian by
  construction (`Aᴴ * A`, `dilation A`, `hermitianPart A`, `0`, `1`, a real diagonal,
  `U * diagonal d * Uᴴ`), or the statement is an identity whose two sides are junk together
  (`eigenvalue_neg`, `eigenvalue_real_smul`, `eigenvalue_complexify`,
  `eigenvalue_submatrix_equiv`, unitary conjugation), which is the total function paying off:
  these hold for every matrix with no hypothesis to discharge. The out-of-range value was
  checked the same day, for `eigenvalue` and `singularValues` together. The shapes in which the
  padding could make a statement say less than it seems are an index bound by `∃` in a
  conclusion (`∃ k, -3 < eigenvalue A k` is true by taking `k` out of range) and an index bound
  by `∀` in a hypothesis (`∀ k, 0 < eigenvalue A k` can never hold, so a theorem assuming it is
  empty). The library has 6 existential and 47 universal index binders of this kind. Every
  existential one ranges over `Fin`, an equivalence into `Fin (card n)`, or carries a bound.
  Of the universal ones, 18 have no written bound: 13 range over a `Fin` type through the term
  they index, and 5 are over `ℕ` on purpose, where the padding is harmless
  (`A.PosSemidef ↔ ∀ k, 0 ≤ eigenvalue A k`; comparison of singular values at every index).
  The strict statement is bounded, as it must be:
  `A.PosDef ↔ ∀ k < Fintype.card n, 0 < eigenvalue A k`. The scan is textual; a statement that
  hides an index inside a definition would escape it. The explanation for users, with the
  example, is in the module docstring of `NLAlib/Matrix/Spectral/Eigenvalues.lean`; the rule
  for contributors is in `CONTRIBUTING.md` §5.2.

## 2. Singular values

- **Mathlib.** `LinearMap.singularValues T : ℕ →₀ ℝ` for a linear map between finite-dimensional
  inner product spaces: `ℕ`-indexed, zero-padded.
- **NLAlib.** `singularValues A : ℕ → ℝ` for a matrix: Mathlib's definition applied to
  `x ↦ A *ᵥ x` between Euclidean spaces, coerced to a function. `singularValuesFinsupp A` keeps
  the finitely supported form for symmetric gauges.
- **Why.** Statements are about matrices, and Mathlib has no matrix-level name. The indexing is
  Mathlib's own.
- **Cost.** One unfolding to reach Mathlib's API. **Status: low risk.**

## 3. Matrix norms are named functions

- **Mathlib.** `‖A‖`, with the norm chosen by a scoped instance: `Matrix.Norms.L2Operator`,
  `Matrix.Norms.Frobenius`, `Matrix.Norms.Elementwise`, and others. With no scope open there is
  no norm on matrices.
- **NLAlib.** `specNorm A`, `frobNorm A` (and `nuclearNorm`, `schattenNorm q`, `kyFanNorm k`,
  `Φ.matrixNorm`, which Mathlib does not have). `‖A‖` does not appear in statements.
- **Bridge.** `specNorm_eq_norm`, `frobNorm_eq_norm`, each under its scope.
- **Why.** A statement with `‖A‖` means different things depending on which scope is open where
  it is read, and one statement often needs two norms at once. `specNorm` also needs no
  `DecidableEq`, which Mathlib's instance does.
- **Cost.** Mathlib's normed-space lemmas apply only after the bridge, inside a proof, with the
  scope opened locally. **Status: in the contract from the start (§5.1).**

## 4. Orthonormal columns and unitaries

- **Mathlib.** `U ∈ Matrix.unitaryGroup n 𝕜` for square matrices; `Orthonormal 𝕜 v` for a family
  of vectors in an inner product space.
- **NLAlib.** `HasOrthonormalCols Q := Qᴴ * Q = 1` for any shape. A unitary is a square `Q` with
  this property.
- **Bridge.** `hasOrthonormalCols_iff_orthonormal`, `hasOrthonormalCols_iff_mem_unitaryGroup`.
- **Why.** Most orthonormal factors in numerical linear algebra are rectangular (thin QR, SVD
  factors, Krylov bases, range finders); the unitary group cannot express them, and bundled
  group elements need coercions in every product.
- **Cost.** Mathlib's group structure on unitaries is one bridge away. **Status: in the contract
  from the start (§5.3).**

## 5. Vectors and column spaces

- **Mathlib.** Euclidean geometry lives on `EuclideanSpace 𝕜 n`; `Matrix.mulVec` acts on plain
  functions `n → 𝕜`, which carry the sup norm.
- **NLAlib.** Vectors are `n → 𝕜`, the Euclidean norm is written `‖WithLp.toLp 2 x‖`, the column
  space is `LinearMap.range A.mulVecLin`, and the projector onto it is the matrix
  `rangeProjector A` rather than `Submodule.starProjection` of a submodule of Euclidean space.
- **Bridge.** `toEuclideanLin_rangeProjector`, `rayleighQuotient_eq_toEuclideanCLM`.
- **Why.** Statements stay in the type where `*ᵥ`, `⬝ᵥ` and matrix products live, with no
  transport between `n → 𝕜` and `EuclideanSpace 𝕜 n` in statements.
- **Cost.** The norm spelling is long. **Status: in the contract (§5.1, §5.3).**

## 6. The matrix logarithm

- **Mathlib.** `CFC.log A`, defined for a `NormedRing` with a `NormedAlgebra ℝ` structure.
- **NLAlib.** `cfc Real.log A`, which is what `CFC.log` unfolds to.
- **Why.** Matrices have no global normed ring structure (entry 3), so `CFC.log` does not
  elaborate without opening a norm scope in the statement.
- **Cost.** Mathlib lemmas named `CFC.log_*` need the scope opened locally and a `rfl`.
  **Status: forced by Mathlib's instances; revisit if Mathlib relaxes the hypothesis.**

## 7. Spectral radius

- **Mathlib.** `spectralRadius 𝕜 a : ℝ≥0∞`, for an element of a normed algebra.
- **NLAlib.** `specRadius A : ℝ := (spectralRadius ℂ (complexify A)).toReal`, for a matrix over
  `𝕜`.
- **Bridge.** `specRadius_eq_toReal_spectralRadius`.
- **Why.** It is always finite for a matrix, and a real value works with `positivity`, `gcongr`
  and comparison with `specNorm`. Going through `ℂ` makes it the modulus of the largest complex
  eigenvalue also for a real matrix, whose real spectrum may be empty.
- **Cost.** A second name next to Mathlib's. **Status: open (`Matrix-Structured.md` §7.3).**

## 8. Eigenvalues of a general matrix

- **Mathlib.** `spectrum 𝕜 A` (a set), `A.charpoly.roots` (a multiset), `Polynomial.Splits`.
- **NLAlib.** `IsEigenvalueListing A d`: `A.charpoly = ∏ i, (X - C (d i))` for a family `d`
  indexed by any finite type.
- **Bridge.** `IsEigenvalueListing.spectrum_eq_range`, `exists_isEigenvalueListing`,
  `Matrix.IsHermitian.isEigenvalueListing_eigenvalue`.
- **Why.** Theorems such as Schur's inequality, Hoffman–Wielandt or the eigenvalues of a
  Kronecker product speak of the eigenvalues with multiplicity in some order. A set loses
  multiplicity; a multiset has no indices to sum over or to match with a diagonal.
- **Cost.** A predicate with its own API. **Status: open (`Matrix-Structured.md` §7.1).**

## 9. Diagonalisability

- **Mathlib.** `Module.End.IsSemisimple` for endomorphisms; no matrix predicate.
- **NLAlib.** `IsDiagonalizable A`.
- **Bridge.** `isDiagonalizable_iff_isSemisimple` (algebraically closed field),
  `isDiagonalizable_iff_iSup_eigenspace_eq_top`.
- **Why.** Semisimple and diagonalisable differ over a field that is not algebraically closed.
- **Status: open (`Matrix-Structured.md` §7.4).**

## 10. Derivatives of matrix-valued curves

- **Mathlib.** `HasDerivAt` in a normed space, which for matrices needs a norm scope.
- **NLAlib.** Entrywise: `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t`.
- **Bridge.** `Matrix.hasDerivAt_iff_forall_apply`.
- **Why.** No norm scope in statements (entry 3). **Status: open (`Matrix-Functions.md` §7.6).**

## 11. Inertia

- **Mathlib.** Real quadratic forms are equivalent to a weighted sum of squares with weights in
  `{1, 0, -1}` (`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`).
- **NLAlib.** `inertiaPos A`, `inertiaNeg A`: the numbers of positive and negative eigenvalues of
  a Hermitian matrix over `𝕜`, with Sylvester's law proved for matrices.
- **Why.** Hermitian matrices over `𝕜`, and numbers that statements can compute with.
- **Status: open (`Matrix-Structured.md` §7.2).**

## 12. A measurable space on matrices

- **Mathlib.** None.
- **NLAlib.** `Matrix.instMeasurableSpace`, the product σ-algebra, as a global instance in
  `NLAlib/ForMathlib/MeasureTheory/Matrix.lean`.
- **Risk.** If Mathlib adds an instance later, the two may differ syntactically.
- **Why.** Mathlib has a global `TopologicalSpace (Matrix m n R)`
  (`Mathlib/Topology/Instances/Matrix.lean`); the product σ-algebra is the measurable-space
  counterpart, and it is the Borel σ-algebra of that topology for second-countable `R`
  (the Borel instance in the same file). Transporting to `m → n → R` at each use is what the
  prototype did and cost a lemma per statement.
- **Status: kept (maintainer, 2026-10-14; `docs/PORT_PROBABILITY.md` D8).** The Matrix layer does
  not import it; the statements that use it are in `NLAlib/Probability/Measurability/Matrix.lean`.
  If Mathlib adds an instance, this one is deleted in its favour.

## 13. Integrals of matrix-valued functions

- **Mathlib.** `∫ ω, X ω ∂μ`, `Integrable X μ` and `μ[X | m]` need a normed-group and
  `NormedSpace ℝ` instance on the codomain. On `Matrix m n 𝕜` Mathlib has only scoped ones
  (`Matrix.Norms.Frobenius`, `Matrix.Norms.Elementwise`, `Matrix.Norms.L2Operator`). Under the
  first two, `Integrable X μ` does not elaborate in the pinned Mathlib: the global matrix topology
  (`Mathlib/Topology/Instances/Matrix.lean`, defined with `inferInstanceAs`) is not reducibly the
  product topology those norms carry, so `ContinuousENorm` is not found. `L2Operator` is built
  with `replaceTopology` and works, but has `NormedSpace 𝕜` and no `NormedSpace ℝ`.
- **NLAlib.** Every file that integrates or conditions a matrix-valued function opens
  `open scoped Matrix.Norms.L2Operator` (one scope, library-wide; the one the Matrix layer already
  opens for its functional-calculus files). `NLAlib/ForMathlib` adds, under that scope,
  `NormedSpace ℝ (Matrix m n 𝕜)` on the existing `Module ℝ` (no new data; at `𝕜 = ℂ` it agrees
  with `NormedSpace.complexToReal` by `with_reducible_and_instances rfl`, checked), and the Matrix
  layer's `Matrix.instOrderClosedTopology` (scoped to `MatrixOrder`, over `𝕜`) makes Mathlib's
  `integral_mono_ae` apply to the Loewner order. Statements never mention the norm, only the integral, whose value
  does not depend on it; `NLAlib/Probability/MatrixIntegral.lean` proves the norm-free bridges
  (`(∫ X) i j = ∫ X · i j`, integrability iff entrywise, trace, conjugate transpose, products,
  Hermitian and positive semidefinite integrals).
- **Why.** Mathlib's integral, conditional-expectation and Jensen API applies as is; the
  alternative, entrywise integrals with their own API, would rebuild conditional expectation and
  Jensen. (Maintainer: D10, 2026-10-14; the scope amended from Frobenius to `L2Operator` on
  2026-10-14, `docs/design/Probability-P0.md` §7 Q1.)
- **Cost.** `[DecidableEq n]` on matrix-expectation statements (the `L2Operator` instance needs
  it). A user must open the scope to state a matrix expectation. If Mathlib makes the global
  topology reducibly the product one, Frobenius would work too; switching would change instance
  arguments only.
- **Rule.** For analysis on matrices (integrals, Mathlib's normed API), open only
  `Matrix.Norms.L2Operator` (`CONTRIBUTING.md` §5.1).
- **Bridges.** `Matrix.integral_apply`, `Matrix.integrable_iff` and the rest of
  `NLAlib/Probability/MatrixIntegral.lean`.

## Small spelling choices

- `principalMinor A s` for `(A.submatrix (↑) (↑)).det` with `s : Finset n`
  (`det_submatrix_eq_principalMinor`).
- `quadForm A x` for `star x ⬝ᵥ A *ᵥ x`; `hermitianPart A`
  (`hermitianPart_eq_selfAdjointPart`).
- `complexify A` for `A.map RCLike.toComplex`.

## Additions where Mathlib has nothing

`pinv` and `IsPinv`, `conditionNumber`, `IsLeastSquaresSolution`
(`isLeastSquaresSolution_iff_isMinOn` bridges to `IsMinOn`), `IsSVD` and `truncatedSVD`,
`Majorized`, `SymmetricGauge`, the Schatten, nuclear and Ky Fan norms, `OperatorConvexOn`, the
factorization predicates and `gaussState`, `polarFactor`, `principalAngle`, `tangentMatrix`.

## Used as Mathlib has them

`Matrix.IsHermitian`, `Matrix.PosSemidef`, `Matrix.PosDef` and the Loewner order,
`IsStarProjection`, `IsIdempotentElem`, `IsStarNormal`, `cfc`, `NormedSpace.exp`, `CFC.sqrt`,
`CFC.abs`, `A ^ r`, `Matrix.IsUpperTriangular`, `Matrix.kronecker`, `Matrix.circulant`,
`Matrix.IsHadamard`, `gramSchmidt`, `Metric.IsCover`, `ENNReal.HolderTriple`.
