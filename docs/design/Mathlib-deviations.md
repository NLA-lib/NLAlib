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
  matrix inline, and rewriting the matrix under that proof needs a congruence lemma. A function of the matrix alone rewrites with
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
- **Bridge.** `singularValues_eq_linearMap`
  (`singularValues A = ⇑(Matrix.toEuclideanLin A).singularValues`, by `rfl`),
  `singularValuesFinsupp_eq_linearMap`, `coe_singularValuesFinsupp`.
- **Why.** Statements are about matrices, and Mathlib has no matrix-level name. The indexing is
  Mathlib's own.
- **Cost.** One unfolding to reach Mathlib's API. The bridge needs `[DecidableEq n]` (for
  `Matrix.toEuclideanLin`), which the definition does not.
- **Status: not yet reviewed by the maintainer.** Judged low risk when made: the indexing and
  the zero padding are Mathlib's.

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
  scope opened locally.
- **Status: not yet reviewed by the maintainer.** In the contract from the start (§5.1). The
  maintainer's decision of 2026-10-14 that `Matrix.Norms.L2Operator` is the only scope opened for
  analysis (entry 13) concerns which scope a proof opens, not the named norms.

## 4. Orthonormal columns and unitaries

- **Mathlib.** `U ∈ Matrix.unitaryGroup n 𝕜` for square matrices; `Orthonormal 𝕜 v` for a family
  of vectors in an inner product space.
- **NLAlib.** `HasOrthonormalCols Q := Qᴴ * Q = 1` for any shape. A unitary is a square `Q` with
  this property.
- **Bridge.** `hasOrthonormalCols_iff_orthonormal`, `hasOrthonormalCols_iff_mem_unitaryGroup`.
- **Why.** Most orthonormal factors in numerical linear algebra are rectangular (thin QR, SVD
  factors, Krylov bases, range finders); the unitary group cannot express them, and bundled
  group elements need coercions in every product.
- **Cost.** Mathlib's group structure on unitaries is one bridge away.
- **Status: not yet reviewed by the maintainer.** In the contract from the start (§5.3).

## 5. Vectors and column spaces

- **Mathlib.** Euclidean geometry lives on `EuclideanSpace 𝕜 n`; `Matrix.mulVec` acts on plain
  functions `n → 𝕜`, which carry the sup norm.
- **NLAlib.** Vectors are `n → 𝕜`, the Euclidean norm is written `‖WithLp.toLp 2 x‖`, the column
  space is `LinearMap.range A.mulVecLin`, and the projector onto it is the matrix
  `rangeProjector A` rather than `Submodule.starProjection` of a submodule of Euclidean space.
- **Bridge.** `toEuclideanLin_rangeProjector`, `rayleighQuotient_eq_toEuclideanCLM`.
- **Why.** Statements stay in the type where `*ᵥ`, `⬝ᵥ` and matrix products live, with no
  transport between `n → 𝕜` and `EuclideanSpace 𝕜 n` in statements.
- **Cost.** The norm spelling is long.
- **Status: not yet reviewed by the maintainer.** In the contract (§5.1, §5.3).

## 6. The matrix logarithm

- **Mathlib.** `CFC.log A`, defined for a `NormedRing` with a `NormedAlgebra ℝ` structure.
- **NLAlib.** `cfc Real.log A`, which is what `CFC.log` unfolds to.
- **Bridge.** None as a lemma: `CFC.log A` is `cfc Real.log A` by Mathlib's definition, so under
  `open scoped Matrix.Norms.L2Operator` the two agree by `rfl`. `Matrix.PosDef.cfc_log_le_cfc_log`
  applies `CFC.log_le_log` this way, on complex matrices through `complexify`.
- **Why.** Matrices have no global normed ring structure (entry 3), so `CFC.log` does not
  elaborate without opening a norm scope in the statement.
- **Cost.** Mathlib lemmas named `CFC.log_*` need the scope opened locally and a `rfl`.
- **Status: not yet reviewed by the maintainer.** Forced by Mathlib's instances; revisit if
  Mathlib relaxes the hypothesis.

## 7. Spectral radius

- **Mathlib.** `spectralRadius 𝕜 a : ℝ≥0∞`, for an element of a normed algebra.
- **NLAlib.** `specRadius A : ℝ := (spectralRadius ℂ (complexify A)).toReal`, for a matrix over
  `𝕜`.
- **Bridge.** `specRadius_eq_toReal_spectralRadius`.
- **Why.** It is always finite for a matrix, and a real value works with `positivity`, `gcongr`
  and comparison with `specNorm`. Going through `ℂ` makes it the modulus of the largest complex
  eigenvalue also for a real matrix, whose real spectrum may be empty.
- **Cost.** A second name next to Mathlib's.
- **Status: not yet reviewed by the maintainer.** Open.

## 8. Eigenvalues of a general matrix

- **Mathlib.** `spectrum 𝕜 A` (a set), `A.charpoly.roots` (a multiset), `Polynomial.Splits`.
- **NLAlib.** `IsEigenvalueListing A d`: `A.charpoly = ∏ i, (X - C (d i))` for a family `d`
  indexed by any finite type.
- **Bridge.** `IsEigenvalueListing.spectrum_eq_range`, `exists_isEigenvalueListing`,
  `Matrix.IsHermitian.isEigenvalueListing_eigenvalue`.
- **Why.** Theorems such as Schur's inequality, Hoffman–Wielandt or the eigenvalues of a
  Kronecker product speak of the eigenvalues with multiplicity in some order. A set loses
  multiplicity; a multiset has no indices to sum over or to match with a diagonal.
- **Cost.** A predicate with its own API.
- **Status: not yet reviewed by the maintainer.** Open.

## 9. Diagonalisability

- **Mathlib.** `Module.End.IsSemisimple` for endomorphisms; no matrix predicate.
- **NLAlib.** `IsDiagonalizable A`.
- **Bridge.** `isDiagonalizable_iff_isSemisimple` (algebraically closed field),
  `isDiagonalizable_iff_iSup_eigenspace_eq_top`.
- **Why.** Semisimple and diagonalisable differ over a field that is not algebraically closed.
- **Cost.** A predicate with its own API. Mathlib's `Module.End.IsSemisimple` lemmas reach it
  only through `Matrix.toLin'` and the bridge, and over a field that is not algebraically closed
  (`ℝ`) only in one direction (`IsDiagonalizable.isSemisimple`). The predicate needs
  `[DecidableEq n]` (for `Matrix.diagonal`).
- **Status: open.**

## 10. Derivatives of matrix-valued curves

- **Mathlib.** `HasDerivAt A A' t`. In the pinned Mathlib, `HasDerivAt` asks only for a
  topological vector space (`[AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousSMul 𝕜 F]`, `Mathlib/Analysis/Calculus/Deriv/Basic.lean`), so it is stated for a
  matrix curve with Mathlib's global product topology and no norm scope; the bridge below is
  stated that way. The calculus rules are not: `HasDerivAt.mul`, `HasDerivAt.pow` and the
  inverse rules ask for `[NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]`, which matrices have only under a
  norm scope (`Matrix.Norms.L2Operator`, and only over an `RCLike` field).
- **NLAlib.** Entrywise: `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t`.
- **Bridge.** `Matrix.hasDerivAt_iff_forall_apply`.
- **Why.** Corrected 2026-10-20: this entry said that `HasDerivAt` on matrices needs a norm scope,
  which is false in the pinned Mathlib (above). What remains is the calculus rules: over a general
  `NormedCommRing` entry ring (the generality of
  `NLAlib/ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`) no norm scope supplies the
  `NormedRing` instance Mathlib's product, power and inverse rules need, and the entrywise proofs
  go through the scalar rules. That is a reason for the proofs, not for the statements: a
  statement with hypothesis `HasDerivAt A A' t` could be proved by the same entrywise argument
  through the bridge.
- **Cost.** Hypotheses are `∀ i j` families rather than one `HasDerivAt`, so Mathlib's calculus
  rules are not applied to the matrix curve: the product, power, trace, determinant and inverse
  rules are proved again entrywise (`Matrix.hasDerivAt_mul_apply`,
  `Matrix.hasDerivAt_pow_succ_apply`, `Matrix.hasDerivAt_det`, `Matrix.hasDerivAt_inv_apply`). A
  user holding a Mathlib `HasDerivAt A A' t` converts with the bridge.
- **Status: not yet reviewed by the maintainer.** Open. With the
  norm-scope reason withdrawn (2026-10-20), removing the deviation would cost: restating the six
  entrywise lemmas of `NLAlib/ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`
  (`Matrix.hasDerivAt_mul_apply`, `Matrix.hasDerivAt_trace`, `Matrix.hasDerivAt_pow_succ_apply`,
  `Matrix.hasDerivAt_trace_pow_succ`, `Matrix.hasDerivAt_det`, `Matrix.hasDerivAt_inv_apply`) and
  `Matrix.hasDerivAt_log_det` with `HasDerivAt A A' t` hypotheses and matrix conclusions, each
  proof prefixed by the bridge; no other library file uses them (checked 2026-10-20), and the
  matrix form is the one an upstream PR would want. Not done: a statement change awaiting the
  maintainer.

## 11. Inertia

- **Mathlib.** Real quadratic forms are equivalent to a weighted sum of squares with weights in
  `{1, 0, -1}` (`QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`).
- **NLAlib.** `inertiaPos A`, `inertiaNeg A`: the numbers of positive and negative eigenvalues of
  a Hermitian matrix over `𝕜`, with Sylvester's law proved for matrices.
- **Bridge.** None yet. It would say that, for a real symmetric `A`, the numbers of weights `1`
  and `-1` in Mathlib's weighted sum of squares equivalent to the quadratic form of `A` are
  `inertiaPos A` and `inertiaNeg A`. The nearest statements are `inertiaPos_diagonal`,
  `inertiaNeg_diagonal` and Sylvester's law `Matrix.IsHermitian.inertiaPos_conjTranspose_mul_mul`.
- **Why.** Hermitian matrices over `𝕜`, and numbers that statements can compute with.
- **Cost.** Sylvester's law is proved a second time, and Mathlib's quadratic-form API
  (equivalence of forms, the weighted-sum normal form) does not apply to the counts without the
  missing bridge. The counts are defined through `eigenvalue` and are `0` for a matrix that is
  not Hermitian, so statements carry `hA : A.IsHermitian` (entry 1).
- **Status: open.**

## 12. A measurable space on matrices

- **Mathlib.** None.
- **NLAlib.** `Matrix.instMeasurableSpace`, the product σ-algebra, as a global instance in
  `NLAlib/ForMathlib/MeasureTheory/Matrix.lean`.
- **Bridge.** To Mathlib's σ-algebra on `m → n → R`: the instance is `MeasurableSpace.pi` by
  definition; `Matrix.measurable_iff` (measurable exactly when every entry is) and
  `Matrix.instBorelSpace` (the Borel σ-algebra of Mathlib's global matrix topology, by
  `inferInstanceAs` from `m → n → R`).
- **Risk.** If Mathlib adds an instance later, the two may differ syntactically.
- **Why.** Mathlib has a global `TopologicalSpace (Matrix m n R)`
  (`Mathlib/Topology/Instances/Matrix.lean`); the product σ-algebra is the measurable-space
  counterpart, and it is the Borel σ-algebra of that topology for second-countable `R`
  (the Borel instance in the same file). Transporting to `m → n → R` at each use would
  cost a lemma per statement.
- **Cost.** A global instance on a Mathlib type, seen by every file that imports it: a project
  that puts another σ-algebra on matrices meets a conflict, and if Mathlib adds its own
  instance every statement about random matrices may have to switch to it (the risk above).
  Upstreamed statements need Mathlib to take the instance first.
- **Status: kept (maintainer, 2026-10-14).** The Matrix layer does
  not import it; the statements that use it are in `NLAlib/Probability/Measurability/Matrix.lean`.
  If Mathlib adds an instance, this one is deleted in its favour.
- **Companion instance (2026-10-14).** Mathlib also has no `SecondCountableTopology (Matrix m n R)`,
  so `MeasurableAdd₂` and `MeasurableMul₂` (which Mathlib derives from continuity under second
  countability) were not found for matrices under the global topology, and `Measurable.add`,
  `AEMeasurable.add` and `Measurable.mul` failed on matrix-valued functions unless a norm scope was
  opened. `Matrix.instSecondCountableTopology` (`NLAlib/ForMathlib/Topology/Instances/Matrix.lean`,
  countable index types, second countable entries, by `inferInstanceAs` from `m → n → R`) is the
  instance Mathlib would add; it is a `Prop`, so it cannot create a diamond. Deleted when Mathlib
  has it.

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
  does not depend on it; `NLAlib/ForMathlib/MeasureTheory/SpecificCodomains/Matrix.lean` proves
  the norm-free bridges (`(∫ X) i j = ∫ X · i j`, integrability iff entrywise, trace, conjugate
  transpose, products, Hermitian, positive semidefinite and positive definite integrals), and
  `NLAlib/ForMathlib/MeasureTheory/Function/ConditionalExpectation/Matrix.lean` their conditional
  forms; the bridges about NLAlib's objects (quadratic forms, the functional calculus, the
  dilation, positive definite conditional expectations) are in
  `NLAlib/Probability/MatrixIntegral.lean` and
  `NLAlib/Probability/MatrixConditionalExpectation.lean`.
- **Why.** Mathlib's integral, conditional-expectation and Jensen API applies as is; the
  alternative, entrywise integrals with their own API, would rebuild conditional expectation and
  Jensen. (Maintainer: D10, 2026-10-14; the scope amended from Frobenius to `L2Operator` on
  2026-10-14.)
- **Cost.** `[DecidableEq n]` on matrix-expectation statements (the `L2Operator` instance needs
  it). A user must open the scope to state a matrix expectation. If Mathlib makes the global
  topology reducibly the product one, Frobenius would work too; switching would change instance
  arguments only.
- **Status: decided (maintainer, 2026-10-14; the scope
  amended from Frobenius to `L2Operator`).**
- **Rule.** For analysis on matrices (integrals, Mathlib's normed API), open only
  `Matrix.Norms.L2Operator` (`CONTRIBUTING.md` §5.1).
- **Bridges.** `Matrix.integral_apply`, `Matrix.integrable_iff` and the rest of
  `NLAlib/ForMathlib/MeasureTheory/SpecificCodomains/Matrix.lean`.

## 14. Unitarily invariant laws of random matrices

- **Mathlib.** `Measure.IsMulLeftInvariant` and `Measure.IsMulRightInvariant` for a measure on a
  group, and `SMulInvariantMeasure G α μ` for a measure on a space with a `MulAction G α`. For
  `G = Matrix.unitaryGroup n 𝕜` acting on `Matrix n k 𝕜` this needs a global `MulAction` of the
  unitary group on rectangular matrices, which Mathlib does not have.
- **NLAlib.** Two classes on a measure `ν : Measure (Matrix n k 𝕜)`, over `𝕜`:
  `IsLeftUnitarilyInvariant ν` (`∀ U : Matrix n n 𝕜, HasOrthonormalCols U → ν.map (U * ·) = ν`)
  and `IsRightUnitarilyInvariant ν` (`… ν.map (· * V) = ν`), in
  `NLAlib/RandomMatrix/UnitaryInvariance.lean`. Instances: `gaussianMatrix`, `haarFrame`.
- **Bridge.** `isLeftUnitarilyInvariant_iff : IsLeftUnitarilyInvariant ν ↔
  ∀ U : Matrix.unitaryGroup n 𝕜, ν.map ((U : Matrix n n 𝕜) * ·) = ν`, by
  `hasOrthonormalCols_iff_mem_unitaryGroup` (entry 4); `isRightUnitarilyInvariant_iff` likewise.
- **Why.** Consumers hold unitaries as `Matrix` values with `HasOrthonormalCols` (entry 4), as
  every theorem of the Matrix layer states them; a bundled group element would need a coercion in
  every product. Adding the `MulAction` instance would put a global instance on Mathlib types that
  Mathlib has not chosen (`CONTRIBUTING.md` §7). A `class`, as Mathlib's invariance notions are, so
  the instances on the concrete laws are found by typeclass search.
- **Cost.** A user who has `SMulInvariantMeasure` or a bundled unitary goes through the bridge.
  If Mathlib adds the action, the classes could become abbreviations of `SMulInvariantMeasure`;
  the field statements would not change.
- **Status: open.** Decision (classes over `𝕜`, left and right separately), 2026-10-14.

## 15. Haar measure on the orthogonal group, as a law on matrices

- **Mathlib.** `Measure.haarMeasure K₀` on a locally compact group, normalised by a compact set
  `K₀`; for the compact group `Matrix.orthogonalGroup n ℝ`, `haarMeasure ⊤` is the probability
  Haar measure, a measure on the bundled subtype. Mathlib has no `CompactSpace` instance for
  `Matrix.unitaryGroup n 𝕜` and no Haar law on rectangular frames.
- **NLAlib.** `haarFrame n k : Measure (Matrix n k ℝ) := (gaussianMatrix n k).map polarFactor`,
  the law of a Haar frame of any shape, as a measure on matrices
  (`NLAlib/RandomMatrix/Haar/Basic.lean`). The square case `haarFrame n n` is the library's Haar
  measure on the orthogonal group.
- **Bridge.** `haarFrame_eq_map_haarMeasure : haarFrame n n =
  (Measure.haarMeasure ⊤ : Measure (Matrix.orthogonalGroup n ℝ)).map Subtype.val`
  (`NLAlib/RandomMatrix/Haar/Uniqueness.lean`), a corollary of the characterization
  `hasLaw_haarFrame_of_isLeftUnitarilyInvariant`. It uses the instance
  `Matrix.compactSpace_unitaryGroup` (`NLAlib/ForMathlib/LinearAlgebra/UnitaryGroup.lean`, an
  upstream candidate).
- **Why.** Rectangular frames (range finders and Haar sketches use `n × k` frames, which no group
  measure describes), `Matrix` values rather than subtype elements (entry 4), and one definition
  for every shape (the polar factor of a Gaussian). The
  characterization is proved against `haarFrame n n` itself, so it needs neither Haar uniqueness
  nor compactness; those enter only through the bridge.
- **Cost.** A user with Mathlib's Haar measure on `O(n)` rewrites with the bridge; group-level
  facts (`IsHaarMeasure`, uniqueness up to scaling) are reached only through it.
- **Status: bridge proved** (`haarFrame_eq_map_haarMeasure`,
  `RandomMatrix/Haar/Uniqueness.lean`), 2026-10-14.

## 16. The uniform law on the sphere

- **Mathlib.** `Measure.toSphere`: the surface measure on `Metric.sphere (0 : E) 1`, a subtype, not
  normalised.
- **NLAlib.** `uniformSphereVector n : Measure (n → ℝ)`, the probability law of `g / ‖g‖` for a
  standard Gaussian vector `g` (`NLAlib/RandomMatrix/Haar/Basic.lean`), on the library's vectors
  `n → ℝ` (docs/contributing/statements.md §1) and with the Gaussian construction the Haar frames use.
- **Why.** Consumers (JL, the column law of a Haar frame) hold vectors in `n → ℝ` and a probability
  measure; the subtype carrier and the normalisation would be re-done at every use.
- **Cost.** A user with Mathlib's `Measure.toSphere` rewrites with the bridge, which needs
  `[Nonempty n]`: for empty `n` the two laws differ. The law lives on all of `n → ℝ`, so that a
  sample has norm `1` is an almost-sure fact, not part of its type, and the library states it
  only as a private lemma.
- **Bridge (planned).** `uniformSphereVector n` is the normalisation of `Measure.toSphere` on
  `EuclideanSpace ℝ n`, pushed forward by `WithLp.ofLp ∘ Subtype.val`.
- **Status: bridge proved** (`uniformSphereVector_eq_map_toSphere`, `RandomMatrix/Haar/Uniqueness.lean`; needs `[Nonempty n]`: for empty `n` the sphere is empty while `uniformSphereVector n` is a point mass).

## 17. Conditional moment generating function bounds

- **Mathlib.** `HasCondSubgaussianMGF m hm X c μ :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)`: a bound on the moment
  generating function of `X` under the conditional expectation kernel, for every `t` on one
  almost-sure set. The kernel needs `[StandardBorelSpace Ω]` (and `[IsFiniteMeasure μ]`). The
  form consumers use is `HasCondSubgaussianMGF.ae_condExp_le`:
  `∀ t, ∀ᵐ ω ∂μ, μ[fun ω => exp (t * X ω) | m] ω ≤ exp (c * t ^ 2 / 2)`.
- **NLAlib.** `HasCondMatrixMGFBound m X g A s μ`, the conditional matrix MGF bound
  (`NLAlib/Probability/MatrixConcentration/ConditionalMGFBound.lean`), spelled with Mathlib's
  conditional expectation: `∀ θ ∈ s, μ[fun ω => exp (θ • X ω) | m] ≤ᵐ[μ] fun ω =>
  exp (g θ • A ω)` in the Loewner order, with an `m`-measurable, almost surely Hermitian bound
  `A`, the integrability of `exp (θ • X)` and `X` almost surely Hermitian as fields. The
  quantifier over `θ` is outside the almost-everywhere statement; no Borel hypothesis. It takes
  no proof of `m ≤ mΩ`, so it no longer mirrors the argument list of
  `HasCondSubgaussianMGF m hm` (maintainer decision 2026-10-20): Mathlib needs `hm` there for
  `μ.trim hm` to typecheck, while `μ[· | m]` is defined for every `m`. No field uses the
  inclusion, so as a parameter it was unused, and every Freedman statement carried the proof
  term `ℱ.le j` (rule T9). The constructors and lemmas that use it take it as a hypothesis
  (`hasCondMatrixMGFBound_of_condExp_eq_zero_of_le`, `condExp_re_trace_exp_add_le`); Freedman's
  statements get it from the filtration.
- **Bridge.** `hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF [StandardBorelSpace Ω]
  [IsFiniteMeasure μ] (hγ : HasCondSubgaussianMGF m hm γ c μ) (hB : B.IsHermitian) :
  HasCondMatrixMGFBound m (fun ω => γ ω • B) (fun θ => θ ^ 2 / 2)
  (fun _ => (c : ℝ) • B ^ 2) Set.univ μ`, in the same file, through
  `HasCondSubgaussianMGF.ae_condExp_le` on the spectral decomposition of `B`. It is the only
  statement of the conditional interface that needs `[StandardBorelSpace Ω]`.
- **Why.** The trace supermartingale and Freedman's inequality
  (`NLAlib/Probability/MatrixConcentration/Freedman.lean`) use one `θ` at a time, so the
  per-`θ` almost-sure form is what the proofs consume; it is the form Mathlib's own API exposes
  (`ae_condExp_le`). The kernel form would put `[StandardBorelSpace Ω]` on every Freedman
  statement, and it would not shorten the one hard proof, conditional Lieb for an
  `m`-measurable `H`: `condExpKernel_ae_eq_condExp` holds per measurable set, so `H` is constant
  under the kernel only through the same approximation by countably valued `m`-measurable
  matrices.
- **Cost.** A user holding `HasCondSubgaussianMGF` goes through the bridge, and needs a standard
  Borel space there. Kernel-level facts (the conditional law as a measure) are not available
  from `HasCondMatrixMGFBound`; no consumer uses them.
- **Status: bridge proved** (`hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF`), 2026-10-14.
  Conditional Lieb for an `m`-measurable `H` was proved through a dense sequence of fixed
  Hermitian offsets and the perturbation bound `tr exp A ≤ e^{‖A - B‖} tr exp B`, not through an
  approximation of `H`; the kernel would not have shortened that either.
  Amended 2026-10-20 (maintainer decision): the unused parameter `hm : m ≤ mΩ` was dropped
  (`docs/renames/2026-10-rules.json`, `statementChanged`).

## 18. Bounded orthonormal transforms

- **Mathlib.** `Matrix.IsHadamard H`: a square matrix over a `*`-semiring with unitary entries and
  `H * Hᴴ = Hᴴ * H = card n • 1`, the unnormalised Hadamard matrix (`±1` over `ℝ`, unimodular
  over `ℂ`).
- **NLAlib.** `IsBoundedOrthonormal F β` (`NLAlib/Matrix/Structured/BoundedOrthonormal.lean`): a
  unitary `F` (`HasOrthonormalCols F`) whose entries satisfy `card n * ‖F i j‖ ^ 2 ≤ β`, the
  hypothesis of every SRHT statement.
- **Why.** Generality, not convenience. The hypothesis is strictly weaker than `IsHadamard` on
  `√(card n) • F`: an inequality on the entries admits the discrete cosine and Hartley transforms
  (`β = 2`), which are not Hadamard and which Martinsson and Tropp list as SRTT transforms (the
  Hartley transform is their recommended real choice, after Avron et al.). The flattening proof
  uses only unitarity and the entry bound (Camaño, Epperly, Meyer and Tropp's remark after their
  Imported Theorem 4.3), and `β` enters every bound linearly.
- **Bridge.** `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul : H.IsHadamard →
  IsBoundedOrthonormal (((√(card n))⁻¹ : ℝ) • H) 1`, in the same file.
- **Cost.** A user holding `IsHadamard` applies the bridge once; nothing else changes.
- **Status: bridge proved**, with the Walsh and Fourier instances
  (`isBoundedOrthonormal_smul_walshHadamard`, `isBoundedOrthonormal_fourierMatrix`), 2026-10-15
 .

## 19. Oblique projectors from a basis and a sketch

- **Mathlib.** `Submodule.projection p q h` (an endomorphism) and `Submodule.linearProjOfIsCompl`
  (a map into `p` through an injection), in `LinearAlgebra/Projection.lean`, project onto `p`
  along a complement `q` and take a proof `h : IsCompl p q`; `LinearMap.IsProj p f` is the
  predicate. The idempotent predicate `IsIdempotentElem` is used as Mathlib has it.
- **NLAlib.** `obliqueProjector X S := X * pinv (S * X) * S`
  (`NLAlib/Matrix/Subspaces/ObliqueProjector.lean`), a total matrix-valued function of a basis
  `X : Matrix m r 𝕜` and a sketch `S : Matrix k m 𝕜` with no proof argument. It is always
  idempotent; under `(S * X).rank = X.rank` it projects onto `range X` along
  `{v | S *ᵥ v ⟂ range (S * X)}`.
- **Why.** Generality, not convenience. (1) Every rank and shape: through `pinv` the formula is
  defined and idempotent for every `X` and `S`, it projects onto `range X` exactly under the
  rank hypothesis, and onto the smaller range of `X * (S * X)ᴴ` otherwise; Mathlib's projection
  exists only after an `IsCompl` proof. The probabilistic results need the total form: they
  integrate `obliqueProjector X (Ψ ω)ᴴ` over every `ω`, including the null set where the rank
  hypothesis fails, and `measurable_pinv` makes it a random matrix, which a proof-carrying
  projection is not without a junk branch. (2) It is the matrix the algorithms compute:
  generalized Nyström, sketch-and-solve and the formulas of Tropp, Yurtsever, Udell and
  Cevher, Epperly and Webber, and Camaño, Epperly, Meyer and Tropp are literally
  $\mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$, and `generalizedNystrom_def` and
  `sketchAndSolve` unfold to them with no transport. (3) The complement is not a datum the user
  has: when `S` has more rows than `rank X` the kernel is the preimage under `S` of the
  orthogonal complement of `range (S * X)`, which is `ker S` only when
  `range (S * X) = range S`. Mathlib's form would require constructing that subspace and proving
  complementarity at every use, and it hides the sketch, which is the variable of every theorem
  (the injection hypothesis, the law of `S`).
- **Bridge.** To the predicate: `isIdempotentElem_obliqueProjector` and
  `IsIdempotentElem.obliqueProjector_eq` (every idempotent is one). To Mathlib's projections:
  not stated, added on demand in the same file; it would
  read `LinearMap.IsProj (LinearMap.range X.mulVecLin) (obliqueProjector X S).mulVecLin` under
  the rank hypothesis, a corollary of `range_obliqueProjector` and
  `obliqueProjector_mul_eq_self_of_range_le`.
- **Cost.** A user holding `Submodule.projection` writes the bridge first. The §5.3 two-bases
  spelling `X * (Yᴴ * X)⁻¹ * Yᴴ` becomes a lemma (`obliqueProjector_of_isUnit`), and six
  `Oblique.lean` lemmas are deprecated for one release.
- **Status: proposed**, 2026-10-15; not
  approved by the maintainer.

## 20. Binary rounding with gradual underflow and a finite exponent range

- **Mathlib.** `Real.floatGrid` and `Real.roundNearest` use an unbounded exponent range.
  Lean core supplies `Float.Model.Format`, unpacked words and logical rounding/packing
  operations. Searched the pinned Mathlib and NLAlib: no real-valued bridge with a lower
  exponent clamp and no certified finite-format scalar arithmetic contract was found.
- **NLAlib.** The upstream candidates `Float.Model.BinaryRounding.IsBinaryFloat` and
  `Float.Model.BinaryRounding.IsNearestFloat` express the lower-clamped grid and nearest
  rounding. `Float.Model.UnpackedFloat.toReal`, `Float.Model.UnpackedFloat.IsFinite`,
  `Float.Model.UnpackedFloat.IsCanonical` and `Float.Model.UnpackedFloat.Sign.toReal`
  connect the existing core words to real arithmetic. The proof-level predicates
  `Float.Model.UnpackedFloat.ExtendedMantissa.Approximates` and `Float.Model.UnpackedFloat.FitsExponentRange`
  express the core extended mantissa's real interval and the packer's finite exponent domain.
  Format parameters use the shared
  core namespace: `Float.Model.Format.unitRoundoff`, `Float.Model.Format.underflowBound`,
  `Float.Model.Format.maxExponentBound` and `Float.Model.Format.maxFinite`.
- **Bridge.** `Float.Model.BinaryRounding.IsBinaryFloat.mem_floatGrid` embeds the lower-clamped
  grid in Mathlib's grid. `Float.Model.UnpackedFloat.isBinaryFloat_toReal` connects canonical
  words to that grid. `Computation.isBinaryRep_floatDecode` records the full bounded
  representation. `Ops.Float64.mixedModel_machine` supplies guarded mixed-error accuracy
  for native finite-word arithmetic; its rational literal policy uses the separately specified
  logical quantizer, and overflow has an explicit finite fallback.
- **Why.** A pure relative-error model cannot account for a nonzero subnormal result
  rounding to zero. Finite exponent limits specify where the total word operations meet their accuracy contract.
  Total program certificates additionally prove every required operation admission.
- **Cost.** Additional upstream-candidate real decoding and lower-grid facts; they use the
  existing core layout and operations. The mathematical bounded selector model is separate
  from native Float's ties-to-even semantics. No second bit layout, private dependency or
  toolchain change is introduced. Native runtime and machine-cost certification remain open.
- **Status.** Implemented locally, 2026-11-05. Adapted proof provenance and redistribution
  status are recorded in [Finite-Precision-Arithmetic.md](Finite-Precision-Arithmetic.md).

## 21. Frobenius Hilbert space of Hermitian matrices

- **Mathlib.** The real submodule `selfAdjoint.submodule ℝ (Matrix n n 𝕜)` carries its ambient
  matrix norm. Mathlib also supplies scoped matrix norms. The spectral norm is needed for
  differentiation of the matrix algebra, while the K-transform contraction is measured on
  Hermitian directions in the Frobenius norm.
- **NLAlib.** `hermitianFrobenius 𝕜 n` equips the same real vector space with `frobInner`
  and `frobNorm`. The core `hermitianFrobeniusCore` determines the norm and inner product.
- **Bridge.** `hermitianFrobeniusEquiv` identifies the underlying real vector spaces.
  `hermitianFrobeniusMatrix` realizes a vector as a matrix, `hermitianFrobeniusMatrixLinear`
  bundles that map, and `toHermitianFrobenius` takes a Hermitian matrix back.
  `inner_eq_frobInner` and `norm_eq_frobNorm` identify the Hilbert operations
  with the matrix Frobenius pairing and norm.
- **Why.** Both norms occur in the same K-transform theorem. Choosing the carrier fixes the
  induced operator norm appearing in the contraction criterion.
- **Cost.** Statements moving between the ambient derivative and the Hermitian stability
  operator use the realization map. The positive-cone results work over both scalar fields.
- **Status.** Proposed in the matrix K-transform port.

## Small spelling choices

- `principalMinor A s` for `(A.submatrix (↑) (↑)).det` with `s : Finset n`
  (`det_submatrix_eq_principalMinor`).
- `quadForm A x` for `star x ⬝ᵥ A *ᵥ x`; `hermitianPart A`
  (`hermitianPart_eq_selfAdjointPart`).
- `complexify A` for `A.map RCLike.toComplex`.
- `gaussianVector n` for `Measure.pi fun _ : n => gaussianReal 0 1`, an `abbrev` (so Mathlib's
  `Measure.pi` and `gaussianReal` lemmas apply by `rfl`), where Mathlib names the standard
  Gaussian `stdGaussian (EuclideanSpace ℝ n)`: the law lives on the library's vectors `n → ℝ`
  (entry 5). Bridge: Mathlib's `map_pi_eq_stdGaussian` (the image under `WithLp.toLp 2` is
  `stdGaussian`), through which `gaussianVector n` gets its `IsGaussian` instance.

## Additions where Mathlib has nothing

`pinv` and `IsPinv`, `pseudoConditionNumber`, `IsLeastSquaresSolution`
(`isLeastSquaresSolution_iff_isMinOn` bridges to `IsMinOn`), `IsSVD` and `truncatedSVD`,
`Majorized`, `SymmetricGauge`, the Schatten, nuclear and Ky Fan norms, `OperatorConvexOn`, the
factorization predicates and `gaussState`, `polarFactor`, `principalAngle`, `tangentMatrix`.
`obliqueProjector` (entry 19), `sketchAndSolve`, `rsvd`, `generalizedNystrom`, `nystrom`. `IsBestRankApprox`
(`isBestRankApprox_iff_isMinOn` bridges to `IsMinOn`).
`earlyTruncatedRSVD`, `earlyTruncatedGeneralizedNystrom`, `IsProjectionCostPreserving`. `svdU` and `svdV`, the chosen thin SVD from which
`truncatedSVD` is now built.
`HasProjectionCostPreserving`, the tail form of `IsProjectionCostPreserving`. `girardHutchinson` (trace estimation).

(2026-10-16) `Metric.IsUniformApproxOn` adds a fixed-error predicate absent from the
pinned Mathlib; it uses Mathlib's `dist` directly and its compact continuous-map bridge is
`ContinuousMap.dist_le`. `chebyshevResidual` is an affine composition and scalar normalization
of Mathlib's `Polynomial.Chebyshev.T`, not another Chebyshev family. These are additions with
no competing Mathlib spelling, so no numbered deviation is introduced.

(2026-10-16) `chebyshevCoeff` and `chebyshevTrunc` add the canonical full coefficient
and finite inclusive truncation absent from pinned Mathlib. They reuse Mathlib's Chebyshev T,
cosine substitution, orthogonality and polynomial sequence span machinery. The coefficient is
one RCLike cosine-integral spelling; later contour/Fourier representations must be bridges,
not competing objects. No numbered deviation is introduced.

(2026-10-16) `openBernsteinEllipse` adds a focal-distance sublevel set absent from
pinned Mathlib. Openness uses continuity of the focal-distance sum; Joukowski annulus membership
is a bridge, not a claim that the two sets agree for every parameter. Analytic
hypotheses use existing `DifferentiableOn`, `Set.EqOn` and `Metric.IsUniformApproxOn`; coefficients
and truncation retain their spelling. No numbered deviation is introduced.

Krylov (2026-10-17): `krylovMatrix` and `krylovSpace`, the Krylov
space as the column space of the Krylov matrix. Mathlib's nearest notion is the cyclic submodule
`Submodule.span R[X] {AEval'.of φ b}` in the type synonym `Module.AEval'`, which cannot be stated
about vectors `n → 𝕜` without transport; the column space plugs the space into `rangeProjector`,
`rank`, `pinv` and `gramSchmidtQ`, and `mem_krylovSpace_iff` is the polynomial description.
`krylovGrade`, the grade, is the rank of the Krylov matrix with `Fintype.card n` columns, the
dimension of that cyclic submodule; a bridge to Mathlib's `minpoly` (the grade is at most the
degree of the minimal polynomial) is planned for when a result needs it. `galerkinInverse` and
`cgIterate` (the Galerkin approximation and the CG iterate, with `IsMinOn` as the bridge for
optimality), `IsGradedKrylovBasis` and `arnoldiMatrix` (on Mathlib's `gramSchmidtNormed` through
`gramSchmidtQ`), and the recurrences `lanczosState` and `cgState` are additions with no Mathlib
counterpart. No numbered deviation is introduced.

Best polynomial approximation (2026-10-25): `minimaxError f s n`,
the best uniform error on a raw `f : ℝ → ℝ` and `s : Set ℝ`, defined as the infimum of the
errors of `Metric.IsUniformApproxOn` for degree-`n` polynomials (junk `0` where the true value
is $+\infty$ and for `s = ∅`), the chosen best approximation `minimaxPoly f s n` (junk `0` when
none exists; canonical on an interval), and the predicate `AlternatesOn`. Mathlib's nearest notion is
`Metric.infDist` in `C(s, ℝ)` to the image of `Polynomial.degreeLE ℝ n` under
`Polynomial.toContinuousMapOnAlgHom s`; the bridge is `minimaxError_eq_infDist`. The pointwise
form is what the Krylov and SLQ consumers hold. No numbered deviation is introduced.

Lower bounds (2026-10-25): `QueryAlgorithm`,
a deterministic adaptive query algorithm as transcript functions (`query i` of the first `i`
responses, `output` of all `q`), with `history`, `transcript`, `run`, `queries`, `queryMatrix`,
`IsNonAdaptive`, `IsMeasurable`, `IsMeasurableFamily` (randomized algorithms as seeded families)
and `gramSimulation`; Mathlib's nearest notions are Markov kernels with `Kernel.traj` and the
decision-theory risks `bayesRisk`, `minimaxRisk` (`Mathlib/Probability/Decision`), which state
randomized procedures as kernels; a bridge (an algorithm and a seed law give a kernel from inputs
to outputs) is deferred until a consumer states a result in that API. `QueryAlgorithm.resample`
(the matrix with its unqueried block replaced) has no counterpart. `InformationTheory.tvDist`,
the total variation distance of two measures as a real supremum over measurable sets, is an
addition next to Mathlib's `InformationTheory.klDiv`; Mathlib's
`MeasureTheory.SignedMeasure.totalVariation` is the variation measure of one signed measure, and
a bridge (for probability measures `tvDist μ ν` is half the total mass of the variation of
`μ - ν` as a signed measure) is deferred. No numbered deviation is introduced.

## Used as Mathlib has them

`Matrix.IsHermitian`, `Matrix.PosSemidef`, `Matrix.PosDef` and the Loewner order,
`IsStarProjection`, `IsIdempotentElem`, `IsStarNormal`, `cfc`, `NormedSpace.exp`, `CFC.sqrt`,
`CFC.abs`, `A ^ r`, `Matrix.IsUpperTriangular`, `Matrix.kronecker`, `Matrix.circulant`,
`Matrix.IsHadamard`, `gramSchmidt`, `Metric.IsCover`, `ENNReal.HolderTriple`.
