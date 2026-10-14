# Design note: Matrix stage M10, structured matrices and the remaining spectral theory

Status: written 2026-10-14 by the orchestrator while M7 was being proved, reviewed by a Fable
agent the same day (§8); to be implemented without a maintainer approval stop, by the standing instruction in `docs/port/status.md`. Choices
a maintainer would have been asked about are in §7. The skeleton (eighteen files) elaborates
against the pinned Mathlib and the earlier stages.

## 0. Scope

Kronecker products; circulant matrices and the discrete Fourier transform; Walsh–Hadamard
matrices; Cauchy and Hilbert matrices. Schur triangularisation and Schur's inequality; normal
matrices (spectral theorem, Fuglede–Putnam, unitary similarity, Hoffman–Wielandt); simultaneous
triangularisation and diagonalisation; diagonalisable matrices, eigenvector pairings and the
Sylvester equation; the real Schur form and descent from `ℂ` to `ℝ`; inertia (Sylvester's law,
Haynsworth, Ostrowski, counting eigenvalues by pivots); Sylvester's criterion and principal
minors against the characteristic polynomial; simultaneous diagonalisation by congruence and the
QZ decomposition; Gershgorin discs and diagonal dominance; the spectral radius and powers of a
matrix; rank-one updates, bordered matrices and the converses of interlacing; the Hermitian part;
measurability of the spectral quantities.

Owed to this stage by earlier ones, and paid here: Hoffman–Wielandt for normal matrices (M3a);
the inertia form of low-rank interlacing and strict variational bounds (M3); the characteristic
polynomial of a rank-one update and eigenvalues determined by the characteristic polynomial
(M3); majorization of real parts by the Hermitian part (M7); Kronecker norm facts (M2);
measurability (M5, M6, M9).

Not here: Jordan and Weyr forms, the minimal polynomial beyond what Mathlib has; nonnegative
matrices and Perron–Frobenius (Mathlib's `Matrix.IsIrreducible` is used only for Taussky's
theorem); Toeplitz and Hankel matrices (the prototype has definitions and one bridge lemma);
functions of non-normal matrices; pseudospectra.

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| eigenvalues of a general matrix | `IsEigenvalueListing A d` (new): `A.charpoly = ∏ i, (X - C (d i))`, `d : ι → K` | `Matrix.IsUpperTriangular.isEigenvalueListing_diag` |
| sorted eigenvalues of a Hermitian matrix | `eigenvalue A k` (M3) | `Matrix.IsHermitian.isEigenvalueListing_eigenvalue` (new) |
| normal matrix | Mathlib's `IsStarNormal A` | — |
| unitary matrix | `HasOrthonormalCols U`, `U` square (as before) | `HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` |
| upper triangular in a chosen order | `Matrix.IsUpperTriangular` on `[LinearOrder n]` | — |
| diagonalisable | `IsDiagonalizable A` (new): `A * V = V * diagonal d`, `IsUnit V.det` | `Module.End.IsSemisimple` over an algebraically closed field |
| quasi-triangular, real Schur form | `IsUpperQuasiTriangular T`, `IsRealSchurForm T`, `Fin`-indexed (new) | — |
| inertia | `inertiaPos A`, `inertiaNeg A` (new): counts of positive and negative `eigenvalue A i` | — |
| leading principal minor | `principalMinor A (Finset.Iic i)` (as in M9) | — |
| generalized eigenvalues of a definite pair | the diagonal `d` in `A = S Sᴴ`, `B = S diag(d) Sᴴ`; `spectrum ℝ (A⁻¹ * B)` (as in M7) | — |
| Gershgorin radius | `gershgorinRadius A i` (new); columns are `gershgorinRadius Aᵀ j` | `gershgorinRadius_def` (Mathlib's spelling) |
| spectral radius | `specRadius A : ℝ` (new) `= (spectralRadius ℂ (complexify A)).toReal` | — |
| Hermitian part | `hermitianPart A` (new) `= (2⁻¹ : ℝ) • (A + Aᴴ)` | `hermitianPart_eq_selfAdjointPart` |
| Kronecker product | Mathlib's `A ⊗ₖ B` | — |
| circulant matrix | Mathlib's `Matrix.circulant v` | — |
| Fourier matrix | `fourierMatrix n` (new) | — |
| Walsh–Hadamard matrix | `walshHadamard R b`, indexed by `Fin b → ZMod 2` (new) | `Matrix.IsHadamard` |
| Cauchy, Hilbert matrix | `cauchyMatrix x y`, `hilbertMatrix n` (new) | — |
| σ-algebra on matrices | `Matrix.instMeasurableSpace` (new, `ForMathlib`) | `MeasurableSpace.pi` |

Not ported as names: `gershgorinRowDisc`, `gershgorinRowUnion` and the column twins; `charpolyRootCountIn`; `matrixPowerBoundConstant`; `trailingMinor`,
`leadingMinor`; `IsRealNormalForm`; `sylvesterLinearMap`; `realMatrixComplexification` (replaced
by M8's `complexify`); `cyclicShiftMatrix`, `toeplitzMatrix`, `hankelMatrix`; `WalshIndex`,
`walshBitSign`, `walshCharacter`, `walshMatrixFin`.

## 2. Interfaces

**Eigenvalues of a matrix that is not Hermitian are a listing of the roots of the characteristic
polynomial.** A statement about "the eigenvalues `d` of `A`" takes
`hd : IsEigenvalueListing A d`, which unfolds to `A.charpoly = ∏ i, (X - C (d i))`, with `d`
indexed by any finite type; an existence statement produces `d`. Over `ℂ` a listing
always exists; over `𝕜` the hypothesis says the characteristic polynomial splits. Two listings
differ by a permutation. For a Hermitian matrix the sorted `eigenvalue A` is such a listing.

**Unitary similarity is written out**, `Uᴴ * A * U` with `HasOrthonormalCols U`, and triangular
means `Matrix.IsUpperTriangular` in the order of the index type. Schur's theorem prescribes the
diagonal in any order; over `𝕜` it holds whenever the characteristic polynomial splits, which
covers orthogonal triangularisation of a real matrix with real eigenvalues.

**Statements over `ℂ` when eigenvalues must exist, over `𝕜` otherwise.** The spectral theorem for
normal matrices, Fuglede–Putnam, simultaneous triangularisation, QZ and the Gershgorin count are
complex. Hermitian families, inertia, Sylvester's criterion, definite pairs and diagonal
dominance are over `𝕜`. The real Schur form and the descent theorems are real.

**Inertia is defined through `eigenvalue`**, not through the signature of a quadratic form as in
the prototype, so that it is available over `𝕜` and is literally the count the consumers use;
Sylvester's law is then a theorem about congruence, and the variational characterisation
(`le_inertiaPos_iff_exists_posDef`) is the bridge to subspaces. The eigenvalue count below a
shift is `inertiaNeg (A - x • 1)`, computed by the signs of the pivots of M9's `gaussState`.

**The spectral radius is a real number defined on matrices over `𝕜`**, through the
complexification of M8. Mathlib's `spectralRadius ℂ A : ℝ≥0∞` remains the general object; the
real-valued `specRadius` composes with `specNorm` and with `Tendsto` statements about powers
without coercions, and it is the right notion for a real matrix (whose real spectrum may be
empty).

**Gershgorin statements use `gershgorinRadius`**, which unfolds to Mathlib's spelling of the
radius, and are about `spectrum 𝕜 A`; no disc or union sets are defined. The counting theorem is stated with the multiset of roots of
the characteristic polynomial.

**Structured matrices use Mathlib's definitions** (`⊗ₖ`, `circulant`, `IsHadamard`). The
Kronecker file gives the decompositions of a product from those of the factors (`IsSVD.kronecker`,
unitary diagonalisations) and reads the norm, rank and pseudoinverse identities off them. The
Walsh–Hadamard matrix is the unnormalised `±1` matrix over any ring, indexed by bit strings; the
normalised orthogonal matrix is a scalar multiple.

**Measurability.** The product σ-algebra on matrices is an instance in `ForMathlib`, as the
contract foresaw. Continuous quantities are measurable through `BorelSpace`; the pseudoinverse,
the rank, the range projector, the polar factor and Gram–Schmidt are measurable without being
continuous.

## 3. Statement shapes

The skeleton is the authority; this is the map.

`Structured/Kronecker.lean`: `HasOrthonormalCols.kronecker`, `Matrix.IsHermitian.kronecker`,
`IsSVD.kronecker`, `kronecker_eq_mul_diagonal_mul_conjTranspose`, the Kronecker sum, extreme
eigenvalues, `specNorm_kronecker`, `frobNorm_kronecker`, `nuclearNorm_kronecker`,
`rank_kronecker`, `pinv_kronecker`, `conditionNumber_kronecker`.

`Structured/Circulant.lean`: `circulant_mulVec_pow` (eigenvectors over any field),
`mul_circulant_single_comm_iff`, `fourierMatrix` with unitarity,
`circulant_eq_fourierMatrix_mul_diagonal_mul_conjTranspose`, `isStarNormal_circulant`,
`specNorm_circulant_le_iff`, `det_circulant`.

`Structured/Walsh.lean`: `walshHadamard` with symmetry, character identities,
`walshHadamard_mul_self`, `isHadamard_walshHadamard`, `hasOrthonormalCols_smul_walshHadamard`,
flatness of the entries.

`Structured/Cauchy.lean`: `cauchyMatrix`, `det_cauchyMatrix`, positivity, `hilbertMatrix`,
`posDef_hilbertMatrix`.

`Spectral/Schur.lean`: listings (`exists_charpoly_eq_prod`, `exists_perm_eq_of_prod_X_sub_C_eq`,
spectrum, trace, determinant, real listings of a real matrix with real spectrum);
`exists_hasOrthonormalCols_isUpperTriangular_of_charpoly_eq` and the complex corollary;
`exists_isUpperTriangular_inv_mul_mul_norm_apply_lt` (nearly diagonal triangular form); Schur's
inequality and its equality case; eigenvalues of commuting matrices; density of separable
characteristic polynomials.

`Spectral/Normal.lean`: the spectral theorem in three forms, `isDiag_of_isUpperTriangular`,
block form, Hermitian and unitary through the eigenvalues, Frobenius and spectral norms through
the eigenvalues, Fuglede–Putnam, unitary similarity, Hoffman–Wielandt.

`Spectral/Simultaneous.lean`: common eigenvector, simultaneous Schur form, commuting normal
families, commuting Hermitian families over `𝕜`, products of commuting positive semidefinite
matrices.

`Spectral/Diagonalizable.lean`: `IsDiagonalizable` with its equivalent forms, distinct
eigenvalues, semisimplicity, blocks, Hermitian and normal matrices, commuting families; left and
right eigenvectors, biorthogonality, simple eigenvalues through the pairing, the adjugate at a
simple eigenvalue; the Sylvester equation and block diagonalisation.

`Spectral/RealSchur.lean`: `IsUpperQuasiTriangular`, `IsRealSchurForm`,
`exists_hasOrthonormalCols_isRealSchurForm`, the real normal form, real QZ, descent of similarity and of unitary similarity.

`Spectral/Inertia.lean`: `inertiaPos`, `inertiaNeg`, rank, diagonal, definiteness, the
variational characterisation; Sylvester's law (invertible and general congruence), Ostrowski; inertia forms of interlacing and a strict Courant–Fischer bound;
blocks and Haynsworth; counting eigenvalues by a shift, by `L D Lᴴ`, by pivots.

`Spectral/SylvesterCriterion.lean`: leading and trailing criteria, the semidefinite criterion
with all principal minors, coefficients of the characteristic polynomial as sums of principal
minors, elementary symmetric functions of the eigenvalues.

`Spectral/Congruence.lean`: the definite pair and its consequences for `A⁻¹ B` and `A B`,
semidefinite pairs, the real indefinite criterion, QZ.

`Spectral/Gershgorin.lean`: rows, columns, row sums, weighted row sums; diagonal dominance and
positive definiteness, the right half plane, Taussky; the counting theorem.

`Spectral/SpectralRadius.lean`: `specRadius` with its basic properties, comparison with
`specNorm`, normal matrices, row sums, commuting matrices; Gelfand's formula, growth of powers,
convergence of powers and of the Neumann series, similarity to within `ε`, power-bounded
matrices.

`Spectral/RankOneUpdate.lean`: `det_add_vecMulVec`, `det_diagonal_add_vecMulVec`, the secular
equation, the arrowhead characteristic polynomial, Brauer's theorem,
`Matrix.IsHermitian.isEigenvalueListing_eigenvalue`, the two converses of interlacing.

`Spectral/HermitianPart.lean`: `hermitianPart`, Ky Fan's majorization, Bendixson's bounds.

`ForMathlib/MeasureTheory/Matrix.lean`, `Measurability/Basic.lean`: §2.

## 4. Consumers

- **Iterative methods**: `specRadius`, convergence of powers and Neumann series, Gershgorin and
  diagonal dominance (Jacobi, Gauss–Seidel), `IsStarNormal.specNorm_eq_specRadius`.
- **Eigenvalue algorithms**: Schur and real Schur forms (the target of the QR iteration), the
  Sturm count (bisection), the secular equation (divide and conquer), Brauer's theorem
  (deflation), simultaneous diagonalisation.
- **Randomized algorithms**: `walshHadamard` and `fourierMatrix` (subsampled randomized
  Hadamard and Fourier transforms: unitary with flat entries), Kronecker norms and ranks
  (Kronecker and Khatri–Rao sketches), measurability of every quantity a probability statement
  mentions.
- **Optimization and statistics**: Sylvester's criterion, inertia and Haynsworth (KKT matrices,
  saddle point systems), definite pairs (generalized eigenvalue problems, canonical correlation,
  LDA), simultaneous diagonalisation of commuting Hermitian matrices.
- **Perturbation theory**: Hoffman–Wielandt for normal matrices, the simple-eigenvalue pairing,
  the Sylvester equation and block diagonalisation, the Hermitian part (numerical range bounds).

## 5. Files

Amended 2026-10-14 after the stage was proved: eight files were added or split off during the
stage (marked "new" below), and the imports are the ones the files have now.

`NLAlib/Matrix/Structured/`: `Kronecker.lean`, `Circulant.lean`, `Walsh.lean`, `Cauchy.lean`
(independent of each other; they import M1 to M4, `Kronecker.lean` also `Spectral/Schur` for the
eigenvalue listings of a Kronecker product and sum, `Cauchy.lean` M9 `Elimination`).

`NLAlib/Matrix/Spectral/`, in dependency order:

- `EigenvalueListing.lean` (new; imports M8 `Complexification`, `Factorizations/Triangular`):
  the predicate `IsEigenvalueListing`, its interface (relabelling, spectrum, trace, determinant,
  powers), `charpoly_mul_mul_of_mul_eq_one`, the block lemmas of a deflation step, and
  simultaneous triangularisation of a commuting pair by a similarity over any field.
- `EigenvectorPairing.lean` (new; Mathlib only): left and right eigenvectors, biorthogonality,
  simple eigenvalues through the pairing `y ⬝ᵥ x`, the adjugate at a simple eigenvalue.
- `SylvesterEquation.lean` (new; Mathlib only): `A X - X B = C` has exactly one solution when the
  characteristic polynomials are coprime; block diagonalisation of a block triangular matrix.
- `QuasiTriangular.lean` (new; M9 `Hessenberg`): `IsUpperQuasiTriangular` and its stability under
  triangular factors and under assembling blocks.
- `Schur.lean` (EigenvalueListing, `Factorizations/QR`).
- `Normal.lean` (Schur, M3a `Schur`).
- `Simultaneous.lean` (Normal).
- `Diagonalizable.lean` (Simultaneous, EigenvectorPairing).
- `RealSchur.lean` (Simultaneous, QuasiTriangular).
- `RealSimilarity.lean` (new; M8 `Complexification`, M9 `Polar`): real matrices similar, or
  unitarily similar, over `ℂ` are similar, or orthogonally similar, over `ℝ`.
- `Inertia.lean` (M3 `Interlacing`, `Weyl`, `SingularValues`).
- `InertiaElimination.lean` (new; Inertia, `Factorizations/GaussState`): Haynsworth additivity
  of the inertia, the inertia of a saddle-point matrix, and counting the eigenvalues below `x` by
  the signs of the pivots of `A - x • 1`.
- `SylvesterCriterion.lean` (InertiaElimination, Schur).
- `Congruence.lean` (Diagonalizable, Inertia, `Factorizations/QR`, `Subspaces/Frames`,
  `ForMathlib/LinearAlgebra/Matrix/ConjTranspose`).
- `Gershgorin.lean` (Schur).
- `SpectralRadius.lean` (Normal, Gershgorin).
- `PowerBounds.lean` (new; SpectralRadius, `Pseudoinverse/ConditionNumber`): Gelfand's formula,
  growth and convergence of the powers, the Neumann series, a similarity to within `ε` of the
  spectral radius, power-bounded matrices.
- `RankOneUpdate.lean` (SylvesterCriterion, M3 `Weyl`).
- `InterlacingConverse.lean` (new; RankOneUpdate): every interlacing sequence is the spectrum of
  a rank-one update and of a bordering, through the secular equation.
- `HermitianPart.lean` (Schur, EigenvectorPairing, M3a `Schur`).

`NLAlib/ForMathlib/MeasureTheory/Matrix.lean`; `NLAlib/Matrix/Measurability/Basic.lean` (imports
M6 `Continuity`, M9 `Polar`, `GramSchmidt`).

Order for proving: the four structured files and `Schur`, `Inertia`, the
measure-theory file first; then `Normal`, `Gershgorin`, `SylvesterCriterion`, `HermitianPart`;
then `Simultaneous`, `SpectralRadius`, `RankOneUpdate`; then `Diagonalizable`, `RealSchur`; then
`Congruence`, `Measurability`. Each new file was proved with the file that first imports it.

Names settled at the wrap-up of the stage: the spectral radius through a listing is
`IsEigenvalueListing.specRadius_le_iff` (any finite index type); the nearly diagonal triangular
form is `IsEigenvalueListing.exists_isUpperTriangular_inv_mul_mul_norm_apply_lt` over `𝕜`, with
`exists_isUpperTriangular_inv_mul_mul_norm_apply_lt` its corollary over `ℂ`; the eigenvalues of a
commuting pair with a prescribed listing of the first are
`IsEigenvalueListing.exists_isEigenvalueListing_add_mul_of_commute`, with
`exists_isEigenvalueListing_add_mul_of_commute` its corollary over `ℂ`; invariance of normality
under unitary similarity is `IsStarNormal.conjTranspose_mul_mul`.

## 6. Material

Prototype `Matrix/Structured/*` (66 declarations), the part of `Matrix/Spectral/*` not consumed
by M3 (about 350 declarations in 90 modules), `Matrix/Measurability/*` (13), and the
`ForMathlib/Analysis` files for Schur and simultaneous triangularisation, pencils and power
bounded operators. Almost all of it is proved in the prototype (one Sturm count is not). The
prototype states most of it over `ℝ` or `ℂ` separately, with eigenvalue listings as in §2, with
`Fin (card n) ≃ n` orderings where this note uses `[LinearOrder n]`, and with unitary groups
where this note uses `HasOrthonormalCols`.

Proof machinery that stays private or is not ported: the interlacing-converse construction
files (`InterlacingInduction`, `…Restoration`, `…Reindex`, `…OrthogonalTransport`,
`…StrictConstruction`, `…Determinants`, `…Trace`), the real Schur plane and invariant subspace
lemmas, the eigenvector deflation block lemmas, `SpectrumCount` and its continuity,
`PowerBoundedOrbits`, `GeneralizedEigenDecay`, `QuasiPencilBasis`, `PrimaryTriangularization`,
`SmallTriangularSimilarity` (one statement is kept), the Walsh character lemmas over `ZMod 2`.

## 7. Decisions taken without approval

1. Eigenvalue listings by the characteristic polynomial as the interface for non-Hermitian
   matrices.
2. `inertiaPos`, `inertiaNeg` defined through `eigenvalue`, over `𝕜`.
3. `specRadius` as a real-valued function on matrices over `𝕜`.
4. `IsDiagonalizable` as a new predicate (Mathlib has semisimplicity of endomorphisms, not a
   matrix predicate).
5. `gershgorinRadius` is a definition; no disc or union sets, no root-count definition.
6. `fourierMatrix`, `walshHadamard`, `cauchyMatrix`, `hilbertMatrix` as new definitions;
   Toeplitz and Hankel matrices not ported.
7. `Matrix.instMeasurableSpace` as a global instance in `ForMathlib`.
8. New statements with no prototype counterpart: Hoffman–Wielandt for normal matrices in listing
   form, the variational characterisation of the
   inertia, the Sturm count through `gaussState`, the Fourier diagonalisation of circulants,
   positive definiteness of the Hilbert matrix, `specRadius` of commuting sums and products,
   the nuclear norm, pseudoinverse and condition number of a Kronecker product, measurability of
   the rank, the range projector, the condition number and every `Φ.matrixNorm`.
9. Not ported: Bauer–Fike for raw absolute norms, the bounded-power constant as a definition,
   the quasi-pencil and primary triangularisation lemmas, the trailing-minor definition.

## 8. Review (Fable, 2026-10-14) and what changed

The review checked the roughly two hundred statements, with hand checks of the sign and index
conventions (Fourier diagonalisation, secular and arrowhead polynomials, Cauchy's determinant,
coefficients of the characteristic polynomial, the adjugate at a simple eigenvalue, the Sylvester
block identity). Findings and their resolution:

1. **False statements.** `eigenvalue_add_le_of_inertiaPos` was quantified over all indices; for
   `A = [-1]`, `B = [1]` it reads `0 ≤ -1` through the zero value of `eigenvalue` beyond the
   size. The index hypothesis was added. `specRadius_pow` and `specRadius_pow_le_specNorm_pow`
   fail for a matrix of size zero and exponent zero; `[Nonempty n]` was added, with
   `specRadius_one`.
2. The listing equation was spelled out in some forty statements; it is now the predicate
   `IsEigenvalueListing A d`, indexed by any finite type, with `card_eq`, `exists_equiv_eq`,
   `comp_equiv`, `spectrum_eq_range`, `trace_eq_sum`, `det_eq_prod`, `pow`, the triangular and
   Hermitian instances, and `IsEigenvalueListing.kronecker` for Kronecker products and sums.
3. Dot notation: the lemmas whose first explicit hypothesis is `hA : A.IsHermitian` moved to
   `Matrix.IsHermitian.*` (inertia, Sylvester's criterion, commuting pairs).
4. The Sturm count is stated with `inertiaNeg (A - x • 1)` on the left and named accordingly;
   the Gershgorin count no longer has an instance term in its statement and counts with
   `Multiset.card (roots.filter …)`.
5. Hypotheses dropped: `x ≠ 0` in Brauer's theorem, algebraic closure in the simple-eigenvalue
   pairing, `NoZeroDivisors` for quasi-triangular products, `MeasurableSingletonClass` for
   measurable powers; the semisimplicity equivalence is split so that only one direction asks
   for algebraic closure.
6. `Matrix.PosDef.spectrum_mul_subset_Ici` said nothing about non-real eigenvalues over `ℂ`; it
   is replaced by the listing form `Matrix.PosDef.exists_isEigenvalueListing_mul_nonneg`.
7. Definitions where a formula was repeated: `hermitianPart`, `gershgorinRadius`; the discrete
   Fourier transform of the first column of a circulant is written `√n • (Fᴴ *ᵥ v)`, with one
   lemma giving the explicit sum.
8. Real statements use `ᴴ`, as the contract asks; junk values are stated in the docstrings of
   `inertiaPos` and `inertiaNeg`; `_pair` names replaced.
9. Removed as having no consumer: the converse of real-part majorization, the congruence
   classification by inertia, the skew-symmetric and orthogonal specialisations of the real
   normal form.
10. Added for the consumers: `specRadius_one_sub_inv_diagonal_mul_lt_one` (convergence of the
    Jacobi iteration), the inertia of a saddle-point matrix
    (`Matrix.PosDef.inertiaPos_fromBlocks_zero`, `inertiaNeg_fromBlocks_zero`),
    `specNorm_pow_le_conditionNumber_mul` (powers through a similarity), the bridges
    `specRadius_eq_toReal_spectralRadius`, `specRadius_complexify`, and the Hermitian-part
    lemmas over `𝕜`.
11. Not taken: removing Cauchy and Hilbert matrices (the brief lists them) and Fuglede–Putnam;
    the growth bound `exists_forall_specNorm_pow_le_mul_pow` keeps its existential constant,
    since over `ℝ` the similarity that realises it is complex.
12. Mathlib supplies several proofs (`Matrix.charpoly_coeff_eq_sum_minors`,
    `Matrix.det_add_replicateCol_mul_replicateRow`, `eigenvalue_mem_ball`, Gelfand's formula,
    `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀`); the statements stay in the vocabulary
    of this library.

## 9. Stage report (2026-10-14)

**Outcome.** Twenty-seven files, all proved; nothing in `NLAlibScaffold`. The skeleton had
eighteen; eight were split off at proof time to stay under 500 lines (`EigenvalueListing.lean`,
`EigenvectorPairing.lean`, `SylvesterEquation.lean`, `InertiaElimination.lean`,
`InterlacingConverse.lean`, `PowerBounds.lean`, `QuasiTriangular.lean`, `RealSimilarity.lean`,
all under `Matrix/Spectral/`) and `ForMathlib/LinearAlgebra/Matrix/ConjTranspose.lean` was added
at wrap-up. With every earlier stage the library builds with no warnings, the axiom audit covers
3493 declarations with no violation, the environment linters pass on 2680 declarations,
and references check clean.

**False statements.** None found by the proof agents. The review (§8) had already added the
index hypothesis of `eigenvalue_add_le_of_inertiaPos` and `[Nonempty n]` on `specRadius_pow` and
`specRadius_pow_le_specNorm_pow`.

**What changed from the design.**

- Unitary Schur triangularisation is the similarity over a field followed by a QR factorization
  of the similarity; the same file gives commuting pairs and families over any field with split
  characteristic polynomials (`IsEigenvalueListing.exists_isEigenvalueListing_add_mul_of_commute`,
  `exists_hasOrthonormalCols_forall_isUpperTriangular_of_forall_splits`), of which the complex
  and Hermitian theorems are corollaries.
- The pairing criterion for a simple eigenvalue
  (`rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero`) holds over any field, by a new
  argument for the forward direction.
- Sylvester's criterion is proved by interlacing, with no pivots; both interlacing converses
  (rank-one update and bordering) are proved, in `InterlacingConverse.lean`.
- Real Schur, the real normal form and the real generalised Schur form share one deflation
  through an invariant subspace of dimension one or two; the complex generalised Schur form is
  Schur of `B⁻¹ * A` for invertible `B` and a compactness limit in general.
- The Hilbert matrix is positive definite through `Matrix.IsHermitian.posDef_iff_eliminationStep`
  (public: `posDef_cauchyMatrix_self`), with no integrals.
- `measurable_pinv` glues continuity on the pieces of constant rank over the measurable rank.
- `inertiaNeg_eq_inertiaPos_neg` lost an unused Hermitian hypothesis;
  `specRadius_le_iff_of_charpoly_eq` became `IsEigenvalueListing.specRadius_le_iff` over any
  index; `Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal` now also gives
  nonnegative diagonals.
- Added at wrap-up: `IsPinv.kronecker`, `det_ne_zero_of_posDef_hermitianPart`,
  `IsStarNormal.conjTranspose_mul_mul`, `Measurable.matrix_sub`, `matrix_neg`, `matrix_smul`,
  `matrix_const_smul`, `matrix_vecMul`, `walshHadamard_apply`, and upstream
  `Matrix.IsHermitian.gaussState`, `specNorm_pow_le`, `complexify_eq_self`,
  `charpoly_complexify`, `Commute.complexify`, `IsSVD.nuclearNorm_eq_sum`,
  `HasOrthonormalCols.singularValues_eq_one`, `principalMinor_transpose`,
  `IsStarProjection.norm_toLp_sq_eq_add`, `IsQR.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`,
  `Matrix.IsHermitian.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose`.

**Mathlib overlap.** `Matrix.PosSemidef.mul_of_commute` was Mathlib's `Commute.mul_nonneg` and
was deleted. `exists_norm_sub_le_sum_of_mem_spectrum` restates `eigenvalue_mem_ball` for the
spectrum; `charpoly_coeff_eq_sum_principalMinor` is `Matrix.charpoly_coeff_eq_sum_minors` and
`det_add_vecMulVec` is `Matrix.det_add_replicateCol_mul_replicateRow` in `vecMulVec` form.
Mathlib has no measurable space on matrices, no `rank_kronecker`, and Fuglede–Putnam only for
one C⋆-algebra (the square case).

**Not ported, by decision.** §7.9, and from the ledger pass: simultaneous triangularisation with
a prescribed listing for one member, the eigenspace dimension criterion for diagonalisability,
irreducible weak diagonal dominance for the real parts, the converse direction of the Sylvester
operator's injectivity, root-count constancy as a public statement, the negative rank-one
converse, eigenvector deflation, Toeplitz and Hankel matrices. The ledger accounts for every
public prototype declaration of `Matrix/Spectral`, `Matrix/Structured` and
`Matrix/Measurability`.

**After the stage reports (all stages).** Two passes followed the last stage. A follow-up pass
added statements that the ledger passes had found useful and missing (idempotents in oblique
form, invariance of principal angles, `Spectral/ProjectedLowRank.lean`, the determinant of a
compression against the top eigenvalues, `frobInner_polarFactor`, `givens_apply`, kernel
monotonicity of an elimination step). An audit of the dropped prototype declarations that the
prototype's upper layers use (`docs/port/matrix-downstream-audit.md`) then found six general
facts and two convenience lemmas missing; they were added: the trace-tail inequality behind
randomly pivoted Cholesky (`Majorization/KyFan.lean`), the scaled Gram-error bounds and
`Spectral/LeastSingularValue.lean`, `Matrix.IsHermitian.specNorm_exp` and
`specNorm_exp_sum_le_prod`, the polynomial bound in a general weight
(`Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`), the per-vector tangent bound
(`Subspaces/Tangent.lean`), the real entrywise forms of `frobNorm` and `frobInner`,
`singularValues_complexify`, `continuous_complexify`, `specRadius_transpose` and the column-sum
bound.

**Amendment, 2026-10-14 (maintainer).** Measurability belongs to the Probability layer.
`NLAlib/Matrix/Measurability/Basic.lean` is now `NLAlib/Probability/Measurability/Matrix.lean`,
with its statements and names unchanged; `ForMathlib/MeasureTheory/Matrix.lean` stays where it
is and is imported only from there.
