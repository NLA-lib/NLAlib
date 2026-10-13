# Design note: Matrix stage M10, structured matrices and the remaining spectral theory

Status: written 2026-10-14 by the orchestrator while M7 was being proved; to be implemented
without a maintainer approval stop, by the standing instruction in `docs/port/status.md`. Choices
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
| eigenvalues of a general matrix | a listing `d : n → K` with `A.charpoly = ∏ i, (X - C (d i))` | `Matrix.charpoly_of_isUpperTriangular` |
| sorted eigenvalues of a Hermitian matrix | `eigenvalue A k` (M3) | `Matrix.IsHermitian.charpoly_eq_prod_eigenvalue` (new) |
| normal matrix | Mathlib's `IsStarNormal A` | — |
| unitary matrix | `HasOrthonormalCols U`, `U` square (as before) | `HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` |
| upper triangular in a chosen order | `Matrix.IsUpperTriangular` on `[LinearOrder n]` | — |
| diagonalisable | `IsDiagonalizable A` (new): `A * V = V * diagonal d`, `IsUnit V.det` | `Module.End.IsSemisimple` over an algebraically closed field |
| quasi-triangular, real Schur form | `IsUpperQuasiTriangular T`, `IsRealSchurForm T`, `Fin`-indexed (new) | — |
| inertia | `inertiaPos A`, `inertiaNeg A` (new): counts of positive and negative `eigenvalue A i` | — |
| leading principal minor | `principalMinor A (Finset.Iic i)` (as in M9) | — |
| generalized eigenvalues of a definite pair | the diagonal `d` in `A = S Sᴴ`, `B = S diag(d) Sᴴ`; `spectrum ℝ (A⁻¹ * B)` (as in M7) | — |
| Gershgorin radius | `∑ j ∈ Finset.univ.erase i, ‖A i j‖` (Mathlib's spelling) | `eigenvalue_mem_ball` |
| spectral radius | `specRadius A : ℝ` (new) `= (spectralRadius ℂ (complexify A)).toReal` | — |
| Hermitian part | `(2⁻¹ : ℝ) • (A + Aᴴ)` | `selfAdjointPart ℝ A` |
| Kronecker product | Mathlib's `A ⊗ₖ B` | — |
| circulant matrix | Mathlib's `Matrix.circulant v` | — |
| Fourier matrix | `fourierMatrix n` (new) | — |
| Walsh–Hadamard matrix | `walshHadamard R b`, indexed by `Fin b → ZMod 2` (new) | `Matrix.IsHadamard` |
| Cauchy, Hilbert matrix | `cauchyMatrix x y`, `hilbertMatrix n` (new) | — |
| σ-algebra on matrices | `Matrix.instMeasurableSpace` (new, `ForMathlib`) | `MeasurableSpace.pi` |

Not ported as names: `gershgorinRowRadius`, `gershgorinRowDisc`, `gershgorinRowUnion` and the
column twins; `charpolyRootCountIn`; `matrixPowerBoundConstant`; `trailingMinor`,
`leadingMinor`; `IsRealNormalForm`; `sylvesterLinearMap`; `realMatrixComplexification` (replaced
by M8's `complexify`); `cyclicShiftMatrix`, `toeplitzMatrix`, `hankelMatrix`; `WalshIndex`,
`walshBitSign`, `walshCharacter`, `walshMatrixFin`.

## 2. Interfaces

**Eigenvalues of a matrix that is not Hermitian are a listing of the roots of the characteristic
polynomial.** A statement about "the eigenvalues `d` of `A`" takes
`hd : A.charpoly = ∏ i, (X - C (d i))`; an existence statement produces `d`. Over `ℂ` a listing
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

**Gershgorin statements use Mathlib's spelling of the radius** and are about `spectrum 𝕜 A`;
no disc or union sets are defined. The counting theorem is stated with the multiset of roots of
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
`exists_hasOrthonormalCols_isRealSchurForm`, the real normal, skew-symmetric and orthogonal
forms, real QZ, descent of similarity and of unitary similarity.

`Spectral/Inertia.lean`: `inertiaPos`, `inertiaNeg`, rank, diagonal, definiteness, the
variational characterisation; Sylvester's law (invertible and general congruence), the congruence
classification, Ostrowski; inertia forms of interlacing and a strict Courant–Fischer bound;
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
`Matrix.IsHermitian.charpoly_eq_prod_eigenvalue`, the two converses of interlacing.

`Spectral/HermitianPart.lean`: Ky Fan's majorization, Bendixson's bounds, the converse.

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

`NLAlib/Matrix/Structured/`: `Kronecker.lean`, `Circulant.lean`, `Walsh.lean`, `Cauchy.lean`
(independent of each other; they import M1 to M4).

`NLAlib/Matrix/Spectral/`, in dependency order: `Schur.lean` (imports M8 `Complexification`);
`Normal.lean` (Schur, M3a `DoublyStochastic`); `Simultaneous.lean` (Normal);
`Diagonalizable.lean` (Simultaneous); `RealSchur.lean` (Simultaneous, M9 `Hessenberg`);
`Inertia.lean` (M3 `Interlacing`, M9 `Elimination`); `SylvesterCriterion.lean` (Inertia, Schur);
`Congruence.lean` (Diagonalizable, Inertia); `Gershgorin.lean` (Schur); `SpectralRadius.lean`
(Normal, Gershgorin); `RankOneUpdate.lean` (SylvesterCriterion, M3 `Weyl`); `HermitianPart.lean`
(Schur, M3a `Schur`).

`NLAlib/ForMathlib/MeasureTheory/Matrix.lean`; `NLAlib/Matrix/Measurability/Basic.lean` (imports
M6 `Continuity`, M9 `Polar`, `GramSchmidt`).

Order for proving: the four structured files and `Schur`, `Inertia`, the measure-theory file
first; then `Normal`, `Gershgorin`, `SylvesterCriterion`, `HermitianPart`; then `Simultaneous`,
`SpectralRadius`, `RankOneUpdate`; then `Diagonalizable`, `RealSchur`; then `Congruence`,
`Measurability`.

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
5. No Gershgorin disc definitions; no root-count definition.
6. `fourierMatrix`, `walshHadamard`, `cauchyMatrix`, `hilbertMatrix` as new definitions;
   Toeplitz and Hankel matrices not ported.
7. `Matrix.instMeasurableSpace` as a global instance in `ForMathlib`.
8. New statements with no prototype counterpart: Hoffman–Wielandt for normal matrices in listing
   form, the congruence classification by inertia, the variational characterisation of the
   inertia, the Sturm count through `gaussState`, the Fourier diagonalisation of circulants,
   positive definiteness of the Hilbert matrix, `specRadius` of commuting sums and products,
   the nuclear norm, pseudoinverse and condition number of a Kronecker product, measurability of
   the rank, the range projector, the condition number and every `Φ.matrixNorm`.
9. Not ported: Bauer–Fike for raw absolute norms, the bounded-power constant as a definition,
   the quasi-pencil and primary triangularisation lemmas, the trailing-minor definition.
