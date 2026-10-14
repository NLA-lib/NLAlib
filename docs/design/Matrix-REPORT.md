# Matrix layer: final report

Date: 2026-10-14. Branch `scaffold`, local commits only, nothing pushed.

This is the report that `docs/PORT_MATRIX.md` §6 asks for: what the layer exports, counts, and
what `CONTRIBUTING.md` should say differently before the Probability layer is designed. The
per-stage detail is in the twelve design notes `docs/design/Matrix-*.md`, each of which ends with
a review section and a stage report.

## 1. State

- `NLAlib/Matrix/` and `NLAlib/ForMathlib/`: 144 files, 41,393 lines, 2624 declarations
  of which 2048 are public and 84 are definitions or structures. Every proof is complete.
- `NLAlibScaffold/` is empty. Every statement that was unproved in the prototype and belongs to
  this layer is proved here: the rank pattern of pivoted Cholesky, the Hessenberg reduction, the
  QR factorization of a Hessenberg matrix, the implicit Q theorem.
- `LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold` succeeds with no warnings.
  `scripts/Audit.lean`: 3493 declarations, 0 violations. `scripts/Lint.lean`: 2680 declarations,
  clean. `scripts/check_refs.py`: 32 bibliography keys, 0 problems.
- `docs/port/ledger.json` accounts for all 2734 public declarations of the prototype's
  `Matrix/`: 1767 map to 1264 declarations of the new library, 967 are dropped with
  a reason. `python3 scripts/ledger_check.py` confirms every target exists.
- Stages, in the order built: M0 bootstrap, M1 foundations (`Basic/`), M2 norms, M3 spectral
  core, M4 pseudoinverse, M3a majorization, M3b invariant norms, M5 subspaces, M6 perturbation,
  M7 inequalities, M8 matrix functions, M9 factorizations, M10 structured matrices, the remaining
  spectral theory and measurability.

### Two things that are not as the brief says

1. **No design note was approved by the maintainer.** The approval stop was waived during the
   run ("do not stop for me for the matrix part"). Each note was reviewed by a Fable agent
   instead, and each records the decisions that were the maintainer's to make in a section
   "Decisions taken without approval". §3 below collects the ones that later layers inherit.
2. **Measurability was first put in the layer**, although the brief's §4 says it is designed
   with Probability. The maintainer moved it on 2026-10-14: the statements (measurability of the
   norms, singular values, eigenvalues, rank, `pinv`, `rangeProjector`, `conditionNumber`,
   `polarFactor` and `gramSchmidtQ`) are now `NLAlib/Probability/Measurability/Matrix.lean`,
   the first file of the Probability layer, and the Matrix layer has no measure theory. The
   product measurable space on `Matrix m n α`, a **global instance** (Mathlib has none) with a
   Borel instance, stays in `NLAlib/ForMathlib/MeasureTheory/Matrix.lean`, because it is about
   Mathlib's objects only; nothing in `NLAlib/Matrix/` imports it. Whether a global instance is
   the right form is a question for the Probability design.

## 2. How much changed from the prototype

| | prototype `Matrix/` | new layer |
|---|---|---|
| files | 463 | 144 |
| lines | 57,797 | 41,393 |
| public declarations | 2734 | 2048 |

- 1767 prototype declarations (65%) have a counterpart; because real and complex
  twins, `Fin` twins and special cases merge, they land on 1264 declarations. Only
  326 kept their name: almost everything was restated over `𝕜` or in the new vocabulary.
- 967 (35%) have none. By the reason recorded, in round numbers: 300 belong to
  objects and recursions deliberately not reproduced, with a further 140 of the same kind
  recorded in other words (no rectangular diagonal, no chosen eigenframes, no sorting); 170 are
  proof helpers now private or inlined; 160 are statements judged not worth porting; 90 are
  one-step corollaries and bundles; 80 are facts Mathlib already has; 20 are twins.
- About 780 public declarations of the new layer have no prototype ancestor.
- By a textual search (`scripts/downstream_nulls.py`), only about 450 of the 2734 prototype
  declarations are used by prototype code outside `Matrix/`. See §5.

**False statements.** Eleven statements of the skeletons were false and were repaired, every one
in a degenerate case: an empty index type or a negative constant
(`specNorm_sub_smul_one_le_of_le`, `conditionNumber_le_div_of_smul_one_le_of_le_smul_one`,
`conditionNumber_conjTranspose_mul_mul_le_div`, `Matrix.PosSemidef.re_det_add_le`,
`specNorm_pow_le_re_trace_pow`, `specRadius_pow`, `specRadius_pow_le_specNorm_pow`, the
coefficient bound of the rank-revealing selection), or a missing index bound
(`eigenvalue_le_of_forall_mem`, the rank-revealing singular value bounds,
`eigenvalue_add_le_of_inertiaPos`). Proof agents found three of them by failing to prove the
statement and producing the counterexample; reviews and the writing of skeletons found the rest
before proofs started. Each is recorded in its stage's note.

## 3. Interfaces the layer exports

`CONTRIBUTING.md` §5.3 now has a row for each of these. The list below is ordered by how much
the layers above depend on the choice; "consumers" are the prototype's upper layers.

| Interface | Form | Consumers |
|---|---|---|
| orthonormal columns | `HasOrthonormalCols Q`; a unitary is a square one; rows are `HasOrthonormalCols Qᴴ` | everything: sketches, range finders, Krylov bases |
| eigenvalues of a Hermitian matrix | `eigenvalue A k : ℝ`, `k : ℕ`, non-increasing, `0` out of range | concentration (`eigenvalue A 0`), Krylov, PCA |
| singular values | `singularValues A k`, `k : ℕ`, zero-padded; smallest is index `k` with `k + 1 = card n` | subspace embeddings, random matrices, low rank |
| norms | `specNorm`, `frobNorm` (square written `frobNorm A ^ 2`, no `frobSq`), `nuclearNorm`, `schattenNorm q`, `kyFanNorm k`, `Φ.matrixNorm` for `Φ : SymmetricGauge` | every error bound |
| spectral bounds on a factor | Loewner inequalities on the Gram matrix, `a • 1 ≤ Tᴴ * T ≤ b • 1` | subspace embedding, preconditioning |
| SVD and low rank | `IsSVD A U σ V` (thin, any column type), `truncatedSVD A k`, tail in `frobNorm_sub_truncatedSVD_sq`; `Spectral/ProjectedLowRank.lean` for the truncation step | randomized SVD, Nyström |
| pseudoinverse and projector | `pinv A` (every shape and rank) recognised by `IsPinv`; `rangeProjector A`; residual `(1 - rangeProjector Y) * A`; `conditionNumber A : ℝ`; `IsLeastSquaresSolution A b x` | sketch-and-solve, least squares, range finders |
| subspaces | the matrix `(1 - Q) * P` of two star projections in a norm; `principalAngle X Y k`; `tangentMatrix U Y` | subspace iteration, Davis–Kahan consumers |
| majorization | `Majorized x y`, `WeaklyMajorized x y` on unsorted vectors through `sumLargest` | invariant-norm bounds |
| functions of a Hermitian matrix | Mathlib's `cfc f A`; `NormedSpace.exp A`; `cfc Real.log A`; `A ^ r`; `CFC.sqrt A`; no `matrixExp`, `traceExp`, `lambdaMax` | matrix concentration (Lieb, Golden–Thompson, trace exponential), Krylov error bounds |
| transfer from `𝕜` to `ℂ` | `complexify A` | wherever Mathlib has a complex-only result |
| operator convexity | `OperatorConvexOn s f` with `a • A + b • B`, `a + b = 1`; operator monotonicity is stated directly as a Loewner implication | matrix Jensen, concentration |
| derivative of a matrix curve | entrywise `HasDerivAt`, `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean` | Stein and interpolation arguments |
| algorithms | a total recursion indexed by the step (`gaussState`, `householderState`), breakdown as a value, a realisation theorem under a hypothesis on computed pivots | Krylov processes, pivoted factorizations, solvers |
| factorizations | `IsLU`, `IsCholesky`, `IsQR` (thin); `eliminationStep`; `polarFactor`; `IsLocalMaxVolume A e f` | randomly pivoted Cholesky, CUR, QR-based solvers |
| eigenvalues of a general matrix | `IsEigenvalueListing A d`: `A.charpoly = ∏ i, (X - C (d i))` | non-Hermitian iterations, spectral radius |
| normal, diagonalisable, inertia, spectral radius | Mathlib's `IsStarNormal`; `IsDiagonalizable`; `inertiaPos`, `inertiaNeg`; `specRadius A : ℝ` | stationary iterations, saddle-point systems |
| structured matrices | Mathlib's `⊗ₖ` and `circulant`; `fourierMatrix`, `walshHadamard`, `cauchyMatrix`, `hilbertMatrix` | SRHT and other fast transforms |

Predicates in the sense of §5.4 (hypotheses and conclusions that theorems exchange):
`HasOrthonormalCols`, `IsSVD`, `IsPinv`, `IsLeastSquaresSolution`, `Majorized`,
`WeaklyMajorized`, `SymmetricGauge` (a structure), `OperatorConvexOn`, `IsLU`, `IsCholesky`,
`IsQR`, `IsUnitLowerTriangular`, `IsUpperTrapezoidal`, `IsUpperHessenberg`, `IsTridiagonal`,
`IsUpperQuasiTriangular`, `IsRealSchurForm`, `IsLocalMaxVolume`, `IsEigenvalueListing`,
`IsDiagonalizable`; from Mathlib, used as the interface with no wrapper: `IsStarProjection`,
`IsIdempotentElem`, `IsStarNormal`, `Matrix.IsHermitian`, `Matrix.PosSemidef`, `Matrix.PosDef`,
`Metric.IsCover`.

**Decisions to confirm before they spread.** Each is argued in the note cited; those that
depart from Mathlib are set out, with justification and cost, in
`docs/design/Mathlib-deviations.md`.

1. `eigenvalue A k` indexed by `ℕ` and total, replacing `hA.eigenvalues₀ i` in statements
   (`Matrix-Spectral.md` §7.1). This changed a row of §5.3 and a line of the brief.
2. `frobSq` removed; the square is `frobNorm A ^ 2` (`Matrix-Norms.md` §7.1). Expectations of
   squared errors read `∫ ω, frobNorm (E ω) ^ 2 ∂μ`.
3. One pseudoinverse `pinv` with `IsPinv`, a real-valued `conditionNumber` for every shape
   (`Matrix-Pseudoinverse.md` §7.1 to §7.3). This contradicted an example in §5.2, now amended.
4. The projector is primitive and the residual has no name (`Matrix-Foundations.md` §7.1).
5. Unitarily invariant norms through `SymmetricGauge` on `ℕ →₀ ℝ` (`Matrix-InvariantNorms.md`
   §7.1).
6. No `matrixExp`, `matrixLog`, `traceExp`, `lambdaMax`; `cfc Real.log A` because Mathlib's
   `CFC.log` needs a global normed ring on matrices (`Matrix-Functions.md` §7.1, §7.2).
7. The algorithm convention (`Matrix-Factorizations.md` §2, §7.1): the Krylov and solver layers
   will follow it or replace it, so it deserves a decision before they are designed.
8. `IsEigenvalueListing` as the interface for non-Hermitian spectra, `specRadius` real-valued
   over `𝕜` (`Matrix-Structured.md` §7.1, §7.3).
9. The global measurable-space instance on matrices (`Matrix-Structured.md` §7.7; §1 above).

## 4. What `CONTRIBUTING.md` should say differently

Already amended during the port (see `git diff 7d0b33a -- CONTRIBUTING.md`): the build commands
(`LEAN_NUM_THREADS`, `lake lean` in place of `lake env lean`), the junk-value rule with
real-valued quantities, the Mathlib-overlap rule of §8, the two-agent rule of §11, and the §5.3
rows above. Proposed, not yet written into the contract:

1. **§8, design from the consumers.** Only about one prototype Matrix declaration in six is used
   outside `Matrix/`. A design note should start from the list of what the layers above use
   (`scripts/downstream_nulls.py` and a reverse-dependency listing from the atlas), not from the
   prototype's file list. A review cut the continuity of Lieb's function as dead weight and it
   had to be restored for the concentration layer.
2. **§5.2, a degenerate-case checklist for every statement**: empty index type, zero matrix,
   size one, constants that may be zero or negative, indices beyond the size, rank deficiency.
   Every false statement of the layer fails one of these. The proof agents' rule "do not patch;
   leave it and report the counterexample" worked and should be in §11.
3. **§5.2, diagonalisation hypotheses take a frame.** Lemmas that consume a unitary
   diagonalisation take `U : Matrix n r 𝕜` with `HasOrthonormalCols U` and
   `Fintype.card r = Fintype.card n`, so that sorted eigenvector frames indexed by
   `Fin (card n)` apply without reindexing.
4. **§8, budget the file split in the note.** The 500-line limit forced more than fifteen splits
   at proof time. A skeleton file should carry at most about fifteen statements, or the note should
   name the split in advance.
5. **§8, search the library, not only Mathlib, for duplicates** before a statement enters a
   skeleton. Three lemmas of M8 restated lemmas of M3, and several private helpers were proved
   in two to four files before a wrap-up pass made one public copy
   (`conjTranspose_diagonal_ofReal`, `isHermitian_gaussState`, similarity invariance of the
   characteristic polynomial). A helper that a second file could want is public from the start.
6. **§9, stage checks on a partial library.** `scripts/Audit.lean` and `scripts/Lint.lean`
   import all of `NLAlib`, which cannot build while a later skeleton has `sorry`.
   `scripts/stage_check.sh` runs them on the fully proved modules; §9 should name it.
7. **§9, a wrap-up pass and a ledger pass close every stage.** The wrap-up agent gets a fixed
   list collected from the proof agents' reports (publish, dedupe, rename, generalise); a
   read-only agent then maps the stage's leftover prototype declarations and reports useful
   statements that were not ported. Ledger notes must not say "deferred": forty-five such notes
   went stale and had to be resolved at the end.
8. **§6, citation locators.** Theorem and section numbers in docstrings were often carried over
   from the prototype or written from memory by agents. `check_refs.py` checks keys, not
   locators. Either a locator is checked against the source or the citation gives the key only.
   Known unchecked: `[Carlen2010, Theorem 2.9]`, `[Bhatia1997, §IX.1]`, `[Bhatia1997, §IX.2]`,
   `[HornJohnson2013, Theorem 7.7.18]`, `[HornJohnson2013, §7.4.4]`,
   `[HalkoMartinssonTropp2011, Theorem 9.1 (proof)]`.
9. **§11, proof agents may own a short chain of files**, and are told which files another agent
   is editing. Both were practised throughout; the second is not in the contract.

## 5. What the upper layers will find missing

`docs/port/matrix-downstream-audit.md` classifies the 142 dropped prototype declarations whose
names occur in the prototype outside `Matrix/`: 104 are covered by another spelling (the table
there gives the new spelling for each, which is the translation guide for porting the upper
layers), 19 are coincidences of name, and 19 were gaps.

- Six general facts and two convenience lemmas were added after the audit (the trace-tail
  inequality behind randomly pivoted Cholesky, the scaled Gram-error bounds of Vershynin's lemma,
  the column distance bound for a small least singular value, `specNorm_exp_sum_le_prod`, the
  polynomial bound in a general weight for CG and MINRES, the per-vector tangent bound for
  subspace iteration; the real entrywise forms of `frobNorm` and `frobInner`).
- Seven helpers of single proofs are left to the layer that uses them, as the ledger says: the
  growth bound and coordinate derivative of the Khintchine polynomial series, three derivatives
  of traces of inverse powers (Wishart), a CountSketch fourth-moment contraction sum, and the
  Freedman crossing bound.

Statements judged useful but not added, with no current consumer: equality cases of Minkowski's
determinant inequality, of von Neumann's trace inequality and of Mirsky's theorem; the strict
generalised-eigenvalue criterion; the gradient of the Rayleigh quotient; simultaneous
triangularisation with a prescribed listing for one member; the eigenspace-dimension criterion
for diagonalisability; irreducible weak diagonal dominance for real parts; the scaled orthogonal
Procrustes problem.

## 6. Tools added

`scripts/proto_sigs.py` (prototype signatures by module, the reading list for a design note),
`scripts/ledger_from_ports.py`, `scripts/ledger_add.py`, `scripts/ledger_missing.py`,
`scripts/ledger_check.py` (ledger filling and checking), `scripts/proved_modules.py` and
`scripts/stage_check.sh` (checks on the proved part), `scripts/downstream_nulls.py` (dropped
declarations that upper layers use), and `docs/port/proof-agent-brief.md` (the standing brief
for proof agents).
