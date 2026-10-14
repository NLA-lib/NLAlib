# Contributing to NLAlib

NLAlib is a Lean 4 library, built on Mathlib, of the foundations of numerical linear algebra:
matrix analysis, matrix perturbation theory, random matrices, concentration, sketching, low-rank
approximation, Krylov methods and randomized solvers.

**The goal is to make proving new results easy.** The library exists so that someone analysing a
new algorithm can import a statement and apply it with `exact`, `rw` or `apply`. It is not a
transcription of the literature: a result is stated in the form most useful for building on it,
proved by whatever argument is cleanest, and cited where it (or the result it generalises) appears
in print. The statement is the product. A proof can be replaced; a statement nobody can apply is
wasted.

This file is the contract. Everything in it is enforced by CI, by review, or both. It is written
for human contributors and for the AI agents that do much of the work; the rules are the same.

Sections: 1 Ground rules · 2 Layout · 3 File template · 4 Names · 5 Statements · 6 Docstrings
and citations · 7 Proofs, `sorry` and the scaffold library · 8 Designing a stage · 9 Workflow and
checks · 10 Building without running out of memory · 11 Rules for agents.

## 1. Ground rules

1. **Built for use, not transcription.** Choose the statement a downstream proof wants: the
   general form, the hypotheses it will actually have, the conclusion in the shape it will
   rewrite with. The printed version in a source is provenance, not a specification; deviating
   from it (generalising, changing the constant, restating as a tail instead of a sample size,
   splitting or merging) is normal and is recorded in the docstring.
2. **One interface per kind of hypothesis** (§5.4). Hypotheses are named predicates and structures
   shared across the library (`HasOrthonormalCols`, `IsSubspaceEmbedding`, an isotropy predicate,
   a spectral-gap predicate), never raw conditions re-spelled per theorem. If you write a raw
   condition a second time, it is an interface. If a theorem's hypotheses do not fit an existing
   interface, that is a design question (§8), not a reason to invent a local one.
3. **Mathlib first.** Before defining or proving anything, search Mathlib (`grep -rn` in
   `.lake/packages/mathlib/Mathlib`, `exact?`, `apply?`, `rw?`, Loogle). If Mathlib has the
   statement, use it. If Mathlib has the object (`Matrix.PosSemidef`, `IsHermitian.eigenvalues₀`,
   `LinearMap.singularValues`, `cfc`, `MatrixOrder`, `HasLaw`, `HasSubgaussianMGF`), build on it and
   never define a parallel one. If you must define your own, ship the bridge lemma to Mathlib's
   notion in the same file.
4. **One spelling per concept** (§5.3). A second spelling, a `Complex*` twin, an `ᵀ` copy of an
   `ᴴ` lemma, or a local re-definition is a defect, whatever its reason.
5. **General once, then corollaries.** Over `[RCLike 𝕜]` and arbitrary `[Fintype]` index types
   unless the mathematics needs ℝ or `Fin` (§5.1). The ℝ corollary, when useful, is one line.
6. **Every public declaration is documented and cited** (§6).
7. **No `sorry` on `main`** in the library. Deferred statements live in `NLAlibScaffold` (§7).
   No `axiom`, no `native_decide`, no `admit`, no weakening a statement to make it provable.
8. **Files are topics, not proofs.** 300 to 500 lines, one mathematical topic, ordered
   definitions → basic API → main theorems → corollaries. No file named after a paper, a round of
   work, or a proof technique. No "toolkit", "bundle" or "part 2" files.
9. **Design before code** (§8). Each stage of the library starts with a written design: the
   objects, the hypothesis interfaces, the statement shapes, and how later layers will consume
   them. Nothing is inherited from the prototype library by default; its organisation, names and
   interfaces are material to evaluate, not a template.

## 2. Layout

```
NLAlib/
  ForMathlib/      general facts not about NLAlib's objects, headed upstream;
                   files named after the Mathlib file they would join            (layer −1)
  Matrix/          deterministic matrix analysis                                  (layer 0)
  Polynomial/      Chebyshev, minimax, Markov, interpolation                        (layer 0)
  Probability/     scalar and vector probability, concentration                    (layer 1)
  Krylov/          deterministic Krylov theory                                      (layer 1)
  RandomMatrix/    Gaussian, sub-Gaussian, Haar random matrices                     (layer 2)
  Sketching/       sketch distributions and their embedding guarantees             (layer 3)
  LowRank/  Estimation/                                                            (layer 4)
  Solvers/                                                                         (layer 5)
NLAlibScaffold/    same tree; statements with deferred proofs (§7)
docs/              references.bib, design notes (docs/design/), port ledger (docs/port/)
scripts/           Audit.lean, Lint.lean, check_refs.py, stage_check.sh, ledger and prototype tools
```

The subdirectories of each layer are decided in that layer's design note (§8), not in advance.
A module imports only its own layer and lower. The root files `NLAlib.lean` and
`NLAlibScaffold.lean` are generated by `lake exe mk_all --module --lib <name>`; CI checks they are current.
There are no per-directory aggregator files: a user imports the file they need.

`ForMathlib` holds only facts with no NLAlib vocabulary in their statement. They are declared in
the Mathlib namespace they would have upstream, marked in the module docstring as upstream
candidates, and deleted when they land in Mathlib.

## 3. File template

Every file has this shape. The header linter checks the first lines; the module system is the
one Mathlib uses.

```lean
/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import NLAlib.Matrix.Norms.Spectral

/-!
# Weyl's inequalities

Perturbation bounds for the eigenvalues of Hermitian matrices and the singular values of
arbitrary matrices.

## Main results

* `NLAlib.eigenvalue_add_le`: Weyl's inequality `λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)`.
* `NLAlib.singularValues_add_le`: the singular-value form.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

...

end NLAlib
```

Rules:

- The header linter requires a non-empty `Authors:` line; use `NLAlib contributors` unless the
  file is a port that must keep its original attribution.
- `module`, then `public import` lines (specific Mathlib files; never `import Mathlib` or
  `import Mathlib.Tactic`), then the module docstring, then `@[expose] public section`.
- Everything is in `namespace NLAlib`, except lemmas whose subject is a Mathlib structure
  hypothesis (`Matrix.IsHermitian`, `Matrix.PosSemidef`), which are declared
  `theorem _root_.Matrix.IsHermitian.foo` inside `namespace NLAlib` so that `hA.foo` works.
- No file-level `set_option maxHeartbeats`, `set_option backward.*`, `open Classical` or
  `open scoped Classical`. A single declaration that needs a heartbeat bump gets
  `set_option maxHeartbeats N in` on that declaration, with a comment saying why.
- `private` for proof-local helpers only. A lemma a second file could want is public, named by §4,
  documented by §6, and placed in the file that owns its subject, not the file that needed it first.
- `noncomputable section` is not opened at file level; mark individual definitions `noncomputable`
  when Lean requires it.

## 4. Names

Mathlib's conventions, https://leanprover-community.github.io/contribute/naming.html, in full.

| Kind | Case | Examples |
|---|---|---|
| theorem, lemma | `snake_case` | `frobNorm_nonneg`, `specNorm_mul_le`, `singularValues_add_le` |
| definition returning data | `lowerCamelCase` | `specNorm`, `singularValues`, `rangeProjector` |
| structure, class, Prop-valued predicate | `UpperCamelCase` | `IsSVD`, `HasOrthonormalCols`, `IsSubspaceEmbedding` |
| namespace, file, directory | `UpperCamelCase` | `NLAlib.Matrix.Spectral.Weyl` |

A theorem name spells its conclusion left to right from the head symbols:
`frobNorm_mul_le_specNorm_mul_frobNorm` is `frobNorm (A * B) ≤ specNorm A * frobNorm B`.
Standard suffixes `_eq`, `_le`, `_lt`, `_iff`, `_ne_zero`, `_pos`, `_nonneg`, `_left`, `_right`,
`_apply`, `exists_`, `_of_<hypothesis>`; measure-theory prefixes `integral_`, `measurable_`,
`integrable_`, `variance_`. Hypotheses are `h`-prefixed (`hA`, `hQ`, `hk`).

Never name a declaration after its source, its chapter, its author, a paper's lemma number or a
project. The source goes in the docstring. Named quantities and tail expressions are definitions
named for what they are (`bernsteinTail d v L t`, `conditionNumber A`), never inline formulas
repeated across statements.

Renames after the `v0.1` tag keep `@[deprecated (since := "YYYY-MM-DD")] alias old := new` for one
release.

## 5. Statements

### 5.1 Types

- Scalars: `{𝕜 : Type*} [RCLike 𝕜]` for all deterministic matrix theory, including matrix
  functions and the concentration layer's vocabulary. ℝ only where the mathematics is real:
  Gaussian and Rademacher laws, the real spectral quantities they feed. A real corollary of a `𝕜`
  theorem is stated only when a downstream user needs it in `ᵀ` form that `simp` cannot produce.
- Index types: `{m n : Type*} [Fintype m] [Fintype n]` plus `[DecidableEq _]` where Mathlib
  needs it. `Fin k` is appropriate where its order or recursion carries content: the `k` sorted
  columns of an SVD produced by an existence theorem, total recursions
  defining algorithms. A theorem stated over `Fin` because a dependency was is a defect to fix at
  the dependency.
- Transpose: lemmas are stated with `ᴴ`. Over ℝ, `Aᴴ = Aᵀ` is `Matrix.conjTranspose_eq_transpose_of_trivial`
  (`@[simp]`). Transpose twins are not written.
- Vectors: `n → 𝕜` with `⬝ᵥ` as the pairing; the Euclidean norm is `‖WithLp.toLp 2 x‖`
  (Mathlib's `EuclideanSpace`), never `Real.sqrt (x ⬝ᵥ x)` in a statement.
- Matrix norms are named functions (§5.3), never `‖A‖`: Mathlib's four matrix norms are scoped
  instances and a signature cannot show which one is open. `‖A‖` appears only in bridge lemmas
  and, under a file-level `open scoped Matrix.Norms.L2Operator`, in the C*-algebra and
  functional-calculus files that need Mathlib's normed API.

### 5.2 Shape

- Every hypothesis explicit, minimal, and an instance of a named interface (§5.4). Nothing that
  follows from another hypothesis (`(A + B).IsHermitian` next to `hA hB`; `Measurable X` next to
  `HasLaw X ν μ`).
- Definitions are total, Mathlib-style (`⁻¹` of a singular matrix is `0`, `eigenvalue A k` is `0`
  for `k` out of range, `conditionNumber` of a singular matrix is the ratio to its smallest nonzero
  singular value); the theorem carries the hypothesis that excludes the junk value and the
  definition's docstring states the junk value. Real-valued quantities stay real-valued: a `⊤` in
  `ℝ≥0∞` costs coercions, `positivity` and `gcongr` at every use.
- **A quantified index of a padded sequence carries its range.** `∃ k, -3 < eigenvalue A k` is
  true of every matrix (take `k` out of range, where the value is `0`), and a hypothesis
  `∀ k, 0 < eigenvalue A k` is never satisfied. An index of `eigenvalue` or `singularValues`
  quantified by `∃`, or by `∀` in a hypothesis, has a bound (`k < Fintype.card n`, `k + 1 = Fintype.card n`,
  `k ∈ Finset.range r`), unless the statement is meant to hold of the padding and does
  (`A.PosSemidef ↔ ∀ k, 0 ≤ eigenvalue A k`). The module docstring of
  `NLAlib/Matrix/Spectral/Eigenvalues.lean` explains this to users.
- Two-sided bounds are two theorems. A conjunction is split when its parts are useful alone.
  Equational forms (`eigenvalue A k = ⨆ … ⨅ …`) are stated when a user would `rw` with them;
  inequality halves are corollaries.
- General form first, corollaries after, in the same file. A corollary specialises the field, the
  index type, or a hypothesis; it does not restate the proof.
- Probabilistic results are stated as tails, not sample sizes: the primary theorem bounds the
  failure probability in closed form (`μ.real {ω | ¬ good ω} ≤ 2 d exp (−ε² k / (3 L))`); the
  "`k ≥ …` suffices" form is a corollary. Inverting the tail is where ugly constants and side
  conditions appear, so it is done once, not by every consumer.
- Constants, in order of preference:
  1. The source's constant, when the source gives one and the proof reaches it.
  2. An explicit constant the proof reaches, **behind a name** when it is not the source's or is
     not small: `gaussianEmbeddingSampleSize d ε δ := …`, `sparseEmbeddingConstant : ℝ := …`,
     with the docstring stating the source's value and the gap. Improving the proof then changes
     one definition and no signature.
  3. A universal constant with no explicit value in the literature becomes a named
     `noncomputable def` chosen from an existence lemma quantified outside all dimensions, and is
     documented as such.
  A bare `∃ C` never appears in a statement: quantified after the dimensions it is unusable, and
  it hides loose proofs.
- Spectral statements never quantify over `hA.eigenvectorBasis i`; they take an eigenvector `u`
  with `A *ᵥ u = c • u` and `‖WithLp.toLp 2 u‖ = 1`, an invariance equation `A * U = U * M` with
  `HasOrthonormalCols U`, or speak of `eigenvalue A k`.
- No proof term inside a statement. Introduce the needed hypothesis or state through a definition.
- Dot notation: a lemma whose first explicit argument is `hA : A.IsHermitian` lives in
  `Matrix.IsHermitian`; one about an `IsSVD` lives in `IsSVD`.

### 5.3 Vocabulary

One spelling per concept. The table is the current state; it grows only through a design note
(§8) and the PR that adds the row together with its bridge. Rows for later layers are added when
those layers are designed.

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| spectral norm | `specNorm A : ℝ`, no `DecidableEq` needed | `specNorm_eq_norm` (L2Operator scope), `rfl` |
| Frobenius | `frobNorm A`; its square is always `frobNorm A ^ 2`; `frobInner A B : ℝ` | `frobNorm_eq_norm` (Frobenius scope); `frobInner_eq_re_trace` |
| scalar multiple of the identity in a Loewner inequality | `(a : ℝ) • (1 : Matrix n n 𝕜)`, the real scalar action; a real scalar on a `𝕜`-matrix is `a • A` | Mathlib's; `RCLike.real_smul_eq_coe_smul` |
| spectral bound on a factor | Loewner form on its Gram matrix: `a • 1 ≤ Tᴴ * T`, `Tᴴ * T ≤ b • 1` | `smul_one_le_conjTranspose_mul_self_iff`, `specNorm_sq_le_iff_conjTranspose_mul_self_le` |
| ε-net of the unit sphere | `Metric.IsCover ε (Metric.sphere 0 1) N` in `EuclideanSpace 𝕜 n` | Mathlib's |
| singular values | `singularValues A : ℕ → ℝ` (antitone, zero-padded, no `DecidableEq`); largest is index `0`, the smallest of a matrix with `n` columns is index `k` with `k + 1 = card n` | `singularValues_eq_linearMap`, `rfl` |
| eigenvalues of Hermitian `A` | `eigenvalue A k : ℝ`, `k : ℕ`: sorted non-increasing for `k < card n`, `0` beyond and for non-Hermitian `A`; largest is `eigenvalue A 0`; the smallest is index `k` with `k + 1 = card n`, and bounds on it are stated in Loewner form `c • 1 ≤ A` | `hA.eigenvalue_eq_eigenvalues₀` to Mathlib's `hA.eigenvalues₀` |
| SVD | `IsSVD A U σ V`: thin, any finite column type, `σ : r → ℝ` nonnegative, `A = U * diagonal σ * Vᴴ` | — |
| best rank-`k` approximation | `truncatedSVD A k`; optimal errors `singularValues A k` (spectral) and `frobNorm (A - truncatedSVD A k)` (Frobenius) | `frobNorm_sub_truncatedSVD_sq` |
| spectral gap | `eigengap A k`, `singularGap A k`, indexed by the dimension `k` of the leading subspace | `eigengap_succ`, `singularGap_succ` |
| pseudoinverse | `pinv A`, every shape and rank; recognised through `IsPinv A B` (the four Penrose identities); full-rank formulas are lemmas, not definitions | `pinv_of_isUnit`; `mul_pinv : A * pinv A = rangeProjector A` |
| full row rank | `Function.Injective Aᴴ.mulVec` | — |
| least-squares solution | `IsLeastSquaresSolution A b x`; the optimal residual is `(1 - rangeProjector A) *ᵥ b` | `isLeastSquaresSolution_iff_isMinOn` |
| condition number | `conditionNumber A : ℝ := specNorm A * specNorm (pinv A)`, any shape | `conditionNumber_of_isUnit` |
| generalized Schur complement | `C - Bᴴ * pinv A * B`, no definition | — |
| majorization | `Majorized x y`, `WeaklyMajorized x y` for `x y : ι → ℝ` on one finite index type, unsorted, through `sumLargest x k`; between sorted spectra, the partial-sum inequalities are stated directly | `majorized_iff_exists_doublyStochastic`; `sumLargest_fin_eq_sum_range` |
| Ky Fan norm | `kyFanNorm k A`, the sum of the `k` largest singular values; eigenvalue partial sums are written `∑ i ∈ Finset.range k, eigenvalue A i` | `kyFanNorm_eq_sum_range`, `kyFanNorm_one` |
| nuclear and Schatten norms | `nuclearNorm A`; `schattenNorm q A` with `q : ℝ≥0∞`; `1 ≤ q` and `q ≠ 0` are explicit hypotheses; Hölder exponents through Mathlib's `ENNReal.HolderTriple` and `ENNReal.HolderConjugate` | `schattenNorm_one`, `schattenNorm_two`, `schattenNorm_top` |
| unitarily invariant norm | `Φ.matrixNorm A` for `Φ : SymmetricGauge` (a norm on `ℕ →₀ ℝ` invariant under permutations and absolute values, extending Mathlib's `Seminorm`), one gauge for every shape; "for every unitarily invariant norm" is `∀ Φ : SymmetricGauge`; `singularValuesFinsupp A` appears only as the argument of a gauge | `lpGauge_matrixNorm`, `kyFanGauge_matrixNorm` |
| distance between subspaces | the matrix `(1 - Q) * P` of the two orthogonal projectors (`IsStarProjection`; `U * Uᴴ` for a frame, `rangeProjector X` in general), in a norm; no named gap. Its singular values are the sines of `principalAngle X Y k` (ℕ-indexed, non-decreasing, `π / 2` beyond the smaller dimension) | `HasOrthonormalCols.cos_principalAngle`: cosines are `singularValues (Uᴴ * V) k` |
| tangent of the angles between subspaces | `tangentMatrix U Y := (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹` for a frame `U` and a basis `Y` with as many columns, in a norm; the acute hypothesis is `IsUnit (Uᴴ * Y)` | `HasOrthonormalCols.singularValues_tangentMatrix` |
| oblique projector | `P` with Mathlib's `IsIdempotentElem P`; from two bases, `X * (Yᴴ * X)⁻¹ * Yᴴ` | — |
| matrix square root | Mathlib's `CFC.sqrt A`; no NLAlib definition | — |
| principal minor | `principalMinor A s` for `s : Finset n`; determinants of Hermitian matrices are compared through `RCLike.re A.det` | `principalMinor_univ`, `Matrix.IsHermitian.det_eq_re_det` |
| spectral equivalence | the Loewner sandwich `a • M ≤ A ≤ b • M`; its consequence is `conditionNumber (Cᴴ * A * C) ≤ b / a` for `Cᴴ * M * C = 1` | `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset` |
| index shift in a statement | an auxiliary `d` with an equation, `hd : card p + d = card n`; never truncated subtraction | — |
| Loewner order | `A ≤ B` under `open scoped MatrixOrder` | `Matrix.le_iff` |
| PSD, PD, Hermitian | `A.PosSemidef`, `A.PosDef`, `A.IsHermitian` | Mathlib's |
| quadratic form | `quadForm A z := star z ⬝ᵥ (A *ᵥ z) : 𝕜` | `Matrix.PosSemidef` form |
| orthonormal columns | `HasOrthonormalCols Q := Qᴴ * Q = 1`, always as this hypothesis; rows are `HasOrthonormalCols Qᴴ`; a unitary is a square `Q` with this property | `hasOrthonormalCols_iff_orthonormal`, `hasOrthonormalCols_iff_mem_unitaryGroup` |
| orthogonal projector (predicate) | `IsStarProjection P` | Mathlib's |
| projector onto a column space | `rangeProjector A`, every shape and rank | `toEuclideanLin_rangeProjector` |
| projection residual | `(1 - rangeProjector Y) * A`, no definition | `one_sub_rangeProjector_mul` expands it |
| column space, range containment | `LinearMap.range A.mulVecLin`; `LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin` | Mathlib's |
| full column rank | `Function.Injective A.mulVec`, as a hypothesis | Mathlib's; `isUnit_conjTranspose_mul_self_iff`, `mulVec_injective_iff_rank_eq` |
| Gram matrix, Schur complement | `Aᴴ * A`; `D - C * A⁻¹ * B`; no definitions | Mathlib's |
| Rayleigh quotient | `rayleighQuotient A x : ℝ := re (quadForm A x) / ‖toLp 2 x‖ ^ 2` | `rayleighQuotient_eq_toEuclideanCLM` |
| column selection as a matrix | `selectionMatrix s`; a bare selection is `A.submatrix id s` | `mul_selectionMatrix` |
| Hermitian dilation | `dilation A := fromBlocks 0 A Aᴴ 0` | `dilation_def`, `rfl` |
| plane rotation | `planeRotation u v c s`, `c s : ℝ` | — |
| function of a Hermitian matrix | Mathlib's `cfc f A`, `f : ℝ → ℝ`; no `matrixExp`, `matrixLog`, `traceExp`, `lambdaMax` names | `cfc_eq_mul_diagonal_mul_conjTranspose`, `Matrix.IsHermitian.re_trace_cfc` |
| matrix exponential, logarithm | `NormedSpace.exp A`; `cfc Real.log A` | `Matrix.IsHermitian.exp_eq_cfc` |
| real power, absolute value, positive part, inverse square root | Mathlib's `A ^ r`, `CFC.abs A` (rectangular: `CFC.sqrt (Aᴴ * A)`), `A⁺`, `(CFC.sqrt A)⁻¹`, under `MatrixOrder` | `CFC.rpow_eq_cfc_real`, `CFC.abs_eq_cfc_norm`, `Matrix.PosDef.inv_sqrt_eq_cfc` |
| location of the spectrum | `spectrum ℝ A ⊆ s`; for an interval the Loewner sandwich `a • 1 ≤ A`, `A ≤ b • 1` | `Matrix.IsHermitian.spectrum_subset_iff` |
| transfer from `𝕜` to `ℂ` | `complexify A = A.map RCLike.toComplex` | `complexify_cfc`, `complexify_le_complexify_iff` |
| operator convexity | `OperatorConvexOn s f`; convex combinations as `a • A + b • B`, `a + b = 1` | `OperatorConvexOn.cfc_smul_add_smul_le` |
| derivative of a matrix curve | entrywise, `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t` | `Matrix.hasDerivAt_iff_forall_apply` |
| triangular, unit triangular | Mathlib's `Matrix.IsUpperTriangular`, `Matrix.IsLowerTriangular`; `IsUnitLowerTriangular`, `IsUnitUpperTriangular` | `Matrix.BlockTriangular` |
| trapezoidal, Hessenberg, tridiagonal, quasi-triangular | `IsUpperTrapezoidal`, `IsUpperHessenberg`, `IsTridiagonal`, `IsUpperQuasiTriangular`, for matrices indexed by `Fin` | — |
| factorizations | predicates `IsLU A L U`, `IsCholesky A L`, `IsQR A Q R` (thin); a full QR is a square `Q` with `HasOrthonormalCols Q` and `IsUpperTrapezoidal R` | — |
| algorithm | a total recursion indexed by the step (`gaussState`, `householderState`), breakdown as a value, a realisation theorem under a hypothesis on the computed pivots | `isLU_luLower_luUpper` |
| elimination | `eliminationStep A t`; in the natural order `gaussState A k`; along pivots `l.foldl eliminationStep A` | `gaussState_eq_foldl` |
| leading principal minor | `principalMinor A (Finset.Iic i)`; proper ones `Finset.Iio i` | — |
| polar factor | `polarFactor A = A * pinv (CFC.sqrt (Aᴴ * A))`, every shape and rank | `IsSVD.polarFactor_eq` |
| rank-revealing column selection | `C = A.submatrix id e` with coefficients `pinv C * A` and residual `(1 - rangeProjector C) * A`; certificate `IsLocalMaxVolume A e f` | — |
| eigenvalues of a general matrix | a listing, `IsEigenvalueListing A d`: `A.charpoly = ∏ i, (X - C (d i))` | `Matrix.IsHermitian.isEigenvalueListing_eigenvalue` |
| normal, diagonalisable | Mathlib's `IsStarNormal A`; `IsDiagonalizable A` | `isDiagonalizable_iff_isSemisimple` |
| inertia | `inertiaPos A`, `inertiaNeg A` | `Matrix.IsHermitian.inertiaPos_add_inertiaNeg` |
| spectral radius | `specRadius A : ℝ`, for matrices over `𝕜` | Mathlib's `spectralRadius ℂ (complexify A)` |
| Gershgorin radius | `gershgorinRadius A i` | `gershgorinRadius_def`; Mathlib's `eigenvalue_mem_ball` |
| Hermitian part | `hermitianPart A` | `hermitianPart_eq_selfAdjointPart` |
| structured matrices | Mathlib's `A ⊗ₖ B`, `Matrix.circulant v`; `fourierMatrix n`, `walshHadamard R b`, `cauchyMatrix x y` | `Matrix.IsHadamard` |
| random matrix | `X : Ω → Matrix m n 𝕜`, `Measurable X` (global `Matrix.instMeasurableSpace`, `ForMathlib`) | — |
| law | `HasLaw X ν μ` | Mathlib's |
| tail | `μ.real {ω | ¬ good ω} ≤ δ` | — |
| expectation | `∫ ω, f (X ω) ∂μ` (Bochner) | — |
| sub-Gaussian | `HasSubgaussianMGF X c μ` | Mathlib's |

Rows the remaining Matrix design notes are expected to add: majorization, the Schatten family
and unitarily invariant norms, the principal-angle / subspace-distance interface. Rows from the
foundations stage (`docs/design/Matrix-Foundations.md`) are in the table.

### 5.4 Interfaces and reusable hypotheses

This is the rule the prototype library broke most, and the one that matters most for proving new
things. There, a sketch had five different conclusion shapes across five distributions, isotropy
was a four-hypothesis bundle repeated in every estimator theorem, orthonormality was sometimes a
predicate and sometimes `Qᵀ * Q = 1`, and nothing downstream could take "any sketch with
property P" as an input.

- **A hypothesis is a named interface.** A `structure` or `def … : Prop` with a docstring, a
  constructor lemma from the obvious raw condition, and the API lemmas a consumer needs
  (`HasOrthonormalCols.conjTranspose_mul_self`, `.mul_conjTranspose_isHermitian`, `.specNorm_le_one`).
  Theorems take the interface, never the raw condition.
- **A conclusion is an interface too.** A theorem that establishes a property concludes the named
  predicate (`IsSubspaceEmbedding (S ω) U ε`), so the next theorem can take it as a hypothesis
  without unpacking. Distribution-specific theorems (Gaussian, SRHT, sparse) all conclude the same
  predicate with the same tail shape; the downstream theorem (sketch-and-solve, range finder) takes
  that predicate and knows nothing about the distribution.
- **Parametrise over the interface, not the instance.** "Any `Q` with `HasOrthonormalCols Q`
  whose range contains `K`" rather than "the Arnoldi basis"; "any random `S` with
  `HasOSE S U ε δ`" rather than "`gaussianMatrix`"; "any unitarily invariant norm" rather than
  Frobenius and spectral separately, when the proof is the same. The instance-specific theorem is
  then a corollary: the instance satisfies the interface.
- **Interfaces are designed, not accreted.** Introducing one is a §8 decision: what it bundles,
  what it leaves as separate hypotheses, which Mathlib notion it bridges to, which downstream
  theorems will consume it. A local predicate invented to make one file compile is a defect.
- **Fewer, broader interfaces.** Before adding a new one, check whether an existing one with one
  more field, or one fewer, covers the case. The test is the downstream user: can they state their
  theorem with the interfaces that exist?

## 6. Docstrings and citations

Every public declaration has a docstring. It is the record the documentation site, the search
index and the literature map are generated from, so its parts are fixed:

```lean
/-- **Weyl's inequality.** For Hermitian `A`, `B` and `i + j` a valid index,
`λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)`, eigenvalues non-increasing and indexed from `0`.
[HornJohnson2013, Theorem 4.3.1]; stated there over ℂ with eigenvalues in increasing order, here
over any `RCLike` field, any finite index type, non-increasing.
Result: weyl-inequality -/
theorem eigenvalue_add_le ...
```

1. **First sentence:** what it asserts, in words, with the bold name of the result if it has one.
2. **Citation:** `[Key, label]` where `Key` is an entry of `docs/references.bib` and `label` is the
   printed theorem, section or equation, for every source where this result or the result it
   generalises or specialises appears. Several are separated by `;`. Then the relation to the
   printed statement: generalisation, different constant, tail form instead of sample size,
   different indexing. The citation is provenance for the reader and the literature map; it does
   not bind the statement or the proof. A helper or a bridge needs no citation; it says what it
   is for.
3. **Port provenance** when the proof was ported: the old library's declaration name, or the
   external library and commit.
4. **`Result: <id>`** on its own last line, for a declaration that *is* the formal statement of a
   named mathematical result (`weyl-inequality`, `eckart-young-frobenius`). Several ids are
   comma-separated. Helpers carry none. The ids key the literature map maintained in the
   `explore` repository; a new id is fine, a misspelt existing one is a review comment.

Module docstrings follow Mathlib: `# Title`, a paragraph, `## Main results` listing the names.

`scripts/check_refs.py` fails CI on an unknown bibliography key or a malformed result id.
`docs/references.bib` grows by adding the entry before citing it; keys are `AuthorSurnames + year`.

## 7. Proofs, `sorry` and the scaffold library

- `import NLAlib` is sorry-free; `scripts/Audit.lean` checks every reachable declaration against
  `propext`, `Classical.choice`, `Quot.sound` only.
- A statement worth having before its proof goes in `NLAlibScaffold/` under the same path it will
  have in `NLAlib/`, with the full docstring, a `sorry` body, and a line
  `Proof: <sketch, what it reduces to, estimated difficulty>` in the docstring. It compiles, is
  linted and documented like library code, and may import `NLAlib` but is never imported by it.
  When proved, the declaration moves to `NLAlib/` in the same PR that proves it. A scaffold is for
  a statement you are confident of; it is not a place to park the hard part of the result you are
  claiming.
- Proofs are free to differ from any source. Choose the argument that is shortest in Lean and
  reuses the most library API; a clever proof from the literature is worth nothing if a
  three-line one through Mathlib exists.
- Proof style: tactic proofs, `simp only` with named lemmas rather than bare `simp` on large
  goals, no `simp_all`, no `decide` on anything but tiny finite goals, `nlinarith`/`positivity`/
  `gcongr` welcome. A proof over about 80 lines is split into named lemmas. Terminal `exact?`
  and `apply?` do not appear in committed code.
- Instances: no global instance on a Mathlib type unless it is the one Mathlib would add
  (`Matrix.instMeasurableSpace` is the one exception, in `ForMathlib`). No `attribute [instance]`
  at file level.

## 8. Designing a stage

The library is built in stages, one at a time, in dependency order. Each stage covers one
coherent body of mathematics (the norms; the spectral core; perturbation theory; …) and begins with
a design note, `docs/design/<Stage>.md`, written by the orchestrating agent and approved by the
maintainer before any proof is written. The note answers, with specifics:

1. **Objects.** Which definitions this stage introduces, each as a §5.3 row with its Mathlib
   bridge, and which Mathlib objects it uses directly instead.
2. **Interfaces.** Which hypothesis predicates and structures (§5.4) this stage introduces or
   extends, what each bundles, and the raw-condition constructor for each.
3. **Statement shapes.** For each headline result, the exact Lean signature: field, index types,
   interfaces taken, conclusion form, constants handling (§5.2), and the corollaries it will have.
   Written out, not described.
4. **Consumers.** For each interface and headline statement, which later stage or layer will use
   it and in what form; a statement with no foreseeable consumer is questioned.
5. **Files.** The file split for this stage, each file a topic of 300 to 500 lines, with the
   declarations it will hold in order.
6. **Material.** Which files of the prototype library were read, what in them is reused (as
   mathematics to cover, as proof material), and what is deliberately not reproduced and why
   (twins, bundles, transport lemmas, local interfaces).
7. **Open questions** for the maintainer, with a recommendation each.

For each bridge and each API lemma that restates a Mathlib fact, the note names the Mathlib lemma
it found, or records "searched, none". An exact overlap ships as an `alias` or a one-line proof
citing the Mathlib lemma, never as an independent proof. A file added or split during the stage is
recorded as a dated amendment to the note's file list when it happens, not first in the stage
report.

**Deviations from Mathlib are recorded.** Where Mathlib has a notion and the library states things
with another one (a different index type, a total function in place of one that takes a proof, a
named function in place of a scoped instance, a new predicate next to a Mathlib one), the design
note says so, and `docs/design/Mathlib-deviations.md` gets an entry in the same commit: what
Mathlib has, what the library does, why, what it costs, and the bridge lemma. A deviation with no
entry is a defect. (Maintainer, 2026-10-14.)

The note is reviewed as a design, with the question "will this be the interface people reach for
in five years?", before the stage is implemented. The implementation PRs reference it. A
divergence discovered during implementation is a one-line amendment to the note, approved the
same way.

## 9. Workflow and checks

One topic per branch and PR. A PR adds or changes one file's worth of mathematics (a new topic
file, or a coherent change to one), plus the consumers it breaks, plus the ledger entry if it
ports material. Before opening it, run:

```
LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold
lake exe mk_all --lib NLAlib --check && lake exe mk_all --lib NLAlibScaffold --check
lake env lean scripts/Audit.lean
lake env lean scripts/Lint.lean
python3 scripts/check_refs.py
```

The PR description contains a read-back: for each headline theorem, what the Lean statement says,
written from the Lean alone. The reviewer checks the read-back against the design note and the
source, the names against §4, the hypotheses against §5.4, the vocabulary against §5.3. A green CI
plus one approving review merges; a change to a §5.3 row or a §5.4 interface needs two.

Mathlib bumps are their own PRs and are tagged. Releases are tagged with the Lean version they
build against (`v4.33.1-nlalib.1`).

## 10. Building without running out of memory

The development machine has 8 cores and 31 GB. A default `lake build` runs 8 Lean workers; heavy
files on top of Mathlib take 3 to 6 GB each, and the terminal gets killed. Rules:

- **Never run a bare `lake build`.** Use `LEAN_NUM_THREADS=4 lake build <targets>`; `LEAN_NUM_THREADS=2` when another build,
  a Lean language server with files open, or another agent is running on the machine.
- Lake 5 has no `-j` flag. The `LEAN_NUM_THREADS` environment variable caps the number of Lean
  processes Lake runs at once (measured: `LEAN_NUM_THREADS=N` gives exactly `N`).
- Check a file with `lake lean`, not `lake env lean`. `lake env lean` ignores the options in
  `lakefile.toml`, so `autoImplicit` is on (a typo becomes a variable) and the Mathlib linters are
  off. `lake lean <file> -- -M 8000` applies them and builds missing imports first; prefix it with
  `LEAN_NUM_THREADS=2`.
- **One build per machine at a time.** If `lake build` is running, wait for it.
- **Check a single file** with `lake lean NLAlib/Matrix/Spectral/Weyl.lean -- -M 8000`
  (`-M` caps that process at 8000 MB). Imports of other NLAlib modules need their `.olean`:
  `LEAN_NUM_THREADS=4 lake build NLAlib.Matrix.Norms.Spectral` first.
- **Run long builds in the background with a log**: `LEAN_NUM_THREADS=4 lake build NLAlib > /tmp/build.log 2>&1`,
  then read the log. Do not stream a full build into a terminal or an agent's context.
- **Keep files under 500 lines and proofs under 80 lines.** Memory and heartbeat blowups come from
  single huge elaborations: a `simp` with hundreds of lemmas, an `nlinarith` on a goal with many
  atoms, a `decide` on a finite type. Split the proof.
- **Never `import Mathlib` or `import Mathlib.Tactic`**, even in a scratch file inside the
  repository; both load far more than needed.
- `lake exe cache get` fetches Mathlib's oleans once; never build Mathlib from source.

## 11. Rules for agents

- Read this file, then the current stage's design note in `docs/design/` (or the port brief if the
  note is not yet written), then `docs/port/status.md`, then the file you are about to write.
- The library is built **sequentially**: one stage at a time, and within a stage one file at a
  time unless the design note marks files independent. At most two proof agents run at once. A
  proof agent normally owns one file; two or three small files that the note marks independent of
  the rest of the stage, or that form a short import chain, may be given to one agent together
  (amended 2026-10-14 after stage M1, where this was done and worked). Do not fan out proving agents across a
  stage; the point of the sequence is that each file is designed against the ones before it.
- The orchestrating agent writes the design note (§8) before any implementation and stops for
  the maintainer's approval. It does not inherit the prototype's organisation, interfaces or
  names; it reads them as material and decides.
- The orchestrator writes design notes, skeletons and file reviews itself; sends design notes,
  unsettled interface questions and stage reports to `model: "fable"` agents for bounded review
  (comments in, comments out, never proofs or long tasks); delegates proofs to `model: "opus"`
  agents, one file at a time; and delegates mechanical passes (docstring formatting, ledger
  updates, `mk_all`, grep checks) to `model: "sonnet"` or `model: "haiku"` agents. Every `Agent`
  call passes `model` explicitly; an omitted model inherits the session's, with its usage limits,
  and that has killed agents mid-work before.
- Report state on disk (`docs/port/status.md`) at every stopping point so a successor can continue
  from a cut-off.
- Search before proving: Mathlib, then the already-built `NLAlib/`, then the prototype.
- Do not weaken a statement to make it provable. If a proof fails within budget, the statement goes
  to `NLAlibScaffold` with a `Proof:` note and the difficulty you observed, and you move on.
- Do not add work beyond the brief: no new theorems "while you are there", no cleanup of files you
  do not own, no new §5.3 rows or §5.4 interfaces outside a design note. Note what you saw in
  `docs/port/status.md`.
- Never commit or push without being asked; never run a bare `lake build` (§10).
