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

Every rule a script checks carries its id in brackets where it is stated, [F1], and the check's
messages cite the same id. The ids are a letter for the area and a number: N names (§4,
`scripts/check_names.py`); F file template, P placement and layers, S source and proof style,
T types and statement shape, V vocabulary, B bounds, D docstrings, M notation, C citations,
R result ids, G design records (`scripts/check_rules.py`, §9.1), E programs (§5.5;
`scripts/Programs.lean` and `scripts/check_rules.py`). `python3 scripts/check_rules.py
--list` prints every id with its level; a rule with no id is judged by review.

Sections: Setup · 1 Ground rules · 2 Layout · 3 File template · 4 Names · 5 Statements ·
6 Docstrings and citations · 7 Proofs and what each library may contain · 8 Designing new
material · 9 Workflow, checks and pull requests · 10 Building without running out of memory ·
11 AI agents.

## Setup

```
git clone https://github.com/NLA-lib/nlalib.git && cd nlalib
lake exe cache get                                  # Mathlib's .olean files; never build Mathlib
LEAN_NUM_THREADS=4 lake build NLAlib > /tmp/build.log 2>&1
```

The toolchain is pinned in `lean-toolchain` (Lean and Mathlib `v4.33.1`); `elan` installs it.
The checks also need Python 3.11 or later and, for the LaTeX check, Node 20 with
`npm install --no-save --no-package-lock katex@0.16.22`. Read §10 before your first build: an
unbounded `lake build` can exhaust the memory of a laptop. Before opening a PR, run
`bash scripts/stage_check.sh` (§9).

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
7. **No `sorry` on `main`.** A PR contains complete, checked work (§9); how you stage unfinished
   work on your own branch is up to you. No `axiom`, no `native_decide`, no `admit`, no weakening
   a statement to make it provable.
8. **Files are topics, not proofs.** Up to about 1000 lines [F10] (Mathlib's linter limit of
   1500 is the hard ceiling; maintainer, 2026-10-14), one mathematical topic, ordered
   definitions → basic API → main theorems → corollaries. No file named after a paper, a round of
   work, or a proof technique. No "toolkit", "bundle" or "part 2" files [F11].
9. **Design before code** (§8). New material of any size starts with a written design: the
   objects, the hypothesis interfaces, the statement shapes, and how later layers will consume
   them. Existing developments elsewhere are material to evaluate, not a template.

## 2. Layout

```
NLAlib/
  ForMathlib/      general facts not about NLAlib's objects, headed upstream;
                   files named after the Mathlib file they would join            (layer −1)
  Computation/     programs over memory buffers: syntax, runs, counts, memory,
                   substitution, exact arithmetic, BLAS kernels, oracle
                   implementations (amended 2026-10-23)                           (layer 0)
  Matrix/          deterministic matrix analysis                                  (layer 0)
  Polynomial/      scalar approximation theory and the function classes it
                   approximates (amended 2026-10-17)                             (layer 0)
  Krylov/          deterministic Krylov theory                                      (layer 1)
  Probability/     scalar and vector probability, concentration                  (layer 1.5)
  RandomMatrix/    Gaussian, sub-Gaussian, Haar random matrices                     (layer 2)
  Sketching/       sketch distributions and their embedding guarantees             (layer 3)
  Regression/      randomized least squares and linear-system solvers
                   (sketch-and-solve, sketch-and-precondition, iterative
                   sketching, Kaczmarz, sketch-and-project)                      (layer 3.5)
  LowRank/         low-rank approximation                                          (layer 4)
  Estimation/      trace and spectral-density estimation                         (layer 4.5)
  LowerBounds/     lower bounds for randomized algorithms and named estimators,
                   one subfolder per topic (LowRank/, ...); may import every
                   other folder, and only LowerBounds imports it                  (layer 5)
NLAlibTools/       tools, not library: the Float interpreter, the NumPy emitter, examples
docs/              references.bib, constants.toml (named bounds), targets.toml and targets.approved
                   (the target registry, §5.5), rules/ (rule data, generated digest),
                   design/ (design notes), renames/ (rename maps, §4.2 N12)
scripts/           the checks (§9): stage_check.sh, Audit.lean, Replay.lean, Lint.lean,
                   Programs.lean, Targets.lean, check_rules.py, check_refs.py, ..., and their tests
```

The subdirectories of each layer are decided in that layer's design note (§8), not in advance.
A file in `NLAlib/Computation` imports only Mathlib, `NLAlib.ForMathlib` and `NLAlib.Computation`
[E5], so that programs over the library's objects live in their topic files
(`docs/design/Computation.md`, D7).
A module imports only modules of its own layer number or lower [P1]: folders with the same number
(Computation, Matrix and Polynomial, all 0) may import one another, except where P11 and E5 below
forbid it. `scripts/check_rules.py` (`LAYER`) holds the same numbers, and a top-level folder
missing from it is a P1 error; `python3 scripts/check_rules.py --files <files>` checks the import
rules of the files you changed in seconds. The half layers follow
the imports, not the topics (maintainer decision 2026-10-25): Probability may import Krylov, and
Krylov does not import Probability; Regression may import Sketching, and Sketching does not
import Regression; LowRank may import Regression; Estimation may import LowRank, and LowRank
does not import Estimation. Lower bounds (for the matrix-vector query model and for specific
estimators) combine Krylov, probability, sketching and low-rank theory, so they form the top layer
`LowerBounds/` with topic subfolders (maintainer decision LOWERBOUNDS-FOLDER, 2026-10-25); a lemma
they need that is not itself a lower bound stays in its topic folder. Randomized linear-system
solvers (Kaczmarz, sketch-and-project) live in Regression; finding results by task is the
explorer's job. The root file `NLAlib.lean` is generated by `lake exe mk_all --module --lib
NLAlib`; CI checks it is current.
There are no per-directory aggregator files: a user imports the file they need [P2].

`ForMathlib` holds only facts with no NLAlib vocabulary in their statement [P4]. They are declared
in the Mathlib namespace they would have upstream [P5], marked in the module docstring as upstream
candidates [P6], in a file named after the Mathlib file they would join [P7], and deleted when
they land in Mathlib.

The boundary (maintainer, 2026-10-19). A topic file keeps every statement about NLAlib's objects
and every statement in Mathlib's matrix or probability vocabulary whose subject is a Mathlib
hypothesis structure (`theorem _root_.Matrix.PosSemidef.foo`, §3). What belongs in ForMathlib is
the general fact about neither: a scalar inequality, a real-analysis or measure-theory lemma with
no matrix or measure in its statement [P9], and a declaration outside `NLAlib` that is not API of
a Mathlib hypothesis structure [P8].

The Polynomial layer is exempt from P9 (maintainer decision 2026-10-20): its headline scalar
results (Chebyshev residuals and minimax, approximation of $1/x$, interpolation of Stieltjes
functions) stay in `NLAlib/Polynomial`. The condition is that the
layer stays easy to upstream to Mathlib as a whole: a file in `NLAlib/Polynomial` imports only
Mathlib, `NLAlib.ForMathlib` and `NLAlib.Polynomial` [P11], and ForMathlib imports nothing outside
ForMathlib (P1), so it never depends on the layer. The checker grants the exemption only while P11
holds.
Weyl's majorant lemma `NLAlib.sum_range_rpow_le_of_forall_prod_range_le`
is scalar but stays in `NLAlib/Matrix/Majorization/Horn.lean`, allowlisted for P9 (maintainer
decision 2026-10-20): its proof needs the Matrix layer's majorization theory, which ForMathlib
cannot import (P1).

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

* `Matrix.IsHermitian.eigenvalue_add_le`: Weyl's inequality `λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)`.
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

- The header linter requires a non-empty `Authors:` line [F1]; use `NLAlib contributors` unless
  the file keeps the attribution of material taken from elsewhere.
- `module`, then `public import` lines (specific Mathlib files; never `import Mathlib` or
  `import Mathlib.Tactic` [F3]), then the module docstring, then `@[expose] public section` [F2].
- Everything is in `namespace NLAlib` [F4], except lemmas whose subject is a Mathlib structure
  hypothesis (`Matrix.IsHermitian`, `Matrix.PosSemidef`), which are declared
  `theorem _root_.Matrix.IsHermitian.foo` inside `namespace NLAlib` so that `hA.foo` works [P8].
- No file-level `set_option` [F5] (`maxHeartbeats`, `backward.*`, a linter), `open Classical` or
  `open scoped Classical` [F7]. A single declaration that needs a heartbeat bump gets
  `set_option maxHeartbeats N in` on that declaration, with a comment saying why [F6].
- `private` for proof-local helpers only. A lemma a second file could want is public, named by §4,
  documented by §6, and placed in the file that owns its subject, not the file that needed it
  first (review list: [S5]).
- `noncomputable section` is not opened at file level [F8]; mark individual definitions
  `noncomputable` when Lean requires it.
- Lines are at most 100 characters [S7]. Only a line that one identifier or a URL makes long may
  be longer (a declaration name on its own line, a backticked name in a docstring), under
  `set_option linter.style.longLine false in` on that declaration with a comment saying why, and
  only where a line needs it [S8] (maintainer, 2026-10-19). CI builds with `--wfail`, so the
  Mathlib linters (header, long lines, `open Classical`, `set_option`) fail the build.

## 4. Names

Mathlib's conventions, https://leanprover-community.github.io/contribute/naming.html, in full,
refined below into one grammar for the whole library (maintainer, 2026-10-19; the evidence and
the decisions are in `docs/design/Naming.md`). Each rule has an id, N1 to N18, which briefs,
reviews and `scripts/check_names.py` cite. A theorem's name is its conclusion read left to
right, then its hypotheses: someone who knows the statement can guess the name, and someone
who reads the name knows the statement.

| Kind | Case | Examples |
|---|---|---|
| theorem, lemma | `snake_case` | `frobNorm_nonneg`, `specNorm_mul_le`, `singularValues_add_le` |
| definition returning data | `lowerCamelCase` | `specNorm`, `singularValues`, `rangeProjector` |
| structure, class, Prop-valued predicate | `UpperCamelCase` | `IsSVD`, `HasOrthonormalCols`, `IsSubspaceEmbedding` |
| namespace, file, directory | `UpperCamelCase` | `NLAlib.Matrix.Spectral.Weyl` |

### 4.1 Grammar

```
name    ::= [ns "."] body
body    ::= ["exists_forall_"] concl {"_of_" hyp}                      -- N3; N17 for exists_forall_
concl   ::= det | stat | "exists_" concl | "forall_" concl | "ae_" concl
det     ::= expr ["_" rel ["_" rhs]]                                  -- `=` usually omitted
rel     ::= "le" | "lt" | "eq" | "ne" | "iff" | "nonneg" | "pos" | "mem" | "subset"
          | "ge" | "gt"                                -- only when the second argument varies
expr    ::= head {"_" arg}                             -- left to right from the head symbol (N2)
          | norm "_sub_" alg                           -- an error ‖exact − computed‖ (N10)
          | expr "_sq" | expr "_pow" | expr "_rpow"    -- after the argument (N6)
rhs     ::= tokens of the right side, only to tell coexisting theorems apart (N8)
stat    ::= "integral_" expr ["_sq"] "_" rel [rhs]     -- 𝔼 f(X); 𝔼‖·‖² has _sq (N13)
          | "variance_" expr "_" rel [rhs]             -- Var[f(X); μ]
          | "measureReal_" event "_" ("le" | "eq") [rhs] -- μ.real {ω | event} ≤ δ (N14)
          | "measure_" event "_" ("le" | "eq") [rhs]   -- μ {ω | event} ≤ δ, in ℝ≥0∞
          | ("integrable_" | "measurable_" | "aemeasurable_" | "memLp_") expr
event   ::= [subject "_"] ("ge" | "gt" | "le" | "lt") ["_" rhs]  -- subject first (N15)
          | "not_" pred | "exists_" event | subject "_mem"
hyp     ::= "hasLaw_" law | class | predicate | relation              -- N9
ns      ::= the predicate or structure a lemma is API for, or the sketch-property interface it
            consumes (N9); never `HasLaw`, never for exists_forall_
```

Tokens are the lowerCamel forms of the identifiers in the statement (`IsSVD` → `isSVD`), in the
spellings of §4.3. Hypothesis variables are `h`-prefixed (`hA`, `hQ`, `hk`). Examples:

| statement | name |
|---|---|
| `frobNorm (A * B) ≤ specNorm A * frobNorm B` | `frobNorm_mul_le_specNorm_mul_frobNorm` |
| `δ * Φ.matrixNorm (V⊥ᴴ * U) ≤ Φ.matrixNorm R` (Davis–Kahan) | `mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue` |
| `re (quadForm A (xs - cgIterate A b x₀ q)) ≤ …` | `re_quadForm_sub_cgIterate_le_four_mul_pow` |
| `IsLU A (luLower A) (luUpper A)` | `isLU_luLower_luUpper` |
| `singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k` | `singularValues_sq` |
| `∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤ …`, Gaussian `X` | `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` |
| `μ.real {ω \| b < frobNorm (A - rsvd A (X ω))} ≤ δ` | `measureReal_frobNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix` |
| the same under an injection interface `hS : HasSubspaceInjection …` | `HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le` |
| `μ.real {ω \| ε * nuclearNorm A < \|A.trace - hutchpp A (S ω) (G ω)\|} ≤ δ` | `measureReal_abs_trace_sub_hutchpp_gt_mul_nuclearNorm_le_of_isSubgaussianVector` |
| `μ.real {ω \| ¬ (a • 1 ≤ (X ω)ᴴ * X ω)} ≤ δ` (Loewner) | `measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix` |
| `μ.real {ω \| ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ …` (subject a variable) | `measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix` |
| `Var[fun ω => hutchpp A (S ω) (G ω); μ] ≤ …` | `variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix` |
| its O(·) form | `exists_forall_variance_hutchpp_le_of_hasLaw_gaussianMatrix` |

### 4.2 Rules for every topic

| id | rule | checked |
|---|---|---|
| N1 | Case by kind, as in the table above; acronyms follow Mathlib's grouping (`rsvd`, `earlyTruncatedRSVD`). | yes |
| N2 | The first token is the head of the conclusion's left side, or an operator on its leftmost spine (`mul_` for `c * f x ≤ …`), `nonneg`/`pos` for `0 ≤ x`/`0 < x` (`frobNorm_nonneg`), or the layer `exists_`, `forall_`, `ae_`. Mathlib's dot-notation readings stand: `(M).submatrix e f` is `submatrix_…`, a measure `ν.map f` is `ν_map_…` (`gaussianReal_map_add_const`). | yes |
| N3 | The conclusion part ends at the first `_of_` and names the main relation: `le`, `lt`, `ne`, `iff`, `mem`, `subset`, `nonneg`, `pos`; `eq` may be omitted, as in Mathlib; `ge`/`gt` only when the second argument is the one that varies; Mathlib's `mono`, `anti`, `monotone`, `antitone` count. Nothing of the conclusion comes after `_of_` (`variance_quadForm_le_of_hasLaw_rademacherVector`, not `…_of_hasLaw_rademacherVector_le`). | yes |
| N4 | Every token that is a library function occurs in the statement, conclusion tokens in the conclusion and hypothesis tokens in the hypotheses. Matrix notation counts (`conjTranspose` for `ᴴ`, `mulVec` for `*ᵥ`, `integral` for `∫`). | yes |
| N5 | One token per concept: the spellings of §4.3, never a synonym. | the listed synonyms |
| N6 | A power comes after its argument, for every head: `frobNorm_sub_rsvd_sq`, `singularValues_sq`, `sum_singularValues_sub_sq_le` (Mathlib's `norm_sub_sq`). `^ 2` is `sq`, `^ n` is `pow`, `^ r` (real) is `rpow`. Mathlib's own `sq_abs`, `sq_sqrt` are Mathlib's names, not a pattern. | `sq_f` anywhere, `pow_f` on the left |
| N7 | No source, chapter, author, lemma number or project in a name, and no word for how good a bound is (`_sharp`, `_improved`, `_tight`, `_v2`, `_strong`) or for its role (`aux`, `main`, `key`); the source goes in the docstring (§5.2 "Numerical bounds"). Classical names stay where the subject uses them (`bernstein`, `hansonWright`, `freedman`). | yes |
| N8 | Right-side tokens only to tell coexisting theorems apart (§5.2 rule 4): `measureReal_norm_sq_ge_mul_card_le` next to `measureReal_norm_sq_le_mul_card_le`. A bound that improves keeps its name. | no |
| N9 | Hypotheses. A law is the suffix `_of_hasLaw_<law>`, for any law (`_of_hasLaw_gaussianMatrix`, `_of_hasLaw_haarFrame`). A distribution class is `_of_<class>`, also when it is an instance argument (`_of_isSubgaussianVector`, `_of_isLeftUnitarilyInvariant`, `_of_isIsotropic`). A sketch-property interface that is the main hypothesis (`HasSubspaceInjection`, `IsObliviousSubspaceInjection`, `HasSubspaceEmbedding`, `IsObliviousSubspaceEmbedding`, `HasJLMoment`, `HasJLProperty`, `HasProjectionCostPreserving`, `HasGramTraceMoment`, `HasMatrixMGFBound`) is the namespace: `HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`. The API of a predicate or structure lives in its namespace (§5.2, dot notation), and so does a theorem whose first explicit argument is one of the hypotheses of N18. `HasLaw.` is never a namespace for a consumer; a law hypothesis first is named by its suffix. Other hypotheses are named only when they distinguish the theorem from a sibling. | the law suffix |
| N10 | Errors are `exact − computed`, so names say `norm_sub_<alg>`: `frobNorm_sub_rsvd`, `quadForm_sub_cgIterate`, `trace_sub_hutchpp`. A name never has `<alg>_sub_…`, except `<alg>_sub_truncatedSVD` (the optimal approximation of the algorithm's output, `frobNorm_rsvd_sub_truncatedSVD_le`), `<iterate>_sub_mem` (`x_k − x_0 ∈ K`, not an error) and a final `_sub` of a linearity lemma (`lanczosFA_sub`). | yes |
| N11 | Named quantities and tail expressions are definitions named for what they are (`bernsteinTail d v L t`, `pseudoConditionNumber A`), never inline formulas repeated across statements. A named bound (`docs/constants.toml`) ends in its kind: `…Constant` (an absolute constant), `…Factor` (a multiplier in a bound), `…Tail` (a failure probability), `…Bound` (another bound), `…Ratio`, `…Dim` (a sample size, §4.4). | the suffix |
| N12 | Renames. Before the `v0.1` tag a rename needs no alias; it is listed in a rename map `docs/renames/<YYYY-MM>-<topic>.json` (`{"renames": [{"old", "new", "rule"}], "statementChanged": [names]}`, full names), from which the explorer redirects old `#d/` links. A deleted declaration is listed with `"removed": true` and, as `new`, the declaration that now carries its content (a Jensen corollary's higher-moment theorem, T15). After `v0.1`, a rename keeps `@[deprecated (since := "YYYY-MM-DD")] alias old := new` for one release, and is also listed in a rename map. | no |
| N18 | Dot notation (§5.2, maintainer, 2026-10-19: enforced). A root-namespace theorem whose first explicit argument is `hA : A.IsHermitian`, `hA : A.PosSemidef`, `hA : A.PosDef` (of any matrix expression, `(fromBlocks A B Bᴴ C).PosSemidef` included), `h : IsSVD A U σ V` or `hU : HasOrthonormalCols U` lives in that predicate's namespace (`Matrix.IsHermitian.eigenvalue_add_le`, `HasOrthonormalCols.gramSchmidtQ_mul_left`), so that `hA.eigenvalue_add_le hB k` works; the name then drops the `_of_<predicate>` it no longer needs (`Matrix.PosSemidef.re_det_fromBlocks_le`). A theorem already in an interface namespace (N9) or another predicate's namespace keeps it, and asymptotic forms stay in the root namespace (N17). | yes |

### 4.3 Spellings

The tokens of the §5.3 vocabulary, and the ones a statement shape forces:

| concept | token | not |
|---|---|---|
| `Aᴴ * A`, `A * Aᴴ` | `conjTranspose_mul_self`, `mul_conjTranspose_self` | `gram`, which is Mathlib's `Matrix.gram` |
| `fromBlocks A 0 0 B` | `fromBlocks_zero₁₂_zero₂₁` (Mathlib's `fromBlocks_zero₁₂`, `fromBlocks_zero₂₁`) | `fromBlocks_diagonal`, which Mathlib uses for `fromBlocks (diagonal d₁) 0 0 (diagonal d₂)` |
| column space, kernel `LinearMap.range A.mulVecLin`, `…ker` | `range`, `ker`: `range_rangeProjector`, `range_le_iff_exists_mul`, `_of_range_le` | `range_mulVecLin` |
| intrinsic dimension | `intrinsicDimension` | `intrinsicDim` |
| `singularValues A k ^ 2` | `singularValues_sq` (N6) | `sq_singularValues` |
| an algorithm's output | the definition's name: `rsvd`, `nystrom`, `generalizedNystrom`, `rbki`, `nystromBKI`, `earlyTruncatedRSVD`, `sketchAndSolve`, `hutchpp`, `girardHutchinson`, `cgIterate`, `lanczosFA` | `rangeFinder`, `randomizedSVD` |
| norms, pseudoinverse, eigenvalues | `specNorm`, `frobNorm`, `nuclearNorm`, `schattenNorm`, `matrixNorm`, `pinv`, `eigenvalue` | `opNorm`, `pseudoinverse`, `eig` |
| the vector 2-norm `‖WithLp.toLp 2 x‖` | `norm` | |

### 4.4 Rules for one topic

**Probability: statistics and tails** (Probability, RandomMatrix, and every tail bound elsewhere).

| id | rule | checked |
|---|---|---|
| N13 | A statistic on the left is the prefix: `integral_` (Bochner `∫ … ∂μ`), `variance_` (`Var[…]`), `covariance_` (`cov[…]`), `condExp_` (`μ[…\|m]`); never `expected`, `expectation`, `mean`. A mean square `∫ ‖·‖ ^ 2` has `_sq` before the relation (`integral_frobNorm_sub_rsvd_sq_le`); a mean `∫ ‖·‖` has none. | yes |
| N14 | The tail prefix follows the statement, in every namespace, Mathlib's included: `μ.real {…}` is `measureReal_`, `μ {…}` (in `ℝ≥0∞`) is `measure_`. Tails are stated in `μ.real`. (Replaces the 2026-10-14 rule, namespaced `measure_`; Mathlib's own `HasSubgaussianMGF.measure_ge_le` keeps its name.) | yes |
| N15 | The event comes first, subject first: the subject is the side that mentions `ω`, named by its tokens, then the event relation, then the tail relation: `{ω \| b < X ω}` is `X_gt`, `{ω \| b ≤ X ω}` `X_ge`, `{ω \| X ω ≤ b}` `X_le`, `{ω \| X ω < b}` `X_lt`; so a tail name has two relation tokens, `measureReal_frobNorm_sub_rsvd_sq_gt_le`. A subject with no token (a variable function `f (X ω)`) is left out: `measureReal_ge_integral_add_le`. A scalar event is stated positively, `{ω \| b < err ω}`, never `{ω \| ¬ (err ω ≤ b)}`, and `¬ ∀ i, x i ≤ b` is stated `∃ i, b < x i` (`measureReal_exists_…_gt_le`). `¬` stays only where there is no `<` form: a Loewner inequality, a conjunction, a named predicate (`measureReal_not_isSubspaceEmbedding_le`); the name says `not_`. | yes |

**Sketching, low-rank approximation, regression.**

| id | rule | checked |
|---|---|---|
| N16 | A sample size (rows of a sketch) is a named bound `<sketch><property>Dim`: `jlDim`, `gaussianEmbeddingDim`, `gaussianInjectionDim`, `subgaussianJLDim`, `subgaussianEmbeddingDim`, `countSketchEmbeddingDim`, `samplingEmbeddingDim`, `samplingInjectionDim`, `projectionCostTailDim`; never `…Rows`, `…Size`. The theorem that assumes it is `_of_<size>_le`. Algorithm errors follow N10 and the algorithm tokens of §4.3; interfaces give the namespace (N9). | the suffix (N11) |

**Trace estimation.** No rule of its own: errors are `tr A − estimate` (N10), so
`trace_sub_hutchpp`, `integral_norm_trace_sub_girardHutchinson_sq`,
`measureReal_abs_trace_sub_hutchpp_ge_le` (flipped 2026-10-19 from `estimate − trace`).

**Matrix and Krylov.** No rule of its own beyond §4.3. A leading scalar factor is named
(`mul_matrixNorm_…` for `δ * ‖·‖`), so a reader looking for the measured quantity skips
`mul_`. `x_k − x_0 ∈ K` statements are `cgIterate_sub_mem_krylovSpace` (N10).

**Asymptotic forms** (§5.2 rule 3).

| id | rule | checked |
|---|---|---|
| N17 | The name of an `O(·)` corollary is derived from its explicit theorem: `exists_forall_`, then the explicit conclusion part (for `integral_`/`variance_` names, up to its main relation, the right-side tokens dropped), then `_of_singularGapRatio_pos` for a gapped bound, then the explicit hypotheses without the size threshold (`_of_jlDim_le`, `_of_le_card`, …). It is in the root namespace: `∃ C` comes before every hypothesis, so dot notation is impossible. `integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix` → `exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`. | yes |

### 4.5 Exceptions and the allowlist

There are no standing exceptions. A name the checker misreads, because the grammar has no
readable form for its statement or the splitter misparses it, goes in `scripts/names_allow.toml`
with the rule it is excused from and a one-line reason that says why:

```
[[allow]]
name = "exists_bernstein_exponent"
rule = "N3"
reason = "names the optimised exponent θ; the inequality has no readable token form"
```

An entry is reviewed like code and is never the fix for a real violation. The checker fails on a
stale entry (the declaration is gone or no longer breaks the rule), so the list stays short.

### 4.6 Checking

`scripts/check_names.py` checks the rules marked "yes" on the extraction (§9), and prints
`N<k> <name>: <what is wrong>`; in CI it runs inside `scripts/check_rules.py` (§9.1). It reads
Lean's pretty-printed statements, so it cannot judge what needs judgement: whether a right side
should be named (N8), whether a hypothesis deserves mention or a side condition the namespace
(N9), argument order inside a long deterministic name, classical names, or whether a `_sub_` is
an error or a comparison. Reviewers check those.

## 5. Statements

### 5.1 Types

- Scalars: `{𝕜 : Type*} [RCLike 𝕜]` for all deterministic matrix theory, including matrix
  functions, and in the probability layers wherever the proof allows: random vectors, isotropy,
  moments, quadratic forms, matrix-valued integrals, matrix concentration. ℝ only where the
  object is a real number (scalar MGFs and tails, the norm or singular value a tail is about) and,
  for now, for the Gaussian and Haar matrix laws, whose interfaces are still stated over `𝕜`
  (maintainer, 2026-10-14). A real corollary of a `𝕜`
  theorem is stated only when a downstream user needs it in `ᵀ` form that `simp` cannot produce.
- Index types: `{m n : Type*} [Fintype m] [Fintype n]` plus `[DecidableEq _]` where Mathlib
  needs it. `Fin k` is appropriate where its order or recursion carries content: the `k` sorted
  columns of an SVD produced by an existence theorem, total recursions
  defining algorithms. A theorem stated over `Fin` because a dependency was is a defect to fix at
  the dependency (review lists: [T6], and [T7] for theorems over ℝ only).
- Transpose: lemmas are stated with `ᴴ` [T5]. Over ℝ, `Aᴴ = Aᵀ` is `Matrix.conjTranspose_eq_transpose_of_trivial`
  (`@[simp]`). Transpose twins are not written.
- Vectors: `n → 𝕜` with `⬝ᵥ` as the pairing; the Euclidean norm is `‖WithLp.toLp 2 x‖`
  (Mathlib's `EuclideanSpace`), never `Real.sqrt (x ⬝ᵥ x)` in a statement [T1].
- A real quantity used where Mathlib wants `ℝ≥0` (a sub-Gaussian proxy `c * ‖specNorm A‖₊ ^ 2`, a
  coefficient `‖a i‖₊ ^ 2 * c`) is written with `‖·‖₊`, never `⟨x, hx⟩` or `Real.toNNReal x` [T2].
- Matrix norms are named functions (§5.3), never `‖A‖` [T4]: Mathlib's four matrix norms are scoped
  instances and a signature cannot show which one is open. `‖A‖` appears only in bridge lemmas
  and, under a file-level `open scoped Matrix.Norms.L2Operator`, in the C*-algebra and
  functional-calculus files that need Mathlib's normed API. `Matrix.Norms.L2Operator` is the only matrix norm scope
  opened for analysis [T3], including integrals and conditional expectations of matrix-valued
  functions; never `Matrix.Norms.Frobenius` or `Matrix.Norms.Elementwise`, whose topology does not
  match Mathlib's global matrix topology, so `Integrable`, `Continuous` and limits do not elaborate
  under them (`docs/design/Mathlib-deviations.md` entry 13; maintainer, 2026-10-14).

### 5.2 Shape

- Every hypothesis explicit, minimal, and an instance of a named interface (§5.4). Nothing that
  follows from another hypothesis (`(A + B).IsHermitian` next to `hA hB`; `Integrable X μ` next to
  `HasSubgaussianMGF X c μ`; not `Measurable X` next to `HasLaw X ν μ`, which gives only
  `AEMeasurable`). A hypothesis the proof does not use is dropped, not renamed `_h` [T13].
- Definitions are total, Mathlib-style (`⁻¹` of a singular matrix is `0`, `eigenvalue A k` is `0`
  for `k` out of range, `pseudoConditionNumber` of a singular matrix is the ratio to its smallest
  nonzero singular value); the theorem carries the hypothesis that excludes the junk value and the
  definition's docstring states the junk value. Real-valued quantities stay real-valued: a `⊤` in
  `ℝ≥0∞` costs coercions, `positivity` and `gcongr` at every use.
- **A quantified index of a padded sequence carries its range.** `∃ k, -3 < eigenvalue A k` is
  true of every matrix (take `k` out of range, where the value is `0`), and a hypothesis
  `∀ k, 0 < eigenvalue A k` is never satisfied. An index of `eigenvalue` or `singularValues`
  quantified by `∃`, or by `∀` in a hypothesis, has a bound (`k < Fintype.card n`, `k + 1 = Fintype.card n`,
  `k ∈ Finset.range r`), unless the statement is meant to hold of the padding and does
  (`A.PosSemidef ↔ ∀ k, 0 ≤ eigenvalue A k`) [T12]. The module docstring of
  `NLAlib/Matrix/Spectral/Eigenvalues.lean` explains this to users.
- Two-sided bounds are two theorems. A conjunction is split when its parts are useful alone
  (review list: [T11]).
  Equational forms (`eigenvalue A k = ⨆ … ⨅ …`) are stated when a user would `rw` with them;
  inequality halves are corollaries.
- General form first, corollaries after, in the same file. A corollary specialises the field, the
  index type, or a hypothesis; it does not restate the proof.
- Probabilistic results are stated as tails, not sample sizes: the primary theorem bounds the
  failure probability in closed form (`μ.real {ω | ¬ good ω} ≤ 2 d exp (−ε² k / (3 L))` for a
  predicate `good`; a scalar event is stated positively, `{ω | b < err ω}`, §4 N15); the
  "`k ≥ …` suffices" form is a corollary. Inverting the tail is where ugly constants and side
  conditions appear, so it is done once, not by every consumer. Tails are in `μ.real` [T14].
- **A lower moment from a higher one is not a separate theorem** (maintainer, 2026-10-19) [T15].
  The primary statement is the moment the proof gives, usually the squared one. When a source
  prints the Jensen-weakened form (HMT Theorem 10.5's $\mathbb{E}\|\cdot\|_{\mathsf{F}}$), the
  higher-moment theorem's docstring says so in a sentence, so that a search on the citation finds
  it: "[HalkoMartinssonTropp2011, Theorem 10.5] prints the first-moment form …, which follows from
  this bound by Jensen's inequality (`ProbabilityTheory.integral_le_sqrt_integral_sq`)." A Jensen
  corollary stays only if another library proof uses it, allowlisted with "used by …"; otherwise
  that proof takes the Jensen step itself. A lower-moment bound proved independently (HMT 10.6's
  $\mathbb{E}\|\cdot\|_2$) is a separate result.
- **Numerical bounds** (maintainer, 2026-10-14). A later
  improvement, and a new proof whose bound is incomparable with the old one, must fit without a
  rename:
  1. A name says what the statement is, never how good it is: no `_sharp`, `_improved`,
     `_tight`, `_v2`, `_strong`. Classical names stay where the subject uses them (`bernstein`,
     `hoeffding`, `hansonWright`, `freedman`).
  2. The source's constant, when the proof reaches it and it is small, is written in the
     statement (Hoeffding's `exp (-t ^ 2 / (2 * c))`). Any other constant or tail function is a
     definition,
     `irreducible_def hansonWrightConstant : ℝ := …`, `matrixBernsteinTail d v L t : ℝ`, whose
     docstring gives the source's value, the value proved and the gap. Consumers use only its API,
     chosen to stay true when the bound improves: positivity, monotonicity where a consumer inverts
     the tail, and a one-sided explicit comparison
     (`1 / (256 * exp 2) ≤ hansonWrightConstant`). An improvement of the same shape changes the
     body and that comparison, no statement and no name.

     When a proof establishes a stronger bound under the same hypotheses, expose that bound
     through the existing theorem and named-bound API. Record its relation to the source rather
     than weaken it solely to reproduce the source's constant or an earlier approved draft.
     Changes to hypotheses, mathematical scope or public interfaces retain their normal design
     review.

     **A docstring that uses a named bound shows its current value inside its equations**
     (maintainer, 2026-10-15). Statements keep the name; the docstring writes the value in place
     of the constant, in the formula itself. One exception (maintainer, 2026-10-19): a sample size
     that uses a named constant may write it as $C$ in its formula and give the value in the same
     docstring, "with <!-- value subgaussianJLConstant -->$C = 1/36$", as the header of
     `docs/constants.toml` says; the span after the marker is the value, as everywhere else:
     ```
     … the expected error satisfies <!-- value gaussianPinvSpecNormBound k \ell -->
     $$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
     \Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
     \frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
     \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$$
     ```
     and may name the Lean constant in prose nearby ("the constant is
     `gaussianPinvSpecNormBound k ℓ`"). A value with no formula to sit in (a module docstring's
     list, the constant's own docstring) is a math span of its own. The value marker
     `<!-- value NAME ARGS -->` annotates the math span right after it (only whitespace, at most
     one line break, and other markers between; one marker per constant in the span; no closing
     marker): `NAME` is the bound, `ARGS` this docstring's LaTeX for its explicit arguments, in
     Lean order. A marker never begins a line, since Markdown reads such a line as an HTML block
     and ends the paragraph; it follows the text before it. The registry `docs/constants.toml`
     holds, per named bound, a LaTeX template of its value (`latex`, `#1`, `#2`, … for the
     arguments; optionally `display`, a `\frac` form for displays), its Lean body as text and a
     hash of the body. `scripts/check_constants.py` (CI) fails when a body differs from the
     registry, when an annotated span does not contain the filled template (whitespace ignored;
     grouping around it, `\bigl(…\bigr)` or `{…}`, is the docstring's choice), and when a
     docstring names a registered bound in backticks without a marker of it (the opt-out
     `<!-- mention NAME -->` is for a name mentioned only in passing, and is rare); the
     definition's own docstring shows its value. The script's docstring has the exact syntax.
     A new named bound gets its registry entry in the commit that defines it [B1]; the check
     treats a public definition whose name ends in `Constant`, `Bound`, `Tail`, `Dim`, `Factor`,
     `Size`, `Rows`, `Rate`, `Exponent` or `Threshold` as a named bound (a `…Ratio` is not
     detected; register it by hand). To change a
     bound: edit its body; in the registry move `latex` (and `display`) to `previous_latex` (and
     `previous_display`) and write the new value; run
     `python3 scripts/check_constants.py --update NAME`, which replaces the previous value by the
     new one inside every annotated span, records the new body and hash and drops the
     `previous_*` fields; and let CI confirm. Nothing checks the LaTeX against the Lean
     mathematically: the reviewer compares `lean_body` and `latex`, which sit side by side in
     the diff, on every change to a bound.
  3. A universal constant with no explicit value in the literature is a named
     `noncomputable def` chosen from an existence lemma quantified outside all dimensions, and is
     documented as such. A bare `∃ C` never appears in a statement [B2]: quantified after the
     dimensions it is unusable, and it hides loose proofs.
     **Asymptotic forms** (maintainer, 2026-10-16). A sample-size result of the subspace-embedding
     or algorithm kind (JL, OSE, OSI, the $(1+\varepsilon)$ bounds of the low-rank algorithms,
     PCP constructors) also gets the computer-science reading "$O(\cdot)$ suffices" as a corollary:
     `∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n … : Type} [instances] (μ) (A) (sketches) (k) (ε) …,
     hypotheses → 0 < ε → ε ≤ ε₀ → C * (threshold without constants) ≤ size → conclusion`. Every
     constant is existential and comes before every dimension, type, measure, matrix and
     parameter, so it is absolute; a dimension dependence the result really has (a $\log n$)
     appears in the threshold, never inside $C$. Index types are fixed to `Type` [B4]. A result
     of this kind without its asymptotic form is on a review list [B5]. The name starts
     `exists_forall_`, derived from the explicit theorem's name (§4 N17); the proof instantiates
     the explicit theorem, which stays primary and whose docstring names its asymptotic form. The
     asymptotic form's docstring says "$O(\ldots)$ suffices" in words [B3] and ends with the line
     `Asymptotic: <full name of the explicit theorem>` (before any `Result:` line), so tools (the
     explorer, `scripts/check_refs.py`) can find and check these corollaries.
  4. Incomparable bounds coexist, each named by what distinguishes it: its hypothesis
     (`_of_bounded`, `_of_variance_le`) or the parameter its bound is in (`_intrinsicDimension`). Each
     docstring says in which regime it is better and names the other.
  5. A statement whose bound is the minimum of two others is added only when both have identical
     hypotheses and side conditions.
  6. A dominated result (the new bound is at least as good in every regime) is reproved from the
     new one and keeps its name when consumers cite its simpler form; otherwise it becomes
     `@[deprecated]` and is removed after a release.
  7. A bound is stated in its readable form when a sharper form differs from it only by a factor
     that is at most an absolute constant and tends to 1 as the bound becomes small (maintainer,
     2026-10-20) [B6]. The typical case is a Chebyshev value: the proof bounds
     $1/T_q(\cdot)^2 = \operatorname{sech}^2(x) = 4e^{-2x}/(1 + e^{-2x})^2$, and the statement
     gives $4e^{-2x}$, as the sources print it (the CG bound $4\rho^{2q}$, the gapped block Krylov
     factor). The docstring gives the sharp form in one sentence and names the lost factor
     ($(1 + e^{-2x})^2 \le 4$). A separate sharp theorem is added only when another proof in the
     library uses it; an exact (equality) result, such as the CG worst case, is a result of its
     own and stays.
- Spectral statements never quantify over `hA.eigenvectorBasis i` [T8]; they take an eigenvector `u`
  with `A *ᵥ u = c • u` and `‖WithLp.toLp 2 u‖ = 1`, an invariance equation `A * U = U * M` with
  `HasOrthonormalCols U`, or speak of `eigenvalue A k`.
- No proof term inside a statement [T9]. Introduce the needed hypothesis or state through a
  definition.
- A bound variable that only meets `•` gets its type written: `∀ θ : ℝ, … θ • Y ω …`. Without it
  Lean elaborates `θ : ℕ` (`ℕ` acts on every additive monoid), and the hypothesis silently quantifies
  over natural numbers (2026-10-14) [T10].
- Dot notation: a lemma whose first explicit argument is `hA : A.IsHermitian` lives in
  `Matrix.IsHermitian`; one about an `IsSVD` lives in `IsSVD` (§4 N18, checked for `IsHermitian`,
  `PosSemidef`, `PosDef`, `IsSVD` and `HasOrthonormalCols`).

### 5.3 Vocabulary

One spelling per concept. The table is the current state; it grows only through a design note
(§8) and the PR that adds the row together with its bridge. Checked spellings: raw orthonormality
`Qᴴ * Q = 1` [V1], truncated `Fintype.card n - k` [V2], a spelled-out singular-value ratio [V3],
`frobNorm A * frobNorm A` [V4], the forbidden names of the rows below [V5]; every Lean name this
file (outside §4) or `docs/design/Mathlib-deviations.md` cites exists [V6]; a public definition
in neither is on a review list [V7]. Rows for later layers are added when
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
| SVD | `IsSVD A U σ V`: thin, any finite column type, `σ : r → ℝ` nonnegative, `A = U * diagonal σ * Vᴴ`; the library's chosen one (the lexicographically least thin SVD) is `svdU A`, `svdV A` | `isSVD_svdU_svdV` |
| generalized SVD of a pair | `IsGSVD A B X c s`: invertible common right coordinates, diagonal Gram matrices with nonnegative `c`, `s`, and `c i ^ 2 + s i ^ 2` equal to zero or one; no row-dimension or rank assumption | `exists_isGSVD`, `IsGSVD.rank_fromRows`, `IsGSVD.ker_inf_ker_eq_span`; no Mathlib GSVD predicate (searched) |
| best rank-`k` approximation | `truncatedSVD A k`, the truncation of `svdU A`, `svdV A` (Borel measurable in `A`); any best approximation `IsBestRankApprox A k Y`; optimal errors `singularValues A k` (spectral) and `frobNorm (A - truncatedSVD A k)` (Frobenius) | `frobNorm_sub_truncatedSVD_sq`, `measurable_truncatedSVD`, `isBestRankApprox_iff_exists_isSVD` |
| spectral gap | `eigengap A k`, `singularGap A k`, indexed by the dimension `k` of the leading subspace | `eigengap_succ`, `singularGap_succ` |
| relative singular gap | `singularGapRatio A i j := (σᵢ - σⱼ) / (σᵢ + σⱼ)`, Tropp–Webber's γ, indices from `0`, in `[0, 1]` for `i ≤ j`; `0` when both singular values vanish; gap-dependent Krylov bounds take it, never the ratio `σⱼ / σᵢ` spelled out (2026-10-18) | `one_sub_singularGapRatio_div_one_add_singularGapRatio` (`(1 - γ) / (1 + γ) = σⱼ / σᵢ`), `singularGapRatio_nonneg`, `singularGapRatio_le_one`; Mathlib has none |
| pseudoinverse | `pinv A`, every shape and rank; recognised through `IsPinv A B` (the four Penrose identities); full-rank formulas are lemmas, not definitions | `pinv_of_isUnit`; `mul_pinv : A * pinv A = rangeProjector A` |
| full row rank | `Function.Injective Aᴴ.mulVec` | — |
| least-squares solution | `IsLeastSquaresSolution A b x`; the optimal residual is `(1 - rangeProjector A) *ᵥ b` | `isLeastSquaresSolution_iff_isMinOn` |
| condition number | `pseudoConditionNumber A : ℝ := specNorm A * specNorm (pinv A)`, any shape; ignores zero singular values, so it is the classical `σ_max / σ_min` only at full column rank (renamed from `conditionNumber`, 2026-10-14) | `pseudoConditionNumber_of_isUnit`, `pseudoConditionNumber_of_injective` |
| generalized Schur complement | `C - Bᴴ * pinv A * B`, no definition | — |
| majorization | `Majorized x y`, `WeaklyMajorized x y` for `x y : ι → ℝ` on one finite index type, unsorted, through `sumLargest x k`; between sorted spectra, the partial-sum inequalities are stated directly | `majorized_iff_exists_doublyStochastic`; `sumLargest_fin_eq_sum_range` |
| Ky Fan norm | `kyFanNorm k A`, the sum of the `k` largest singular values; eigenvalue partial sums are written `∑ i ∈ Finset.range k, eigenvalue A i` | `kyFanNorm_eq_sum_range`, `kyFanNorm_one` |
| nuclear and Schatten norms | `nuclearNorm A`; `schattenNorm q A` with `q : ℝ≥0∞`; `1 ≤ q` and `q ≠ 0` are explicit hypotheses; Hölder exponents through Mathlib's `ENNReal.HolderTriple` and `ENNReal.HolderConjugate` | `schattenNorm_one`, `schattenNorm_two`, `schattenNorm_top` |
| unitarily invariant norm | `Φ.matrixNorm A` for `Φ : SymmetricGauge` (a norm on `ℕ →₀ ℝ` invariant under permutations and absolute values, extending Mathlib's `Seminorm`), one gauge for every shape; "for every unitarily invariant norm" is `∀ Φ : SymmetricGauge`; `singularValuesFinsupp A` appears only as the argument of a gauge | `lpGauge_matrixNorm`, `kyFanGauge_matrixNorm` |
| distance between subspaces | the matrix `(1 - Q) * P` of the two orthogonal projectors (`IsStarProjection`; `U * Uᴴ` for a frame, `rangeProjector X` in general), in a norm; no named gap. Its singular values are the sines of `principalAngle X Y k` (ℕ-indexed, non-decreasing, `π / 2` beyond the smaller dimension) | `HasOrthonormalCols.cos_principalAngle`: cosines are `singularValues (Uᴴ * V) k` |
| tangent of the angles between subspaces | `tangentMatrix U Y := (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹` for a frame `U` and a basis `Y` with as many columns, in a norm; the acute hypothesis is `IsUnit (Uᴴ * Y)` | `HasOrthonormalCols.singularValues_tangentMatrix` |
| oblique projector | `obliqueProjector X S := X * pinv (S * X) * S` for a basis `X : Matrix m r 𝕜` and a sketch `S : Matrix k m 𝕜`, total, every shape and rank, no proof argument; it projects onto the range of `X` under `(S * X).rank = X.rank`; the predicate form is Mathlib's `IsIdempotentElem P`; from two bases, `obliqueProjector X Yᴴ`, the formula `X * (Yᴴ * X)⁻¹ * Yᴴ` being a lemma (Mathlib-deviations entry 19) | `isIdempotentElem_obliqueProjector`, `IsIdempotentElem.obliqueProjector_eq` (every idempotent is one), `range_obliqueProjector`, `obliqueProjector_of_isUnit`, `obliqueProjector_conjTranspose_self` (`= rangeProjector X`) |
| matrix square root | Mathlib's `CFC.sqrt A`; no NLAlib definition | — |
| principal minor | `principalMinor A s` for `s : Finset n`; determinants of Hermitian matrices are compared through `RCLike.re A.det` | `principalMinor_univ`, `Matrix.IsHermitian.det_eq_re_det` |
| spectral equivalence | the Loewner sandwich `a • M ≤ A ≤ b • M`; its consequence is `pseudoConditionNumber (Cᴴ * A * C) ≤ b / a` for `Cᴴ * M * C = 1` | `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset` |
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
| function of a Hermitian matrix | Mathlib's `cfc f A`, `f : ℝ → ℝ`; no `matrixExp`, `matrixLog`, `traceExp`, `lambdaMax` names | `HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`, `Matrix.IsHermitian.re_trace_cfc` |
| matrix exponential, logarithm | `NormedSpace.exp A`; `cfc Real.log A` | `Matrix.IsHermitian.exp_eq_cfc` |
| real power, absolute value, positive part, inverse square root | Mathlib's `A ^ r`, `CFC.abs A` (rectangular: `CFC.sqrt (Aᴴ * A)`), `A⁺`, `(CFC.sqrt A)⁻¹`, under `MatrixOrder` | `CFC.rpow_eq_cfc_real`, `CFC.abs_eq_cfc_norm`, `Matrix.PosDef.inv_sqrt_eq_cfc` |
| uniform scalar/function approximation | `Metric.IsUniformApproxOn g f s ε`: pointwise `dist (g x) (f x) ≤ ε` on `s`, with only a pseudometric codomain; degree, continuity, compactness and nonnegative error remain separate | `Metric.isUniformApproxOn_iff`; `Metric.isUniformApproxOn_iff_dist_le` uses Mathlib `ContinuousMap.dist_le` on compact domains |
| normalized Chebyshev residual | `chebyshevResidual a b q : ℝ[X]`, the affine composition of Mathlib `Polynomial.Chebyshev.T`, normalized at zero for `0 < a < b`; scalar approximation bounds use the shared metric predicate | `eval_chebyshevResidual`, `degree_chebyshevResidual_le`, `eval_chebyshevResidual_zero`; inverse/division junk values documented in the definition |
| residual minimax value | `residualMinimax s q : ℝ`, $\inf_p\sup_{x\in s}\lvert p(x)\rvert$ over real $p$ with `p.degree ≤ q` and `p.eval 0 = 1`, for `s : Set ℝ`; meaningful for bounded `s` (a finite spectrum, `Set.Icc a a'`), junk `0` for empty `s` and for unbounded `s` at `q ≥ 1`; the spectrum-optimal CG, PCG and MINRES bounds take it | `residualMinimax_le` (any residual polynomial bounds it), `residualMinimax_Icc` (the Chebyshev value on an interval, from `isLeast_chebyshev_minimax`), `exists_residualMinimax_sq_le_sum_mul_norm_sq` (weighted least-squares dual on a finite set); Mathlib has none |
| Chebyshev extrema and dual weights | `chebyshevExtremum a a' q k`, $\xi_k=\tfrac{a'+a}{2}-\tfrac{a'-a}{2}\cos(k\pi/q)$, increasing for $k\le q$, where `chebyshevResidual a a' q` alternates (junk `a` at `q = 0`); `chebyshevWeight a a' q k` $=\lvert\ell_k(0)\rvert$ for `k : Fin (q + 1)`, $\ell_k$ the Lagrange basis at the extrema; the worst-case Krylov instances are built from them | `eval_chebyshevResidual_chebyshevExtremum` (alternation), `sum_chebyshevWeight`, `chebyshevWeight_pos`, `inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq` (the dual certificate); the extremum is the affine image of Mathlib's `Polynomial.Chebyshev.node q k` by unfolding, no bridge lemma |
| even Chebyshev filter | `evenChebyshevFilter k : ℝ[X]`, $U_{2k}(\sqrt x)/(2k+1)$, of degree at most $k$ in $x$, value $1$ at $1$ (Krylov-spectral note, 2026-10-22) | `eval_evenChebyshevFilter` (for `0 ≤ x`) |
| open Bernstein ellipse | `openBernsteinEllipse ρ : Set ℂ`, focal-distance sum `‖z-1‖+‖z+1‖ < ρ+ρ⁻¹`; approximation assumes `1 < ρ` | `isOpen_openBernsteinEllipse`, `ofReal_mem_openBernsteinEllipse`, `joukowski_mem_openBernsteinEllipse`; no outer-boundary regularity |
| full Chebyshev coefficient | `chebyshevCoeff f k` for `f : ℝ → 𝕜`, `[RCLike 𝕜]`; cosine Bochner integral, normalization 1/π at zero and 2/π otherwise | raw cosine integral by definition; `chebyshevCoeff_eval_T` gives basis delta; Mathlib cosine substitution/orthogonality reused |
| degree-N Chebyshev truncation | `chebyshevTrunc f N : 𝕜[X]`, inclusive terms 0 through N using the same coefficient | `eval_chebyshevTrunc`, `degree_chebyshevTrunc_le`, `chebyshevTrunc_eval`; zero coefficients and N=0 included |
| Jackson damping | `jacksonDamping N k : ℝ`, normalized sine autocorrelation; zero for `k > N`, zeroth mode 1, values in `[0,1]` | Raw autocorrelation by definition; `jacksonDamping_of_le` gives its trigonometric representation; no matching pinned Mathlib object |
| nonnegative periodic Jackson kernel | `jacksonKernel N θ : ℝ`, finite cosine polynomial; period `2π`, integral `2π` | `jacksonKernel_eq_norm_sq`, `integral_jacksonKernel`, `integral_cos_mul_jacksonKernel`; ordinary functions, no new circle-function type |
| canonical Jackson approximant | `jacksonApprox f N : 𝕜[X]` for `[RCLike 𝕜]`, `f : ℝ → 𝕜`; inclusive sum `0..N` with damping times the existing full coefficients | `eval_jacksonApprox`, `degree_jacksonApprox_le`, `chebyshevCoeff_jacksonApprox`; no arbitrary-function reconstruction claim |
| Jackson approximation factor | `jacksonApproximationConstant : ℝ`, currently `Real.pi`, improving the source's `π²/2`; supporting numerical API | `jacksonApproximationConstant_pos`, `jacksonApproximationConstant_le`; the current-value comparison is `≤ Real.pi` |
| divided difference | `dividedDifference s v r := ∑ i ∈ s, Lagrange.nodalWeight s v i * r i` for nodes `v : ι → F` on `s : Finset ι`, Mathlib's nodal weights; distinct nodes as `Set.InjOn v s`, the count as `#s = q + 1` (2026-10-17) | `dividedDifference_eq_coeff_interpolate` (from Mathlib's `Lagrange.coeff_eq_sum`) |
| location of the spectrum | `spectrum ℝ A ⊆ s` for Hermitian `A`, the same format for an interval (`s = Set.Icc a b`) and a union of intervals; polynomial bounds on it are `∀ x ∈ s, \|p.eval x\| ≤ M`; a Loewner sandwich `a • 1 ≤ A`, `A ≤ b • 1` reaches it through a bridge (maintainer, 2026-10-17) | `Matrix.IsHermitian.spectrum_subset_iff`, `spectrum_subset_Icc_of_le`; Mathlib's `le_algebraMap_iff_spectrum_le`, `algebraMap_le_iff_le_spectrum` |
| transfer from `𝕜` to `ℂ` | `complexify A = A.map RCLike.toComplex` | `Matrix.IsHermitian.complexify_cfc`, `complexify_le_complexify_iff` |
| operator convexity | `OperatorConvexOn s f`; convex combinations as `a • A + b • B`, `a + b = 1` | `OperatorConvexOn.cfc_smul_add_smul_le` |
| supporting line of a real function | `HasSupportingLineOn f s x := ∃ c, ∀ y ∈ s, f x + c * (y - x) ≤ f y` (ForMathlib, root namespace), for `f : ℝ → ℝ`; the hypothesis of Jensen's inequality for a function that need not be convex, never a raw `∃ c` in a statement (2026-10-18) | `ConvexOn.hasSupportingLineOn` (convex and differentiable at `x ∈ s`); Mathlib has no subgradient of a real function (searched) |
| derivative of a matrix curve | entrywise, `∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t` | `Matrix.hasDerivAt_iff_forall_apply` |
| triangular, unit triangular | Mathlib's `Matrix.IsUpperTriangular`, `Matrix.IsLowerTriangular`; `IsUnitLowerTriangular`, `IsUnitUpperTriangular` | `Matrix.BlockTriangular` |
| trapezoidal, Hessenberg, tridiagonal, quasi-triangular | `IsUpperTrapezoidal`, `IsUpperHessenberg`, `IsTridiagonal`, `IsUpperQuasiTriangular`, for matrices indexed by `Fin` | — |
| factorizations | predicates `IsLU A L U`, `IsCholesky A L`, `IsQR A Q R` (thin); a full QR is a square `Q` with `HasOrthonormalCols Q` and `IsUpperTrapezoidal R` | — |
| algorithm | a total recursion indexed by the step (`gaussState`, `householderState`), breakdown as a value, a realisation theorem under a hypothesis on the computed pivots | `isLU_luLower_luUpper` |
| short algorithm names in `\mathsf` | `\mathsf{gn}` for `generalizedNystrom`, `\mathsf{earlyTruncatedGN}` for `earlyTruncatedGeneralizedNystrom`: the only short names a docstring may write in `\mathsf` (§6 item 5, M4); every other algorithm output is written with its Lean name verbatim. `scripts/check_rules.py` reads this row (maintainer, 2026-10-19) | — |
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
| standard Gaussian vector | `gaussianVector n := Measure.pi fun _ : n => gaussianReal 0 1`, an `abbrev` on `n → ℝ`, as a law `HasLaw g (gaussianVector n) μ`; an `IsGaussian` instance; a theorem taking it is `_of_hasLaw_gaussianVector` (N9) | Mathlib's `Measure.pi` and `gaussianReal` by `rfl`; to `stdGaussian (EuclideanSpace ℝ n)` through Mathlib's `map_pi_eq_stdGaussian`; `isIsotropic_of_hasLaw_gaussianVector`, `hasLaw_dotProduct_of_hasLaw_gaussianVector` |
| tail | `μ.real {ω \| b < err ω} ≤ δ` for a scalar error, the event stated positively (amended 2026-10-19); `μ.real {ω \| ¬ P ω} ≤ δ` only for a Loewner, conjunction or predicate event `P`; names by §4 N14, N15 | — |
| expectation | `∫ ω, f (X ω) ∂μ` (Bochner) | — |
| sub-Gaussian | `HasSubgaussianMGF X c μ` | Mathlib's |
| sub-Gaussian random vector | `IsSubgaussianVector x c μ` for `x : Ω → n → 𝕜`: every `RCLike.re (u ⬝ᵥ x ω)` (no conjugation) has `HasSubgaussianMGF` with proxy `c * ‖WithLp.toLp 2 u‖₊ ^ 2`; it depends only on the law | `IsSubgaussianVector.hasSubgaussianMGF_re_apply` (coordinates), `IsSubgaussianVector.mulVec`, `IsSubgaussianVector.of_iIndepFun` (independent real coordinates), `isSubgaussianVector_of_hasLaw_gaussianVector`, `isSubgaussianVector_of_hasLaw_rademacherVector`, `ProbabilityTheory.HasLaw.isSubgaussianVector_iff`; Mathlib's `HasSubgaussianMGF` is scalar, no vector notion |
| independent test matrices | `IndepFun S G μ` for two random matrices (Hutch++'s sketch and residual test matrices, of any widths and laws; a deterministic one is a constant map); conditioning on one is `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral` (Hutch++ note §6, 2026-10-18) | Mathlib's; `indepFun_iff_map_prod_eq_prod_map_map`. To integrate out a factor $W$ with a named law (`HasLaw W ν μ`), the preferred route is the `ProbabilityTheory.IndepFun` conditioning lemmas: `lintegral_comp_eq_lintegral_lintegral_of_hasLaw`, `lintegral_ofReal_comp_eq_lintegral_ofReal_integral`, `integrable_comp_of_integral_le`, `integral_comp_le_of_integral_le`; `integrable_comp_iff` transfers integrability to the product of the laws (Consolidation note D1, 2026-10-22) |
| Girard–Hutchinson estimate | `girardHutchinson A Ω := (Ωᴴ * A * Ω).trace / card m`, the probes the `m` columns of `Ω : Matrix n m 𝕜`; `0` with no columns; the column average is `girardHutchinson_eq_sum` (trace estimation note §4, 2026-10-18) | `girardHutchinson_eq_sum`; Mathlib has none |
| Hutch++ | `hutchpp A S G := (rsvd A S).trace + girardHutchinson ((1 - P) * A * (1 - P)) G`, `P = rangeProjector (A * S)`, basis-free; the papers' orthonormal-basis form is a bridge (Hutch++ note §6, 2026-10-18) | `hutchpp_eq_of_mul_conjTranspose_self_eq_rangeProjector`, `trace_sub_hutchpp`; Mathlib has none |
| projection-cost-preserving sketch | deterministic: `IsProjectionCostPreserving A Ã k a b`; random: `HasProjectionCostPreserving S A k a b δ μ`, the tail `μ.real {ω \| ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) k a b} ≤ δ`, with the sketch `S : Ω → Matrix l n 𝕜` in the Sketching orientation; on a LowRank test matrix, `fun ω => (X ω)ᴴ`; no oblivious (all-`A`) predicate | `HasSubspaceEmbedding.hasProjectionCostPreserving`, `IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`, `hasProjectionCostPreserving_conjTranspose_iff` (the LowRank orientation); Mathlib has none |
| preconditioned Richardson iteration | `richardsonIterate A M b x₀ q` for `A : Matrix m n 𝕜`, `M : Matrix n m 𝕜` (rectangular; a step size is folded into `M`), a total recursion; error `xs - richardsonIterate …` (sketch-and-precondition note D3, 2026-10-19) | `richardsonIterate_mul_conjTranspose` (Richardson through `Aᴴ` is Richardson on the normal equations), `sub_richardsonIterate_eq`; Mathlib has none |
| sketch-and-precondition | `sketchAndPrecondition A S y x₀ q := pcgIterate (Aᴴ * A) (pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q`, basis-free; the start is explicit and the sketch-and-solve start is the hypothesis `IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀` (note D1, D2) | `IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`, `IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate`, `pcgState_x_eq_sketchAndPrecondition`; Mathlib has none |
| iterative sketching | `iterativeSketching A S ω y x₀ q := richardsonIterate A (ω • (pinv ((S * A)ᴴ * (S * A)) * Aᴴ)) y x₀ q`, one sketch for all steps | `iterativeSketching_eq`, `IsQR.iterativeSketching_succ`; Mathlib has none |
| i.i.d. sequence | `HasLaw ξ (iidSequence ν) μ` for `ξ : Ω → ℕ → β`, with `iidSequence ν := Measure.infinitePi fun _ : ℕ => ν` (an `abbrev`); a theorem taking it is `_of_hasLaw_iidSequence` (N9); a function of the first `q` terms is `DependsOn F (Set.Iio q)`; conditioning on the past is `ProbabilityTheory.HasLaw.integral_comp_eq_integral_integral_of_dependsOn` (Kaczmarz note D2, 2026-10-19; named law, maintainer, 2026-10-20) | `hasLaw_infinitePi_iff`; Mathlib's `ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi` |
| sketch-and-project | `sketchAndProject A S b x := x + pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ x))`, iterate `sketchAndProjectIterate A S b x₀ q` for `S : ℕ → Matrix k m 𝕜`; expected projector `∫ T, rangeProjector (T * A)ᴴ ∂ν`, no definition; error `xs - …` | `isLeastSquaresSolution_sketchAndProject`; Mathlib has none |
| randomized Kaczmarz | `kaczmarzIterate A ι b x₀ q`, rows `ι : ℕ → m`, the sketch-and-project iterate with row-selection sketches; law `samplingMeasure (rowNormSqDistribution A)` | `kaczmarzIterate_succ` (row-action formula); Mathlib has none |
| Frobenius pseudo-condition number | `frobPseudoConditionNumber A := frobNorm A * specNorm (pinv A)`, any shape and rank; written out in docstrings, $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$ (§6 keeps $\kappa$ for the classical condition number) | `frobPseudoConditionNumber_eq_frobNorm_div_singularValues`; Mathlib has none |
| spectral measure of a matrix and a vector | `spectralMeasure A b : Measure ℝ`, total, unnormalised (mass $\|\mathbf{b}\|^2$), one atom per distinct eigenvalue, $0$ off Hermitian; its integral of every $f$ is $\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ (Krylov-spectral note SD1, 2026-10-22) | `integral_spectralMeasure`; to an eigenbasis, `HasOrthonormalCols.spectralMeasure_eq_sum`; Mathlib has none (searched) |
| empirical spectral measure | `empiricalSpectralMeasure A`, $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert}\delta_{\lambda_k}$, multiplicities counted (SD1) | `Matrix.IsHermitian.integral_empiricalSpectralMeasure` (the normalised trace of `cfc f A`); Mathlib has none |
| probe spectral measure | `probeSpectralMeasure A Ω`, $(\lvert n\rvert m)^{-1}\sum_j\mu_{\mathbf{A},\boldsymbol{\omega}_j}$ over the `m` columns of `Ω : Matrix n m 𝕜`; its integral of `f` is the Girard–Hutchinson estimate of $\operatorname{tr}f(\mathbf{A})/\lvert n\rvert$, and isotropic probes give the empirical spectral measure in expectation; junk `0` off Hermitian and with no rows or columns (SLQ note) | `integral_probeSpectralMeasure`, `integral_integral_probeSpectralMeasure`; Mathlib has none |
| angle between a vector and an eigenspace | `spectralTangentSq A b c` $= \mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$, junk $0$; eigenvalue bounds take `0 < (spectralMeasure A b).real {c}`, no eigenvector hypothesis (SD6) | `Matrix.IsHermitian.spectralTangentSq_le` (eigenvector form) |
| moment matching | `MatchesMoments μ ν N`: equal integrals of every real polynomial of degree $< N$ (SD2); measures in the Polynomial layer are `[IsFiniteMeasure μ]` with `∀ᵐ x ∂μ, x ∈ Set.Icc a b` (SD3) | `matchesMoments_iff_forall_mem_degreeLT`, `matchesMoments_measureT` (Mathlib's Chebyshev–Gauss) |
| orthogonality to lower degrees | `IsOrthogonalPolynomial μ k p`; monicity and degree stay separate hypotheses (SD4) | — |
| positive definiteness up to a degree | `IsMomentPosDef μ k`: $\int p^2\,d\mu>0$ for every nonzero real `p` with `p.degree < k`, the $L^2$ form; vacuous at `k = 0`; the hypothesis of uniqueness of the orthogonal polynomials and of $k$ distinct Gauss nodes | `isMomentPosDef_iff_forall_finset` (at least $k$ support points), `isMomentPosDef_succ_iff` (the last norm is positive), `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` (`k ≤ krylovGrade A b`); Mathlib has no moment-definiteness predicate (searched); the Hankel form through Mathlib's `Matrix.posDef_gram_iff_linearIndependent` is not stated |
| monic orthogonal polynomials, Jacobi matrix | `orthogonalPolynomial μ k : ℝ[X]`, defined by the Stieltjes three-term recurrence, monic of degree `k` for every `μ`; coefficients `jacobiAlpha μ k`, `jacobiBeta μ k` in Gautschi's convention ($\beta_k=\int\pi_k^2/\int\pi_{k-1}^2$, `jacobiBeta μ 0 = μ.real Set.univ`, junk `0` on a zero norm; OQ3); `jacobiMatrix μ k : Matrix (Fin k) (Fin k) ℝ` carries $\alpha_i$ and $\sqrt{\beta_i}$, the layout of `lanczosTridiagonal` | `orthogonalPolynomial_add_two` (`rfl`), `isOrthogonalPolynomial_orthogonalPolynomial`, `IsMomentPosDef.eq_orthogonalPolynomial`, `MatchesMoments.jacobiMatrix_eq`, `Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`; Mathlib has none for a general measure (its orthogonal families are for fixed weights, `Polynomial.Chebyshev.measureT`) |
| Gauss rule at given nodes | `interpolatoryQuadrature μ s`, weight $\int\ell_x\,d\mu$ at each node, truncated at $0$; Gauss exactness under `IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)` (SD4) | `IsOrthogonalPolynomial.integral_interpolatoryQuadrature`; Mathlib has none beyond `Polynomial.Chebyshev.measureT` |
| canonical $k$-point Gauss rule | `gaussQuadrature μ k := interpolatoryQuadrature μ (gaussNodes μ k)`, a finite measure for every `μ` and `k`; `gaussNodes μ k := (orthogonalPolynomial μ k).roots.toFinset`, `k` nodes under `IsMomentPosDef μ k`, and past the number of support points the rule is `μ` itself; Gauss statements take it, never the roots spelled out | `matchesMoments_gaussQuadrature` (exactness to degree $<2k$), `integral_gaussQuadrature_eq_sum`, `MatchesMoments.eq_gaussQuadrature` (uniqueness), `IsMomentPosDef.card_gaussNodes`; to Lanczos, `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, `spectralMeasure_jacobiMatrix` (Golub–Welsch); Mathlib has none beyond `Polynomial.Chebyshev.measureT` |
| Radau modified measure $\lvert x - c\rvert\,d\mu$ | `radauMeasure μ c` | `integral_radauMeasure` |
| Radau rule, prescribed node $c$, $k$ free nodes | `radauQuadrature μ c k`; nodes `radauNodes μ c k` | `matchesMoments_radauQuadrature`, `integral_radauQuadrature` |
| Lobatto modified measure, rule | `lobattoMeasure μ a b`, `lobattoQuadrature μ a b k`, `lobattoNodes μ a b k` | `integral_lobattoMeasure`, `matchesMoments_lobattoQuadrature`, `integral_lobattoQuadrature` |
| Radau Jacobi matrix (Golub) | `radauJacobiMatrix μ c k`, corner `radauJacobiAlpha μ c k` | `spectralMeasure_radauJacobiMatrix` |
| nodes with multiplicity, nodal polynomial | `m : Multiset ℝ`, `(m.map fun y => X - C y).prod` | Mathlib's `Multiset` API; `Lagrange.nodal s id` for a `Finset` |
| jets | `(derivative^[k] H).eval y` (polynomial), `iteratedDeriv k f y` (function) | `Polynomial.iteratedDeriv` |
| Lanczos quadrature rule | `lanczosQuadrature A b q`, the spectral measure of the projector compression; the scalar quadrature is `RCLike.re (star b ⬝ᵥ lanczosFA A f b q)` (SD5) | `integral_lanczosQuadrature`, `HasOrthonormalCols.lanczosQuadrature_eq`; Mathlib has none |
| stochastic Lanczos quadrature | one estimator, two objects: `slq A f Ω q : 𝕜`, $m^{-1}\sum_j\int f\,d\,\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\boldsymbol{\omega}_j},q)$, is canonical for trace estimates of $\operatorname{tr}f(\mathbf{A})$; `slqMeasure A Ω q : Measure ℝ`, scaled as `probeSpectralMeasure`, is canonical for spectral-density statements (distribution functions, Lipschitz test functions); the two are joined only by `integral_slqMeasure`, and neither is defined through the other; junk `0` with no probes or at `q = 0` | `integral_slqMeasure` (`∫ f ∂slqMeasure A Ω q = RCLike.re (slq A f Ω q) / card n`), `Matrix.IsHermitian.slq_eq_sum_lanczosFA` (the algorithm), `Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`, `matchesMoments_probeSpectralMeasure_slqMeasure`, `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`; Mathlib has none |
| query algorithm | `QueryAlgorithm Q R q β`, deterministic and adaptive: `query i` of the first `i` responses, `output` of all `q`; run against an oracle `f : Q → R` with `alg.transcript f`, `alg.run f`, the `i`-th query `alg.queryAt f i`; queries from a transcript `alg.queries τ`, for vector queries `alg.queryMatrix τ` (queries as columns); a randomized algorithm is `alg : S → QueryAlgorithm …` with `QueryAlgorithm.IsMeasurableFamily alg` and a seed independent of the input; lower bounds take `alg.IsMeasurable` | `QueryAlgorithm.history_apply`, `QueryAlgorithm.queryAt_eq_queries_transcript`; Mathlib has none (Markov kernels: §8) |
| matrix–vector oracle | `A.mulVec` (one-sided, products $\mathbf{A}\mathbf{x}$); two-sided access is `twoSidedMulVec A`, pair query $(\mathbf{x}, \mathbf{y})$ ↦ $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$; right and left query matrices `alg.rightQueryMatrix τ`, `alg.leftQueryMatrix τ`; costs per side `alg.rightCount τ`, `alg.leftCount τ` (rounds with a nonzero part), budgets as hypotheses `∀ τ, alg.rightCount τ ≤ q` per side; one-sided `alg.IsOneSided`; one pass = `IsNonAdaptive` (both parts fixed up front) | `QueryAlgorithm.rank_rightQueryMatrix_le_rightCount`, `QueryAlgorithm.rank_leftQueryMatrix_le_leftCount` |
| Gram simulation, truncation, Gaussian resampling | `alg.gramSimulation k`, the `2q`-round algorithm against `twoSidedMulVec X` that runs `q` queries to `X * Xᴴ`, its simulated responses `QueryAlgorithm.gramDecode h`; the first `i` rounds as an algorithm `alg.truncate i`; the transcript-dependent Gaussian resampling `alg.resample X X'` | `QueryAlgorithm.run_gramSimulation`, `QueryAlgorithm.gramDecode_history_gramSimulation`, `QueryAlgorithm.transcript_truncate`, `QueryAlgorithm.transcript_resample`; Mathlib has none |
| passes | `alg.IsPassStructured pass` for `pass : ℕ → ℕ` monotone: query `i` depends only on the responses of rounds in earlier passes; a `p`-pass algorithm adds `∀ i < q, pass i < p`; one pass is `IsNonAdaptive`, one query per pass is every algorithm; a weaker oracle `alg.comapResponse f`, a post-processed output `alg.mapOutput g` (2026-10-26) | `QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive` (one pass), `QueryAlgorithm.isPassStructured_id`; Mathlib has none |
| hidden rotation, Krylov coupling | the oracle `hiddenRotationOracle U D`, $\mathbf{x} \mapsto (\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$, simulated on `twoSidedMulVec U` by `alg.hiddenRotationSimulation D`; the conclusion of the coupling theorem is the predicate `IsKrylovCoupling μ D s G₀ V G` (Gaussian `G` independent of `G₀`, a.s. `range V ≤ blockKrylovSpace D (fromCols G₀ G) s`), which lower bounds take as hypothesis | `QueryAlgorithm.gramSimulation` is the case $\mathbf{D} = \mathbf{I}$ of the simulation; `QueryAlgorithm.run_hiddenRotationSimulation`; the coupling theorem is in the LB-C scaffold; Mathlib has none |
| hard spectra of the hidden-rotation lower bounds | `IsChebyshevTwoIntervalSpectrum κ s M d` (values on the points $\pm\sqrt{\xi_j}$ of $[1, \kappa^2]$, multiplicities dominating the dual weights; linear systems); `equispacedLevelSpectrum k m p` (head $p + 2$, tail levels $1, \dots, p + 1$; few-pass low-rank approximation) | built from `chebyshevExtremum`, `chebyshevWeight`; existence `exists_isChebyshevTwoIntervalSpectrum`; Mathlib has none |
| program | `Computation.Stmt P ι VB VI` (tags `P`, oracle names `ι`, handles `VB`, indices `VI`), scalar instructions `Computation.Instr P VB VI`; a program `<spec>Prog` lives in its topic file (`hutchppProg`, `gramSchmidtProg`, the sweep `orthAgainst`), its counts `<spec>Count` with its targets (`hutchppCount`, `gramSchmidtCount`); the first-order program it compiles to, `Computation.FStmt P ι nb ni`, `Computation.Prog P ι r b`, run by `Computation.Prog.exec` and budgeted by `Computation.Prog.RunsWithin`; the compiler `Computation.Stmt.compile`, `Computation.ProgFamily.compile`, and the registered trees `hutchppProg.compiled`, `hutchppProg.compiledDense`, `gramSchmidtProg.compiled` (§5.5; computation note, 2026-10-23) | Mathlib has no syntax for imperative programs (searched) |
| `do` notation for programs | `Computation.Builder P ι VB VI β`, an abbreviation of Mathlib's `ContT (Stmt P ι VB VI) Id β`, with `Builder.run`, `Builder.stmt`, `Builder.ins`, `Builder.alloc` (scoped to the rest of the block), `Builder.forRange`, `Builder.ifThenElse`, `Builder.named`, `Builder.scope` | Mathlib's `ContT`, `ContT.run` |
| index expression, cell | `Computation.IExp VI`, `Computation.Cell VB VI` | — |
| store, state, interpretation, run | `Computation.Store P K`, `Computation.St P K C` (with bit memory), `Computation.Interp P ι K C` (with read-only data and widths), `Computation.exec`; block access `Store.readBlock`, `Store.writeBlock`, `Store.shape`; one comparison `cmpStep`; the initial state of a realisation `Computation.inputState` | — |
| value semantics | `Computation.ScalarSem P K`; exact arithmetic `Computation.exactSem` | — |
| running within a budget | `Computation.RunsWithin I s st₀ c m Q`: success, counts at most `c` more, peak plus read-only data at most `m`, postcondition `Q`; an upper bound | `Computation.measureReal_not_runsWithin_le` (tails transfer) |
| operation counts | `Computation.OpCount P ι := OpKind P ι →₀ ℕ`; a weighted total is `Finsupp.weight`; substituted counts `Computation.substCountG`, `Computation.substCount` | Mathlib's `Finsupp` |
| matrix layout | column-major from an offset: `Computation.flatten`, `Computation.unflatten`, `Computation.Holds s p b off M`, through a decoding `Computation.HoldsDecoded s dec p b off M`; a test matrix drawn from the tape `Computation.tapeMatrix x off N k` | `Matrix.of`; `Computation.unflatten_flatten` |
| oracle semantics | `Computation.matOracle A`, `Computation.exactInterp (A : ι → Matrix (Fin N) (Fin N) 𝕜) ξ`; realisations at `Fin N`, reindexing lemmas for the specification (`hutchpp_reindex`) | Mathlib's matrix product |
| substitution | `Computation.Stmt.subst`, `Computation.Stmt.substOracle`; certificates `Computation.ImplementsInstr`, `Computation.ImplementsOracle`; `Computation.RunsWithin.subst`, `Computation.RunsWithin.substOracle`; the oracle-only cost `substKind`, the simulation `Sim`, `St.withCnt` | — |
| oracle implementations | `Computation.denseImpl`, `Computation.denseInterp`, `Computation.denseCost`; `Computation.cooImpl`, `Computation.cooMatrix`, `Computation.cooInterp`, `Computation.cooCost` | — |
| error contract | `Computation.IsRelErrSem u dec safe sem`, error and success clauses per operation family; the real operations `BinOp.realOp` on `BinOp.IsArith`; the failing semantics `failSem`; the arithmetic part for an error relation, `Computation.IsArithErrSem err dec safe sem` (standard model: `Computation.RelErr`), and `Computation.AddsZeroExactly dec sem`; a witness with $u > 0$, `Computation.gridSem t` (rounding to nearest `Real.roundNearest` onto `Real.floatGrid`) | `Computation.isRelErrSem_exactSem`, `Computation.IsRelErrSem.isArithErrSem`, `Computation.isRelErrSem_gridSem` |
| rounding factor | $\gamma_n$ is `Computation.roundingFactor n u` $= nu/(1 - nu)$, every lemma under $nu < 1$ | none; Mathlib has no floating-point model (`Mathlib.Data.FP` has no theorems) |
| rounding traces | the decoded intermediate values of a kernel run under an error relation: `Computation.IsDotTrace` (`dot`, each entry of `gemv` and `gemm`), `Computation.IsSubstRowTrace`, `Computation.IsSubstTrace` (`trsvLower`) | — |
| straight-line runs | `Computation.Stmt.StraightLine` (no `ite`, no `whileFuel`); the usage of a state `Computation.St.usage` (tape positions, counts, memory) | `Computation.usage_eq_of_exec_eq_some_of_straightLine` |
| random tape | `HasLaw ξ (iidSequence ν) μ` per distribution (the i.i.d. sequence row); the law of the whole tape `Computation.tapeLaw`, the tapes independent, the tape of `d` i.i.d. with law `Computation.Dist.law d` (guarantees, 2026-10-23) | `hasLaw_tapeMatrix_of_hasLaw_iidSequence`, `ProbabilityTheory.HasLaw.comp_of_injective`, `Computation.hasLaw_apply_of_hasLaw_tapeLaw` |
| access models | `Computation.MatrixFree`, `Computation.MatrixFreeProb`, `Computation.StoredEntries` (interpretation `Computation.storedInterp`) on a first-order program; on a program family `Computation.ProgFamily P ι r b` (`ProgFamily.inst`, `ProgFamily.substOracle`), the proof infrastructure `Computation.ProgFamily.MatrixFree`, `Computation.ProgFamily.MatrixFreeProb`, `Computation.ProgFamily.StoredEntries`, with the transfer `Computation.ProgFamily.MatrixFree.prog`, §5.5 (guarantees, 2026-10-23) | `Computation.ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl`, `Computation.ProgFamily.MatrixFree.storedEntries_substOracle_cooImpl` |
| target | a `Prop` in `<Topic>/<Spec>Targets.lean`, an access model about a registered tree, registered in `docs/targets.toml` and proved by one theorem whose type is the constant: `MatrixFreeGramSchmidt`, `MatrixFreeHutchpp`, `MatrixFreeProbHutchpp`, `StoredEntriesDenseHutchpp`, `StoredEntriesCooHutchpp` (§5.5; first-order programs and target statements, 2026-10-23) | — |
| BLAS kernels | `Computation.dot`, `Computation.axpy`, `Computation.scal`, `Computation.rscl`, `Computation.copyv`, `Computation.nrm2`, `Computation.gemv`, `Computation.ger`, `Computation.gemm`, `Computation.trsvLower`, each with its specification `Computation.exec_<kernel>` | — |

### 5.4 Interfaces and reusable hypotheses

This is the rule that matters most for proving new things. Without it, a sketch ends up with five
different conclusion shapes across five distributions, isotropy becomes a four-hypothesis bundle
repeated in every estimator theorem, orthonormality is sometimes a predicate and sometimes
`Qᵀ * Q = 1`, and nothing downstream can take "any sketch with property P" as an input.

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

### 5.5 Programs

Algorithms analysed for their cost are programs over memory buffers (`NLAlib/Computation`,
`docs/design/Computation.md`). A program `<spec>Prog` is written with the builder in its topic
file, next to its specification, and compiled once, at symbolic sizes, into one first-order tree
for all sizes, `<spec>Prog.compiled : Computation.Prog P ι r b` (a registered tree). A published
cost result is a **target** (maintainer, 2026-10-23: "this stuff needs to be watertight, because
we will be allowing stuff to prove autonomously"; first-order programs and target statements,
2026-10-23):

- A target is a library definition of type `Prop`, written and reviewed by the library, in a
  file of its own, `<Topic>/<Spec>Targets.lean`, and registered in `docs/targets.toml`. It states
  an access model about a registered tree: `Computation.MatrixFree`, `Computation.MatrixFreeProb`
  or `Computation.StoredEntries`, which bind the program before the sizes and quantify over the
  matrix, the tape and the declared inputs afterwards, so the counts and the memory are functions
  of the sizes by the statement itself. Its name is the model, then the specification
  (`MatrixFreeHutchpp`).
- A result is `theorem matrixFreeHutchpp : MatrixFreeHutchpp`: its type is the target constant,
  with no hypothesis, parameter or postcondition of the prover's, and each registered target has
  exactly one such proof. A `Result:` theorem whose statement reaches a run or a budget proves a
  registered target; a lemma about a program family is proof infrastructure and has no result id
  [E3].
- The registry records each target's closure hash (every library constant its statement reaches,
  proofs erased and hygienic names numbered, the registered trees as leaves hashed by their
  constructor normal forms, which the kernel checks are the trees), its printed statement, each
  tree's printed normal form, the toolchain, the Mathlib revision and the SHA-256 of
  `lake-manifest.json` and `lakefile.toml`; `docs/targets.approved` holds the registry's SHA-256. A
  change of a target, of a definition it unfolds to, or of a tree changes a hash and needs the
  maintainer's approval (Q3): he reviews the diff that `TARGETS_UPDATE=1 lake env lean
  scripts/Targets.lean` writes and approves it with `sha256sum docs/targets.toml >
  docs/targets.approved`. A declared input computed from the sizes carries the registry flag
  `precomputed` and a `Precomputed:` docstring sentence (Q5) [E3].
- Every `<spec>Prog` has a registered tree, named by a registered target, whose definition calls
  it [E4]. This is completeness, not soundness. So a new program lands in `NLAlib` together with its registered
  target, and only the maintainer registers targets: a PR that needs one proposes the target
  statement in its description.
- What the models prove and what they trust is listed in `docs/design/Computation.md`,
  "Guarantees: what is proved and what is trusted", re-classified in its F10. A reader of a target
  still reads its size condition, its declared inputs, its postcondition and its bound: the model
  guarantees that the program meets exactly that statement, not that the statement is the
  interesting one.

The other rules are hygiene: the guarantees do not rest on them.

- Programs, kernels, implementations and compiled trees are computable: not `noncomputable`,
  `partial`, `opaque` or `unsafe`, and they run no code other than their definition (no
  implemented-by attribute) [E2]. It matters for the emitter and the `Float` runner.
- An `alloc` is live for the rest of the enclosing block, so a program that another program calls
  wraps its allocations in `scope` (a kernel is closed by its `named` node) [E9]. An open `alloc`
  is still counted, in the target's `mem`, so the rule is a warning: it keeps the peak the author
  intends.
- Only `NLAlib/Computation` defines a value semantics (`Computation.ScalarSem`) or an
  interpretation (`Computation.Interp`), each with its certificate [E6].
- `Stmt.named`, which the NumPy emitter prints as a call into its prelude, is constructed only in
  the BLAS and implementation files; a theorem may mention it [E8].

A builder need not be generic in its variable sorts (the old E1, retired 2026-10-23): the theorem
is about the compiled tree, and a handle forged from a number does not compile. E3 is checked by
`scripts/Targets.lean`, whose fixtures (an axiom of a target's type, a vacuous outer hypothesis,
an outer parameter, a postcondition of the prover's, a claim phrased through `exec`, a target of
the prover's, a claim wrapped in a structure, in `Nonempty` of one, in an inductive `Prop` or in a
class instance, a definition of type `Prop` with a result id; a term that is not a tree's normal
form, which the kernel rejects; edits of a count, of the value under an `irreducible_def` and of a
ForMathlib definition, each changing the hash, and of a proof, which does not; a toolchain, a
manifest and a Lake configuration mismatch; a declared input computed from the sizes) must be
rejected or detected. E2, E4 and E9 are checked by `scripts/Programs.lean`, with
fixtures (a forged handle that does not compile, a noncomputable and a `partial` program, a
program with no registered tree, a callee with an open `alloc`).
`scripts/AccessModelFixtures.lean` proves that the model forms of the audit's cheating programs
are false. E5, E6 and E8 are checked by `scripts/check_rules.py`. The tools library
`NLAlibTools` (§7) is not part of the library and is not held to its rules.

## 6. Docstrings and citations

Every public declaration has a docstring. It is the record the documentation site, the search
index and the literature map are generated from, so its parts are fixed:

```lean
/-- **Weyl's inequality.** For Hermitian $\mathbf{A}, \mathbf{B}$ and $i + j$ a valid index,
$\lambda_{i+j}(\mathbf{A} + \mathbf{B}) \le \lambda_i(\mathbf{A}) + \lambda_j(\mathbf{B})$, eigenvalues
non-increasing and indexed from $0$.
[HornJohnson2013, Theorem 4.3.1]; stated there over $\mathbb{C}$ with eigenvalues in increasing
order, here over any `RCLike` field, any finite index type, non-increasing.
Result: weyl-inequality -/
theorem Matrix.IsHermitian.eigenvalue_add_le ...
```

1. **First sentence:** what it asserts, in words, with the bold name of the result if it has one
   (a `Result:` declaration has one [D1]).
   Its mathematics is LaTeX (item 5); a reader of the documentation site or the explorer should
   learn the statement from it without reading the Lean. So the docstring states its hypotheses
   and notation itself, never "under the hypotheses of `X`", "as there", "as in the tail", "on the
   same instance" or "if moreover" [D2]. Independence of the summands, rows or sketches is always
   said in words, and a headline theorem names the law of each `HasLaw` hypothesis [D12]; a
   headline theorem's `[Nonempty n]` is said too ("$n$ nonempty", review list: [D13]).
2. **Citation:** `[Key, label]` where `Key` is an entry of `docs/references.bib` and `label` is the
   printed theorem, section or equation, for every source where this result or the result it
   generalises or specialises appears. A citation of a specific result carries its label; a bare
   `[Key]` is for module docstrings only [C2] (maintainer, 2026-10-19). A `Result:` declaration
   cites its source, or says "No printed source." [C1] (the check accepts any wording it reads as
   saying so: "no printed source", "no (literature) source", "without a source", "not in the
   literature", "new here", "proved here", "folklore", "standard"; write "No printed source."); a bracket that looks like a citation is
   one `check_refs.py` can parse [C4]; a bold-named theorem with neither citation nor id is on a
   review list [C9]. Several are separated by `;`. Then the relation to the
   printed statement: generalisation, different constant, tail form instead of sample size,
   different indexing. The citation is provenance for the reader and the literature map; it does
   not bind the statement or the proof. A helper or a bridge needs no citation; it says what it
   is for.
3. **Provenance** when a statement or proof is taken from another formal library: the library
   and commit.
4. **`Result: <id>`** on its own last line, for a declaration that *is* the formal statement of a
   named mathematical result (`weyl-inequality`, `eckart-young-frobenius`). Several ids are
   comma-separated. Helpers carry none, and neither do definitions and structures [R1]
   (maintainer, 2026-10-19; an instance of a Prop-valued class is a statement and may). The ids
   key the literature map maintained in the `explore` repository; a new id is fine, a misspelt
   existing one is an error [R2] (checked as: two ids of length at least 8 within edit distance 2
   are rejected as near-duplicates, unless they differ in one dash-separated word by a `p` prefix
   or a listed pair such as `ose`/`osi`; distinguish variants by words, `-frobenius`/`-spectral`,
   not by a digit), and an id or declaration the explorer names must exist [R3].
4b. **`Algorithm: <id>`** on its own last line, for a definition, recurrence, run model or program
   that is part of a named algorithm (maintainer, 2026-10-29; the explorer's algorithm pages,
   `docs/design/algorithm-pages.md` in the `explore` repository):

   ```lean
   /-- The **Hestenes–Stiefel recurrence** (the conjugate gradient algorithm) from the start …
   [HestenesStiefel1952, (3:1)]; …
   Algorithm: cg -/
   noncomputable def cgState …
   ```

   The id is a slug like a result id, and follows the result-id prefixes in use (`cg`, `pcg`,
   `lanczos`, `hutchpp`, `randomized-svd`, `sketch-and-solve`, `gram-schmidt`), so that the
   explorer attaches the results `cg-…` to the page `cg` without configuration. An optional role in
   parentheses: `Algorithm: cg (specification)` on the definition of *what* is computed when a
   separate recurrence computes it (`cgIterate`, `pcgIterate`), `Algorithm: lanczos (run model)`
   on a model of a run in finite precision (`LanczosRun`); without a role the declaration is a
   definition, and the explorer reads from its type whether it is a program. The tag goes on `def`,
   `abbrev`, `structure` and `inductive` declarations only [A2], never on theorems: results reach an
   algorithm through their ids and statements, and a cost target through the program its tree
   comes from. The line is standalone and last, the id a slug, the role `specification` or
   `run model` [A1]. A declaration belongs to at most one algorithm [A3]: a shared building block
   (`galerkinInverse`, `gramSchmidtQ` inside Hutch++) carries the tag of the algorithm it
   defines, or none, and is found through dependencies. Several declarations of one algorithm are
   expected (`cgState` and `cgIterate`; `rsvd` and `earlyTruncatedRSVD`; `hutchpp` and
   `hutchppProg`). A variant with a different definition has its own id (`pcg`).
5. **Mathematics is LaTeX** (amended 2026-10-14): `$…$` inline and `$$…$$` displayed, as doc-gen4
   and the explorer render it with KaTeX. Standard LaTeX only, no custom macros [M12]. A named
   bound's value is written inside the equation in place of the constant (§5.2 rule 2), and the
   value marker `<!-- value NAME ARGS -->` placed just before that math span, never at the start
   of a line, is an HTML comment, not a macro: HTML comments cannot go inside `$…$`; doc-gen4
   hides them, the explorer's build strips them and `scripts/check_latex.mjs` skips them. A Lean name stays
   in backticks (`` `specNorm` ``, `` `RCLike` ``); it is a reference, never inside `$…$` [D6].
   Informal Unicode maths in backticks (`` `‖A‖₂` ``) is the old style, replaced when a docstring
   is touched [D7]. The notation, so that every docstring reads the same (the rows with an id are
   checked):

   | Object | LaTeX | Shown |
   |---|---|---|
   | matrix, vector | `\mathbf{A}`, `\mathbf{x}`; entries `\mathbf{A}_{i,j}`, `\mathbf{x}_i` | bold upright |
   | scalars, indices, dimensions | `c`, `t`, `i`, `k`, `n`; the size of an index type `n` is `\lvert n \rvert` | italic |
   | random variables | random scalar `X` (capital, italic); random vector `\mathbf{x}`, `\mathbf{g}` (lowercase bold, like every vector, and lowercase in the Lean too: `x : Ω → n → ℝ`); random matrix `\mathbf{G}`; a random process over an arbitrary index set stays `X_t` | |
   | submatrix on index sets `s`, `t` (`s : Finset n`) | `\mathbf{A}_{s,t}`, principal `\mathbf{A}_{s,s}`, minor `\det \mathbf{A}_{s,s}` | |
   | identity, zero matrix | `\mathbf{I}`, `\mathbf{0}` | |
   | conjugate transpose, transpose [M7] | `\mathbf{A}^{\mathsf{H}}`, `\mathbf{A}^{\mathsf{T}}` | |
   | inverse, pseudoinverse | `\mathbf{A}^{-1}`, `\mathbf{A}^{+}` | |
   | block matrix | `\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}` | |
   | spectral, Frobenius, nuclear norm [M6, M15] | `\|\mathbf{A}\|_2`, `\|\mathbf{A}\|_{\mathsf{F}}`, `\|\mathbf{A}\|_*` | |
   | Schatten, Ky Fan, unitarily invariant norm | `\|\mathbf{A}\|_{S_q}`, `\|\mathbf{A}\|_{(k)}`, `\|\mathbf{A}\|_{\Phi}` | |
   | vector 2-norm, inner product | `\|\mathbf{x}\|`, `\langle \mathbf{x}, \mathbf{y} \rangle` | |
   | eigenvalues, singular values (library indexing: from `0`, non-increasing) | `\lambda_k(\mathbf{A})`, `\sigma_k(\mathbf{A})`, `\sigma_{\min}(\mathbf{A})` | |
   | condition number, pseudo-condition number, projector onto the range | `\kappa(\mathbf{A})` only for the classical condition number (invertible or full column rank, where it equals `` `pseudoConditionNumber` ``); otherwise the pseudo-condition number is written out, `\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2`, never `\kappa`; `\mathbf{P}_{\mathbf{A}}` | |
   | trace, determinant, rank, diagonal [M9] | `\operatorname{tr}`, `\det`, `\operatorname{rank}`, `\operatorname{diag}` | |
   | Loewner order [M17] | `\mathbf{A} \preceq \mathbf{B}`, `\mathbf{0} \preceq \mathbf{A}` | |
   | expectation, probability, variance [M10, M1] | `\mathbb{E}`, `\mathbb{P}`, `\operatorname{Var}` | |
   | number fields, the `RCLike` field [M13] | `\mathbb{R}`, `\mathbb{C}`, `\Bbbk` | |
   | named constants (maintainer, 2026-10-15) | the value in place of the constant, `\exp\bigl(-\tfrac{1}{196}\min(…)\bigr)`, with a value marker before the span and the Lean name in words nearby (`` `hansonWrightConstant` ``); a symbol such as `C_{\mathrm{HW}}` only in prose about the constant itself | |
   | truncated SVD (best rank-`k` approximation) [M14] | `\llbracket \mathbf{A} \rrbracket_k` | |
   | named algorithm outputs (maintainer, 2026-10-15) [M2, M3, M4, M5] | `\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})`, `\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})`, `\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})`: the Lean name verbatim in `\mathsf`, or a short name registered in the §5.3 row "short algorithm names in `\mathsf`" (`gn`; maintainer, 2026-10-19), never the formula it unfolds to; the definition's docstring alone shows the formula, as `\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}) := \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}` | |
   | bold Greek matrices [M11] | `\mathbf{\Sigma}`, `\mathbf{\Lambda}` | |
   | real part, adjugate, Frobenius inner product | `\operatorname{Re}`, `\operatorname{adj}`, `\langle \mathbf{A}, \mathbf{B} \rangle_{\mathsf{F}}` | |
   | absolute value; epsilon, phi [M16, M8] | `\lvert x \rvert`; `\varepsilon`, `\varphi` | |

   **Probability notation** (maintainer, 2026-10-16): mathematical probability statements use
   `$\mathbb{P}[E]$`, with square brackets around the event [M1]. Use
   `$\mathbb{P}\bigl[E\bigr]$` or `$\mathbb{P}\left[E\right]$` when sizing is needed;
   preserve parentheses belonging to functions inside the event. Conditional probability is
   `$\mathbb{P}[E \mid F]$`; a subscript may identify the random sketch or law. Do not use
   `$P(E)$`, `$\Pr(E)$` or round event delimiters. A displayed high-probability guarantee
   states its event explicitly, for example `$\mathbb{P}[\mathrm{error}\le t]\ge1-\delta$`;
   prose may still say "with probability at least $1-\delta$". This is a documentation
   convention; formal Lean statements keep the measure interface in §5.4.

   A conclusion with a fraction or longer than a line is displayed (`$$…$$`, review list: [D3]),
   a long display split with `\begin{aligned}`; `\frac` in displays, `/` inline [D4].
   Punctuation that ends a sentence after a display goes inside it (`… \,.$$`) [D5]. Mathematics
   stays out of citation brackets [C3]: the label in `[Key, label]` is plain text, and a remark
   with mathematics follows the bracket. A matrix variable is bold (review list: [M18]). A symbol
   the table does not fix (a Rayleigh quotient `\rho`, a gap `\delta`) is introduced in words
   where it is used.

   `scripts/check_latex.mjs` renders every docstring's LaTeX with KaTeX in CI and fails on an
   error; it checks the syntax, not that the LaTeX says what the Lean says, which is the
   reviewer's job.

Module docstrings follow Mathlib [D9]: `# Title`, a paragraph, `## Main results` [D10] listing the
names, which exist [D11].

The explorer separates mathematical headlines from supporting API. Named bounds registered in
`docs/constants.toml` are supporting API by default: searchable, linkable and available with the
file's other declarations, but not separate headline catalogue entries or graph nodes. An entry
may set `explorer_role = "concept"` when the definition itself warrants headline presentation.
This is presentation metadata; it does not change visibility or the Lean API. Module summaries
list actual declaration names, with supporting numerical API in a separate section when useful.

For results with `Asymptotic:` metadata, the explorer leads with the asymptotic docstring and
offers the corresponding explicit bound alongside it. Both docstrings must therefore state
their hypotheses and conclusions independently; the explicit theorem remains the primary Lean
API. At least one member of every explicit/asymptotic pair carries a `Result:` id so the pair
appears in result navigation; the reference checker enforces this. The extraction wrapper
records source hashes so source-body enrichment cannot silently
combine extracted declarations with a different checkout.

`scripts/check_refs.py` fails CI on an unknown bibliography key or a malformed result id.
`docs/references.bib` grows by adding the entry before citing it; keys are `AuthorSurnames + year`
[C5], once each [C6], in alphabetical order [C7]; an entry nobody cites is on a review list [C8].

## 7. Proofs and what each library may contain

- `import NLAlib` is sorry-free; `scripts/Audit.lean` checks every reachable declaration against
  `propext`, `Classical.choice`, `Quot.sound` only.
- `lakefile.toml` has two libraries that matter to contributors. `NLAlib` is the library: proved,
  documented and checked by every rule here. `NLAlibTools` holds tools that are not part of the
  library: the `Float` interpreter, the NumPy emitter of first-order trees and the fixed-point
  example. Its files import `NLAlib`, are plain (non-`module`) files so that `#eval` runs the
  library's programs, may contain `sorry` and are not held to the library's rules; CI builds
  them, checks their root file and replays them, non-strictly.
- A library docstring has no `Proof:` sketch line [D8]: what is merged is proved.
- Proofs are free to differ from any source. Choose the argument that is shortest in Lean and
  reuses the most library API; a clever proof from the literature is worth nothing if a
  three-line one through Mathlib exists.
- Proof style: tactic proofs, `simp only` with named lemmas rather than bare `simp` on large
  goals, no `simp_all` [S1], no `decide` on anything but tiny finite goals (review list: [S3]),
  `nlinarith`/`positivity`/`gcongr` welcome. A proof over 80 lines is split into named lemmas
  [S4]. Terminal `exact?` and `apply?` do not appear in committed code [S2].
- Nothing in `NLAlib/` (or the `leanOptions` of `lakefile.toml`) is
  `unsafe`, `partial`, `implemented_by` or `extern`, or sets a `debug.` option or a kernel option
  (`set_option debug.skipKernelTC true in` makes the elaborator skip the kernel, and an `unsafe`
  definition then inhabits any type with no axiom) [S9] (final audit, 2026-10-24). The checks
  behind it: `scripts/Replay.lean` sends every constant of the package's `.olean` files (every
  library of `lakefile.toml`) to the kernel again (Lean core's `Environment.replay`, as
  `lean4checker` does), trusts as its base only modules read from `.lake/packages/` and the
  toolchain, and in `NLAlib` (and any library it imports) fails on an `unsafe` or `partial`
  constant, an axiom or a use of `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or
  `Lean.trustCompiler`; `scripts/Audit.lean` fails on an `unsafe` or `partial` constant.
- `NLAlib`, every file and the root `NLAlib.lean`, imports no other library of the package:
  neither `NLAlibTools` nor any other library of `lakefile.toml` [P3, P12]
  (final audits, 2026-10-24). It imports itself, Mathlib and Mathlib's dependencies only.
- Instances: no global instance on a Mathlib type unless it is the one Mathlib would add
  (`Matrix.instMeasurableSpace` is the one exception, in `ForMathlib`; the others are allowlisted
  with their reason) [S6]. No `attribute [instance]` at file level [F9].

## 8. Designing new material

New material of any size (a new topic, a new interface, a new layer, or a batch of results that
will be built on) starts with a design note, `docs/design/<Topic>.md`, reviewed before the proofs
are written. It answers, with specifics:

1. **Objects.** Which definitions it introduces, each as a §5.3 row with its Mathlib bridge, and
   which Mathlib objects it uses directly instead.
2. **Interfaces.** Which hypothesis predicates and structures (§5.4) it introduces or extends,
   what each bundles, and the raw-condition constructor for each.
3. **Statement shapes.** For each headline result, the exact Lean signature: field, index types,
   interfaces taken, conclusion form, constants handling (§5.2), and the corollaries it will have.
   Written out, not described.
4. **Consumers.** For each interface and headline statement, which later topic or layer will use
   it and in what form; a statement with no foreseeable consumer is questioned.
5. **Files.** The file split, each file a topic of up to about 1000 lines, with the declarations
   it will hold in order.
   **Placement** (maintainer, 2026-10-15): every new declaration, including each one added to a
   lower layer or to an existing file, goes where a user looking for its topic would find it,
   judged by what the statement is about, never by what its proof imports. The note lists every
   addition outside its own new files with its home and a one-line reason. A declaration placed
   anywhere else (for an import cycle, or a file that cannot yet import it) is flagged in the note
   with its intended home. Reviews check placement explicitly (review list: [P10]).
6. **Material.** Which sources and existing developments were read, what in them is reused (as
   mathematics to cover, as proof material), and what is deliberately not reproduced and why
   (twins, bundles, transport lemmas, local interfaces).
7. **Open questions** for the maintainer, with a recommendation each.

For each bridge and each API lemma that restates a Mathlib fact, the note names the Mathlib lemma
it found, or records "searched, none". An exact overlap ships as an `alias` or a one-line proof
citing the Mathlib lemma, never as an independent proof. A file added or split during the work is
recorded as a dated amendment to the note's file list.

**Deviations from Mathlib are recorded.** Where Mathlib has a notion and the library states things
with another one (a different index type, a total function in place of one that takes a proof, a
named function in place of a scoped instance, a new predicate next to a Mathlib one), the design
note says so, and `docs/design/Mathlib-deviations.md` gets an entry in the same commit: what
Mathlib has, what the library does, why, what it costs, and the bridge lemma; an entry has the
fields Mathlib, NLAlib, Bridge, Why, Cost and Status [G1]. A deviation with no entry is a defect.
(Maintainer, 2026-10-14.)

The note is reviewed as a design, with the question "will this be the interface people reach for
in five years?". The implementation PRs reference it. A divergence discovered during
implementation is a one-line amendment to the note, approved the same way.

## 9. Workflow, checks and pull requests

**Pull requests.** One topic per branch and PR. A PR adds or changes one file's worth of
mathematics (a new topic file, or a coherent change to one), plus the consumers it breaks. It
contains complete, checked work: every statement proved, documented and cited, and the checks
below green. How you stage unfinished work on your own branch is up to you.

**The one command before a PR.** From the repository root, with nothing else building:

```
bash scripts/stage_check.sh > /tmp/stage-check.log 2>&1; echo $?
```

It must exit 0. It writes its logs to `$TMPDIR/nlalib-stage-check` (default `/tmp`). With an
up-to-date build it takes roughly 10 to 20 minutes (9 minutes measured with 3 Lean threads, most
of it the kernel replay, the extraction and the full build); after a Mathlib bump or a change low
in the import graph, longer.
It runs, in order:

1. `lake build --wfail` of every NLAlib module (warnings are fatal, as in CI), then the axiom
   audit `scripts/Audit.lean` and the environment linters `scripts/Lint.lean` on those modules;
2. `lake build` of every library of `lakefile.toml`, `lake exe mk_all --lib NLAlib --check` (the
   root `NLAlib.lean` is current), and the freshness check `lake build --no-build --rehash`;
3. the kernel replay `scripts/Replay.lean` (every constant re-checked by Lean's kernel, §7) and
   its fixtures `scripts/replay_fixtures.sh`;
4. the program checks `scripts/Programs.lean` (E2, E4, E9), the target lint `scripts/Targets.lean`
   (E3: the registry, its closure hashes and its approval) and `scripts/AccessModelFixtures.lean`
   (§5.5);
5. `scripts/check_refs.py` (citations, result ids, `Asymptotic:` and `Algorithm:` tags),
   `scripts/gen_rules_md.py --check` (the generated rule files are current),
   `scripts/check_constants.py` (named-bound values, §5.2), and `scripts/check_latex.mjs`
   (docstring LaTeX renders with KaTeX; skipped with a message if KaTeX is not installed:
   `npm install --no-save --no-package-lock katex@0.16.22`);
6. the declaration extraction (`scripts/Explore.lean`) and `scripts/check_rules.py` on it: every
   rule with an id, the naming rules N1–N18 included, against the ratchet (§9.1);
7. the duplicate-statement report `scripts/Duplicates.lean`, which never fails the script.

`scripts/stage_check.sh EXCLUDE_REGEX` leaves out the modules matching the regex from steps 1
and 6, for files you are still editing. CI (`.github/workflows/ci.yml`) runs the same checks on
every push and PR, and in addition the unit tests of the checks
(`python3 -m unittest discover -s scripts -p 'test_*.py'` and
`node --test scripts/test_check_latex.mjs`, also on Windows) and `mk_all --check` for
`NLAlibTools`; run the unit tests too if you touched `scripts/`.

While working, the fast checks are `lake lean <file> -- -M 8000` (§10) and
`python3 scripts/check_rules.py --files <the files you changed>`, which checks the source-text
rules (P1, P3, P11, P12, E5, the docstring, citation and notation rules) in seconds without a
build.

**When a step fails.** A build or linter failure is fixed in the source; `--wfail` makes every
warning fatal. An Audit or Replay failure means an axiom, `sorry`, `unsafe` or `partial` constant
reached the library (§7). A `mk_all` failure: run `lake exe mk_all --module --lib NLAlib`. A
freshness failure: rebuild. A Targets failure on the approval hash means `docs/targets.toml`
changed: only the maintainer approves it (§5.5); never edit `docs/targets.approved`. A
message of the rules checker reads `<ID> <file>:<line> <declaration>: <what is wrong and the
fix>`; `python3 scripts/check_rules.py --list` prints every id.

**The pull request.** The description contains a read-back: for each headline theorem, what the
Lean statement says, written from the Lean alone (hypotheses, conclusion, degenerate cases). The
reviewer checks the read-back against the design note and the source, the names against §4, the
hypotheses against §5.4, the vocabulary against §5.3. A green CI plus one approving review
merges; a change to a §5.3 row or a §5.4 interface needs two. Changes to the checks, the rule
data, the allowlists, the ratchet baseline, CI and the target registry need the maintainer's
review (`.github/CODEOWNERS`).

Branches are named by kind: `feat/`, `fix/`, `design/`, `cleanup/`, `docs/`. A commit message
starts with the file or topic it changes and says what changed (`Krylov/CG: …`).

Mathlib bumps are their own PRs and are tagged. Releases are tagged with the Lean version they
build against (`v4.33.1-nlalib.1`).

### 9.1 The rules checker

The rule data is in `docs/rules/rules.toml`, one entry per id: area, severity, what the check
needs, scope (the whole library or topic directories), the rule in one line, the fix and the
section here. It is the single source: `scripts/check_rules.py` and `scripts/check_names.py`
take severity, messages and scope from it, and `scripts/gen_rules_md.py` generates from it
`NLAlib/<Topic>/RULES.md`, the rules of one topic with its own first, and
`docs/rules/DIGEST.md`, every error rule in one line. CI and `scripts/stage_check.sh` fail when a
generated file is stale (`--check`); a test checks that every id stated here is in `rules.toml`
and the reverse.

`python3 scripts/check_rules.py [DATA.json]` checks every rule with an id, the naming rules
included, on the extraction that `scripts/explore_data.sh` writes from the built library (about
a minute after `lake build NLAlib`), and prints each violation as `<ID> <file>:<line>
<declaration>: <what is wrong and the fix>`. Without the extraction it checks the source-text
rules only (`--files <files>`). `scripts/check_names.py` is the naming part (§4), with
`scripts/names_allow.toml` as its allowlist (§4.5).

- **Errors and warnings.** An error fails CI. A warning is a heuristic too noisy to fail on (its
  message says so); `--warnings` prints them, and reviewers read them as a review list.
- **The ratchet** (maintainer, 2026-10-19). Debt that existed when a rule became checked is in
  `scripts/rules_baseline.json`, a count per rule and file. A count may only fall: CI fails when it
  rises, and on any violation of a rule with no baseline entry. When a count falls the check says
  so; lower it in the same commit with `--update-baseline`, which refuses to raise a count unless
  `--force` is given. `--force` is for the maintainer: a PR that raises a count says so and needs
  his approval. The baseline file itself lists what is left, by rule and file.
- **The allowlist** `scripts/rules_allow.toml` holds false positives: the rule, the declaration
  (or the file), and a reason. It is never the fix for a real violation, and a stale entry fails.
  An entry is proposed in the PR and approved by the maintainer.

### 9.2 Adding or changing a rule

A rule that arrives as text alone drifts; every rule that shipped with a check and a sweep has
held. So a PR that adds or changes a rule:

1. ships with its entry in `docs/rules/rules.toml` (then `python3 scripts/gen_rules_md.py`) and
   its check in `scripts/check_rules.py` (or `check_names.py`), with a fixture in
   `scripts/test_check_rules.py` that breaks it and one that keeps it, **and** with a sweep of the
   library in the same PR or the remaining count in the baseline; or it says in its text that it is
   judged by review only;
2. is checked for conflicts with the other documents that state rules: this file, `AGENTS.md`,
   `docs/design/Mathlib-deviations.md` and the headers of `docs/references.bib` and
   `docs/constants.toml` (grep the rule's key terms); a conflict is fixed in the same PR, so that
   an author cannot follow one text and break another;
3. gives the rule an id in the area's letter series, cites it in brackets where the rule is
   stated, and uses the same id in the check's messages. Ids are never reused.

### 9.3 The other scripts

`scripts/check_constants.py` enforces §5.2 rule 2's displayed values: every named bound's body
matches `docs/constants.toml`, every math span annotated by a value marker contains its filled
template, and every docstring that names a registered bound shows its value. After a change to a
bound, `--update NAME` rewrites its values inside the annotated spans from the registry's
`previous_latex` and records the new body.

`scripts/check_refs.py` also checks §5.2 rule 3's tags: each `Asymptotic: NAME` line is the last
line (before `Result:`) of an `exists_forall_` theorem's docstring, `NAME` is declared in the same
file, and each docstring names the other in backticks in a sentence (the explorer's "Related"),
the explicit one with "Asymptotic form: `…`."; a tag too long for 100 characters puts
`NAME` alone on the next line.
It also checks §6 item 4b's `Algorithm:` tags [A1, A2, A3], with the same messages as
`scripts/check_rules.py`, and counts the algorithm ids in use.

`scripts/Duplicates.lean` is a report, not a gate: it lists library theorems (private ones
included) whose statements coincide with another library or Mathlib theorem up to universe
levels, binder names, metadata and eta, confirmed by reducible `isDefEq`. A private lemma that
duplicates a public one is deleted in favour of the public one.

`scripts/Reuse.lean` lists, for each declaration named in `scripts/reuse_targets.txt` (or every
public theorem of a `module M` line), the NLAlib and Mathlib constants its proof uses directly,
grouped by module. Run it on a PR's headline theorems to check that they are proved from the
library's API for their topic rather than re-derived.

## 10. Building without running out of memory

Heavy files on top of Mathlib take 3 to 6 GB each, and a default `lake build` runs one Lean
worker per core. Rules:

- **Never run a bare `lake build`.** Use `LEAN_NUM_THREADS=4 lake build <targets>` (on a machine
  with 8 cores and about 32 GB; scale to yours), and `LEAN_NUM_THREADS=2` when another build, a
  Lean language server with files open, or another agent is running on the machine.
- Lake 5 has no `-j` flag. The `LEAN_NUM_THREADS` environment variable caps the number of Lean
  processes Lake runs at once (measured: `LEAN_NUM_THREADS=N` gives exactly `N`).
- Check a file with `lake lean`, not `lake env lean`. `lake env lean` ignores the options in
  `lakefile.toml`, so `autoImplicit` is on (a typo becomes a variable) and the Mathlib linters are
  off. `lake lean <file> -- -M 8000` applies them and builds missing imports first; prefix it with
  `LEAN_NUM_THREADS=2`.
- **One build per checkout at a time.** If `lake build` is running, wait for it.
- **Check a single file** with `lake lean NLAlib/Matrix/Spectral/Weyl.lean -- -M 8000`
  (`-M` caps that process at 8000 MB). Imports of other NLAlib modules need their `.olean`:
  `LEAN_NUM_THREADS=4 lake build NLAlib.Matrix.Norms.Spectral` first.
- **Run long builds in the background with a log**: `LEAN_NUM_THREADS=4 lake build NLAlib > /tmp/build.log 2>&1`,
  then read the log. Do not stream a full build into a terminal or an agent's context.
- **Keep files under about 1000 lines and proofs under 80 lines.** Memory and heartbeat blowups come from
  single huge elaborations: a `simp` with hundreds of lemmas, an `nlinarith` on a goal with many
  atoms, a `decide` on a finite type. Split the proof.
- **Never `import Mathlib` or `import Mathlib.Tactic`**, even in a scratch file inside the
  repository; both load far more than needed.
- `lake exe cache get` fetches Mathlib's oleans once; never build Mathlib from source.

## 11. AI agents

The rules here apply to agents unchanged. `AGENTS.md` adds the few that are specific to agents
(what they may not edit, push or register). A brief to an agent that writes or reviews library
code includes `docs/rules/DIGEST.md` whole and the `NLAlib/<Topic>/RULES.md` of each topic it
touches, so that the rules are in its context (maintainer, rules decision 7).
