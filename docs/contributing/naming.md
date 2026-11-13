# Names

Part of the [contributor guide](../../CONTRIBUTING.md).

Mathlib's conventions, https://leanprover-community.github.io/contribute/naming.html, in full,
refined below into one grammar for the whole library (the evidence and the decisions are in
`docs/design/Naming.md`). Each rule has an id, N1 to N18, which reviews and
`scripts/check_names.py` cite. A theorem's name is its conclusion read left to
right, then its hypotheses: someone who knows the statement can guess the name, and someone
who reads the name knows the statement.

| Kind | Case | Examples |
|---|---|---|
| theorem, lemma | `snake_case` | `frobNorm_nonneg`, `specNorm_mul_le`, `singularValues_add_le` |
| definition returning data | `lowerCamelCase` | `specNorm`, `singularValues`, `rangeProjector` |
| structure, class, type abbreviation, standalone predicate | `UpperCamelCase` | `IsSVD`, `HasOrthonormalCols`, `IsSubspaceEmbedding` |
| predicate component or verb API | `lowerCamelCase` | `admissible`, `contracts`, `inBlock` |
| namespace, file, directory | `UpperCamelCase` | `NLAlib.Matrix.Spectral.Weyl` |

## 1. Grammar

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
spellings of §3. Hypothesis variables are `h`-prefixed (`hA`, `hQ`, `hk`). Examples:

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

## 2. Rules for every topic

| id | rule | checked |
|---|---|---|
| N1 | Case by kind, as in the table above; acronyms follow Mathlib's grouping (`rsvd`, `earlyTruncatedRSVD`). Compiler-generated parser declarations are syntax support, rather than authored data API names. | lexical checks |
| N2 | The first token is the head of the conclusion's left side, or an operator on its leftmost spine (`mul_` for `c * f x ≤ …`), `nonneg`/`pos` for `0 ≤ x`/`0 < x` (`frobNorm_nonneg`), or the layer `exists_`, `forall_`, `ae_`. Mathlib's dot-notation readings stand: `(M).submatrix e f` is `submatrix_…`, a measure `ν.map f` is `ν_map_…` (`gaussianReal_map_add_const`). | review warning |
| N3 | The conclusion part ends at the first `_of_` and names the main relation: `le`, `lt`, `ne`, `iff`, `mem`, `subset`, `nonneg`, `pos`; `eq` may be omitted, as in Mathlib; `ge`/`gt` only when the second argument is the one that varies; Mathlib's `mono`, `anti`, `monotone`, `antitone` count. Nothing of the conclusion comes after `_of_` (`variance_quadForm_le_of_hasLaw_rademacherVector`, not `…_of_hasLaw_rademacherVector_le`). | review warning |
| N4 | Every token that is a library function occurs in the statement, conclusion tokens in the conclusion and hypothesis tokens in the hypotheses. Matrix notation counts (`conjTranspose` for `ᴴ`, `mulVec` for `*ᵥ`, `integral` for `∫`). | review warning |
| N5 | One token per concept: the spellings of §3, never a synonym. | the listed synonyms |
| N6 | A power comes after its argument, for every head: `frobNorm_sub_rsvd_sq`, `singularValues_sq`, `sum_singularValues_sub_sq_le` (Mathlib's `norm_sub_sq`). `^ 2` is `sq`, `^ n` is `pow`, `^ r` (real) is `rpow`. Mathlib's own `sq_abs`, `sq_sqrt` are Mathlib's names, not a pattern. | review warning |
| N7 | No source, chapter, author, lemma number or project in a name, and no word for how good a bound is (`_sharp`, `_improved`, `_tight`, `_v2`, `_strong`) or for its role (`aux`, `main`, `key`); the source goes in the docstring ([statements](statements.md) §2 "Numerical bounds"). Classical names stay where the subject uses them (`bernstein`, `hansonWright`, `freedman`). | yes |
| N8 | Right-side tokens only to tell coexisting theorems apart ([statements](statements.md) §2 rule 4): `measureReal_norm_sq_ge_mul_card_le` next to `measureReal_norm_sq_le_mul_card_le`. A bound that improves keeps its name. | no |
| N9 | Hypotheses. A law is the suffix `_of_hasLaw_<law>`, for any law (`_of_hasLaw_gaussianMatrix`, `_of_hasLaw_haarFrame`). A distribution class is `_of_<class>`, also when it is an instance argument (`_of_isSubgaussianVector`, `_of_isLeftUnitarilyInvariant`, `_of_isIsotropic`). A sketch-property interface that is the main hypothesis (`HasSubspaceInjection`, `IsObliviousSubspaceInjection`, `HasSubspaceEmbedding`, `IsObliviousSubspaceEmbedding`, `HasJLMoment`, `HasJLProperty`, `HasProjectionCostPreserving`, `HasGramTraceMoment`, `HasMatrixMGFBound`) is the namespace: `HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le`. The API of a predicate or structure lives in its namespace, and so does a theorem whose first explicit argument is one of the hypotheses of N18. `HasLaw.` is never a namespace for a consumer; a law hypothesis first is named by its suffix. Other hypotheses are named only when they distinguish the theorem from a sibling. | the law suffix |
| N10 | Errors are `exact − computed`, so names say `norm_sub_<alg>`: `frobNorm_sub_rsvd`, `quadForm_sub_cgIterate`, `trace_sub_hutchpp`. A name never has `<alg>_sub_…`, except `<alg>_sub_truncatedSVD` (the optimal approximation of the algorithm's output, `frobNorm_rsvd_sub_truncatedSVD_le`), `<iterate>_sub_mem` (`x_k − x_0 ∈ K`, not an error) and a final `_sub` of a linearity lemma (`lanczosFA_sub`). | yes |
| N11 | Named quantities and tail expressions are definitions named for what they are (`bernsteinTail d v L t`, `pseudoConditionNumber A`), never inline formulas repeated across statements. A named bound (`docs/constants.toml`) ends in its kind: `…Constant` (an absolute constant), `…Factor` (a multiplier in a bound), `…Tail` (a failure probability), `…Bound` (another bound), `…Ratio`, `…Dim` (a sample size, §4). | the suffix |
| N12 | Renames. Before the `v0.1` tag a rename needs no alias; it is listed in a rename map `docs/renames/<YYYY-MM>-<topic>.json` (`{"renames": [{"old", "new", "rule"}], "statementChanged": [names]}`, full names), from which the explorer redirects old `#d/` links. A deleted declaration is listed with `"removed": true` and, as `new`, the declaration that now carries its content (a Jensen corollary's higher-moment theorem, T15). After `v0.1`, a rename keeps `@[deprecated (since := "YYYY-MM-DD")] alias old := new` for one release, and is also listed in a rename map. | no |
| N18 | Dot notation. A root-namespace theorem whose first explicit argument is `hA : A.IsHermitian`, `hA : A.PosSemidef`, `hA : A.PosDef` (of any matrix expression, `(fromBlocks A B Bᴴ C).PosSemidef` included), `h : IsSVD A U σ V` or `hU : HasOrthonormalCols U` lives in that predicate's namespace (`Matrix.IsHermitian.eigenvalue_add_le`, `HasOrthonormalCols.gramSchmidtQ_mul_left`), so that `hA.eigenvalue_add_le hB k` works; the name then drops the `_of_<predicate>` it no longer needs (`Matrix.PosSemidef.re_det_fromBlocks_le`). A theorem already in an interface namespace (N9) or another predicate's namespace keeps it, and asymptotic forms stay in the root namespace (N17). | yes |

## 3. Spellings

The tokens of the [vocabulary](vocabulary.md) vocabulary, and the ones a statement shape forces:

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

## 4. Rules by subject

**Probability: statistics and tails** (Probability, RandomMatrix, and every tail bound elsewhere).

| id | rule | checked |
|---|---|---|
| N13 | A statistic on the left is the prefix: `integral_` (Bochner `∫ … ∂μ`), `variance_` (`Var[…]`), `covariance_` (`cov[…]`), `condExp_` (`μ[…\|m]`); never `expected`, `expectation`, `mean`. A mean square `∫ ‖·‖ ^ 2` has `_sq` before the relation (`integral_frobNorm_sub_rsvd_sq_le`); a mean `∫ ‖·‖` has none. | yes |
| N14 | The tail prefix follows the statement, in every namespace, Mathlib's included: `μ.real {…}` is `measureReal_`, `μ {…}` (in `ℝ≥0∞`) is `measure_`. Tails are stated in `μ.real` ([statements](statements.md) §2). Mathlib's own declarations keep their names (`HasSubgaussianMGF.measure_ge_le`). | yes |
| N15 | The event comes first, subject first: the subject is the side that mentions `ω`, named by its tokens, then the event relation, then the tail relation: `{ω \| b < X ω}` is `X_gt`, `{ω \| b ≤ X ω}` `X_ge`, `{ω \| X ω ≤ b}` `X_le`, `{ω \| X ω < b}` `X_lt`; so a tail name has two relation tokens, `measureReal_frobNorm_sub_rsvd_sq_gt_le`. A subject with no token (a variable function `f (X ω)`) is left out: `measureReal_ge_integral_add_le`. A scalar event is stated positively, `{ω \| b < err ω}`, never `{ω \| ¬ (err ω ≤ b)}`, and `¬ ∀ i, x i ≤ b` is stated `∃ i, b < x i` (`measureReal_exists_…_gt_le`). `¬` stays only where there is no `<` form: a Loewner inequality, a conjunction, a named predicate (`measureReal_not_isSubspaceEmbedding_le`); the name says `not_`. | yes |

**Sketching, low-rank approximation, regression.**

| id | rule | checked |
|---|---|---|
| N16 | A sample size (rows of a sketch) is a named bound `<sketch><property>Dim`: `jlDim`, `gaussianEmbeddingDim`, `gaussianInjectionDim`, `subgaussianJLDim`, `subgaussianEmbeddingDim`, `countSketchEmbeddingDim`, `samplingEmbeddingDim`, `samplingInjectionDim`, `projectionCostTailDim`; never `…Rows`, `…Size`. The theorem that assumes it is `_of_<size>_le`. Algorithm errors follow N10 and the algorithm tokens of §3; interfaces give the namespace (N9). | the suffix (N11) |

**Trace estimation.** No rule of its own: errors are `tr A − estimate` (N10), so
`trace_sub_hutchpp`, `integral_norm_trace_sub_girardHutchinson_sq`,
`measureReal_abs_trace_sub_hutchpp_ge_le`.

**Matrix and Krylov.** No rule of its own beyond §3. A leading scalar factor is named
(`mul_matrixNorm_…` for `δ * ‖·‖`), so a reader looking for the measured quantity skips
`mul_`. `x_k − x_0 ∈ K` statements are `cgIterate_sub_mem_krylovSpace` (N10).

**Asymptotic forms** ([statements](statements.md) §2 rule 3).

| id | rule | checked |
|---|---|---|
| N17 | The name of an `O(·)` corollary is derived from its explicit theorem: `exists_forall_`, then the explicit conclusion part (for `integral_`/`variance_` names, up to its main relation, the right-side tokens dropped), then `_of_singularGapRatio_pos` for a gapped bound, then the explicit hypotheses without the size threshold (`_of_jlDim_le`, `_of_le_card`, …). It is in the root namespace: `∃ C` comes before every hypothesis, so dot notation is impossible. `integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix` → `exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`. | yes |

## 5. Exceptions and the allowlist

Choose predicate case by its API role: standalone propositions use UpperCamelCase, while
components and verb APIs may use lowerCamelCase. The checker cannot infer that role from a
Prop-valued result. Compiler-generated parser names follow Lean's syntax machinery.

A name the checker misreads, because the grammar has no readable form for its statement or
the splitter misparses it, may go in `scripts/names_allow.toml`
with the rule it is excused from and a one-line reason that says why:

```
[[allow]]
name = "exists_bernstein_exponent"
rule = "N3"
reason = "names the optimised exponent θ; the inequality has no readable token form"
```

An entry is reviewed like code and is never the fix for a real violation. The checker fails on a
stale entry (the declaration is gone or no longer breaks the rule), so the list stays short.

## 6. Checking

`scripts/check_names.py` checks the indicated rules on the extraction ([pull requests and checks](../../CONTRIBUTING.md#pull-requests-and-checks)), and prints
`N<k> <name>: <finding>`; in CI it runs inside `scripts/check_rules.py` ([checks](checks.md) §1).
Rule scopes and severities come from `docs/rules/rules.toml`. Reliable case and vocabulary
violations remain errors. N2, N3, N4 and N6 remain visible as review warnings: their checks
guess semantic heads, relations, function occurrences and power arguments from pretty-printed
text. Aliases, notation, local lets and collisions between short function names make those
guesses unreliable, especially for operation-model contracts. A warning asks the reviewer to
check the naming guidance against the actual statement; it does not require a mechanical rename
or a new allowlist entry. The CLI fails on unallowlisted errors and stale allowlist entries.

The checker also cannot judge whether a right side
should be named (N8), whether a hypothesis deserves mention or a side condition the namespace
(N9), argument order inside a long deterministic name, classical names, or whether a `_sub_` is
an error or a comparison. Reviewers check those.
