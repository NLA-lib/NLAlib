# Headline statements: one simple, checkable statement per result

Design note, 2026-11-16. Branch `design/headline-statements` from `origin/main` @ `04935354`.
**Status: the direction is approved by the maintainer (2026-11-16); this note fixes the details
the approval left open and is itself unreviewed. Nothing here is proved, and no Lean file, check
script, rule datum, allowlist or baseline is changed by it.** The guide amendments of §7 are a
separate commit on this branch.

The maintainer's direction: a *headline* theorem must be as simple as possible for a human to
verify against the mathematics, even at some cost in generality. The general theorems stay as
they are; a headline is derived from its general theorem, in the same file, after it. Evidence:
an audit of the `Result:` declarations at `04935354` (sizes carried by index types, and twelve
other inconsistencies), re-counted for this note (§13).

Label convention. **Verified** means read or counted in the source at `04935354` for this note
(method in §13). **Judgment** is a recommendation of this note. **Not elaborated** marks every
proposed Lean signature: this is a documentation task, no `lake` command was run, and the
signatures are written by hand from the general theorems.

Rule labels. The approved standard has six rules. This note calls them H1–H6, because the
letters first used for them (S and P) are taken: `docs/rules/rules.toml` already has S1–S9
(source and proof style) and P1–P12 (placement), and a test
(`scripts/test_check_rules.py`, `test_every_rule_is_cited_where_it_is_stated`) reads every
bracketed id in the guides as a citation of a rule. H is not an area letter in use. The policy
classes for new Lean statements are called W1–W3 here for the same reason:

- **W1**, prove now, mechanical: a headline corollary that instantiates the general theorem at
  `Fin`; a value theorem for a named constant. A short derivation (target: under 30 lines).
- **W2**, prove now, bounded: a missing asymptotic companion; a sample-size form derived from a
  tail; reindexing a hard instance when the API supports it. About 150 lines, no new definition
  or interface.
- **W3**, not now, design first: new mathematics, a changed hypothesis, a new interface.

## Summary

* **Headline** now has one meaning: the one declaration per result id that the explorer shows
  first. The existing guides use "headline theorem" for any declaration with a `Result:` id or a
  bold name ([D12], [D13], `headline()` in `scripts/check_rules.py`); §7 separates the two.
* **Standard (§1).** H1 one headline per id; H2 a fixed docstring layout with a notes block; H3
  sizes are natural numbers; H4 three kinds of constant; H5 the prose probability is the Lean
  event; H6 one letter per role and one statement shape per type of bound.
* **Letters (§2).** Sketch size $\ell$ (Lean `l`), target rank $k$, test matrix $\mathbf{X}$,
  sketch $\mathbf{S}$, iterations and products $q$. No declaration is renamed (letters are not
  name tokens). First priority touches the docstrings and `variable` lines of 238 `Result:`
  declarations in 51 files; iterations $k \to q$ in `Krylov/FinitePrecision` is second priority.
* **Shapes (§3).** Nine templates, each with a worked example from the library. For lower
  bounds the recommended shape is the *hard instance* form. Of the 22 existing lower-bound
  declarations, 7 have it, 4 display the witness or are universal and stay, 8 reach it by
  contraposition (W1), 1 by `Filter.Eventually.exists` (W1), 1 is a hard instance up to a
  rotation, and 1 has no explicit form yet (W3).
* **Probability (§4).** Keep the bad-event tail. The good-event form does not need measurability
  to be *derived* (only total mass one); it needs measurability to be *used*. So it cannot
  replace the tail, and a second wording is not worth having.
* **Designation (§8).** Recommend a Lean-side role on the tag line, `Result: <id> (headline)`,
  over `primary` in the website's `explore/results.toml`. It needs script changes, so until
  then `primary` stays the mechanism and the guides say so.
* **Disagreements with the brief** are collected in §12.

## 0. What exists (verified)

- 1,232 public declarations carry a `Result:` id, 582 distinct ids; 254 ids have more than one
  declaration, 13 have ten or more. (The audit reports 1,220 declarations, 577 ids and 247
  multi-declaration ids from the built extraction; this note parses the sources with
  `scripts/leansrc.py`. The difference is 12 declarations and does not change any conclusion.)
- 477 of the 1,232 signatures mention `Fintype.card` or `[Nonempty …]` (the detector the
  explorer branch uses, `index_typed_sizes` in `explore/library.py`). 178 ids have at least one
  such declaration; for 145 ids every declaration is of this kind, so their headline is a new
  Lean corollary. 404 ids have none: for them an existing declaration can be the headline and
  only its docstring changes. 38 signatures are already over `Matrix (Fin …)`.
  Instance arguments that a file-level `variable` line supplies are not seen by this count.
- The website (`NLA-lib/NLA-lib.github.io`) sets `primary` for 25 ids in `explore/results.toml`
  at `ce5518dc`; for every other multi-declaration id `explore/library.py` line 134 takes the
  first theorem by name. The `latex` override is used by no id. On that repository's branch
  `feat/headline-statements` (`da715f1`) the fallback is at line 162, is recorded as
  `primary_explicit`, and `explore/audit_primaries.py` lists the unchosen ids; the same commit
  adds `split_notes` in `explore/rendering.py`, which H2 below is written to match.
- Thirteen of the fourteen `kind = "constant"` entries of `docs/constants.toml` have a one-sided
  value theorem named `le_<c>` or `<c>_le` (`le_hansonWrightConstant`,
  `le_subgaussianJLConstant`, `subgaussianRowsConstant_le`, …); `gaussianClippedInvMomentConstant`
  has value theorems at two arguments only.

## 1. The standard

Each rule is stated as what a reviewer checks. "The signature" is the Lean statement of the
headline as doc-gen prints it, file-level `variable` binders included.

**H1. One headline per result id.**
1. Exactly one declaration of the id is designated (§8). It is a `theorem`.
2. Every other member of the id is a general form or a variant, and the headline's notes name
   the general form it is derived from.
3. A headline that is a new corollary sits in the file of its general theorem, after it, and
   its proof is an instantiation (W1) or a short derivation (W2); it never repeats a proof.
4. A headline is never chosen by a default. An id with no designated headline is "not yet
   brought to the standard" and is counted as such.

**H2. Docstring layout.** In this order:
1. *Statement paragraph.* The bold name, then the hypotheses and the conclusion, in words and
   LaTeX. Check: every hypothesis of the signature appears, in the order of the signature; the
   conclusion is the Lean conclusion with the same two sides in the same order and the same
   relation; a named predicate in the conclusion (`IsObliviousSubspaceInjection`) is written
   out once by its definition. The paragraph has no backticked Lean identifier, no proof route,
   no tightness or optimality remark, no comparison with another result. Value markers
   (`<!-- value … -->`) are allowed: they are HTML comments, not prose.
2. *Value line.* If the paragraph uses a symbol for a proof-artifact constant (H4), its last
   sentence starts with `Here` and gives each value:
   `Here <!-- value subgaussianJLConstant -->$C = 1/36$.`
3. *Citation*, as now: `[Key, label]` or "No printed source.", then the relation to the source.
   The Jensen sentence of [T15] belongs here; it may name the Jensen lemma in backticks.
4. *Notes block.* A blank line, then one or more paragraphs, the first starting with the
   literal `Note:` at the start of its first line. Everything else goes here: tightness,
   matching bounds, proof route, degenerate cases, Lean names of related declarations, and the
   sentence "General form: `NLAlib.…`". The blank line is required: the explorer's splitter
   looks for a paragraph that starts with `Note:`.
5. *Tag lines* last, as now: `Asymptotic:` (on an asymptotic form only), then `Result:`.

**H3. Integer sizes.**
1. The signature has no `Fintype.card`, no `[Nonempty …]` and no `[Fintype …]` binder for a
   size. Every size that the statement's formulas or side conditions use is a `ℕ` binder, and
   the matrices and vectors are indexed by `Fin`.
2. A block statement is indexed by a sum or product of `Fin`s (`Fin k ⊕ Fin k`,
   `Fin k ⊕ (Fin 3 × Fin m)`), not flattened to `Fin (k + k)` (judgment, §12 item 3).
3. Positivity is an explicit hypothesis `(hk : 0 < k)` exactly when the other hypotheses do not
   imply it. The author says in the PR which of the two holds; removing a positivity hypothesis
   that is implied is W2.
4. No subtraction of natural numbers in the statement ([V2] extended from `Fintype.card n - k`
   to any `ℕ` size): a difference is cast first, `(l : ℝ) - k - 1`, or sits inside a named bound.
5. The docstring writes each size as a plain letter. No `\lvert k \rvert`, no "$k$ nonempty".
6. A declaration whose signature already satisfies 1 can be the headline itself; no corollary
   is added. Examples: the Krylov bounds over `n → 𝕜`, where no cardinality occurs, and the 71
   results of `Krylov/FinitePrecision`, none of which has `Fintype.card` or `[Nonempty …]` in
   its signature (the run models are over `Fin n`).

**H4. Constants.** Three kinds, decided per constant in the PR read-back:
1. *Part of the mathematics* (exact or sharp: the $1 + k/(\ell - k - 1)$ of the Gaussian
   randomized SVD, the $4$ of the CG bound, the $2$ of Hoeffding): written out literally in the
   formula. A named bound of this kind keeps its value marker.
2. *Explicit proof artifact* (`hansonWrightConstant` $= 1/196$, `subgaussianJLConstant`
   $= 1/36$, the $6400$ of the two-pass lower bound, `lanczosBackwardFactor k` $= 400k^3$): a
   symbol in the formula and the value on the `Here` line. A named sample size, tail or factor
   with arguments (`gaussianInjectionDim d ε δ`) is written out as its formula with its value
   marker, and any artifact constant inside it is a symbol.
3. *Not explicit* (`∃ C`): not allowed in a headline.
4. Every named constant a headline shows has a public value theorem: a one-sided comparison in
   the direction the consumers use (`1 / 196 ≤ hansonWrightConstant` for a constant in an
   exponent, `lanczosBackwardFactor k ≤ 400 * k ^ 3` for a factor in an upper bound).
5. A headline with an artifact constant has an asymptotic companion (`exists_forall_…`,
   [statements](../contributing/statements.md) §2 rule 3, [N17]); the explicit theorem is the
   headline. The companion stays paired with the general theorem (§7.6).

**H5. Probability.** The Lean statement is `μ.real {ω | bad ω} ≤ δ` ([T14]). The docstring
writes exactly that event and that bound, `$\mathbb{P}[\,\text{bad}\,] \le \delta$`, with the
two sides of the event in the Lean order. The statement paragraph does not say "with probability
at least", "except with probability", "outside probability" or "failure probability".

**H6. Letters and shapes.** The letters of §2; the shape of §3 for the type of bound.

## 2. Letters (H6)

### 2.1 What the library does now (verified)

Counts are `Result:` declarations. A random matrix is a binder `V : Ω → Matrix a b F` that the
statement applies to `ω`; binders on file-level `variable` lines are included.

| Role | Sketching | LowRank | Regression | Estimation | LowerBounds | Krylov |
|---|---|---|---|---|---|---|
| sketch size (type whose cardinality is the budget) | `k` (86 decl., 15 files) | `l` (196, 30 files); second sketch `p` (37) | `k` (16) and `p` (17), 8 files | probes `m` (14); Hutch++ `s` and `t` (15 each) | `l` (5), `p` (2) | – |
| target rank, second argument of `truncatedSVD` | `k` (2) | `k` (132), `r` (27), `t` (24), `q` (22) | – | `r` (4), `q` (1) | `Fintype.card k` (6), `q` (4), `k` (1) | – |
| random matrix in Lean | `S` (14), `X` (15), `Q` (15), `G` (12) | `X` (194), `Ψ` (37) | `S` (18), `G` (4), `Q` (8), `X` (3) | `S` (15), `G` (15), `X` (14) | `X` (4+), `Ψ` (2) | – |
| iterations | – | `q` (33) | – | – | queries `q` | `q` (102); `k` in `Krylov/FinitePrecision` (71) |

Further facts:

- **Prose against Lean.** Of 251 declarations whose random matrix is `X` in Lean, the docstring
  writes $\mathbf{\Omega}$ in 97 (LowRank 79, Estimation 14, LowerBounds 4) and $\mathbf{X}$ in
  about 130 (LowRank 109). The reason is mechanical: the deterministic definitions name the
  test matrix `Ω` (`rsvd A Ω`, `nystrom A Ω`, `girardHutchinson A Ω`; 130 binders
  `(Ω : Matrix …)` in 19 files), and a probabilistic theorem cannot, because `Ω` is its sample
  space.
- **Sketch and test matrix.** 208 docstrings say "test matrix" (LowRank 168, Estimation 29);
  169 say "sketch" (Regression 42, Sketching 45, LowRank 58, Estimation 15).
- **Accuracy, failure probability, tail parameter.** `ε` is the accuracy in 126 positivity
  hypotheses, `δ` the failure probability in 82, `t` the free tail parameter in 76. `τ` is a
  tail parameter in 16 Estimation declarations, where `t` is taken by an index type.
- **Subspace dimension** is `d : ℕ` in the oblivious interfaces
  (`IsObliviousSubspaceEmbedding S d a b δ μ`) and the column type `p` of a fixed basis
  `U : Matrix n p 𝕜` in the fixed-subspace ones.
- **Collisions inside a statement.** `k` is the sketch size in Sketching and the target rank in
  LowRank; `HasProjectionCostPreserving (S : Ω → Matrix l n 𝕜) A k a b δ μ` already uses `l`
  for the size and `k` for the rank. `q` is the comparison rank in
  `NLAlib/LowerBounds/LowRank/RotationInvariant.lean` (4 declarations) and the number of
  products everywhere else. `r` is the number of passes in
  `NLAlib/LowerBounds/LowRank/Minimax.lean` and `NuclearMinimax.lean` (4 declarations) and the
  rank of the input elsewhere. `δ` is the relative deviation in the matrix Chernoff bounds.

### 2.2 The table (judgment)

One letter per role, as a pair: the Lean binder and the LaTeX symbol. The pair is fixed, so a
reader can match prose and signature symbol by symbol.

| Role | Lean | LaTeX | Rule |
|---|---|---|---|
| ambient dimensions of $\mathbf{A}$ | `m`, `n` (`A : Matrix (Fin m) (Fin n) 𝕜`); square: `n` | $m$, $n$ | as now |
| target rank | `k` | $k$ | the second argument of `truncatedSVD` in the conclusion |
| rank of the input | `r` | $r$ | only when it is a parameter; otherwise `A.rank`, $\operatorname{rank}\mathbf{A}$ |
| sketch size: rows of a sketch, columns of a test matrix, number of probes | `l` | $\ell$ | |
| size of a second sketch or test matrix | `p` | $p$ | generalized Nyström's $\mathbf{\Psi}$; Hutch++'s residual probes |
| subspace dimension | `d` | $d$ | |
| matrix–vector products, queries | `q` | $q$ | |
| iterations (Krylov steps, block iterations, passes over a recurrence) | `q` | $q$ | an iteration of a single-vector method is one product; a block method with block size $\ell$ uses $q\ell$ or $2q\ell$ products, written as that product |
| accuracy (relative error, distortion, relative deviation) | `ε` | $\varepsilon$ | |
| failure probability | `δ` | $\delta$ | |
| free tail parameter | `t` | $t$ | |
| random test matrix, $n \times \ell$, applied on the right ($\mathbf{A}\mathbf{X}$) | `X` | $\mathbf{X}$ | second one: `Ψ`, $\mathbf{\Psi}$ |
| sketch, $\ell \times n$, applied on the left ($\mathbf{S}\mathbf{A}$) | `S` | $\mathbf{S}$ | a matrix with a named law keeps its letter (`G` Gaussian, `Q` Haar frame) and the statement defines $\mathbf{S}$ from it |

Words: a **test matrix** multiplies on the right and has $\ell$ columns; a **sketch** (sketching
matrix) multiplies on the left and has $\ell$ rows; $\mathbf{S} = \mathbf{X}^{\mathsf{H}}$ relates
them. "Sketch" is never used for a test matrix, and a statement uses one of the two words.

Why these choices minimise change:

- **$\ell$, not $k$, for the sketch size.** With $\ell$: Sketching (86 declarations), Regression
  (33), Estimation (36) change, 155 in 30 files. With $k$: LowRank's 196 size declarations and
  its 132 rank-$k$ statements both change, and the literature's target rank ($k$ in Halko,
  Martinsson and Tropp, in Woodruff, in Tropp and Webber) would need another letter.
- **$\mathbf{X}$, not $\mathbf{\Omega}$, for the test matrix.** With $\mathbf{X}$ the prose
  equals the Lean binder and 97 docstrings change. With $\mathbf{\Omega}$ about 130 docstrings
  change and the prose still differs from the Lean in all 251, unless the sample space is
  renamed in every probabilistic file. The cost of $\mathbf{X}$ is that the literature writes
  $\mathbf{\Omega}$; the citation sentence can say so once ("there $\mathbf{\Omega}$").
- **$q$ for iterations and products.** `q` has 135 uses (Krylov 102, LowRank 33) against 82 for
  `k` (71 in `Krylov/FinitePrecision`, 11 in the CG, MINRES and PCG recurrence files).

### 2.3 What would have to change

No declaration name changes: letters are not name tokens ([N5] spellings are of functions), so
no rename map ([N12]) is needed. The changes are binder names, `variable` lines and docstring
symbols. A binder rename changes named-argument call sites (`(k := …)`); those are found by the
build.

First priority, 238 `Result:` declarations in 51 files (the union of the four rows):

| Change | Declarations | Files | Lean edit |
|---|---|---|---|
| sketch size `k` → `l` in Sketching | 86 | 15 | the `{k n : Type*}` `variable` lines; in a headline `{l n : ℕ}` |
| sketch size `k`, `p` → `l` in Regression | 33 | 8 | `variable` lines of `Regression/*.lean` |
| probes `m` → `l`; Hutch++ `s` → `l`, `t` → `p`; then `τ` → `t` (16 declarations) | 36 | 7 | `variable` lines of `Estimation/Trace/*.lean`, `Estimation/Spectral/*.lean` |
| prose $\mathbf{\Omega}$ → $\mathbf{X}$ where the Lean binder is `X` | 97 | 25 | none |
| sub-Gaussian sketch `X : Ω → Matrix k n ℝ` → `S` in Sketching | 15 | 3 | one `variable` binder per file |

Second priority, done when a file is touched for another reason:

- iterations `k` → `q` in `Krylov/FinitePrecision` (71 declarations in 21 files; 61 docstrings
  use $k$) and in the 11 recurrence statements of `CGRecurrence.lean`, `MINRESRecurrence.lean`,
  `PCGRecurrence.lean` and `Functions/Quadrature.lean`;
- the deterministic binders `(Ω : Matrix …)` → `X` (130 occurrences in 19 files) and the
  definitions' docstrings;
- the three collisions of §2.1: comparison rank `q` → `k` in `RotationInvariant.lean`
  (4 declarations), passes `r` → another letter in the minimax files (4 declarations; `b`
  recommended), Chernoff's deviation `δ` → `ε` (headline only);
- the rank letters `r` (33), `t` (24) and `q` (27) as second argument of `truncatedSVD`. These
  84 declarations were counted, not classified: in the Tropp–Webber bounds `t` is a free
  comparison rank and `r` the target, which is a role the table does not have. Open question 4.

Roles the brief did not list and this note leaves alone: the unit roundoff is `ε` in
`Krylov/FinitePrecision` (a structure field, `L.ε`) and `u` in the `FloatMachine` statements; a
rename to `u` collides with the field `LanczosRun.u`. Backlog (§10).

## 3. One statement shape per type of bound (H6)

Naming of a headline corollary. Its name follows the grammar of
[naming](../contributing/naming.md) applied to *its own* statement; where a size moves from
`Fintype.card k` to a cast `↑k` the name changes by itself
(`div_lt_of_forall_…` becomes `natCast_div_lt_of_forall_…`). Where the grammar gives the general
theorem's name again, this note writes the suffix `_fin`. That suffix is provisional (open
question 1).

Every signature below is **not elaborated**. The one-line proofs are sketches of the
instantiation: `simpa` rewrites `Fintype.card (Fin k)` by `Fintype.card_fin`, and a
`[Nonempty (Fin k)]` instance comes from `0 < k` as `⟨⟨0, hk⟩⟩`.

### 3.1 Algorithm guarantee, high probability

Shape: the sample-size form in $(\varepsilon, \delta)$, bad event.

```lean
theorem measureReal_<error>_gt_le_of_<law>… {m n l k : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    {X : Ω → Matrix (Fin n) (Fin l) 𝕜} (law and independence of X) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : <size> k ε δ ≤ l) :
    μ.real {ω | (1 + ε) * <optimal error> ^ 2 < <error of the algorithm at X ω> ^ 2} ≤ δ
```

The closed-form tail in a free parameter $t$, when there is one, is the general form.

Example: `randomized-svd-tail`. The id has 32 declarations over several kinds of test matrix;
`results.toml` sets `primary` to the Gaussian member,
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`. The sub-Gaussian
member is used here because it shows an index-typed size, a `[Nonempty …]` and a named constant
together. Under H1 it is a variant unless the id is split by law (open question 9).

(a) Current, `NLAlib/LowRank/Oblivious/SubGaussian.lean:143`, under
`variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}`:

```lean
/-- **The randomized SVD with a sub-Gaussian test matrix, relative error**: for $\ell$ nonempty,
if the sketch $\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian rows with
proxy $c$, $\varepsilon, \delta > 0$, <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, and
$\ell \ge 8(16c^2 - 1)k/(\varepsilon\delta)$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)`
and $C$ is `subgaussianJLConstant`. The route: the OSI at constant $1/2$ and failure $\delta/2$,
the JL moment property at $\sqrt{\varepsilon/(4k)}$ and
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_rsvd_sq_gt_le`. Incomparable with its
$\log(1/\delta)$ twin
`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
(rule 4): this one needs fewer columns at constant $\delta$, the twin for small $\delta$; the
asymptotic form `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector` is
proved from the twin.
[Woodruff2014, Lemma 45 and Remark 46]; there for dense sign and Gaussian sketches, constants
unspecified.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : 8 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ
```

What a reader has to untangle: the size is a type ("$\ell$ nonempty"), the prose letter
$\mathbf{\Omega}$ is `X` in Lean, the conclusion is a good event with "except with probability"
where the Lean is a bad event, and the statement sentence carries two Lean expressions, the
proof route and a comparison.

(b) Proposed headline (W1):

```lean
/-- **The randomized SVD with a sub-Gaussian test matrix, relative error.** Let
$\mathbf{A} \in \mathbb{R}^{m \times n}$, let $\ell \ge 1$, and let
$\mathbf{X} \in \mathbb{R}^{n \times \ell}$ be a random matrix such that the $\ell$ rows of
$\mathbf{X}^{\mathsf{H}}$ are independent, sub-Gaussian with proxy $c$, and isotropic. If
$\varepsilon > 0$, $\delta > 0$ and <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$$\frac{25 c^2 (k \log 21 + \log(2/(\delta/2)))}{16 C (1/2)^2} \le \ell
\qquad\text{and}\qquad 8(16c^2 - 1)k \le \varepsilon\delta\ell\,,$$
then
$$\mathbb{P}\bigl[(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
< \|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2\bigr] \le \delta\,.$$
Here <!-- value subgaussianJLConstant -->$C = 1/36$.
[Woodruff2014, Lemma 45 and Remark 46]; there for dense sign and Gaussian sketches, constants
unspecified.

Note: General form: `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`, for
index types of any size. The first size is `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)` and $C$
is `subgaussianJLConstant`. The route: the OSI at constant $1/2$ and failure $\delta/2$, then the
JL moment property at $\sqrt{\varepsilon/(4k)}$. Incomparable with the $\log(1/\delta)$ twin
`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
(rule 4): this one needs fewer columns at constant $\delta$, the twin for small $\delta$. The
$O(\cdot)$ reading is
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_fin {m n l k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hl₀ : 0 < l) {X : Ω → Matrix (Fin n) (Fin l) ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ l)
    (hl' : 8 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε * δ * l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ
-- proof: `haveI : Nonempty (Fin l) := ⟨⟨0, hl₀⟩⟩`, then the general theorem at `Fin`, the
-- two size hypotheses by `simpa using`.
```

`0 < l` is kept explicit: for $c = 0$ both size hypotheses hold at $\ell = 0$, so they do not
imply it. Whether the row hypotheses exclude $c = 0$ is a W2 question for the implementation.

### 3.2 Algorithm guarantee, in expectation

Shape:

```lean
theorem integral_<error>_sq_le_of_hasLaw_<law> {m n l k : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜)
    {X : Ω → Matrix (Fin n) (Fin l) ℝ} (hX : HasLaw X (<law> (Fin n) (Fin l)) μ)
    (hk : k + 2 ≤ l) :
    ∫ ω, <error at X ω> ^ 2 ∂μ ≤ <factor> k l * <optimal error> ^ 2
```

The notes name the integrability lemma of the integrand: a Bochner integral of a non-integrable
function is $0$, so "$\mathbb{E} \le b$" alone says less than a reader assumes.

Example: `randomized-svd-expected-error` (`primary` in `results.toml` is this declaration).

(a) Current, `NLAlib/LowRank/Gaussian/RangeFinder.lean:213`, under
`variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}`:

```lean
/-- **The expected error of the randomized SVD, Frobenius norm** (HMT Theorem 10.5, squared):
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The Frobenius instance of the Gram-form bound above;
Epperly and Webber's sharper factor, with a rank parameter, is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`.
Asymptotic form: `NLAlib.exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; HMT assume $k \ge 2$
and $k + p \le \min\{m, n\}$, neither needed here. [HalkoMartinssonTropp2011, Theorem 10.5]
prints the first-moment form <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,,$$
which follows from this bound by Jensen's inequality
(`ProbabilityTheory.integral_le_sqrt_integral_sq`).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
```

(b) Proposed headline (W1). The factor is exact, so it is written out (H4.1) and there is no
`Here` line:

```lean
/-- **The expected error of the randomized SVD, Frobenius norm.** Let
$\mathbf{A} \in \mathbb{R}^{m \times n}$ and let $\mathbf{X} \in \mathbb{R}^{n \times \ell}$ have
independent standard Gaussian entries. If
$k + 2 \le \ell$, then <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
[HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; HMT assume $k \ge 2$
and $k + p \le \min\{m, n\}$, neither needed here, and write $\mathbf{\Omega}$ for the test
matrix. [HalkoMartinssonTropp2011, Theorem 10.5] prints the first-moment
form <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,,$$
which follows from this bound by Jensen's inequality
(`ProbabilityTheory.integral_le_sqrt_integral_sq`).

Note: General form: `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`, for index
types of any size. The integrand is integrable (`NLAlib.integrable_frobNorm_sub_rsvd_sq`). The
factor is `gaussianProjectionFactor k ℓ`. Epperly and Webber's sharper factor, with a rank
parameter, is `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`. The
$O(k/\varepsilon)$ reading is
`NLAlib.exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_fin {m n l k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {X : Ω → Matrix (Fin n) (Fin l) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin n) (Fin l)) μ) (hk : k + 2 ≤ l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k l * frobNorm (A - truncatedSVD A k) ^ 2
-- proof: the general theorem at `Fin`, `hk` by `simpa using`.
```

### 3.3 Sketch property (OSE, OSI, JL, PCP)

Shape: the sample-size form; the conclusion is the interface predicate, so that the theorem
still composes, and the docstring writes the predicate out.

```lean
theorem is<Property>_of_hasLaw_<law>_of_<size>_le {l n d : ℕ} {G : Ω → Matrix (Fin l) (Fin n) ℝ}
    (hG : HasLaw G (<law> (Fin l) (Fin n)) μ) {ε δ : ℝ} (hε : 0 < ε) (hε' : ε ≤ <range>)
    (hδ : 0 < δ) (hl : <size> d ε δ ≤ l) :
    Is<Property> (fun ω => <scaling> • G ω) d (1 - ε) … δ μ
```

Example: `gaussian-osi` (2 declarations, no `primary`; the alphabetical fallback is the tail
form `NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`, line 556, which has
`[Nonempty k]` and stays as the general form).

(a) Current sample-size form, `NLAlib/Sketching/Gaussian/Gaussian.lean:816`, under
`variable {k n p ι : Type*} [Fintype k] [Fintype n] [Fintype p] {G : Ω → Matrix k n ℝ} … {d d' : ℕ} {t ε ε' δ δ' : ℝ}`:

```lean
/-- **Gaussian OSI, sample-size form**: at
least <!-- value gaussianInjectionDim d \varepsilon \delta -->
$4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2/\varepsilon^2$ rows (`gaussianInjectionDim d ε δ`) give
an oblivious subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon \le 2$ and $0 < \delta < 1$; $k$ is nonempty because
the dimension is positive. [MartinssonTropp2020, §8.7.2] (the tail form: the smallest
singular value of the sketch on the subspace is at most
$1 - (1 + \sqrt{d})/\sqrt{\lvert k \rvert} - t$ with probability at most
$e^{-\lvert k \rvert t^2/2}$); here solved for the row count. Asymptotic form:
`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`.
Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    [DecidableEq n] (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hk : gaussianInjectionDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) δ μ
```

(b) Proposed headline (W1), in the letters of §2 and with the predicate
(`IsObliviousSubspaceInjection`: `IsIsotropicSketch S μ`, and
`HasSubspaceInjection S U a δ μ` for every `U : Matrix n n 𝕜` with `U.rank ≤ d`) written out:

```lean
/-- **The Gaussian sketch is an oblivious subspace injection.** Let
$\mathbf{G} \in \mathbb{R}^{\ell \times n}$ have independent standard Gaussian entries and let
$\mathbf{S} = \ell^{-1/2}\mathbf{G}$. If $0 < \varepsilon \le 2$, $0 < \delta < 1$
and <!-- value gaussianInjectionDim d \varepsilon \delta -->
$$\frac{4 (\sqrt{d} + \sqrt{2 \log(1/\delta)})^2}{\varepsilon^2} \le \ell\,,$$
then the entries of $\mathbf{S}$ are square integrable,
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, and for every
$\mathbf{U} \in \mathbb{R}^{n \times n}$ of rank at most $d$
$$\mathbb{P}\bigl[\neg\,\bigl((1 - \varepsilon)\,\mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq
(\mathbf{S}\mathbf{U})^{\mathsf{H}}(\mathbf{S}\mathbf{U})\bigr)\bigr] \le \delta\,.$$
[MartinssonTropp2020, §8.7.2]; there the tail form, here solved for the row count.

Note: General form:
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le`; the
closed-form tail is `NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`. The
conclusion is the predicate `IsObliviousSubspaceInjection` with constant $1 - \varepsilon$; the
size is `gaussianInjectionDim d ε δ`. The $O(\cdot)$ reading is
`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`.
Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le_fin
    {l n d : ℕ} {G : Ω → Matrix (Fin l) (Fin n) ℝ}
    (hG : HasLaw G (gaussianMatrix (Fin l) (Fin n)) μ) {ε δ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hl : gaussianInjectionDim d ε δ ≤ l) :
    IsObliviousSubspaceInjection (fun ω => (√(l : ℝ))⁻¹ • G ω) d (1 - ε) δ μ
-- proof: the general theorem at `Fin`, `hl` by `simpa using`.
```

No positivity hypothesis: the general theorem has none.

### 3.4 Concentration inequality

Shape: the closed-form tail in a free parameter, as the sources print it.

```lean
theorem measureReal_<statistic>_ge_le… {<sizes> : ℕ} (independence, boundedness, law)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | <threshold in t> ≤ <statistic at ω>} ≤ <tail> <sizes> … t
```

When the statement has no size at all, the existing theorem is the headline (H3.6):
`NLAlib.measureReal_abs_quadForm_sub_integral_ge_le` (`hanson-wright`) takes `x : Ω → n → ℝ` and
its bound does not mention the dimension. Only its docstring changes: the formula writes
$C\min(\cdot,\cdot)$ and the value line is
`Here <!-- value hansonWrightConstant -->$C = 1/196$.` (H4.2).

Example with sizes: `matrix-chernoff-without-replacement`.

(a) Current, `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:203`, under
`variable {k m n : Type*} [Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [MeasurableSpace n] [MeasurableSingletonClass n] {ι : Ω → k → n} {X : n → Matrix m m 𝕜} {L δ : ℝ}`:

```lean
/-- **Matrix Chernoff without replacement, upper tail**, source form. For a population of
$m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over $\Bbbk$,
$i \in n$, $m$ nonempty, with $L > 0$, a uniformly random injection $\iota : k \to n$ (its law
under $\mu$ is uniform on the injections),
$\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$ and $\delta \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \ge
(1 + \delta) \lambda_0(\mathbf{V})\Bigr] \le \lvert m \rvert
\Bigl(\frac{e^\delta}{(1 + \delta)^{1+\delta}}\Bigr)^{\lambda_0(\mathbf{V}) / L} \,.$$
[Tropp2011a, Theorem 2.1] (sampling without replacement from a finite set of matrices; there $B$
is $L$ and $\mu_{\max}$ is $\lambda_0(\mathbf{V})$, here a population that may repeat members);
[Tropp2015, Theorem 5.1.1] (the i.i.d. form, the same bound). No
$\lvert k \rvert \le \lvert n \rvert$: otherwise $\mu = 0$.
Result: matrix-chernoff-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 ≤
        eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 / L)
```

(b) Proposed headline (W1). The file's size letters are kept ($k$ samples from a population of
$n$ matrices of dimension $m$); the relative deviation becomes $\varepsilon$ (§2.2), and the
event is written in the Lean order:

```lean
/-- **Matrix Chernoff without replacement, upper tail.** Let $m \ge 1$, let
$\mathbf{X}_0, \dots, \mathbf{X}_{n-1} \in \Bbbk^{m \times m}$ satisfy
$\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ with $L > 0$, let $\iota$ be a uniformly
random injection of $\{0, \dots, k-1\}$ into $\{0, \dots, n-1\}$, and let
$\mathbf{V} = (k/n) \sum_{i<n} \mathbf{X}_i$. Then for every $\varepsilon \ge 0$
$$\mathbb{P}\Bigl[(1 + \varepsilon) \lambda_0(\mathbf{V}) \le
\lambda_0\Bigl(\sum_{j<k} \mathbf{X}_{\iota(j)}\Bigr)\Bigr] \le m
\Bigl(\frac{e^\varepsilon}{(1 + \varepsilon)^{1+\varepsilon}}\Bigr)^{\lambda_0(\mathbf{V}) / L}
\,.$$
[Tropp2011a, Theorem 2.1] (sampling without replacement from a finite set of matrices; there $B$
is $L$, $\mu_{\max}$ is $\lambda_0(\mathbf{V})$ and the deviation is $\delta$);
[Tropp2015, Theorem 5.1.1] (the i.i.d. form, the same bound).

Note: General form:
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective`, for a
population indexed by any finite type, which may repeat members. No hypothesis $k \le n$: for
$k > n$ there is no injection and the hypothesis on the law of $\iota$ forces $\mu = 0$.
Result: matrix-chernoff-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective_fin
    {k m n : ℕ} (hm : 0 < m) {ι : Ω → Fin k → Fin n} {X : Fin n → Matrix (Fin m) (Fin m) 𝕜}
    {L ε : ℝ} (hι : HasLaw ι (uniformOn {f : Fin k → Fin n | Function.Injective f}) μ)
    (hL : 0 < L) (hpsd : ∀ i, (X i).PosSemidef)
    (hle : ∀ i, X i ≤ L • (1 : Matrix (Fin m) (Fin m) 𝕜)) (hε : 0 ≤ ε) :
    μ.real {ω | (1 + ε) * eigenvalue (((k : ℝ) / n) • ∑ i, X i) 0 ≤
        eigenvalue (∑ j, X (ι ω j)) 0} ≤
      m * (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (eigenvalue (((k : ℝ) / n) • ∑ i, X i) 0 / L)
-- proof: `haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩`, then the general theorem at `Fin`.
```

`0 < m` is explicit: for $m = 0$ both eigenvalues are the junk value $0$, the event is
everything and the bound is $0$.

### 3.5 Lower bound

Six shapes are in use among the 22 lower-bound declarations (verified; the classification is
this note's and differs from the audit's count in two rows):

| # | Shape | Declarations |
|---|---|---|
| A | guarantee ⇒ cost: `(∀ A in the class, p₀ ≤ ρ.real {success}) → bound < q` | 8: `linear-system-matvec-lower-bound`; `two-pass-`, `one-pass-low-rank-lower-bound`; `fixed-batch-low-rank-lower-bound` (2); `fixed-batch-nuclear-lower-bound` (2); `hermitian-diagonalization-precision-lower-bound` (deterministic algorithm, no probability) |
| B | hard instance: `∃ A` (or `∃ b`) in the class with `c * optimal < error` | 7: `randomized-nystrom-`, `randomized-svd-lower-bound`; `generalized-nystrom-lower-bound` (2); `cg-near-optimality-lower-bound`; `lanczos-fa-near-optimality-lower-bound` (2) |
| C | fixed or universal instance: an inequality on a named matrix, on a random instance, or on every matrix of a class | 4: `early-truncated-rsvd-lower-bound` at `Matrix.diagonal ![1, 1 - 1/(4√ℓ)]`; `rbki-multiplicity-lower-bound` (2, every $\mathbf{A}$ with a repeated singular value); `range-recovery-k-queries` (a Gaussian instance, `μ {…} = 0`) |
| D | eventually in a parameter: `∀ᶠ a in atTop, bound - η ≤ ∫ …` | 1: `truncated-gn-lower-bound` |
| E | `∃ U` (a rotation of the given data) | 1: `sketch-and-solve-lower-bound` |
| F | `∃ c C K₀` absolute constants | 1: the block-Gaussian form of `early-truncated-rsvd-lower-bound` |

(The audit counts shape C as 8 and shape B as 3; the totals agree.)

Comparison. A and B are contrapositives of each other by pure logic. A reads as the papers'
sentence ("any algorithm that succeeds on every input uses more than … products") and is the
form a consumer applies to an algorithm's guarantee. B states the bad thing directly, as H5
does for probabilities; its conclusion shows the instance class and the failure in one place;
and it is the only shape that also fits the algorithm-specific bounds, which have no
"guarantee" to assume. C is B with the witness displayed, D and E are B with an extra
quantifier, F is the asymptotic companion of a bound that does not exist yet.

**Recommendation: shape B, the hard-instance form.**

```lean
theorem exists_<class>_<failure>… {<sizes> q : ℕ} (regime) (hq : (q : ℝ) ≤ <threshold>) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, <A in the class> ∧ <lower> < <statistic of the error on A>
```

where the statistic is the error (a deterministic algorithm), its expectation, or
`ρ.real {success}` compared with the success level (`… < 1 / 2`). When the witness is short it
is displayed instead of quantified (shape C stays as it is). The existing theorem of shape A
stays as the general form: it is what consumers apply.

Fit of the existing results:

| Result | Now | To reach B | Class |
|---|---|---|---|
| the 7 of shape B | B | sizes only: `Fintype.card l`, `m`, `n`, `p` → `Fin` for the four rotation-invariant ones; nothing for the three Krylov ones (no index-typed size) | W1 |
| the 6 low-rank query bounds | A | contraposition (`by_contra`, `push_neg`, the general theorem, `not_lt`), with `k`, `m` at `Fin`. The dimension stays the block type `Fin k ⊕ (Fin r × Fin m)` (H3.2) | W1 |
| `linear-system-matvec-lower-bound` | A | contraposition; sizes: `20 * (q + 3) ^ 2 ≤ n` | W1 |
| `hermitian-diagonalization-precision-lower-bound` | A | contraposition; already over `Fin b → ZMod 2` | W1 |
| `early-truncated-rsvd-lower-bound` (diagonal instance) | C | `Fintype.card l` → `l`; the witness stays displayed | W1 |
| `rbki-multiplicity-lower-bound` (2) | C | universal over a class, stronger than B; `Fintype.card l` → `l` | W1 |
| `range-recovery-k-queries` | C | sizes → `Fin`; the statement is in `μ {…}` (`ℝ≥0∞`), not `μ.real` | W1 for sizes; the measure form is W2 |
| `truncated-gn-lower-bound` | D | `Filter.Eventually.exists` gives "for every $\eta > 0$ there is $a$ with …"; blocks at `Fin s ⊕ Fin t` | W1 |
| `sketch-and-solve-lower-bound` | E | already a hard instance $(\mathbf{U}\mathbf{A}, \mathbf{U}\mathbf{B})$; sizes → `Fin`. The statement is a `∫⁻` of `ENNReal.ofReal`; a Bochner form needs integrability | W1 for sizes; the integral form is W2 or W3 |
| block-Gaussian `early-truncated-rsvd-lower-bound` | F | an explicit bound for general $k$ is new mathematics; until then the diagonal instance ($k = 1$) is the headline and this is a variant | W3 |
| any query bound for a general dimension $n$ (not the pinned $n = k + 3\lfloor k/(8\varepsilon)\rfloor$) | – | embedding of the hard instance | W3 |
| any query bound over a flat `Fin n` | – | needs transport of `truncatedSVD` and `QueryAlgorithm` along an `Equiv`; the library has `frobNorm_submatrix_equiv`, `specNorm_submatrix_equiv` and `singularValues_submatrix_equiv` but no such lemma for `truncatedSVD` or the algorithms | W3 (and not recommended, H3.2) |
| the same bounds with a bad event `1 / 2 < ρ.real {failure}` | – | needs measurability of the success event | W3 |

Example: `two-pass-low-rank-lower-bound`.

(a) Current, `NLAlib/LowerBounds/LowRank/FewPasses.lean:962`, under
`variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]`:

```lean
/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: let
$k$ be nonempty, $0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, so the dimension is
$n = \lvert k \rvert + 3\lvert m \rvert < \lvert k \rvert/(2\varepsilon)$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$ with probability at least
$\tfrac12$ for every symmetric $\mathbf{A}$, then
$$q > \frac{\lvert k \rvert}{6400\,\varepsilon} \,.$$
Two passes of randomized SVD with $O(k/\varepsilon)$ products achieve this accuracy in
expectation, so the rate $k/\varepsilon$ is optimal for two-pass algorithms.
No printed source.
Result: two-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q
```

(b) Proposed headline (W1), hard-instance form. No positivity hypothesis: $0 < \varepsilon \le
k/14000$ gives $k \ge 1$. The three numerals are proof artifacts (H4.2):

```lean
/-- **Two-pass low-rank approximation needs more than $k/(C\varepsilon)$ matrix–vector
products.** Let $0 < \varepsilon \le \varepsilon_0$ and $\varepsilon \le k/C'$, let
$m = \lfloor k/(8\varepsilon) \rfloor$ and $n = k + 3m$. Let a randomized algorithm be a
measurable family of deterministic adaptive algorithms indexed by a seed with law $\rho$, each
making $q$ matrix–vector products with its input $\mathbf{A} \in \mathbb{R}^{n \times n}$ in at
most two passes and returning $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$. If
$$q \le \frac{k}{C\varepsilon}\,,$$
then there is a symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$ with
$$\mathbb{P}\bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2\bigr] < \frac12\,.$$
Here $C = 6400$, $\varepsilon_0 = 1/6500$ and $C' = 14000$.
No printed source.

Note: General form: `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`, the
contrapositive, with the blocks indexed by any finite types: an algorithm that succeeds with
probability at least $\tfrac12$ on every symmetric input uses more than $k/(C\varepsilon)$
products. The rows and columns of $\mathbf{A}$ are indexed by the blocks $k + 3 \cdot m$. Two
passes of the randomized SVD with $O(k/\varepsilon)$ products reach this accuracy in expectation,
so the rate $k/\varepsilon$ is optimal for two-pass algorithms.
Result: two-pass-low-rank-lower-bound -/
theorem exists_isHermitian_measureReal_frobNorm_sub_mul_sq_le_lt {k m q : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ k / 14000) (hm : m = ⌊(k : ℝ) / (8 * ε)⌋₊)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (Fin k ⊕ (Fin 3 × Fin m) → ℝ) (Fin k ⊕ (Fin 3 × Fin m) → ℝ) q
      (Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k) ℝ × Matrix (Fin k) (Fin k ⊕ (Fin 3 × Fin m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (hq : (q : ℝ) ≤ k / (6400 * ε)) :
    ∃ A : Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k ⊕ (Fin 3 × Fin m)) ℝ, A.IsHermitian ∧
      ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2} < 1 / 2
-- proof: `by_contra h; push_neg at h`, then the general theorem at `Fin` contradicts `hq`.
```

This is the one template where the prose cannot be short: the model of a randomized pass-limited
algorithm is the hypothesis. The companion H4.5 asks for (`∃ C ε₀ C'` before every size) exists
for no lower bound of shapes A to E and is W2 for each; the one `exists_forall_` theorem among
the lower bounds is the shape F statement, which has no `Asymptotic:` tag.

### 3.6 Deterministic inequality

Shape: hypotheses as interfaces, one inequality; unsquared unless §5 says otherwise.

```lean
theorem <Predicate>.<lhs>_le… {n : ℕ} {A B : Matrix (Fin n) (Fin n) 𝕜} (hA : A.<Predicate>) …
    (hi : <index> < n) : <lhs> ≤ <rhs>
```

Example: `weyl-inequality` (a single declaration, tier 4 of the audit: the only cardinality is
the ambient dimension).

(a) Current, `NLAlib/Matrix/Spectral/Weyl.lean:90`, under
`variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]`:

```lean
/-- **Weyl's inequality.** For Hermitian $\mathbf{A}$, $\mathbf{B}$ and $i + j < \lvert n \rvert$,
$\lambda_{i+j}(\mathbf{A} + \mathbf{B}) \le \lambda_i(\mathbf{A}) + \lambda_j(\mathbf{B})$,
eigenvalues non-increasing and indexed from $0$.
[HornJohnson2013, Theorem 4.3.1]; stated there over $\mathbb{C}$ with eigenvalues in increasing
order.
Result: weyl-inequality -/
theorem _root_.Matrix.IsHermitian.eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    {i j : ℕ} (hij : i + j < Fintype.card n) :
    eigenvalue (A + B) (i + j) ≤ eigenvalue A i + eigenvalue B j
```

(b) Proposed headline (W1):

```lean
/-- **Weyl's inequality.** Let $\mathbf{A}, \mathbf{B} \in \Bbbk^{n \times n}$ be Hermitian and
$i + j < n$. Then
$\lambda_{i+j}(\mathbf{A} + \mathbf{B}) \le \lambda_i(\mathbf{A}) + \lambda_j(\mathbf{B})$,
eigenvalues non-increasing and indexed from $0$.
[HornJohnson2013, Theorem 4.3.1]; stated there over $\mathbb{C}$ with eigenvalues in increasing
order.

Note: General form: `Matrix.IsHermitian.eigenvalue_add_le`, for any finite index type.
Result: weyl-inequality -/
theorem _root_.Matrix.IsHermitian.eigenvalue_add_le_fin {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) {i j : ℕ}
    (hij : i + j < n) : eigenvalue (A + B) (i + j) ≤ eigenvalue A i + eigenvalue B j
-- proof: `hA.eigenvalue_add_le hB (by simpa using hij)`.
```

This is the case where the corollary buys least: its whole content is
`Fintype.card (Fin n) = n`, and [T6] warns on it. §12 item 4 says what to do about tier 4.

### 3.7 Exact identity (unbiasedness, variance)

Shape: an equation, the statistic on the left ([N13]).

```lean
theorem integral_<estimator>… / variance_<estimator>… {n l : ℕ} (hl : 0 < l)
    {X : Ω → Matrix (Fin n) (Fin l) 𝕜} (independence and law of the columns) … :
    <statistic of the estimator> = <closed form in l>
```

Example: `girard-hutchinson-variance`.

(a) Current, `NLAlib/Estimation/Trace/GirardHutchinson.lean:124`, under
`variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [Fintype m]`:

```lean
/-- **The variance of the Girard–Hutchinson estimator**: for $m$ nonempty, independent isotropic
probes whose single-probe estimates are square integrable with second moment $v$ about the mean,
$$\mathbb{E}\lvert \operatorname{tr}\mathbf{A} -
\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega})\rvert^2 = \frac{v}{m}\,.$$
Over $\mathbb{C}$ the left side is the variance of
the complex estimate; the real `variance` form is `NLAlib.variance_girardHutchinson`.
[Epperly2023, Variance].
Result: girard-hutchinson-variance -/
theorem integral_norm_trace_sub_girardHutchinson_sq [DecidableEq n] [Nonempty m]
    {X : Ω → Matrix n m 𝕜} (hind : iIndepFun (fun j ω i => X ω i j) μ)
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜}
    (hL2 : ∀ j, MemLp (fun ω => quadForm A fun i => X ω i j) 2 μ) {v : ℝ}
    (hv : ∀ j, ∫ ω, ‖(quadForm A fun i => X ω i j) - A.trace‖ ^ 2 ∂μ = v) :
    ∫ ω, ‖A.trace - girardHutchinson A (X ω)‖ ^ 2 ∂μ = v / Fintype.card m
```

The docstring already writes $m$ as a number ("$v/m$") next to "$m$ nonempty".

(b) Proposed headline (W1), the number of probes as $\ell$:

```lean
/-- **The variance of the Girard–Hutchinson estimator.** Let
$\mathbf{A} \in \Bbbk^{n \times n}$, let $\ell \ge 1$, and let the columns
$\mathbf{x}_0, \dots, \mathbf{x}_{\ell-1}$ of $\mathbf{X} \in \Bbbk^{n \times \ell}$ be
independent and isotropic, with $\mathbf{x}_j^{\mathsf{H}}\mathbf{A}\mathbf{x}_j$ square
integrable and
$\mathbb{E}\lvert \mathbf{x}_j^{\mathsf{H}}\mathbf{A}\mathbf{x}_j - \operatorname{tr}\mathbf{A}
\rvert^2 = v$ for every $j$. Then
$$\mathbb{E}\lvert \operatorname{tr}\mathbf{A} -
\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{X})\rvert^2 = \frac{v}{\ell}\,.$$
[Epperly2023, Variance].

Note: General form: `NLAlib.integral_norm_trace_sub_girardHutchinson_sq`, for index types of any
size. Over $\mathbb{C}$ the left side is the variance of the complex estimate; the real
`variance` form is `NLAlib.variance_girardHutchinson`.
Result: girard-hutchinson-variance -/
theorem integral_norm_trace_sub_girardHutchinson_sq_fin {n l : ℕ} (hl : 0 < l)
    {X : Ω → Matrix (Fin n) (Fin l) 𝕜} (hind : iIndepFun (fun j ω i => X ω i j) μ)
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix (Fin n) (Fin n) 𝕜}
    (hL2 : ∀ j, MemLp (fun ω => quadForm A fun i => X ω i j) 2 μ) {v : ℝ}
    (hv : ∀ j, ∫ ω, ‖(quadForm A fun i => X ω i j) - A.trace‖ ^ 2 ∂μ = v) :
    ∫ ω, ‖A.trace - girardHutchinson A (X ω)‖ ^ 2 ∂μ = v / l
-- proof: `haveI : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩`, then the general theorem at `Fin`.
```

`0 < l` is explicit: at $\ell = 0$ the estimate is $0$ and the right side is $v/0 = 0$.

### 3.8 Krylov convergence

Shape: the error after $q$ steps against the initial error, a rate to the power $q$, the
spectrum confined to an interval.

```lean
theorem <Predicate>.<error after q steps>_le… {A : Matrix n n 𝕜} (hA : A.<Predicate>)
    {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    <error of the q-th iterate> ≤ <constant> * <rate> ^ <q or 2 * q> * <initial error>
```

No size occurs in the signature, so the existing theorem is the headline (H3.6) and only the
docstring changes.

Example: `cg-chebyshev-bound`, `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`,
`NLAlib/Krylov/LinearSystems/CG.lean:278`, which `results.toml` already names as `primary`.

(a) Current signature (unchanged in (b)) and docstring:

```lean
/-- **The Chebyshev bound for CG** in the condition number $\kappa = a'/a$ of the interval: if
$\mathbf{A}$ is Hermitian with spectrum in $[a, a']$, $0 < a$, and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, then
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2q}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
the square of the classical
$\|\mathbf{e}_q\|_{\mathbf{A}} \le 2\bigl((\sqrt\kappa - 1)/(\sqrt\kappa + 1)\bigr)^q
\|\mathbf{e}_0\|_{\mathbf{A}}$. The proof's polynomial is the shifted Chebyshev residual
(`NLAlib.chebyshevResidual`), whose factor is
$T_q((a' + a)/(a' - a))^{-2} = \operatorname{sech}^2(q \log(1/\rho)) = 4\rho^{2q}/(1 + \rho^{2q})^2$
with $\rho = (\sqrt{a'/a} - 1)/(\sqrt{a'/a} + 1)$ (`NLAlib.inv_eval_T_real_eq_two_mul_pow_div`);
the statement drops the factor $(1 + \rho^{2q})^2 \le 4$, which tends to $1$
(docs/contributing/statements.md §2
rule 7). A Loewner sandwich gives the hypotheses by
`isHermitian_of_le_smul_one` and `spectrum_subset_Icc_of_le`.
[Saad2003, Theorem 6.29]; [TrefethenBau1997, Theorem 38.5]; stated there for the extreme
eigenvalues and the unsquared $\mathbf{A}$-norm, here for any interval containing the spectrum.
Result: cg-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀))
```

(b) Proposed docstring. The $4$ is part of the mathematics (H4.1):

```lean
/-- **The Chebyshev bound for CG.** Let $\mathbf{A} \in \Bbbk^{n \times n}$ be Hermitian with
spectrum in $[a, a']$, $0 < a$, let $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and write
$\|\mathbf{e}\|_{\mathbf{A}}^2 = \operatorname{Re}\,\mathbf{e}^{\mathsf{H}}\mathbf{A}\mathbf{e}$.
Then for every $\mathbf{x}_0$ and every $q$
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2q}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
[Saad2003, Theorem 6.29]; [TrefethenBau1997, Theorem 38.5]; stated there for the extreme
eigenvalues and the unsquared $\mathbf{A}$-norm, here squared and for any interval containing the
spectrum.

Note: The square of the classical
$\|\mathbf{e}_q\|_{\mathbf{A}} \le 2\bigl((\sqrt\kappa - 1)/(\sqrt\kappa + 1)\bigr)^q
\|\mathbf{e}_0\|_{\mathbf{A}}$ with $\kappa = a'/a$. The proof's polynomial is the shifted
Chebyshev residual (`NLAlib.chebyshevResidual`), whose factor is
$T_q((a' + a)/(a' - a))^{-2} = 4\rho^{2q}/(1 + \rho^{2q})^2$ with
$\rho = (\sqrt{a'/a} - 1)/(\sqrt{a'/a} + 1)$ (`NLAlib.inv_eval_T_real_eq_two_mul_pow_div`); the
statement drops the factor $(1 + \rho^{2q})^2 \le 4$, which tends to $1$
(docs/contributing/statements.md §2 rule 7). A Loewner sandwich gives the hypotheses by
`isHermitian_of_le_smul_one` and `spectrum_subset_Icc_of_le`.
Result: cg-chebyshev-bound -/
```

### 3.9 Finite-precision and backward-error result

Shape: a run model (a structure that bundles the arithmetic assumptions), a smallness
hypothesis, and a first-order bound in the precision.

```lean
theorem <Run>.<norm of computed model minus exact object>_le {n k : ℕ} (R : <Run> n k)
    (hsmall : <polynomial in k> * R.ε ≤ <threshold>) :
    <norm> (R.<computed model> - R.<exact object>) ≤ <factor> k * R.ε * <scale of the data>
```

The run models are already over `Fin n` with `n k : ℕ` (`structure LanczosRun (n k : ℕ)`), so
the existing theorem is the headline (H3.6). What a reader cannot check from the statement alone
is the structure: the statement paragraph therefore lists the assumptions the run model bundles,
one clause each, and the notes name the structure and the definitions.

Example: `greenbaum-backward-model`, `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`,
`NLAlib/Krylov/FinitePrecision/Backward.lean:314`, under `variable {n k : ℕ} (L : LanczosRun n k)`.

(a) Current signature (unchanged in (b)) and docstring:

```lean
/-- **Greenbaum-type backward model for finite-precision Lanczos**
(assuming $k\varepsilon \le 1/100$): the symmetric backward model
$\tilde{\mathbf{H}}$ is close to $\mathbf{I}_{k+1} \otimes
\mathbf{H}$, <!-- value lanczosBackwardFactor k -->
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 400k^3\varepsilon\|\mathbf{H}\|_2 \,,$$
and it satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\mathbf{\Delta}\|_2 \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989, (7.10)] has a perturbation of order $\varepsilon^{1/4}$.
Result: greenbaum-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    frobNorm (L.backwardH - L.dilatedH) ≤ lanczosBackwardFactor k * L.ε * specNorm L.H
```

(b) Proposed docstring. The factor is a proof artifact, so it is a symbol with a value line
(H4.2); its value theorem `lanczosBackwardFactor k ≤ 400 * k ^ 3` is W1 and does not exist at
`04935354`. The assumptions are those the docstring of `LanczosRun` lists:

```lean
/-- **Greenbaum-type backward model for finite-precision Lanczos.** Let
$\mathbf{H} \in \mathbb{R}^{n \times n}$ be symmetric and consider $k \ge 1$ steps of the Lanczos
recurrence in Paige's ordering in which every operation is exact up to an error of at most
$\varepsilon$ times its operands, the Lanczos vectors satisfy
$\lvert \|\mathbf{v}_j\|^2 - 1 \rvert \le \varepsilon$, $\beta_j > 0$ before the last step,
$\beta_k \ge 0$ and $\varepsilon \le 1/100$. Let $\tilde{\mathbf{H}}$ be the symmetric backward
model of the run. If $k\varepsilon \le 1/100$, then
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le c_k\,\varepsilon\,\|\mathbf{H}\|_2 \,.$$
Here <!-- value lanczosBackwardFactor k -->$c_k = 400k^3$.
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\mathbf{\Delta}\|_2 \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989, (7.10)] has a perturbation of order $\varepsilon^{1/4}$.

Note: The run is a `LanczosRun n k`; $\tilde{\mathbf{H}}$ is `L.backwardH`,
$\mathbf{I}_{k+1} \otimes \mathbf{H}$ is `L.dilatedH` and $c_k$ is `lanczosBackwardFactor k`. The
backward model satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
Result: greenbaum-backward-model -/
```

The letter $k$ for the number of steps is the file's; §2.3 lists it as second priority.

## 4. Probability form (H5)

The brief chooses the bad-event tail and says in passing that a good-event form "needs
measurability". That is half right, and the half matters for the recommendation.

Concrete case: the headline of §3.1. Its good-event form would be

```lean
    1 - δ ≤ μ.real {ω | frobNorm (A - rsvd A (X ω)) ^ 2 ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2}
```

- **Deriving it from the tail needs no measurability, only total mass one.** The good event is
  the complement of the bad one (`not_lt`), and for every set
  `μ.real s + μ.real sᶜ ≥ μ.real univ` by `measureReal_union_le` and `Set.union_compl_self`;
  with `probReal_univ` this is `1 - μ.real sᶜ ≤ μ.real s`. The library already contains this
  argument as a private lemma, `one_sub_le_measureReal_of_compl_subset` in
  `NLAlib/LowerBounds/LowRank/EarlyTruncationBlockGaussian.lean`, with exactly the hypothesis
  `[IsProbabilityMeasure μ]`. So the cost of a good-event corollary is: one public lemma
  (`1 - δ ≤ μ.real s` from `μ.real sᶜ ≤ δ`), about five lines per headline, and one extra
  hypothesis `[IsProbabilityMeasure μ]` where the theorem does not have a `HasLaw` hypothesis to
  get it from (§3.1 has none: its hypotheses are on the rows of `X`; with a law, Mathlib's
  `HasLaw.isProbabilityMeasure` supplies it).
- **Using it needs measurability.** A consumer who holds two good-event statements and wants
  both at once needs $\mathbb{P}[G_1 \cap G_2] \ge \mathbb{P}[G_1] + \mathbb{P}[G_2] - 1$, which
  is additivity and needs one of the events to be null-measurable. Going back from a good-event
  bound to the tail is Mathlib's `prob_compl_le_one_sub_of_le_prob`, which takes
  `MeasurableSet s`, or `measureReal_compl₀` with `NullMeasurableSet s μ`. For the event above
  that means measurability in `ω` of `frobNorm (A - rsvd A (X ω))`: a measurability lemma for
  each algorithm and `AEMeasurable X μ` as a new hypothesis. With bad events the union bound is
  `measureReal_union_le`, with no hypothesis at all. This is why [T14] tails compose and why the
  library has 172 of them against 7 good-event statements, all 7 of them *hypotheses* of lower
  bounds ("succeeds with probability at least $1/2$").

So the good-event form can only be an extra corollary beside the tail, never a replacement. As
an extra it doubles the statements a reader must compare, adds a hypothesis the general theorem
does not need, and is the second wording H5 exists to remove.

**Recommendation (judgment): keep the bad-event tail, as the brief chose**, and in prose write
the event of the Lean statement. Add the one-line conversion lemma publicly (W1) so that a user
who wants "with probability at least $1 - \delta$" gets it in one step; do not state per-result
good-event corollaries. In lower bounds the success hypothesis stays a good event, since that is
what "the algorithm succeeds" means, and the hard-instance conclusion is `ρ.real {success} < p₀`
(§3.5), which needs no conversion.

## 5. Squared and unsquared error

Verified counts over the `Result:` signatures (a norm counts as squared when `^ 2` follows its
argument): the Frobenius norm is squared in 245 signatures and unsquared in 81 (22 have both);
the spectral norm squared in 59, unsquared in 165; the nuclear norm squared in 3, unsquared in
61. By kind of statement: expectations have squared Frobenius 82 times against 9, tails 77
against 21, deterministic statements 49 against 50. In Krylov, 52 signatures state the energy
norm as `RCLike.re (quadForm A e)`, which is the square; vector 2-norms are unsquared in 64 and
squared in 12. (The audit has 249 and 54 for Frobenius; it counts differently and the picture is
the same.)

Convention per type (judgment), each consistent with [T15] ("the primary statement is the moment
the proof gives, usually the squared one"):

| Type | Convention | Reason |
|---|---|---|
| algorithm guarantee in expectation | squared Frobenius and Schatten norms, $\mathbb{E}\|\cdot\|_{\mathsf{F}}^2$; nuclear norm unsquared; spectral norm in the power the proof gives, and both when both are proved independently (HMT 10.6) | [T15]: the unsquared form is the Jensen weakening, said in the citation sentence |
| algorithm guarantee in high probability | the same power as the expectation bound of the same result id, so squared Frobenius: $(1 + \varepsilon)\|\cdot\|_{\mathsf{F}}^2 < \|\cdot\|_{\mathsf{F}}^2$ | the two events are equal, so nothing is lost; squaring avoids $\sqrt{1 + \varepsilon}$ and matches the tail's proof from a second moment |
| sketch property | whatever the interface predicate has: Gram matrices and squared norms | the interface is fixed ([statements](../contributing/statements.md) §3) |
| concentration inequality | the statistic as the source prints it, unsquared | it is a tail of the statistic itself |
| lower bound | the power of the upper bound it matches | so that the two can be compared at sight |
| deterministic inequality | unsquared, except a Pythagorean or trace identity (Eckart–Young in the Frobenius norm), which is squared | degree-one homogeneity; the identity is in squares |
| exact identity | squared: a variance or a second moment | by definition |
| Krylov convergence | energy-norm error squared (`re (quadForm A e)`, rate to the power $2q$); 2-norm residuals unsquared | no square root in the Lean statement; the docstring gives the classical unsquared form in the notes |
| finite precision, backward error | unsquared | first order in the precision; a square would read as $\varepsilon^2$ |

The 21 unsquared Frobenius tails and the 9 unsquared Frobenius expectations are the exceptions
to look at when their files are touched; no statement is changed for this convention alone.

## 6. Parametrisation of a probabilistic headline

Not asked as a separate item, but H6 needs it and it is the root of the "tails, not sample
sizes" conflict (§7.4). Judgment:

- A **concentration inequality** is headlined by its closed-form tail in a free parameter $t$.
- A **sketch property** or an **algorithm guarantee** is headlined by its sample-size form in
  $(\varepsilon, \delta)$: hypotheses `size ε δ ≤ l`, conclusion `μ.real {bad} ≤ δ`. It is still
  a `μ.real` tail ([T14]); what changes is which of the two existing theorems is shown first.
- The closed-form tail stays the general form and stays first in the file, so "inverting the
  tail is done once" still holds.

Among the 31 Sketching ids of tier 3 only `countsketch-osi` has neither a sample-size
declaration nor an expectation or tail headline of another type (verified by name and hypothesis
pattern); deriving its sample-size form is W2.

## 7. Conflicts with the existing rules

Each item gives the present text, the text proposed instead, and the check affected. The
proposed texts are applied to `docs/contributing/statements.md` and
`docs/contributing/docstrings.md` in the second commit of this branch. They are written so that
every one is true under today's checks: nothing in them asks an author for something a check
rejects. No script, rule datum, allowlist or baseline is changed.

Besides the conflicts, the second commit adds two things that replace nothing: the bullet "One
headline per result" in statements §2 (H1, H3 and the designation of §8) and item 6 "Headline"
in docstrings (H2, H5 and the letter table of §2.2).

The new rules are stated without ids ("judged by review"), as
[checks](../contributing/checks.md) §2 allows, because an id needs an entry in
`docs/rules/rules.toml`. Proposed ids for when the checks are written: T16 (H3), D14 (H2), D15
(H5), R4 (H1), B7 (H4), M19 (H6 letters).

### 7.1 "Headline" has two meanings

Present: [D12] "a headline theorem names the law of each `HasLaw` hypothesis"; [D13] "a headline
theorem's `[Nonempty n]` is said too"; `headline(doc)` in `scripts/check_rules.py` is "a
`Result:` id or a bold name first"; `design.md` item 3 and the PR read-back say "headline
result" for any main theorem.

Proposed (docstrings item 1): "…and a `Result:` or bold-named theorem names the law of each
`HasLaw` hypothesis [D12]; its `[Nonempty n]` is said too ("$n$ nonempty", review list: [D13]).
The *headline* of a result (item 6) is a narrower notion: it has no `[Nonempty n]` to mention,
and its docstring has the fixed layout given there, with remarks in a notes block."

Checks: none must change for this; renaming `headline()` to `named_result()` in
`scripts/check_rules.py` would remove the ambiguity for the next reader ([D12], [D13]).

### 7.2 D13, "$n$ nonempty"

Present (docstrings item 1): "a headline theorem's `[Nonempty n]` is said too ("$n$ nonempty",
review list: [D13])". H3 forbids both the instance and the phrase in a headline.

Proposed: the text of §7.1; in statements §2, "Its signature has no `Fintype.card` and no
`[Nonempty …]`: … positivity is a hypothesis `0 < k` only when the other hypotheses do not
imply it"; and in docstrings item 6, "Sizes are plain letters ($k$, $\ell$, $n$), never
`\lvert k \rvert` or "$k$ nonempty"; a positivity hypothesis `0 < k` is "$k \ge 1$"."

Check [D13] (`d_nonempty_omitted`): keep it for every `Result:` or bold-named declaration that is
not a designated headline. For a designated headline it is replaced by the proposed T16: an
error when the signature contains `Fintype.card` or `[Nonempty `, the detector the explorer
already uses (`index_typed_sizes`). The check needs the designation to be visible in the library
(§8).

### 7.3 The `\lvert n \rvert` notation row

Present (docstrings item 5, row "scalars, indices, dimensions"): "`c`, `t`, `i`, `k`, `n`; the
size of an index type `n` is `\lvert n \rvert`".

Proposed: "`c`, `t`, `i`, `k`, `n`; the size of an index type `n` is `\lvert n \rvert`; a
headline (item 6) has natural-number sizes and writes them as plain letters, never
`\lvert n \rvert`".

Check [M16] is unaffected (it rejects bare bars). Proposed D14 would reject `\lvert x \rvert`
around a single letter that is a `ℕ` binder of a designated headline.

### 7.4 T6, theorems over `Fin`

Present (statements §1): "`Fin k` is appropriate where its order or recursion carries content:
… A theorem stated over `Fin` because a dependency was is a defect to fix at the dependency
(review lists: [T6], and [T7] for theorems over ℝ only)."

Proposed: the same, followed by: "The headline of a result (§2, "One headline per result") is
the one other place for `Fin`: a corollary that instantiates the general theorem at `Fin`, so
that every size is a natural number. It is added after the general theorem, never instead of
it, and nothing is proved from it."

Check [T6] (`t_fin`, a warning, scope `NLAlib/Matrix`): it fires on every `Matrix (Fin ` in a
Matrix signature, so every Matrix headline (the two tier 3 ids and all of tier 4) adds a
warning. It should skip designated headlines. Until it can, the warnings are expected and say
so in the PR.

### 7.5 "Tails, not sample sizes"

Present (statements §2): "Probabilistic results are stated as tails, not sample sizes: the
primary theorem bounds the failure probability in closed form (…); the "`k ≥ …` suffices" form
is a corollary."

"Primary" now names the headline, and §6 makes the sample-size corollary the headline of a
sketch property or an algorithm guarantee.

Proposed: "Probabilistic results are stated as tails, not sample sizes: the general theorem
bounds the failure probability in closed form (…); the "`k ≥ …` suffices" form is a corollary.
… Tails are in `μ.real` [T14]. For a sketch property or an algorithm guarantee the sample-size
corollary, at natural-number sizes, is the result's headline; for a concentration inequality the
closed-form tail is."

No check reads this rule.

### 7.6 B5 and "the explorer leads with the asymptotic form"

Present (statements §2 rule 3): "A result of this kind without its asymptotic form is on a
review list [B5]. … the proof instantiates the explicit theorem, which stays primary and whose
docstring names its asymptotic form. … The explorer leads with the asymptotic form and offers
the explicit bound beside it, so each docstring states its hypotheses and conclusion on its own".

Three conflicts. (1) H1 and H4 make the explicit theorem the headline, so the explorer leads
with it. (2) H4.5 asks for a companion for *every* headline with an artifact constant; [B5] is
scoped to `NLAlib/Sketching` and `NLAlib/LowRank` and its check looks for a hypothesis
`… ≤ Fintype.card …`, which a headline does not have. (3) `scripts/check_refs.py` requires that
a docstring containing the literal "Asymptotic form: `X`" is the target of `X`'s `Asymptotic:`
tag, and [N17] derives the companion's name from its explicit theorem. A headline corollary
therefore cannot say "Asymptotic form: `X`" unless every companion is retargeted and renamed.

Proposed: keep the pairing between the companion and the *general* explicit theorem (no rename,
no change to `check_refs.py`), and write in rule 3: "…the proof instantiates the explicit
theorem, which its `Asymptotic:` tag names and whose docstring names its asymptotic form. … The
explorer leads with the result's headline, which is explicit, and offers the asymptotic form
beside it, so each docstring states its hypotheses and conclusion on its own, … A headline that
is a corollary of the explicit theorem names the asymptotic form in its notes in other words
("the $O(\cdot)$ reading is `…`"): the phrase "Asymptotic form:" belongs to the theorem the tag
points to. A headline that shows a proof-artifact constant has an asymptotic form through its
general theorem, in every topic, not only in the two that [B5] lists."

Check [B5] (`b_asym_missing`, a warning): widen the scope in `rules.toml` from Sketching and
LowRank to the library; match a size hypothesis `… ≤ ↑l` on a `ℕ` binder as well as
`… ≤ Fintype.card l`; and accept a headline whose notes name a general form that has the
companion. The explorer change is in the website repository.

### 7.7 The first-sentence rule has no slot for notes

Present (docstrings): the parts of a docstring are "1. First sentence … 2. Citation …
3. Provenance … 4. `Result: <id>` … 4b. `Algorithm: <id>` … 5. Mathematics is LaTeX". Remarks
have no place of their own, so they went into the statement: 368 `Result:` docstrings name
another declaration, 79 carry a tightness remark, 76 describe the proof route (audit, Part 2).

Proposed: a new item 6, "Headline", with the layout of H2 (statement paragraph, value line,
citation, notes block after a blank line, tags), H3's and H5's wording rules and the letter
table; and in item 1 a pointer to it. The notes block is defined for headlines only; other
docstrings may use it.

Checks. [D1] (bold name first) and [C1] (citation) hold unchanged. [D2] forbids "as in the …"
and "as above" anywhere in a docstring, so a notes block must not use them either; no change.
[D8] forbids a sentence starting `Proof:`; `Note:` is a different marker. `scripts/check_refs.py`
requires `Result:` to be the last line and `Asymptotic:` the last before it; the notes block
comes before both. Proposed D14 would check the order (bold name, first citation, `Note:`
paragraph after a blank line, tags) and that no backticked identifier precedes the first
citation.

### 7.8 Named constants: value in the formula, or a symbol

Present (statements §2 rule 2): "A docstring that uses a named bound shows its current value
inside its equations. Statements keep the name; the docstring writes the value in place of the
constant, in the formula itself. A sample size that uses a named constant may instead write it
as $C$ …"; docstrings table, row "named constants": "the value in place of the constant … a
symbol such as `C_{\mathrm{HW}}` only in prose about the constant itself".

H4.2 turns the exception into the rule for proof-artifact constants in a headline.

Proposed (a paragraph at the end of rule 2): "**In a headline** a constant that is part of the
mathematics (exact or sharp) is written out, and a constant that is an artifact of the proof is
a symbol in the formula with its value in the last sentence of the statement, which starts with
"Here" and carries the marker: "Here <!-- value hansonWrightConstant -->$C = 1/196$." A constant
with no explicit value does not appear in a headline. Every named constant a headline shows has
a public value theorem, a one-sided comparison in the direction its consumers use
(`le_hansonWrightConstant`)."; and in the table row: "…; in a headline a proof-artifact constant
is a symbol with a "Here" value line (item 6)".

Check: `scripts/check_constants.py` needs no change. The marker precedes a math span that
contains the registered value (`$C = 1/196$` contains `1/196`; `$c_k = 400k^3$` contains
`400k^3`), which is the form the existing "with <!-- value subgaussianJLConstant -->$C = 1/36$"
already has; and a docstring that names the bound in backticks in its notes has its marker.

### 7.9 The probability paragraph

Present (docstrings item 5, "Probability notation"): "A displayed high-probability guarantee
states its event explicitly, for example `$\mathbb{P}[\mathrm{error}\le t]\ge1-\delta$`; prose
may still say "with probability at least $1-\delta$"."

Proposed, appended: "A headline (item 6) writes the event of its Lean statement, the bad one,
`$\mathbb{P}[\mathrm{error} > t] \le \delta$`, and no other wording."

Check [M1] is unaffected. Proposed D15 would reject the four phrases of H5 before the first
citation of a designated headline.

### 7.10 Checks that need a change, by rule id

| Rule or script | Change |
|---|---|
| [D13] `d_nonempty_omitted` | skip designated headlines; they fall under T16 |
| [T6] `t_fin` | skip designated headlines |
| [B5] `b_asym_missing`, and its `scope` in `rules.toml` | library-wide; recognise `ℕ` sizes; accept the companion of the general form |
| [V2] `v_trunc_sub` | in a designated headline also reject `a - b` between two `ℕ` binders (H3.4) |
| [D12], [D13] helper `headline()` | rename; no behaviour change |
| [R1], [R2], [R3] and `result_ids`, `has_result` in `scripts/check_rules.py` | parse the role of §8; [R3] also checks that every `primary` in `explore/results.toml` names a declaration of that id (today a stale `primary` fails only the website build) |
| `scripts/check_refs.py`, `Result:` tag | accept `<id> (headline)`; today the value must be comma-separated slugs |
| new T16, D14, D15, R4, B7 | entries in `rules.toml`, checks, fixtures in `scripts/test_check_rules.py`, then `python3 scripts/gen_rules_md.py`; the test `test_every_rule_is_cited_where_it_is_stated` then requires the ids in the guides |
| `scripts/check_constants.py`, `scripts/check_latex.mjs`, `scripts/check_names.py` | none known; whether [N3] accepts a final `_fin` is to be seen on the first such name (open question 1) |
| website `explore/library.py` | read the role; `primary` becomes a fallback, and a disagreement an error |

## 8. How a headline is designated

Today: `primary` in the website's `explore/results.toml` (25 ids). On the website branch
`feat/headline-statements` an audit lists the ids without one.

| | `primary` in `explore/results.toml` | a role on the Lean tag line |
|---|---|---|
| Where the choice is reviewed | another repository, after the statement merged | the PR that adds the statement |
| Can the library's checks see it | no: `scripts/check_rules.py` reads the explorer folder only when given `--explore-repo`, and [R3] does not read `primary` | yes: H2–H5 become checkable on exactly the headlines, and [T6], [D13] can skip them |
| A rename in the library | breaks the website build (`ValueError` in `explore/library.py`) until the TOML is edited | nothing to edit |
| One per id | enforced by the TOML key | needs a check (proposed R4) |
| Cost now | none | `check_refs.py`, `check_rules.py`, `explore/library.py`, their tests |
| Presentation-only data stays out of the library | yes | the role is one word on an existing line |

**Recommendation (judgment): a role on the `Result:` line,**

```
Result: gaussian-osi (headline)
```

in the syntax `Algorithm: <id> (<role>)` already has ([A1]); with several ids,
`Result: a (headline), b`. The tag is a claim that the declaration meets H2–H5, so the checks
apply to it, and "ids with a tagged headline" is the progress count of the rollout. Choosing a
headline is a mathematical decision about a statement, and it belongs where the statement is
reviewed.

Until the scripts accept the role (they reject it today: `check_refs.py` reports "malformed
`Result:` tag"), `primary` in `explore/results.toml` is the mechanism, and the guide amendment
says only that. When the role lands, the website reads it first, keeps `primary` as a fallback
for one release, and fails on a disagreement.

## 9. Rollout

Work packages in order. "Tier" is the audit's. Every package after WP0 is: add the headline
after its general theorem (or restructure the docstring where H3.6 applies), in the letters of
§2 and the shape of §3; add missing value theorems; set `primary`; run
`python3 scripts/check_rules.py --files …`. No package depends on another package's Lean; the
dependencies are on decisions.

| WP | Content | Ids | Files (under `NLAlib/`) | Class | Depends on |
|---|---|---|---|---|---|
| 0a | this note reviewed; open questions 1–4 decided | – | `docs/` | – | – |
| 0b | checks and tag (§7.10, §8), by the maintainer | – | `scripts/`, `docs/rules/rules.toml`, website | – | 0a |
| 1 | value theorems for named constants (pilot branch `feat/headline-constant-values`); the public conversion lemma of §4 | – | the files of the 80 entries of `docs/constants.toml`; one Probability file | W1 | – |
| 2 | tier 1, low-rank query lower bounds (pilot branch `feat/headline-lowrank-lower-bounds`): sizes at `Fin`; then the hard-instance form of §3.5 | 4 | `LowerBounds/LowRank/FewPasses.lean`, `Minimax.lean`, `NuclearMinimax.lean` | W1; companions W2 | 0a for the shape |
| 3 | tier 3, Sketching, Gaussian family | 17 | `Sketching/Gaussian/Gaussian.lean`, `Haar.lean`, `HaarEmbedding.lean`, `ProjectionCost.lean`, `Rademacher.lean`, `SubGaussian.lean` | W1 | 0a for `l` |
| 4 | tier 3, Sketching, sampling, sparse and structured | 14 | `Sketching/Sampling/MatrixMultiplication.lean`, `RowSampling.lean`, `WithoutReplacement.lean`; `Sketching/Sparse/CountSketchEmbedding.lean`; `Sketching/Structured/SRHT.lean`, `SRHTMultiplication.lean` | W1; `countsketch-osi` sample-size form W2 | 0a |
| 5 | tier 3, LowRank, Gaussian test matrices | 16 | `LowRank/Gaussian/BlockKrylov.lean`, `BlockKrylovGapless.lean`, `EarlyTruncation.lean`, `EarlyTruncationHaar.lean`, `EarlyTruncationRSVD.lean`, `Filter.lean`, `GeneralizedNystrom.lean`, `Nystrom.lean`, `NystromBlockKrylov.lean`, `RangeFinder.lean`, `RotationInvariant.lean`, `TruncatedGeneralizedNystrom.lean`, `TruncatedGeneralizedNystromRate.lean`, `TruncatedGeneralizedNystromRelativeError.lean` | W1 | 0a; question 4 for the rank letters |
| 6 | tier 3, LowRank, oblivious test matrices (`randomized-svd-tail`, and the oblivious members of `etrsvd`) | 1 | `LowRank/Oblivious/CountSketch.lean`, `Gaussian.lean`, `Haar.lean`, `RowSampling.lean`, `SRHT.lean`, `SubGaussian.lean`, `WithoutReplacement.lean` | W1; one headline or one per law is open question 9 | 3, 4 for the wording of the sketch properties |
| 7 | tier 3, Regression | 3 | `Regression/CountSketch.lean`, `Gaussian.lean`, `Haar.lean`, `SRHT.lean`, `SubGaussian.lean`, `SketchAndSolve.lean` | W1 | 0a |
| 8 | tier 3, Estimation | 4 | `Estimation/Trace/GirardHutchinson.lean`, `HutchPlusPlus.lean`, `HutchPlusPlusTail.lean` | W1 | 0a for `l`, `p` |
| 9 | tier 3, Probability, RandomMatrix, ForMathlib | 9 | `Probability/MatrixConcentration/BernsteinWithoutReplacement.lean`, `ChernoffWithoutReplacement.lean`, `Freedman.lean`; `RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`, `RandomMatrix/Gaussian/FourthMoment.lean`; `RandomMatrix/Haar/Blocks.lean`; `ForMathlib/Probability/Distributions/ChiSquared.lean` | W1; the ForMathlib headline must keep [P4], [P5] | 0a |
| 10 | tier 3 lower bounds and the two lower bounds of tier 2 | 5 + 2 | `LowerBounds/LowRank/EarlyTruncation.lean`, `EarlyTruncationBlockGaussian.lean`, `RotationInvariant.lean`, `TruncatedGeneralizedNystrom.lean`; `LowerBounds/Regression/SketchAndSolve.lean` | W1 for sizes and for `truncated-gn-lower-bound`; `∫⁻` to `∫` W2; block-Gaussian explicit bound W3 | 2 for the shape |
| 11 | tier 3 Matrix and the rest of tier 2 | 2 + 3 | `Matrix/Inequalities/Minkowski.lean`, `Matrix/Perturbation/GramSoftMin.lean`; `Matrix/Subspaces/CSDecomposition.lean`, `ForMathlib/LinearAlgebra/Matrix/SchurComplement.lean`, `LowRank/Gaussian/RotationInvariantFactor.lean` | W1 with blocks at `Fin p ⊕ Fin q` (H3.2) | question 3 |
| 12 | tier 4, 112 ids where only ambient dimensions are cardinalities | 112 | mostly `Matrix/` | W1, if done at all | §12 item 4 |
| 13 | ids with no index-typed size (404 by §0): designate, restructure the docstring | – | all topics | docstrings only | 0a |

Tier 3 sums to 71 ids (17 + 14 + 16 + 1 + 3 + 4 + 9 + 5 + 2); `early-truncated-rsvd-lower-bound`
is in tiers 2 and 3 and is counted once in WP10's first number. The renames of §2.3 are done in
the package of their file.

Order. WP1 and WP2 are running. Sketching goes before LowRank and Regression because their
docstrings quote the sketch properties and the letter `l` is fixed there. Lower bounds wait for
the shape decision. Tier 4 is last and conditional.

## 10. Backlog (W3 and deferred)

1. Lower bounds for a general dimension $n$ (now pinned to $k + 3\lfloor k/(8\varepsilon)\rfloor$
   and similar).
2. An explicit lower bound for early-truncated RSVD at general $k$, replacing `∃ c C K₀`.
3. Removing the threshold "eventually in $a$" of `truncated-gn-lower-bound` by an explicit $a_0$.
4. Bad-event conclusions for query lower bounds (`1 / 2 < ρ.real {failure}`): measurability of
   the success event of a measurable family.
5. `sketch-and-solve-lower-bound` and `range-recovery-k-queries` in `∫` and `μ.real`: needs
   integrability, respectively finiteness, statements.
6. Asymptotic companions for the lower bounds (none is tagged `Asymptotic:`). W2 each, listed
   here because the shape of a lower-bound companion (`∃ C ε₀, ∀ …, q ≤ k/(Cε) → ∃ A, …`) is
   not covered by [B4]'s text and should be agreed once.
7. Transport of `truncatedSVD`, `rsvd` and `QueryAlgorithm` along an index `Equiv`, if flat
   `Fin n` statements are wanted after all.
8. One letter for the unit roundoff (`ε` in `Krylov/FinitePrecision`, `u` elsewhere); the field
   name `LanczosRun.u` is in the way.
9. A role "comparison rank" in the letter table, after classifying the 84 uses of `r`, `t`, `q`
   as second argument of `truncatedSVD`.
10. Whether a positivity hypothesis `0 < l` is implied by the row hypotheses in the sub-Gaussian
    statements (§3.1), and the same question for each `[Nonempty …]` the general theorems carry.
11. Field shown to the reader (audit Part 2, item 10): 429 real-only signatures, 558 over `𝕜`.
    This note keeps the field of the general theorem in the headline.

## 11. The design-note checklist

1. **Objects.** None. No definition and no vocabulary row.
2. **Interfaces.** None new. The headlines take and conclude the existing interfaces; the
   docstring writes a concluded predicate out (H2.1).
3. **Statement shapes.** §3.
4. **Consumers.** The headline has one consumer, the reader: the explorer page and the PR
   read-back. Nothing in the library is proved from a headline corollary (§7.4); proofs keep
   using the general form. The public conversion lemma of §4 is for users.
5. **Files.** No new file. Each headline is in the file of its general theorem, after it (§9).
   Placement outside its own files: none.
6. **Material.** The audit; the sources of §13; the website repository at `ce5518dc` and its
   branch `feat/headline-statements`.
7. **Shared proof machinery.** The instantiation at `Fin` repeats three steps:
   `Fintype.card_fin` (Mathlib, `simp`), casts of sizes (`push_cast`/`simpa`), and
   `Nonempty (Fin k)` from `0 < k`. All three are one-liners with existing lemmas; no tactic or
   lemma is planned. If WP3 shows a fourth recurring step, it is added as a lemma before WP4.
   The contraposition of §3.5 is logic.
8. **Open questions.** §12.

Mathlib. No Mathlib notion is replaced: the general theorem stays over `[Fintype n]`, as Mathlib
would state it, and the headline is an added corollary. This note therefore adds no entry to
`docs/design/Mathlib-deviations.md`. If the reviewers read "a different index type" in
[design](../contributing/design.md) as covering added corollaries too, the entry is: Mathlib,
statements over `[Fintype n]`; NLAlib, one `Fin` corollary per result, the headline; Bridge, the
general theorem and `Fintype.card_fin`; Why, a statement a reader can check without knowing that
a size is a type; Cost, one more declaration per result and [T6] warnings; Status, per this note.

## 12. Open questions and disagreements with the brief

1. **Name of a headline corollary whose statement has the general theorem's name.**
   Recommendation: suffix `_fin` (Mathlib uses `_fin` for `Fin` specialisations; the library has
   one, `subdiagonalSq_fin`). It needs a line in [naming](../contributing/naming.md) and a look
   at [N3]. The pilot's names (`natCast_div_lt_of_forall_…`) need no suffix because the
   statement's head changed.
2. **Rule labels.** The brief's S1–S6 and P1–P3 collide with rule ids in `rules.toml`
   (S1 "No `simp_all`", P1 the layer rule). Recommendation: H1–H6 and W1–W3 as here; in the
   guides no bracketed id until the rules have entries.
3. **Block statements.** The brief's S3 says "objects indexed by `Fin`". For a statement whose
   content is a block structure (`cs-decomposition`, `jacobi-complementary-minors`, the query
   lower bounds on `k ⊕ (Fin 3 × m)`), flattening to `Fin (p + q)` puts `Fin.castAdd` or a
   `reindex` into the statement and makes it harder to check, against the purpose; it is also
   not provable in budget for the low-rank bounds (§3.5). Recommendation: H3.2, sizes are natural
   numbers and blocks are sums and products of `Fin`.
4. **Tier 4.** For 112 ids the only index-typed size is an ambient dimension (Weyl: $i + j < n$).
   A `Fin` corollary there adds a declaration whose content is `Fintype.card (Fin n) = n` and a
   [T6] warning each. The brief's S3 asks for it. This note keeps the brief's rule but puts
   tier 4 last and recommends deciding after WP3–WP11 whether the gain is worth about 112
   declarations; the alternative is to let the general theorem be the headline when its only
   cardinalities are dimensions of its matrices, with the docstring writing $n$.
5. **Good-event form.** The brief says it "needs measurability". Deriving it does not (§4);
   using it does. The recommendation is the brief's, for a different reason.
6. **Companion pairing.** The brief's S4 reads as if the headline were the explicit member of
   the `Asymptotic:` pair. Keeping the pair on the general theorem (§7.6) avoids renaming the
   91 asymptotic forms; the headline names the companion in its notes.
7. **Expectation statements and integrability.** A `∫ … ≤ b` headline holds trivially when the
   integrand is not integrable. Recommendation: no change of statement; the notes name the
   integrability lemma (§3.2), and a headline whose integrand has none is flagged in review.
8. **Letter $\mathbf{X}$ against the literature's $\mathbf{\Omega}$.** §2.2 follows the Lean and
   the smaller count. If the maintainer prefers the literature's letter, the cost is about 130
   docstrings instead of 97, and the prose then differs from the Lean binder in every
   probabilistic low-rank statement.
9. **Result ids that bundle several laws.** `randomized-svd-tail` (32 declarations), `etrsvd`
   (20) and `sketch-and-solve-ls` (18) each cover Gaussian, sub-Gaussian, SRHT, CountSketch and
   sampling test matrices. One headline per id then shows one law and files the others as
   variants. Recommendation: split such an id by law (`randomized-svd-tail-subgaussian`, …; a new
   id is allowed by [docstrings](../contributing/docstrings.md) item 4, and [R2] asks for
   variants to differ by a word), so that each law has a headline. This multiplies the ids of
   WP6 and WP7 by about five and should be decided before those packages.

## 13. What was verified, and how

- **Declarations and docstrings quoted in §3** were read in the source at `04935354`; the
  current signatures and docstrings are copied from it. Proposed signatures are not elaborated.
- **Counts in §0, §2, §5, §9** come from a script over the Lean sources using
  `scripts/leansrc.py` (read-only): every public declaration with a `Result:` line, its
  statement text and the `variable` lines above it in the file. They are regular-expression
  counts, not elaboration; sections, `omit` and `include` are ignored. The audit's ids were all
  found; all 62 file paths in its tables exist.
- **Rule ids and check behaviour in §7** were read in `docs/rules/rules.toml`,
  `scripts/check_rules.py`, `scripts/check_refs.py` and `scripts/test_check_rules.py`.
- **Website facts** were read in the clone of `NLA-lib/NLA-lib.github.io`: line 134 at
  `ce5518dc`, line 162 and the new audit at `da715f1`.
- **Mathlib names** (`Fintype.card_fin`, `measureReal_union_le`, `measureReal_compl₀`,
  `probReal_univ`, `prob_compl_le_one_sub_of_le_prob`, `HasLaw.isProbabilityMeasure`) were
  found by `grep` in the Mathlib checkout of the main worktree; this worktree has no `.lake`.
- **Not verified:** that any proposed signature elaborates; that the one-line proofs close;
  which positivity hypotheses are implied (stated case by case in §3); the audit's Part 2 counts
  that this note quotes with "(audit)".
