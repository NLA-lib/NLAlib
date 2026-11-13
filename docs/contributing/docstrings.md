# Docstrings and citations

Part of the [contributor guide](../../CONTRIBUTING.md).

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
   `[Key]` is for module docstrings only [C2]. A `Result:` declaration cites its source, or says
   "No printed source." [C1] (the check also accepts close variants such as "folklore" or
   "standard"); a bracket that looks like a citation is one `check_refs.py` can parse [C4]; a bold-named theorem with neither citation nor id is on a
   review list [C9]. Several are separated by `;`. Then the relation to the
   printed statement: generalisation, different constant, tail form instead of sample size,
   different indexing. The citation is provenance for the reader and the literature map; it does
   not bind the statement or the proof. A helper or a bridge needs no citation; it says what it
   is for.
3. **Provenance** when a statement or proof is taken from another formal library: the library
   and commit.
4. **`Result: <id>`** on its own last line, for a declaration that *is* the formal statement of a
   named mathematical result (`weyl-inequality`, `eckart-young-frobenius`). Several ids are
   comma-separated. Helpers carry none, and neither do definitions and structures [R1] (an
   instance of a Prop-valued class is a statement and may). The ids
   key the literature map of the explorer (`explore/` in the website repository,
   NLA-lib/NLA-lib.github.io); a new id is fine, a misspelt
   existing one is an error [R2] (checked as: two ids of length at least 8 within edit distance 2
   are rejected as near-duplicates, unless they differ in one dash-separated word by a `p` prefix
   or a listed pair such as `ose`/`osi`; distinguish variants by words, `-frobenius`/`-spectral`,
   not by a digit), and an id or declaration the explorer names must exist [R3].
4b. **`Algorithm: <id>`** on its own last line, for a definition, recurrence, run model or program
   that is part of a named algorithm. These tags supply searchable declaration metadata;
   human-readable algorithm pages are curated separately:

   ```lean
   /-- The **Hestenes–Stiefel recurrence** (the conjugate gradient algorithm) from the start …
   [HestenesStiefel1952, (3:1)]; …
   Algorithm: cg -/
   noncomputable def cgState …
   ```

   The id is a slug like a result id, and follows the result-id prefixes in use (`cg`, `pcg`,
   `lanczos`, `hutchpp`, `randomized-svd`, `sketch-and-solve`, `gram-schmidt`). Curated pages
   select the relevant declarations and implementations explicitly. An optional role in
   parentheses: `Algorithm: cg (specification)` on the definition of *what* is computed when a
   separate recurrence computes it (`cgIterate`, `pcgIterate`), `Algorithm: lanczos (run model)`
   on a model of a run in finite precision (`LanczosRun`); without a role the declaration is a
   definition, and the explorer reads from its type whether it is a program. The tag goes on `def`,
   `abbrev`, `structure` and `inductive` declarations only [A2], never on theorems: results reach an
   algorithm through their ids and statements. An execution result points to the fixed program
   and operation model that its certificate uses. The line is standalone and last, the id a slug, the role `specification` or
   `run model` [A1]. A declaration belongs to at most one algorithm [A3]: a shared building block
   (`galerkinInverse`, `gramSchmidtQ` inside Hutch++) carries the tag of the algorithm it
   defines, or none, and is found through dependencies. Several declarations of one algorithm are
   expected (`cgState` and `cgIterate`; `rsvd` and `earlyTruncatedRSVD`; `hutchpp` and
   `hutchppProg`). A variant with a different definition has its own id (`pcg`).
5. **Mathematics is LaTeX**: `$…$` inline and `$$…$$` displayed, as doc-gen4
   and the explorer render it with KaTeX. Standard LaTeX only, no custom macros [M12]. A named
   bound's value is written inside the equation in place of the constant ([statements](statements.md) §2 rule 2), and the
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
   | named constants | the value in place of the constant, `\exp\bigl(-\tfrac{1}{196}\min(…)\bigr)`, with a value marker before the span and the Lean name in words nearby (`` `hansonWrightConstant` ``); a symbol such as `C_{\mathrm{HW}}` only in prose about the constant itself | |
   | truncated SVD (best rank-`k` approximation) [M14] | `\llbracket \mathbf{A} \rrbracket_k` | |
   | named algorithm outputs [M2, M3, M4, M5] | `\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})`, `\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})`, `\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})`: the Lean name verbatim in `\mathsf`, or a short name registered in the [vocabulary](vocabulary.md) row "short algorithm names in `\mathsf`" (`gn`), never the formula it unfolds to; the definition's docstring alone shows the formula, as `\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}) := \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}` | |
   | bold Greek matrices [M11] | `\mathbf{\Sigma}`, `\mathbf{\Lambda}` | |
   | real part, adjugate, Frobenius inner product | `\operatorname{Re}`, `\operatorname{adj}`, `\langle \mathbf{A}, \mathbf{B} \rangle_{\mathsf{F}}` | |
   | absolute value; epsilon, phi [M16, M8] | `\lvert x \rvert`; `\varepsilon`, `\varphi` | |

   **Probability notation**: mathematical probability statements use
   `$\mathbb{P}[E]$`, with square brackets around the event [M1]. Use
   `$\mathbb{P}\bigl[E\bigr]$` or `$\mathbb{P}\left[E\right]$` when sizing is needed;
   preserve parentheses belonging to functions inside the event. Conditional probability is
   `$\mathbb{P}[E \mid F]$`; a subscript may identify the random sketch or law. Do not use
   `$P(E)$`, `$\Pr(E)$` or round event delimiters. A displayed high-probability guarantee
   states its event explicitly, for example `$\mathbb{P}[\mathrm{error}\le t]\ge1-\delta$`;
   prose may still say "with probability at least $1-\delta$". This is a documentation
   convention; formal Lean statements keep the measure interface in [statements](statements.md) §3.

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

Curated documentation explains algorithms, variants, operation models and implementations.
The generated declaration reference remains searchable and linkable, including supporting
bounds in `docs/constants.toml`. Presentation metadata changes no Lean API. A module docstring
may list supporting numerical API in a section of its own.

`scripts/check_refs.py` fails CI on an unknown bibliography key or a malformed result id.
`docs/references.bib` grows by adding the entry before citing it; keys are `AuthorSurnames + year`
[C5], once each [C6], in alphabetical order [C7]; an entry nobody cites is on a review list [C8].
