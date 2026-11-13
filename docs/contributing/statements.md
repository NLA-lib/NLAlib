# Statements

Part of the [contributor guide](../../CONTRIBUTING.md).

## 1. Types

- Scalars: `{𝕜 : Type*} [RCLike 𝕜]` for all deterministic matrix theory, including matrix
  functions, and in the probability layers wherever the proof allows: random vectors, isotropy,
  moments, quadratic forms, matrix-valued integrals, matrix concentration. ℝ only where the
  object is a real number (scalar MGFs and tails, the norm or singular value a tail is about) and
  for the Gaussian and Haar matrix laws (`gaussianMatrix`, `haarFrame`), which are real; the
  interfaces they satisfy are stated over `𝕜`. A real corollary of a `𝕜` theorem is stated only
  when a downstream user needs it in `ᵀ` form that `simp` cannot produce.
- Index types: `{m n : Type*} [Fintype m] [Fintype n]` plus `[DecidableEq _]` where Mathlib
  needs it. `Fin k` is appropriate where its order or recursion carries content: the `k` sorted
  columns of an SVD produced by an existence theorem, total recursions
  defining algorithms. A theorem stated over `Fin` because a dependency was is a defect to fix at
  the dependency (review lists: [T6], and [T7] for theorems over ℝ only).
- Transpose: lemmas are stated with `ᴴ` [T5]. Over ℝ, `Aᴴ = Aᵀ` is `Matrix.conjTranspose_eq_transpose_of_trivial`
  (`@[simp]`). Transpose twins are not written.
- Vectors: `n → 𝕜` with `⬝ᵥ` as the pairing; the Euclidean norm is `‖WithLp.toLp 2 x‖`
  (Mathlib's `EuclideanSpace`), rather than `Real.sqrt (x ⬝ᵥ x)` [T1].
  Program contracts may expose the arithmetic a primitive actually computes, including a square
  root of a Hermitian self-dot’s real part; mathematical norm bounds use the norm API.
- A real quantity used where Mathlib wants `ℝ≥0` (a sub-Gaussian proxy `c * ‖specNorm A‖₊ ^ 2`, a
  coefficient `‖a i‖₊ ^ 2 * c`) is written with `‖·‖₊`, never `⟨x, hx⟩` or `Real.toNNReal x` [T2].
- Matrix norms are named functions ([vocabulary](vocabulary.md)), never `‖A‖` [T4]: Mathlib's four matrix norms are scoped
  instances and a signature cannot show which one is open. `‖A‖` appears only in bridge lemmas
  and, under a file-level `open scoped Matrix.Norms.L2Operator`, in the C*-algebra and
  functional-calculus files that need Mathlib's normed API. `Matrix.Norms.L2Operator` is the only matrix norm scope
  opened for analysis [T3], including integrals and conditional expectations of matrix-valued
  functions; never `Matrix.Norms.Frobenius` or `Matrix.Norms.Elementwise`, whose topology does not
  match Mathlib's global matrix topology, so `Integrable`, `Continuous` and limits do not elaborate
  under them (`docs/design/Mathlib-deviations.md` entry 13).

## 2. Shape

- Every hypothesis explicit, minimal, and an instance of a named interface (§3). Nothing that
  follows from another hypothesis (`(A + B).IsHermitian` next to `hA hB`; `Integrable X μ` next to
  `HasSubgaussianMGF X c μ`; not `Measurable X` next to `HasLaw X ν μ`, which gives only
  `AEMeasurable`). Drop unnecessary hypotheses. An `_h` name prompts review [T13],
  but does not establish non-use: tactics, dependent types and shared interfaces require context.
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
  predicate `good`; [naming](naming.md) N15 says how a scalar event is stated); the
  "`k ≥ …` suffices" form is a corollary. Inverting the tail is where ugly constants and side
  conditions appear, so it is done once, not by every consumer. Tails are in `μ.real` [T14].
- **A lower moment from a higher one is not a separate theorem** [T15].
  The primary statement is the moment the proof gives, usually the squared one. When a source
  prints the Jensen-weakened form (HMT Theorem 10.5's $\mathbb{E}\|\cdot\|_{\mathsf{F}}$), the
  higher-moment theorem's docstring says so in a sentence, so that a search on the citation finds
  it: "[HalkoMartinssonTropp2011, Theorem 10.5] prints the first-moment form …, which follows from
  this bound by Jensen's inequality (`ProbabilityTheory.integral_le_sqrt_integral_sq`)." A Jensen
  corollary stays only if another library proof uses it, allowlisted with "used by …"; otherwise
  that proof takes the Jensen step itself. A lower-moment bound proved independently (HMT 10.6's
  $\mathbb{E}\|\cdot\|_2$) is a separate result.
- **Numerical bounds.** A later improvement, and a new proof whose bound is incomparable with
  the old one, must fit without a rename:
  1. A name says what the statement is, never how good it is ([naming](naming.md) N7).
  2. The source's constant, when the proof reaches it and it is small, is written in the
     statement (Hoeffding's `exp (-t ^ 2 / (2 * c))`). Any other constant or tail function is a
     definition,
     `irreducible_def hansonWrightConstant : ℝ := …`, `matrixBernsteinTail d v L t : ℝ`, whose
     docstring gives the source's value, the value proved and the gap. Consumers use only its API,
     chosen to stay true when the bound improves: positivity, monotonicity where a consumer inverts
     the tail, and a one-sided explicit comparison
     (`1 / (256 * exp 2) ≤ hansonWrightConstant`). An improvement of the same shape changes the
     body and that comparison, no statement and no name.

     A proof that reaches a stronger bound under the same hypotheses exposes it through the
     existing theorem and named-bound API, and the docstring records its relation to the source;
     it is not weakened to reproduce the source's constant. A change of hypotheses, scope or
     public interface is a design change ([design](design.md)).

     **A docstring that uses a named bound shows its current value inside its equations.**
     Statements keep the name; the docstring writes the value in place of the constant, in the
     formula itself. A sample size that uses a named constant may instead write it as $C$ in its
     formula and give the value in the same docstring, "with <!-- value subgaussianJLConstant -->$C = 1/36$", as the header of
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
     treats a public definition whose name ends in `Constant`, `Bound`, `Tail`, `Dim` or `Factor`
     as a named bound. Ambiguous structural suffixes such as `Size`, `Rows`, `Rate`,
     `Exponent` and `Threshold` do not classify a definition as a numerical bound;
     register actual numerical bounds with these or other names by hand. To change a
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
     **Asymptotic forms.** A sample-size result of the subspace-embedding
     or algorithm kind (JL, OSE, OSI, the $(1+\varepsilon)$ bounds of the low-rank algorithms,
     PCP constructors) also gets the computer-science reading "$O(\cdot)$ suffices" as a corollary:
     `∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n … : Type} [instances] (μ) (A) (sketches) (k) (ε) …,
     hypotheses → 0 < ε → ε ≤ ε₀ → C * (threshold without constants) ≤ size → conclusion`. Every
     constant is existential and comes before every dimension, type, measure, matrix and
     parameter, so it is absolute; a dimension dependence the result really has (a $\log n$)
     appears in the threshold, never inside $C$. Index types are fixed to `Type` [B4]. A result
     of this kind without its asymptotic form is on a review list [B5]. The name starts
     `exists_forall_`, derived from the explicit theorem's name ([naming](naming.md) N17); the proof instantiates
     the explicit theorem, which stays primary and whose docstring names its asymptotic form. The
     asymptotic form's docstring says "$O(\ldots)$ suffices" in words [B3] and ends with the line
     `Asymptotic: <full name of the explicit theorem>` (before any `Result:` line; a name too long
     for the line goes alone on the next one), and the explicit theorem's docstring says
     "Asymptotic form: `…`." The explorer leads with the asymptotic form and offers the explicit
     bound beside it, so each docstring states its hypotheses and conclusion on its own, and at
     least one of the pair carries a `Result:` id. `scripts/check_refs.py` checks the tags and the
     pairing.
  4. Incomparable bounds coexist, each named by what distinguishes it: its hypothesis
     (`_of_bounded`, `_of_variance_le`) or the parameter its bound is in (`_intrinsicDimension`). Each
     docstring says in which regime it is better and names the other.
  5. A statement whose bound is the minimum of two others is added only when both have identical
     hypotheses and side conditions.
  6. A dominated result (the new bound is at least as good in every regime) is reproved from the
     new one and keeps its name when consumers cite its simpler form; otherwise it becomes
     `@[deprecated]` and is removed after a release.
  7. A bound is stated in its readable form when a sharper form differs from it only by a factor
     that is at most an absolute constant and tends to 1 as the bound becomes small [B6]. The typical case is a Chebyshev value: the proof bounds
     $1/T_q(\cdot)^2 = \operatorname{sech}^2(x) = 4e^{-2x}/(1 + e^{-2x})^2$, and the statement
     gives $4e^{-2x}$, as the sources print it (the CG bound $4\rho^{2q}$, the gapped block Krylov
     factor). The docstring gives the sharp form in one sentence and names the lost factor
     ($(1 + e^{-2x})^2 \le 4$). A separate sharp theorem is added only when another proof in the
     library uses it; an exact (equality) result, such as the CG worst case, is a result of its
     own and stays.
- Spectral statements never quantify over `hA.eigenvectorBasis i` [T8]; they take an eigenvector `u`
  with `A *ᵥ u = c • u` and `‖WithLp.toLp 2 u‖ = 1`, an invariance equation `A * U = U * M` with
  `HasOrthonormalCols U`, or speak of `eigenvalue A k`.
- Review opaque proof terms in statements [T9]. Expose mathematical assumptions as hypotheses
  or state through a definition. Structural evidence for finite indices, coercions and concrete
  resource configurations may remain inline; a printer’s `⋯` can hide generated evidence too.
- A bound variable that only meets `•` gets its type written: `∀ θ : ℝ, … θ • Y ω …`. Without it
  Lean elaborates `θ : ℕ` (`ℕ` acts on every additive monoid), and the hypothesis silently quantifies
  over natural numbers [T10].
- A lemma whose first explicit argument is a hypothesis `hA : A.IsHermitian` lives in that
  predicate's namespace, so that dot notation works ([naming](naming.md) N18).

## 3. Interfaces and reusable hypotheses

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
  `HasSubspaceEmbedding`" rather than "`gaussianMatrix`"; "any unitarily invariant norm" rather than
  Frobenius and spectral separately, when the proof is the same. The instance-specific theorem is
  then a corollary: the instance satisfies the interface.
- **Interfaces are designed, not accreted.** Introducing one is a [design](design.md) decision: what it bundles,
  what it leaves as separate hypotheses, which Mathlib notion it bridges to, which downstream
  theorems will consume it. A local predicate invented to make one file compile is a defect.
- **Fewer, broader interfaces.** Before adding a new one, check whether an existing one with one
  more field, or one fewer, covers the case. The test is the downstream user: can they state their
  theorem with the interfaces that exist?
