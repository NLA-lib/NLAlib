# Design note: Matrix stage M2, norms

Status: drafted 2026-10-14 by the orchestrator while M1 was being proved; implemented without a
maintainer approval stop, by the standing instruction in `docs/port/status.md`. Choices a
maintainer would have been asked about are in §7.

## 0. Scope, and what moved out

M2 is the Frobenius norm, the spectral norm, their relations, their behaviour under orthonormal
factors, projectors and blocks, and the ε-net bound for the spectral norm. Nothing here uses
singular values or eigenvalues.

**The Schatten family, the nuclear and Ky Fan norms, unitarily invariant norms, symmetric gauge
functions and Fan dominance are not in this stage.** Every one of them is a function of the
singular values, and their basic facts (`‖A‖_F² = ∑ σᵢ²`, `‖A‖₂ = σ₀`, invariance, duality) are
facts about the SVD. They form stage M3b, designed after M3 has singular values and `IsSVD`. The
brief left this choice to the note. Rank bounds such as `frobNorm A ≤ √(rank A) * specNorm A` move
with them for the same reason.

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| spectral norm | `specNorm A : ℝ`, no `DecidableEq` | `specNorm_eq_norm` (L2Operator scope), `rfl` |
| Frobenius norm | `frobNorm A : ℝ := √(∑ i, ∑ j, ‖A i j‖ ^ 2)` | `frobNorm_eq_norm` (Frobenius scope) |
| squared Frobenius norm | `frobNorm A ^ 2`; **no `frobSq`** | — |
| Frobenius inner product | `frobInner A B : ℝ := re (Aᴴ * B).trace` | `frobInner_eq_re_trace`, the only bridge to the `𝕜`-valued `(Aᴴ * B).trace` |
| ε-net of the sphere | Mathlib's `Metric.IsCover ε (Metric.sphere 0 1) N` in `EuclideanSpace 𝕜 n` | Mathlib's |
| two-sided spectral bound on `T` | Loewner form `a • 1 ≤ Tᴴ * T`, `Tᴴ * T ≤ b • 1` | `smul_one_le_conjTranspose_mul_self_iff`, `conjTranspose_mul_self_le_smul_one_iff`, `specNorm_sq_le_iff_conjTranspose_mul_self_le` |
| scalar times identity in a Loewner inequality | `(a : ℝ) • (1 : Matrix n n 𝕜)`, the real scalar action | Mathlib's; `RCLike.real_smul_eq_coe_smul` |

`specNorm` is defined as the operator norm of the continuous linear map
`EuclideanSpace 𝕜 n → EuclideanSpace 𝕜 m` built from `A.mulVecLin`. Mathlib's own definition goes
through `Matrix.toEuclideanLin`, which needs `[DecidableEq n]`; the two are definitionally equal,
so the bridge is still `rfl`, and no `specNorm` statement carries a `DecidableEq` it does not
otherwise need. The prototype's `specNorm` required `[DecidableEq n]` on the column type of every
matrix under a `specNorm`.

## 2. Interfaces

No new predicate is introduced.

- **Nets.** The prototype spelled "N is an ε-net of the unit sphere" as a raw condition in three
  theorems, each slightly differently. Mathlib has `Metric.IsCover`; the net theorems take it.
- **Bounded below, bounded above.** The prototype's
  `∀ x, c ^ 2 * x ⬝ᵥ x ≤ T.mulVec x ⬝ᵥ T.mulVec x` becomes the Loewner inequality
  `c ^ 2 • 1 ≤ Tᴴ * T`. This is the form a subspace embedding will deliver
  (`(1 - ε) • 1 ≤ (S U)ᴴ (S U) ≤ (1 + ε) • 1`), so the sketching layer can use these lemmas
  without conversion. `specNorm_le_iff_conjTranspose_mul_self_le` and
  `specNorm_le_iff` (the vector form) are the bridges.
- **Orthonormal factors** are `HasOrthonormalCols` (M1); **projectors** are `IsStarProjection` and
  `rangeProjector` (M1).

A unitarily-invariant-norm interface is M3b's to design. The recommendation recorded here for
that note: the carrier should be a symmetric gauge function on finitely supported sequences
`ℕ → ℝ`, applied to `singularValues A : ℕ → ℝ`, so that one object gives a norm on matrices of
every shape. The prototype's `UnitarilyInvariantNorm 𝕜 m n` is a seminorm on one shape; with it,
`ν (A * B) ≤ specNorm A * ν B` cannot even be stated when `A * B` and `B` have different shapes.

## 3. Statement shapes

Variables as in M1. All of these have been elaborated against the pinned Mathlib.

```lean
noncomputable def specNorm (A : Matrix m n 𝕜) : ℝ
noncomputable def frobNorm (A : Matrix m n 𝕜) : ℝ := √(∑ i, ∑ j, ‖A i j‖ ^ 2)
def frobInner (A B : Matrix m n 𝕜) : ℝ := RCLike.re (Aᴴ * B).trace

theorem frobNorm_sq (A : Matrix m n 𝕜) : frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2
theorem frobInner_self (A : Matrix m n 𝕜) : frobInner A A = frobNorm A ^ 2
theorem frobNorm_add_sq (A B : Matrix m n 𝕜) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + 2 * frobInner A B + frobNorm B ^ 2
theorem abs_frobInner_le (A B : Matrix m n 𝕜) : |frobInner A B| ≤ frobNorm A * frobNorm B

theorem norm_toLp_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖
theorem specNorm_le_iff {A : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ x, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖
theorem specNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    specNorm (A * B) ≤ specNorm A * specNorm B
theorem specNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : specNorm (Aᴴ * A) = specNorm A ^ 2
theorem specNorm_le_frobNorm (A : Matrix m n 𝕜) : specNorm A ≤ frobNorm A
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B
theorem frobNorm_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B

theorem smul_one_le_conjTranspose_mul_self_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    a • (1 : Matrix n n 𝕜) ≤ Tᴴ * T ↔
      ∀ x, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2
theorem specNorm_sq_le_iff_conjTranspose_mul_self_le [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 ≤ a) : specNorm T ^ 2 ≤ a ↔ Tᴴ * T ≤ a • (1 : Matrix n n 𝕜)
theorem mul_specNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * specNorm X ^ 2 ≤ specNorm (T * X) ^ 2
theorem _root_.Matrix.IsHermitian.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ -(c • (1 : Matrix n n 𝕜)) ≤ A ∧ A ≤ c • (1 : Matrix n n 𝕜)
theorem _root_.Matrix.PosSemidef.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) : specNorm A ≤ c ↔ A ≤ c • (1 : Matrix n n 𝕜)
theorem _root_.Matrix.PosSemidef.specNorm_le_specNorm_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : specNorm A ≤ specNorm B

theorem _root_.IsStarProjection.specNorm_le_one {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    specNorm P ≤ 1
theorem _root_.IsStarProjection.frobNorm_sq_eq_add [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = frobNorm (P * A) ^ 2 + frobNorm ((1 - P) * A) ^ 2

theorem specNorm_le_div_of_isCover (A : Matrix m n 𝕜) {N : Set (EuclideanSpace 𝕜 n)} {ε : ℝ≥0}
    (hε : ε < 1) (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ N, ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ M) :
    specNorm A ≤ M / (1 - ε)
theorem exists_finset_specNorm_le_div (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N : Finset (n → 𝕜), (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ (n → 𝕜) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      ∀ {m : Type u} [Fintype m] (A : Matrix m n 𝕜) {M : ℝ}, 0 ≤ M →
        (∀ x ∈ N, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ M) → specNorm A ≤ M / (1 - ε)
theorem exists_finset_specNorm_le_div_of_isHermitian (𝕜 : Type*) [RCLike 𝕜] (n : Type*)
    [Fintype n] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ N : Finset (n → 𝕜), (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ (n → 𝕜) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      ∀ (A : Matrix n n 𝕜), A.IsHermitian → ∀ {M : ℝ}, 0 ≤ M →
        (∀ x ∈ N, |RCLike.re (quadForm A x)| ≤ M) → specNorm A ≤ M / (1 - 2 * ε)
```

Conventions for this stage's statements:

- **Squared statements are written `frobNorm A ^ 2` and `specNorm A ^ 2`.** A bound that is
  naturally linear (`frobNorm (A * B) ≤ specNorm A * frobNorm B`) is stated once, linearly; its
  square follows by `gcongr`. A statement that is naturally quadratic (Pythagoras, additivity
  over blocks, entry sums) is stated once, squared.
- **`positivity` knows both norms.** Each definition file registers a `positivity` extension, so
  `gcongr` side goals and `calc` chains close without quoting `specNorm_nonneg`.
- **Invariance under orthonormal factors** is in the `HasOrthonormalCols` namespace:
  `hQ.specNorm_mul_left : specNorm (Q * A) = specNorm A`,
  `hQ.specNorm_mul_conjTranspose_right : specNorm (A * Qᴴ) = specNorm A`, and the same two for
  `frobNorm` and for `frobInner`. Contraction by `Qᴴ` on the left is
  `hQ.specNorm_conjTranspose_mul_le`.
- **The net cardinality exponent is the real dimension `Module.finrank ℝ (n → 𝕜)`**: `card n` over
  `ℝ` and `2 * card n` over `ℂ` (`finrank_real_fun`).
- **Nets have two levels.** The `Metric.IsCover` statements on `EuclideanSpace 𝕜 n` are the
  proof-level API. The two `exists_finset_…` headlines hide the cover: they hand the consumer a
  finite set of unit vectors in `n → 𝕜` that works for every matrix, with no `toLp`/`ofLp` traffic.
- **Loewner hypotheses take the bound itself, not its square root**: `a • 1 ≤ Tᴴ * T` with
  conclusion `a * specNorm X ^ 2 ≤ specNorm (T * X) ^ 2`. A subspace embedding delivers
  `a = 1 - ε` and nobody has to manufacture `√(1 - ε)`.
- **Two-sided characterisations also ship their halves** (`hA.le_smul_one_of_specNorm_le`,
  `hA.neg_smul_one_le_of_specNorm_le`), since eigenvalue bounds are used one side at a time.

## 4. Consumers

| Item | Consumed by |
|---|---|
| `specNorm`, `frobNorm`, mixed inequalities | every later stage and layer |
| `frobInner`, Pythagoras | M3 Eckart–Young, Mirsky; low-rank approximation error splits |
| Loewner forms of spectral bounds | matrix concentration (Bernstein, Chernoff conclude in this form); subspace embeddings; M6 |
| `IsHermitian.specNorm_le_iff` | Tropp-style bounds on `λ_max`, `λ_min`; M6 |
| projector contraction and Pythagoras | range finders, Nyström, M3 Eckart–Young, M5 |
| block bounds | M5 CS decomposition; M6 Wedin; range finder error splitting |
| nets | sub-Gaussian matrix norms (RandomMatrix), sparse embeddings |

## 5. Files

1. `NLAlib/Matrix/Norms/Frobenius.lean`: `frobInner`, `frobNorm`, bilinearity, Cauchy–Schwarz,
   norm axioms, the bridge, entry and column sums, diagonal, transposes, reindexing, `positivity`.
2. `NLAlib/Matrix/Norms/Spectral.lean`: `specNorm`, the bridge, norm axioms, `specNorm_le_iff`,
   submultiplicativity, the C*-identity, transposes, diagonal, entry bound, the bilinear form
   bound, existence of a maximising unit vector, `positivity`.
3. `NLAlib/Matrix/Norms/Compare.lean` (imports 1, 2, M1 `Orthonormal`): spectral ≤ Frobenius, the
   mixed product inequalities, invariance under orthonormal factors.
4. `NLAlib/Matrix/Norms/Loewner.lean` (imports 3, M1 `QuadForm`): the quadratic form bound, Gram
   matrices bounded above and below, Hermitian and PSD characterisations, monotonicity.
5. `NLAlib/Matrix/Norms/Block.lean` (imports 3, M1 `Dilation`): `fromRows`, `fromCols`,
   `fromBlocks`, submatrices, sums with orthogonal ranges, the Hermitian dilation.
6. `NLAlib/Matrix/Norms/Projector.lean` (imports 3, M1 `Projector`): contraction, Pythagoras,
   best approximation in both norms, monotonicity in the range, trace and Frobenius norm of
   `rangeProjector`.
7. `NLAlib/Matrix/Norms/Net.lean` (imports 4): the covering bounds and the existence of a finite
   net with the volumetric cardinality.

Independent for proving: 1 and 2; then 3; then 4, 5, 6 are independent of each other; 7 after 4.

## 6. Material

Read: prototype `Matrix/Norms/*` (31 files) through `atlas/declarations.json`, and
`Matrix/Subspaces/{Projections, RangeProjector}` for the norm statements M1 deferred.

Reused: `Core`, `Frobenius`, `SpectralNormBounds`, `BlockNormBounds`, `EntryBounds`,
`EuclideanOperatorBounds`, `RayleighNorm`, `Net`, `ColumnNorms`, and the projector norm lemmas.

Not reproduced:

- `frobSq` and the doubled lemma families it caused (`frobSq_mul_le_specNorm_sq_mul_frobSq` next
  to `frobNorm_mul_le_specNorm_mul_frobNorm`, `sum_diag_sq_le_frobSq` next to
  `sum_diag_sq_le_frobNorm_sq`).
- Real-only statements written with `x ⬝ᵥ x` and `√(x ⬝ᵥ x)` as a norm
  (`sqrt_dotProduct_add_le`, `abs_dotProduct_mulVec_le`, the `Net` file): restated over `𝕜` with
  `‖WithLp.toLp 2 x‖`.
- `Reindex.lean`: `specNorm_reindex` and `frobNorm_reindex` are kept as `submatrix` lemmas for
  equivalences; `mul_reindex` is Mathlib's `Matrix.submatrix_mul_equiv`.
- `_of_orthonormal` lemmas taking a raw `Pᴴ * P = 1`: they take `HasOrthonormalCols`.
- `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem`: it is `IsStarProjection.specNorm_le_one`.

Deferred to M3b with their prototype files: `Schatten*`, `Nuclear*`, `KyFanNorm`, `FanDominance`,
`InvariantNorm*`, `SymmetricGauge`, `RectangularDiagonal*`, `RankNorm`.

## 7. Decisions taken without approval

1. **`frobSq` is removed from the vocabulary; the squared norm is `frobNorm A ^ 2`.** This changes
   a §5.3 row. Reasons: it is a second spelling of one quantity, it doubled every Frobenius lemma
   in the prototype, Mathlib itself writes `‖x‖ ^ 2` and has no `normSq` for inner product
   spaces, and with a `positivity` extension `gcongr` moves between the linear and squared forms
   for free. Cost: expectations of squared errors read `∫ ω, frobNorm (E ω) ^ 2 ∂μ`. Alternative:
   keep `frobSq` as a definition with `frobNorm_sq : frobNorm A ^ 2 = frobSq A` as a simp lemma.
2. **Schatten, nuclear, Ky Fan and unitarily invariant norms move to a new stage M3b** after
   singular values.
3. **`specNorm` is redefined without `DecidableEq`**, keeping the `rfl` bridge (checked: the
   bridge elaborates by `rfl`).
4. **Nets use Mathlib's `Metric.IsCover`** on `EuclideanSpace 𝕜 n`, not a list of raw conditions
   on `n → 𝕜`.
5. **Lower and upper spectral bounds on a factor are Loewner inequalities on its Gram matrix.**
6. **`frobInner` stays real-valued** (§5.3 as it stands).

## 8. Design review (Fable, 2026-10-14)

Ruling on the squared Frobenius norm: **`frobNorm A ^ 2`, no `frobSq`** (§7.1 stands). Reasons
given: Mathlib writes `‖x‖ ^ 2` throughout and its integrability and variance API expects that
form; `ring_nf` already normalises `x * x` to `x ^ 2`; a `frobSq` would be a second normal form
and reproduce the prototype's doubled lemmas. Riders adopted: the exponent is always a natural
number, and the entry-sum unfolding `frobNorm_sq_eq_sum` is not a simp lemma.

Folded in from the eleven comments:

- `Matrix.IsHermitian.specNorm_le_iff` and `Matrix.PosSemidef.specNorm_le_iff` take `0 ≤ c`; as
  first written they were false for an empty index type and negative `c`.
- Bounded-below and bounded-above hypotheses take the bound `a` itself with squared conclusions;
  the lower vector bridge `smul_one_le_conjTranspose_mul_self_iff` was added.
- One spelling for a scalar multiple of the identity, the real action `(a : ℝ) • 1`, added as a
  §5.3 row.
- Net headlines over `n → 𝕜` that hide the cover, and the Hermitian quadratic-form net bound.
- `Matrix.PosSemidef.specNorm_le_specNorm_of_le` and the one-sided halves of the Hermitian
  characterisation.
- `Bounds.lean` split into `Compare.lean` and `Loewner.lean`.

Recorded for M3b, from the same review: `schattenNorm p`, `nuclearNorm`, `kyFanNorm k` are named
definitions with bridges `frobNorm_eq_schattenNorm_two` and `specNorm_eq_kyFanNorm_one`; the
unitarily invariant structure bundles a norm on sequences with permutation invariance and
absoluteness, has Fan dominance as an API lemma, and proves `ν (Q * A) = ν A` under
`HasOrthonormalCols` as a lemma on the structure.
