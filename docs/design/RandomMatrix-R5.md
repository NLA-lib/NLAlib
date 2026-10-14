# Design note: RandomMatrix stage R5, Haar frames (random matrices with orthonormal columns)

Status: drafted 2026-10-14 for the orchestrator under `docs/PORT_PROBABILITY.md` (D7 (a): the law is
the polar factor of a Gaussian). **One question of the brief's §2 kind (§7 Q1: the
unitary-invariance interface)**; the files that depend on it (§5: 1 and 3) wait for it, the others
do not.

## 0. Scope and consumers

The law `haarFrame n k` of an orthogonally invariant `n × k` matrix with orthonormal columns
(maintainer: "normalised Gaussians are a first-class distribution"): two-sided invariance, the
characterization by left invariance (giving QR, sub-frames, the column law), second moments from
invariance, isotropy of a rescaled column, and the Gaussian–Haar transfer of range statistics.
Real (D4); the interface over `𝕜`.

| Item | Consumers (`inventory-sketching.md` §7, §10) |
|---|---|
| `haarFrame n k`, a.s. frames, `HasLaw` of the polar factor | everything below; the next round's Haar sketch `S = √(n/k) Qᴴ` |
| transfer of `rangeProjector (A * Ω)` between Gaussian and Haar `Ω` | range-finder family R1 to R6 (each output depends on `Ω` only through `range (A Ω)`); random-start power and Lanczos (E6, `k = 1`) |
| `E [Q B Qᴴ] = (tr B / n) • 1`, `E [Q Qᴴ] = (k/n) • 1`, `E [Qᴴ A Q] = (tr A / n) • 1` | Haar sketch isotropy `E [Sᴴ S] = 1`; trace estimation with an orthonormal `Q` (E4); AMM |
| `E Qᵢⱼ² = 1/n`, isotropy of `√n · Q e_j` | Hutchinson with sphere probes (E1 through `IsIsotropic`) |
| the law of a column, `g / ‖g‖` | E6 (start uniform on the sphere); JL in Dasgupta–Gupta form (next round) |
| QR construction `gramSchmidtQ G` | user expectation (standard treatment; the prototype's one theorem) |
| `IsLeftUnitarilyInvariant` (D6) | R5's characterization; next round's oblivious-embedding proofs for Gaussian and Haar |

Not here: fourth moments (§7 Q4), concentration of `‖Qᴴ x‖²` (Dasgupta–Gupta; with JL in the
next round), Lipschitz concentration on the sphere or `O(n)`, `G = Q R` with `Q`, `R`
independent, the complex law (§7 Q5).

## 1. Objects

| Concept | Spelling | Bridge |
|---|---|---|
| Haar frame law | `haarFrame n k : Measure (Matrix n k ℝ) := (gaussianMatrix n k).map polarFactor`, a `def` with `[DecidableEq k]` (needed by `polarFactor`) | `hasLaw_polarFactor_of_hasLaw_gaussianMatrix` (the definition in `HasLaw` form) |
| its probability instance | `instance isProbabilityMeasure_haarFrame` (R1 §8 rule 1: explicit instances) | — |
| junk value | for `card n < card k`, a Haar frame of `k × n`, conjugate transposed: orthonormal **rows** | `hasLaw_conjTranspose_of_hasLaw_haarFrame` (every shape) |

A `def`, not an `abbrev` like `gaussianMatrix`: access is through the `HasLaw` bridge. Mathlib's
`haarMeasure` on `Matrix.orthogonalGroup` covers only the square case, bundled (§7 Q6). No sphere
measure is defined: the column law is the law of `g / ‖g‖` (§3.3).

**Matrix-layer additions** (the proof agent writes them, over `𝕜`, in the files named):
1. `Factorizations/Polar.lean`: `polarFactor_mul_right {V : Matrix n q 𝕜} (hV : HasOrthonormalCols Vᴴ)
   (A : Matrix m n 𝕜) : polarFactor (A * V) = polarFactor A * V` (any coisometry, so any unitary).
   Proof: `polarFactor_conjTranspose` twice around `polarFactor_mul_left` with `W = Vᴴ`.
2. `Polar.lean`: `rangeProjector_mul_polarFactor (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
   rangeProjector (A * polarFactor B) = rangeProjector (A * B)`, every shape and rank (mutual range
   inclusion from `polarFactor B = B * pinv (CFC.sqrt (Bᴴ * B))` and `polarFactor_mul_sqrt`), and
   `rangeProjector_polarFactor` (`A = 1`). Searched: `polarFactor_mul_conjTranspose_self` is the
   closest; no range statement exists.
3. `Polar.lean`: `specNorm_polarFactor_le_one` (a partial isometry; from
   `conjTranspose_polarFactor_mul_self`). Searched, none.
4. `Polar.lean`: `polarFactor_replicateCol (x : m → 𝕜) : polarFactor (Matrix.replicateCol Unit x) =
   Matrix.replicateCol Unit ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) • x)`, true at `x = 0` (both sides `0`).
5. `Basic/OrthonormalBasis.lean`: `HasOrthonormalCols.exists_mul_eq (hX : HasOrthonormalCols X)
   (hY : HasOrthonormalCols Y) : ∃ U : Matrix m m 𝕜, HasOrthonormalCols U ∧ U * X = Y` (transitivity),
   the private `exists_hasOrthonormalCols_mul_eq` of `Factorizations/Procrustes.lean` made public and
   moved to its owner file (CONTRIBUTING §3).
6. `Basic/OrthonormalBasis.lean`: `eq_smul_one_of_forall_mul_mul_conjTranspose_eq {M : Matrix n n 𝕜}
   (h : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → U * M * Uᴴ = M) :
   M = (M.trace / Fintype.card n) • 1` ("a matrix commuting with every unitary is scalar"; signed
   permutation matrices suffice). Searched: Mathlib's `Matrix.mem_range_scalar_of_commute_single`
   needs commutation with the non-unitary `single i j 1`; none for unitaries.

## 2. Interfaces

`IsLeftUnitarilyInvariant` and `IsRightUnitarilyInvariant` (D6's row), over `𝕜`, on measures,
introduced here (§7 Q1):

```lean
/-- A law on `n × k` matrices is **left unitarily invariant** when `U Q` has the law of `Q` for
every unitary (over `ℝ`, orthogonal) `U`. Mirrors Mathlib's `Measure.IsMulLeftInvariant`. -/
class IsLeftUnitarilyInvariant (ν : Measure (Matrix n k 𝕜)) : Prop where
  map_mul_left_eq_self : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → ν.map (U * ·) = ν
class IsRightUnitarilyInvariant (ν : Measure (Matrix n k 𝕜)) : Prop where
  map_mul_right_eq_self : ∀ V : Matrix k k 𝕜, HasOrthonormalCols V → ν.map (· * V) = ν
```

The class is the raw condition (its constructor is `⟨…⟩`); consumers use the `HasLaw` API of §3.1.
Instances: `gaussianMatrix` (§3.1), `haarFrame` (§3.2). Random frames as hypotheses stay D6's three
Mathlib-form hypotheses, bundled nowhere; `IsIsotropic` is used as P0 defines it.

## 3. Statement shapes

`namespace NLAlib`; `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`,
`{n k q : Type*} [Fintype n] [Fintype k] [Fintype q] [DecidableEq n] [DecidableEq k] [DecidableEq q]`
(instances per statement, R4 §8.4), `{X : Ω → Matrix n k ℝ}`, `hX : HasLaw X (haarFrame n k) μ`,
`hk : Fintype.card k ≤ Fintype.card n` wherever orthonormal columns are used. Every file that
integrates matrices opens `Matrix.Norms.L2Operator` (deviation entry 13). D2: random variables
only, the measure form is `HasLaw.id`; D3: each expectation has its integrability companion; D5:
no constants arise (all moments are exact).

### 3.1 `RandomMatrix/UnitaryInvariance.lean` (over `𝕜`; waits for §7 Q1)

```lean
theorem hasLaw_const_mul_of_isLeftUnitarilyInvariant {ν : Measure (Matrix n k 𝕜)}
    [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ) {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) : HasLaw (fun ω => U * X ω) ν μ
theorem hasLaw_mul_const_of_isRightUnitarilyInvariant … [IsRightUnitarilyInvariant ν]
    (hX : HasLaw X ν μ) {V : Matrix k k 𝕜} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => X ω * V) ν μ
instance isLeftUnitarilyInvariant_gaussianMatrix : IsLeftUnitarilyInvariant (gaussianMatrix n k)
instance isRightUnitarilyInvariant_gaussianMatrix : IsRightUnitarilyInvariant (gaussianMatrix n k)
/-- A left unitarily invariant random matrix has mean zero (`U = -1`); no integrability needed,
since `∫ (-X) = -∫ X` holds for the Bochner integral in every case. -/
theorem integral_eq_zero_of_isLeftUnitarilyInvariant [IsLeftUnitarilyInvariant ν]
    (hX : HasLaw X ν μ) : ∫ ω, X ω ∂μ = 0
/-- **`E [X B Xᴴ]` is scalar** for a left unitarily invariant `X`: it commutes with every unitary. -/
theorem integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant [IsLeftUnitarilyInvariant ν]
    (hX : HasLaw X ν μ) (B : Matrix k k 𝕜) (hint : Integrable (fun ω => X ω * B * (X ω)ᴴ) μ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ =
      ((∫ ω, (X ω * B * (X ω)ᴴ).trace ∂μ) / Fintype.card n) • (1 : Matrix n n 𝕜)
```

The integrability hypothesis is needed: without it the left side is `0` while the trace may still
be integrable. Proof: `Matrix.integral_const_mul`, `Matrix.integral_mul_const`,
`Matrix.integral_trace` (P0) and addition 6. Gaussian instances: R1's
`hasLaw_const_mul_of_hasLaw_gaussianMatrix` with `HasOrthonormalCols.conjTranspose_of_card_eq`.

### 3.2 `RandomMatrix/Haar/Basic.lean`

```lean
/-- The law of an `n × k` **Haar frame**: the polar factor `G (Gᴴ G)^{-1/2}` of a standard Gaussian
`G`. For `card k ≤ card n` it is concentrated on matrices with orthonormal columns and invariant
under orthogonal maps on both sides. Junk value: for `card n < card k` it is the law of `Pᴴ` for a
`k × n` Haar frame `P` (orthonormal rows); every theorem using columns assumes `card k ≤ card n`. -/
noncomputable def haarFrame (n k : Type*) [Fintype n] [Fintype k] [DecidableEq k] :
    Measure (Matrix n k ℝ) := (gaussianMatrix n k).map polarFactor
instance isProbabilityMeasure_haarFrame : IsProbabilityMeasure (haarFrame n k)
/-- **The polar factor of a Gaussian matrix is a Haar frame.** -/
theorem hasLaw_polarFactor_of_hasLaw_gaussianMatrix {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) :
    HasLaw (fun ω => polarFactor (G ω)) (haarFrame n k) μ
theorem ae_hasOrthonormalCols_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) : ∀ᵐ ω ∂μ, HasOrthonormalCols (X ω)
/-- Every shape; for `card n ≤ card k` it says `X` has orthonormal rows a.s. -/
theorem hasLaw_conjTranspose_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ) :
    HasLaw (fun ω => (X ω)ᴴ) (haarFrame k n) μ
theorem ae_specNorm_le_one_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ) :
    ∀ᵐ ω ∂μ, specNorm (X ω) ≤ 1
theorem memLp_apply_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ) (i : n) (j : k)
    (p : ℝ≥0∞) : MemLp (fun ω => X ω i j) p μ
instance isLeftUnitarilyInvariant_haarFrame : IsLeftUnitarilyInvariant (haarFrame n k)
instance isRightUnitarilyInvariant_haarFrame : IsRightUnitarilyInvariant (haarFrame n k)
```

Proofs: frames from R1's `ae_rank_eq_min_…` and `hasOrthonormalCols_polarFactor_iff`, through
the closed set `isClosed_setOf_hasOrthonormalCols`; transpose from `polarFactor_conjTranspose`;
left invariance from `polarFactor_mul_left`, right from addition 1, each with R1's invariance
(square `U`, `V` only: for a tall isometry `W`, `W G` is not Gaussian). Both instances hold for
every shape. Mean zero is §3.1's lemma at the instance, not restated. If §7 Q1 is deferred the
instances become `hasLaw_const_mul_of_hasLaw_haarFrame` and its right twin (square `V`).

### 3.3 `RandomMatrix/Haar/Uniqueness.lean` (waits for §7 Q1)

```lean
/-- **Characterization of the Haar frame**: a random matrix with a.s. orthonormal columns whose
law is left unitarily invariant is a Haar frame. -/
theorem hasLaw_haarFrame_of_isLeftUnitarilyInvariant [IsProbabilityMeasure μ]
    {ν : Measure (Matrix n k ℝ)} [IsLeftUnitarilyInvariant ν] (hX : HasLaw X ν μ)
    (hQ : ∀ᵐ ω ∂μ, HasOrthonormalCols (X ω)) : HasLaw X (haarFrame n k) μ
/-- **The QR construction**: the Gram–Schmidt factor of a tall Gaussian matrix is a Haar frame. -/
theorem hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix [LinearOrder k] [LocallyFiniteOrderBot k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    HasLaw (fun ω => gramSchmidtQ (G ω)) (haarFrame n k) μ
/-- **Sub-frames**: `Q V` is a Haar frame for `V` with orthonormal columns; with
`V = selectionMatrix s`, any set of columns. Square `V` is right invariance. -/
theorem hasLaw_mul_const_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) {V : Matrix k q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => X ω * V) (haarFrame n q) μ
/-- **A column is uniform on the sphere**: it has the law of `g / ‖g‖`, `g` standard Gaussian. -/
theorem hasLaw_col_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    HasLaw (fun ω i => X ω i j)
      ((gaussianVector n).map fun g => (‖WithLp.toLp 2 g‖⁻¹ : ℝ) • g) μ
```

No `hk` in the first: without frames `hQ` forces `μ = 0`. Proof: the prototype's Tonelli argument
(`measure_eq_haarFrameLaw_of_invariant`) with Mathlib's Haar measure on `O(n)` replaced by
`haarFrame n n`, so neither compactness nor Haar uniqueness on the group: for a frame `x` the law
`η_x` of `U x`, `U ~ haarFrame n n`, does not depend on `x` (addition 5 and right invariance), and
`ν s = ∫ U, ν ((U * ·)⁻¹' s) = ∫ x, η_x s ∂ν = η s` by `lintegral_lintegral_swap`; `haarFrame n k`
is one such `ν`. About 150 lines. QR: `gramSchmidtQ_mul_left`, R1's rank, `measurable_gramSchmidtQ`;
sub-frames: `Q V` is a frame with left-invariant law; the column: `V = replicateCol Unit
(Pi.single j 1)` and addition 4 (at `g = 0`, probability zero, both sides are `0`).

### 3.4 `RandomMatrix/Haar/Moments.lean`

```lean
/-- **`E [Q B Qᴴ] = (tr B / n) • 1`** for a Haar frame. -/
theorem integral_mul_mul_conjTranspose_of_hasLaw_haarFrame (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (B : Matrix k k ℝ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ = (B.trace / Fintype.card n) • (1 : Matrix n n ℝ)
theorem integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame (hX : …) (B : Matrix k k ℝ) :
    Integrable (fun ω => X ω * B * (X ω)ᴴ) μ
/-- **`E [Q Qᴴ] = (k / n) • 1`**: a Haar frame's range projector is `k / n` times the identity in
mean. -/
theorem integral_mul_conjTranspose_of_hasLaw_haarFrame (hX : …) (hk : …) :
    ∫ ω, X ω * (X ω)ᴴ ∂μ = ((Fintype.card k : ℝ) / Fintype.card n) • (1 : Matrix n n ℝ)
/-- **`E [Qᴴ A Q] = (tr A / n) • 1`**. -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_haarFrame (hX : …) (hk : …) (A : Matrix n n ℝ) :
    ∫ ω, (X ω)ᴴ * A * X ω ∂μ = (A.trace / Fintype.card n) • (1 : Matrix k k ℝ)
theorem integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame (hX : …) (A : Matrix n n ℝ) :
    Integrable (fun ω => (X ω)ᴴ * A * X ω) μ
theorem integral_apply_sq_of_hasLaw_haarFrame (hX : …) (hk : …) (i : n) (j : k) :
    ∫ ω, X ω i j ^ 2 ∂μ = 1 / Fintype.card n
/-- `√n` times a column of a Haar frame is isotropic. -/
theorem isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame (hX : …) (hk : …) (j : k) :
    IsIsotropic (fun ω i => √(Fintype.card n : ℝ) * X ω i j) μ
```

Proofs from invariance alone: the interface lemma of §3.1 with `tr (X B Xᴴ) = tr (B Xᴴ X) = tr B`
a.s.; `E [Qᴴ A Q]` by the same lemma for `Qᴴ` (law `haarFrame k n`, left invariant), its trace
being `tr (A E [Q Qᴴ]) = k tr A / n`; the entry is the `(i, i)` entry with `B = single j j 1`; isotropy
from `memLp_apply_…` and the same `B`. Companions from `ae_specNorm_le_one_…` (bounded integrands);
the entry's is `(memLp_apply_… 2).integrable_sq`. The `B = 1` case is kept as its own statement
because consumers rewrite with it.

### 3.5 `RandomMatrix/Haar/Transfer.lean`

```lean
/-- **Transfer between Gaussian and Haar test matrices**: the range projector of `A Q` for a Haar
frame `Q` has the law of that of `A G` for a standard Gaussian `G`. Every shape and rank. -/
theorem hasLaw_rangeProjector_mul_of_hasLaw_haarFrame {m : Type*} [Fintype m] (A : Matrix m n ℝ)
    (hX : HasLaw X (haarFrame n k) μ) :
    HasLaw (fun ω => rangeProjector (A * X ω))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) μ
/-- The form a range-finder consumer applies: expectations of any statistic of `range (A Ω)` agree
for a Haar `X` and a Gaussian `G`, on any two probability spaces. -/
theorem integral_comp_rangeProjector_mul_of_hasLaw_haarFrame {m : Type*} [Fintype m]
    (A : Matrix m n ℝ) {f : Matrix m m ℝ → ℝ} (hf : Measurable f)
    (hX : HasLaw X (haarFrame n k) μ) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {G : Ω' → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ') :
    ∫ ω, f (rangeProjector (A * X ω)) ∂μ = ∫ ω', f (rangeProjector (A * G ω')) ∂μ'
```

A statistic of a column space is a function of its projector, so the first theorem is the
general transfer (any measurable `f` by `HasLaw.comp`, hence tails too); `A = 1` is `range Q`. The
residual `(1 - rangeProjector (A Ω)) A` of HMT Theorem 9.1 is such an `f`, so every range-finder
bound proved for Gaussian `Ω` holds verbatim for Haar `Ω`, integrability included. No `hk`:
addition 2 holds at every rank (the brief asked only for full rank). No integrability hypothesis:
both sides integrate against one law. Proof: addition 2, `measurable_rangeProjector`,
`HasLaw.integral_comp`.

## 4. Consumers of the headline statements

§0's table; §3.1's lemma also gives the Gaussian `E [G B Gᴴ] = tr B • 1`.

## 5. Files

1. `RandomMatrix/UnitaryInvariance.lean`: §2 and §3.1 (8); imports R1 `Gaussian/Invariance`, P0
   `MatrixIntegral`. Waits for §7 Q1.
2. `RandomMatrix/Haar/Basic.lean`: §3.2 (9); imports 1 (for the instances), the Matrix additions
   1 to 4, `Measurability/Matrix`, R1 `Gaussian/Rank`.
3. `RandomMatrix/Haar/Uniqueness.lean`: §3.3 (4); imports 2, addition 5. Waits for §7 Q1.
4. `RandomMatrix/Haar/Moments.lean`: §3.4 (7); imports 2, addition 6, P0 `Isotropic`.
5. `RandomMatrix/Haar/Transfer.lean`: §3.5 (2); imports 2.

The Matrix additions are one PR to `Polar.lean` and `OrthonormalBasis.lean` first. 3, 4, 5 are
independent of each other and all import 2.

## 6. Material

Read: the prototype's `RandomMatrix/Haar/{HaarFrameMeasure,HaarQR}.lean` (18 declarations) and
`inventory-probability.md` §8, `inventory-sketching.md` §7, §10. Covered: `haarFrameLaw`,
`haarFrameLaw_map_smul`, `measure_eq_haarFrameLaw_of_invariant` (its Tonelli proof is §3.3's
route), `gaussianMatrix_map_canonicalQRFrame`. Not reproduced: `Stiefel` (bundled, brief §6),
`orthogonalHaar` and instances (replaced by `haarFrame n n`, §7 Q6), `stiefelSquareToOrthogonal`
and its lemmas, `_of_hasLaw` twins (D2), `Fin` indices, "operator re-derivation" citations. Citations:
Haar frames and their moments [Meckes2019, Ch. 1–2] (key to be added to `docs/references.bib`);
the range finder [HalkoMartinssonTropp2011, §4, §10]. `gaussianRangeFrame` is the next
round's (R4 §0).

## 7. Open questions

**Q1 (the brief's §2 kind: it fixes an interface). Introduce `IsLeftUnitarilyInvariant` and
`IsRightUnitarilyInvariant` now, as §2 writes them.** Choices: (i) now or deferred; (ii) a `class`
on a measure, as Mathlib's `IsMulLeftInvariant` and `SMulInvariantMeasure` are, or a `def … : Prop`
like `IsIsotropic`; (iii) the field: `ν.map (U * ·) = ν` for square `U` with `HasOrthonormalCols`,
over `𝕜`. *Recommendation:* now, as a `class` (instances on the concrete laws are found, like
`IsProbabilityMeasure` and `IsGaussian`), with that field, left and right separately. Reason:
§3.3 needs exactly this hypothesis, and spelling it raw there, in the QR proof and in the moments
breaks CONTRIBUTING §5.4; the next round's oblivious-embedding proofs take it. Mathlib's
`SMulInvariantMeasure (Matrix.unitaryGroup n 𝕜) (Matrix n k 𝕜)` needs a global `MulAction` on
rectangular matrices, which Mathlib lacks and CONTRIBUTING §7 forbids adding: deviation entry 14
(why: consumers hold `Matrix` values with `HasOrthonormalCols`, as in entry 4; bridge: none without
that instance). *Rework:* every theorem taking it. Waiting: files 1, 3 and file 2's instances;
files 4 and 5 state no interface (their proofs use file 1, or direct invariance if deferred).

**Q2. The QR construction is in, through the characterization of §3.3** (orchestrator decision).
The brief allows it only without uniqueness of Haar measure. The argument does prove that a
left-invariant law of frames is unique, but against `haarFrame n n`, which is already built; it
needs neither `CompactSpace` of the orthogonal group (absent from Mathlib) nor Mathlib's Haar
uniqueness. Cost: about 150 lines plus addition 5, and it also gives sub-frames and the column law.
Fallback if the proof exceeds its budget: `Uniqueness.lean` goes to `NLAlibScaffold` with that
`Proof:` line; nothing else in R5 depends on it.

**Q3. Degenerate cases.** `haarFrame` is defined on every shape with the documented junk (a
coisometry when `card n < card k`), and column theorems take `hk : card k ≤ card n`, never a proof
term in the definition (the prototype's `haarFrameLaw n k hkn`). Without `hk`, `E [Q Qᴴ] = 1` and
`E Qᵢⱼ² = 1 / card k`, so it is needed. `k` empty: the law is `dirac 0`, a frame, and every
statement holds (`(0 / n) • 1 = 0`). `n` empty, `k` nonempty: `dirac 0`, not a frame, excluded by
`hk`; so `1 / card n` is never `1 / 0` where it matters. `card k = card n`: square orthogonal.

**Q4. Fourth moments deferred.** They do not follow from invariance alone: `E uᵢ⁴ = 3/(n(n+2))`
and `E uᵢ² uⱼ² = 1/(n(n+2))` for a column `u` need the independence of `g / ‖g‖` and `‖g‖` (from
§3.3 applied to finite measures `s ↦ E [1_s(u) h(‖g‖)]`, or Mathlib's
`measurePreserving_homeomorphUnitSphereProd`) and R4's `χ²` moments. Cost about 150 lines; no
consumer in either survey (the frame-contraction sum of CountSketch is deterministic). Added with
the next round's Haar JL if it wants them.

**Q5. Complex analogue.** As P2 §7 Q1 and R1: a parallel `complexHaarFrame n k` later (polar
factor of a complex Gaussian), names carrying `complexHaarFrame`, nothing here renamed. Already
over `𝕜`: §2, §3.1 and Matrix additions 1 to 6; §3.3's argument is field-free.

**Q6. Deviation entry 15, the square case.** `haarFrame n n` re-spells Haar measure on
`Matrix.orthogonalGroup n ℝ` as a measure on matrices (why: rectangular frames, `Matrix` values,
D7 (a)). The bridge `haarFrame n n = (haarMeasure ⊤).map Subtype.val` is blocked on
`CompactSpace (Matrix.unitaryGroup n ℝ)`, absent from Mathlib; given it, it is a corollary of §3.3.

**Q7. Transfer by range projector**, not by a hypothesis "`F (B T) = F B` for invertible `T`":
the projector form needs no rank hypothesis and no new raw condition. A consumer whose statistic
is given otherwise rewrites it through `rangeProjector_mul_of_isUnit`.
