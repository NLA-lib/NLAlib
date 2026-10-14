# Design note: RandomMatrix stage R1, Gaussian matrices

Status: written 2026-10-14 by the orchestrator under `docs/PORT_PROBABILITY.md` (§2 decided; D4:
the Gaussian matrix law is real in this round, with a complex analogue later as a parallel
definition, as P2 §7 Q1 decided for vectors). No question of the brief's §2 kind. Reviewed by a
Fable agent on 2026-10-14; corrections in §8; the skeletons under `NLAlib/RandomMatrix/Gaussian/`
are the statements where they differ from §3.

## 0. Scope and consumers

The law of a random matrix with independent standard Gaussian entries, its decompositions (rows,
columns, flattening), its invariance under orthonormal maps on both sides, the independence of
orthogonal blocks, the law of `G x`, almost sure rank, and Gaussian concentration of Frobenius-
Lipschitz functions of `G` (P4 transported).

| Item | Consumers (prototype files) |
|---|---|
| `gaussianMatrix m n`, entries, rows | 13 files (LowRank 7, Estimation 4, Sketching 2) |
| two-sided orthogonal invariance, transpose | R4 (inverse moments), R5 (the polar factor's law), LowRank |
| independence of orthogonal blocks `V₁ᴴ G`, `V₂ᴴ G` | LowRank (the range finder's `Ω₁`, `Ω₂`: 2 files) |
| `G x ~ N(0, ‖x‖² I)` | JL (Sketching: `GaussianEmbedding`) |
| almost sure rank: `rank (A * G) = min (rank A) t` | LowRank (5 files: range frames, Nyström) |
| concentration of Frobenius-Lipschitz functions | R3 (`σ_max`, `σ_min` about their means) |

Not here: moments of `S G T` (R2), extreme singular values (R3), inverse moments (R4), the polar
factor's law (R5).

## 1. Objects

| Concept | Spelling | Bridge |
|---|---|---|
| standard Gaussian matrix law | `gaussianMatrix m n := Measure.pi fun _ : m => gaussianVector n`, a `noncomputable abbrev` on `Matrix m n ℝ` (the matrix σ-algebra is `MeasurableSpace.pi`, D8) | P0's `hasLaw_pi_pi_iff`, `HasLaw.entry`, `HasLaw.iIndepFun_entry` apply by unification; flattening to `gaussianVector (m × n)` (§3.1) |
| its probability instance | `instance : IsProbabilityMeasure (gaussianMatrix m n)` (P0 report: not found automatically at `Measure (Matrix m n α)`) | — |
| Frobenius norm as a Euclidean norm | `frobNorm A = ‖WithLp.toLp 2 (fun p : m × n => A p.1 p.2)‖` | Matrix layer `frobNorm` |

`gaussianMatrix m n` is written with `gaussianVector n` for the rows so that "the rows are i.i.d.
standard Gaussian vectors" is P0's `HasLaw.eval` with no rewriting.

## 2. Interfaces

None new. Instances from P0–P3 through flattening: `IsIsotropic` and `IsSubgaussianVector` of
the flattened matrix (R2 and R3 state what they need from these).

## 3. Statement shapes

`namespace NLAlib`. Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`,
`{m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]`,
`{X : Ω → Matrix m n ℝ}`. Statements are for a random variable with the law (D2).

### 3.1 `RandomMatrix/Gaussian/Basic.lean`

```lean
noncomputable abbrev gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℝ) :=
  Measure.pi fun _ : m => gaussianVector n
instance isProbabilityMeasure_gaussianMatrix : IsProbabilityMeasure (gaussianMatrix m n)
/-- The rows of a Gaussian matrix are independent standard Gaussian vectors. -/
theorem hasLaw_row_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) (i : m) :
    HasLaw (fun ω => X ω i) (gaussianVector n) μ
theorem iIndepFun_row_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    iIndepFun (fun i ω => X ω i) μ
/-- A Gaussian matrix flattened to `m × n` is a standard Gaussian vector. -/
theorem hasLaw_flatten_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω (k : m × n) => X ω k.1 k.2) (gaussianVector (m × n)) μ
/-- Independent standard Gaussian entries make a Gaussian matrix (the converse). -/
theorem hasLaw_gaussianMatrix_of_hasLaw_flatten
    (hX : HasLaw (fun ω (k : m × n) => X ω k.1 k.2) (gaussianVector (m × n)) μ) :
    HasLaw X (gaussianMatrix m n) μ
theorem frobNorm_eq_norm_toLp_flatten (A : Matrix m n 𝕜) :
    frobNorm A = ‖WithLp.toLp 2 (fun k : m × n => A k.1 k.2)‖
instance isGaussian_gaussianMatrix : IsGaussian (gaussianMatrix m n)
```

`frobNorm_eq_norm_toLp_flatten` is over `𝕜` and belongs to the Matrix layer's
`Norms/Frobenius.lean` (a one-line consequence of `frobNorm_sq_eq_sum`); the proof agent adds it
there. Entries and their independence are P0's `HasLaw.entry`, `HasLaw.iIndepFun_entry` with
`ν i j = gaussianReal 0 1` (after `gaussianVector`'s `abbrev`), not restated. P0's private
`measurePreserving_curry_pi` (`Probability/Law.lean`) becomes public as the flattening step.

### 3.2 `RandomMatrix/Gaussian/Invariance.lean`

```lean
/-- **Orthogonal invariance**: for `U` with orthonormal rows and `V` with orthonormal columns,
`U G V` is a standard Gaussian matrix. -/
theorem hasLaw_mul_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ)
    {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => U * X ω * V) (gaussianMatrix p q) μ
theorem hasLaw_transpose_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω => (X ω)ᵀ) (gaussianMatrix n m) μ
/-- `G x` is a standard Gaussian vector for a unit vector `x`. -/
theorem hasLaw_mulVec_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) : HasLaw (fun ω => X ω *ᵥ x) (gaussianVector m) μ
/-- **Independence of orthogonal blocks**: for frames `V₁`, `V₂` with `V₁ᴴ V₂ = 0`, the blocks
`V₁ᴴ G` and `V₂ᴴ G` are independent standard Gaussian matrices. -/
theorem indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {V₁ : Matrix m p ℝ} {V₂ : Matrix m q ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) :
    IndepFun (fun ω => V₁ᴴ * X ω) (fun ω => V₂ᴴ * X ω) μ
```

The block laws are the first theorem with `U = V₁ᴴ`. Over `ℝ`, `ᴴ = ᵀ` (`conjTranspose_eq_transpose_of_trivial`);
statements use `ᴴ` (CONTRIBUTING §5.1). The proof is Mathlib's `stdGaussian_map` for linear
isometries after flattening (`U ⊗ Vᵀ` acting on `m × n` coordinates is an isometry onto its
range when the frames are orthonormal; for non-square frames, a completion to an orthogonal
matrix and a projection), and independence from `HasGaussianLaw.indepFun_of_covariance_eq_zero`
(or the product structure after completing `[V₁ V₂]`).

### 3.3 `RandomMatrix/Gaussian/Rank.lean`

```lean
/-- A nonzero polynomial in independent coordinates with an atomless law is almost surely
nonzero. -/
theorem ae_eval_ne_zero_of_ne_zero {ι : Type*} [Fintype ι] {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NoAtoms ν] {f : MvPolynomial ι ℝ} (hf : f ≠ 0) :
    ∀ᵐ x ∂Measure.pi fun _ : ι => ν, MvPolynomial.eval x f ≠ 0
/-- A Gaussian matrix has full rank almost surely. -/
theorem ae_rank_eq_min_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (X ω).rank = min (Fintype.card m) (Fintype.card n)
/-- **Rank of a Gaussian sketch**: `rank (A G) = min (rank A) t` almost surely. -/
theorem ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix {l : Type*} [Fintype l] (A : Matrix l m ℝ)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card n)
```

`ae_eval_ne_zero_of_ne_zero` is general measure theory (`ForMathlib/MeasureTheory/` if the proof
agent prefers; it is the source of every "full rank a.s."). Range frames (the prototype's
`gaussianRangeFrame`, chosen from an existence lemma) are R4's, with their consumer.

### 3.4 `RandomMatrix/Gaussian/Concentration.lean`

```lean
/-- **Gaussian concentration** for a function of a Gaussian matrix that is `L`-Lipschitz for the
Frobenius distance. -/
theorem hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {f : Matrix m n ℝ → ℝ} {L : ℝ≥0}
    (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ
theorem integrable_comp_of_hasLaw_gaussianMatrix … : Integrable (fun ω => f (X ω)) μ
theorem measureReal_integral_add_le_of_hasLaw_gaussianMatrix … {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2))
```

The Lipschitz hypothesis is the explicit Frobenius inequality: `Matrix` has no global metric
(P4 review), and the explicit form is what R3 discharges with
`abs_singularValues_sub_le_frobNorm`. Proof: flatten (§3.1), `frobNorm_eq_norm_toLp_flatten`,
P4's `lipschitzWith_ofLp_iff` and `…_of_lipschitzWith_of_hasLaw_gaussianVector`.

## 4. Consumers of the headline statements

See §0. The flattening bridge is what P2–P4's vector results are applied through.

## 5. Files

1. `RandomMatrix/Gaussian/Basic.lean`: §3.1 (8 statements) and the Frobenius bridge in
   `Matrix/Norms/Frobenius.lean`.
2. `RandomMatrix/Gaussian/Invariance.lean`: §3.2 (4).
3. `RandomMatrix/Gaussian/Rank.lean`: §3.3 (3).
4. `RandomMatrix/Gaussian/Concentration.lean`: §3.4 (3).
2, 3, 4 are independent; all import 1.

## 6. Material

Read: the prototype's `RandomMatrix/Gaussian/Basic/*` (43) and `RandomMatrix/Gaussian/Invariance/*`
(15), `RandomMatrix/Gaussian/Moments/SecondMoment.lean` (`ae_ne_zero_mvPolynomial`,
`gaussianMatrix_ae_rank_eq`), `RandomMatrix/Gaussian/Spectral/SketchRank.lean`. Not
reproduced: measure-form statements and `_of_hasLaw` twins (D2); `linForm`, `linFormCLM` (the
flattened vector's dot product); `integrable_gaussianMatrix_iff`, `integral_gaussianMatrix_eq`,
`gaussianMatrix_eq_map_curry` (the `abbrev` and the flattening law); `Fin` index types;
`HasLaw.hasLaw_entry_gaussianReal`, `HasLaw.iIndepFun_entry_of_gaussianMatrix` (P0's general
forms); the polynomial-growth integrability lemmas (`memLp` of every order through the flattening).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. `gaussianMatrix` as rows of `gaussianVector`** (a nested product), an `abbrev`, matching
P2's vectors; flattening is a theorem, not the definition.

**Q2. Frobenius-Lipschitz as an explicit inequality** in §3.4 (no metric on `Matrix`).

## 8. Amendments from the review (2026-10-14)

1. Rule: every typeclass fact about `gaussianMatrix` is an explicit instance in `Basic.lean`
   (`Matrix` is a `def`, so Mathlib's `Measure.pi` instances are not found).
2. "Flatten" is `Function.uncurry`: `hasLaw_uncurry_of_hasLaw_gaussianMatrix`,
   `hasLaw_gaussianMatrix_of_hasLaw_uncurry`, `frobNorm_eq_norm_toLp_uncurry` (the last proved in
   the Matrix layer's `Norms/Frobenius.lean`). A consumer applying a P2/P3 vector result writes the
   variable as `fun ω => Function.uncurry (X ω)`, and `IsIsotropic` of it needs
   `[DecidableEq m] [DecidableEq n]`.
3. Row lemmas dropped (they are `hX.eval i` and `hX.iIndepFun_eval`); column law and column
   independence stated (`hasLaw_col_…`, `iIndepFun_col_…`).
4. One-sided forms `hasLaw_const_mul_…` (`U * X`) and `hasLaw_mul_const_…` (`X * V`), and
   `hasLaw_submatrix_…` on injective maps; the transpose is `hasLaw_conjTranspose_…` with `ᴴ`
   (§5.1). §0's `G x ~ N(0, ‖x‖² I)` is stated for unit `x` (consumers scale).
5. `ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix` (a.s. invertible Gram matrix
   of `A G` when `card n ≤ rank A`), the shape the Nyström consumer uses.
6. The atomless hypothesis is Mathlib's `NullSingletonClass` (`NoAtoms` is deprecated in the
   pinned Mathlib), which `gaussianReal 0 v` has for `v ≠ 0` (`nullSingletonClass_gaussianReal`).
7. Proof routes: the invariance laws by `isGaussian_map` and equality of Gaussian measures by mean
   and covariance (`IsGaussian.ext`), which needs no completion of frames; independence of blocks
   through `HasGaussianLaw.indepFun_of_covariance_…` on the `uncurry`ed blocks.
