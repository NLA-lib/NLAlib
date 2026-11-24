/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.BlockKrylovSum

/-!
# Two block Krylov spaces with Gaussian start blocks

Errors of block Krylov iteration on the sum of two block Krylov spaces,
$\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)$ (`NLAlib.rbkiSum`), for
standard Gaussian test matrices $\mathbf{X}_1$ ($n \times \ell_1$, narrow, run to depth $q_1$)
and $\mathbf{X}_2$ ($n \times \ell_2$, wide, run to depth $q_2$). With
$\ell_1 = 2k + 1$, $\ell_2 = 2(k + j) + 1$, $j + 1 \ge 6k\varepsilon^{-1/3}$,
$q_1 \ge 1 + \log(12k/\varepsilon)/(2\sqrt{2}\,\varepsilon^{1/3})$ and
$q_2 \ge 1 + \log(12/\varepsilon)/3$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
so $O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products with $\mathbf{A}$ or
$\mathbf{A}^{\mathsf{H}}$ give a $(1 + \varepsilon)$ rank-$k$ approximation; the same holds for
the $p$-th power of the Schatten $p$-norm, $1 \le p \le 2$, of the two-sided output. The tail
bounds for $2 \le p < \infty$ are in `NLAlib.LowRank.Gaussian.BlockKrylovSumTail`. This is the
rate of [BakshiClarksonWoodruff2022], for the projection onto the sum of the two Krylov spaces
instead of a selection between two runs, with oversampled blocks, in expectation and with
explicit constants.

The bounds in expectation are stated for $\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})$ at any
measurable test matrix $\mathbf{Y}$ whose sketch contains both block Krylov sketches; no
independence between $\mathbf{X}_1$ and $\mathbf{X}_2$ is used anywhere. The deterministic
content is in `NLAlib.LowRank.Structural.BlockKrylovSum`.

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix`: one
  run, Frobenius norm, per-rank form.
* `NLAlib.integrable_frobNorm_sub_truncatedSVD_rbkiSum_sq`,
  `NLAlib.integrable_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow`: the integrability
  companions of the bounds in expectation.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`: the
  Frobenius error in expectation.
* the Schatten error of the two-sided output in expectation, $1 \le p \le 2$:
  `NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`
  and its general form with `_rsvd_rpow_le_of_range_le_` in place of `_rbkiSum_rpow_le_`.
* the headlines at natural-number sizes,
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`
  and its Schatten twin, and the asymptotic forms, named `exists_forall_` followed by the
  explicit names.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Expectation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n l₁ l₂ : Type*}
  [Fintype l] [Fintype m] [Fintype n] [Fintype l₁] [Fintype l₂] [DecidableEq m]
  [DecidableEq n] {X₁ : Ω → Matrix n l₁ ℝ} {X₂ : Ω → Matrix n l₂ ℝ}

/-! ### One run -/

omit [DecidableEq m] in
/-- **The expected Frobenius error of one truncated run of block Krylov iteration, no gap**: for
a real matrix $\mathbf{A}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries), $k + 2 \le \ell$, $q \ge 1$ blocks and
$0 < \gamma \le 1$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_k
\|_{\mathsf{F}}^2 \le
\Bigl(1 + 4k\,e^{-2\sqrt{2}(q-1)\sqrt{\gamma}}\,\frac{k}{\ell - k - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
k\gamma\,\sigma_k(\mathbf{A})^2\,.$$
No gap in the spectrum is assumed; $\gamma$ is a free parameter. The term
$k\gamma\,\sigma_k^2$ is compared with the optimal error only through
$\sigma_k^2 \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
[MuscoMusco2015, Theorem 12]; there the per-vector guarantee with probability $99/100$, a block
of $k$ columns and unspecified constants, here its sum over the first $k$ singular values, in
expectation, for a block of at least $k + 2$ columns. -/
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {k q : ℕ}
    (hk : k + 2 ≤ Fintype.card l₁) (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X₁ ω) q) k) ^ 2 ∂μ ≤
      (1 + 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1))) * frobNorm (A - truncatedSVD A k) ^ 2 +
        k * γ * singularValues A k ^ 2 := by
  have := hX.isProbabilityMeasure
  obtain ⟨Z, hZ, hAZ, hrk, hRi, hR⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX hk
  set c := 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ)
  have hc : 0 ≤ c := by positivity
  have hY : AEMeasurable (fun ω => blockKrylovMatrix (Aᴴ * A) (X₁ ω) q) μ :=
    (measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable hX.aemeasurable
  have hI : Integrable (fun ω => frobNorm (A - truncatedSVD A k) ^ 2 +
      k * γ * singularValues A k ^ 2 +
      c * frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Zᴴ * X₁ ω)) ^ 2) μ :=
    (integrable_const _).add (hRi.const_mul c)
  simp only [rbki_def]
  refine (integral_mono_ae (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hY k) hI ?_).trans ?_
  · filter_upwards [hrk] with ω hω
    have h := hZ.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul hω hAZ hq hγ hγ1
    rw [rbki_def] at h
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (specNorm_nonneg _)
      (specNorm_le_frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Zᴴ * X₁ ω))) 2) hc
    linarith
  · rw [integral_add (integrable_const _) (hRi.const_mul c), integral_const, probReal_univ,
      one_smul, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left hR hc
    linarith

/-! ### Integrability -/

omit [DecidableEq m] in
/-- The squared Frobenius error
$\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)
\rrbracket_k\|_{\mathsf{F}}^2$ of block Krylov iteration on the sum of two block Krylov spaces
is integrable, for any almost everywhere measurable test matrices and finite measure: the
instance of `NLAlib.integrable_frobNorm_sub_truncatedSVD_rsvd_sq` at the two block Krylov test
matrices side by side. -/
theorem integrable_frobNorm_sub_truncatedSVD_rbkiSum_sq [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    (hX₁ : AEMeasurable X₁ μ) (hX₂ : AEMeasurable X₂ μ) (q₁ q₂ k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2) μ :=
  integrable_frobNorm_sub_truncatedSVD_rsvd_sq A
    ((measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable (hX₁.prodMk hX₂)) k

omit [DecidableEq m] in
/-- The $p$-th power of the Schatten error of the two-sided output of block Krylov iteration on
the sum of two block Krylov spaces is integrable: with
$\mathbf{B} = \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)
\rrbracket_k$ and $\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ the projector onto its row space,
$\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p$ is integrable, for any
almost everywhere measurable test matrices and finite measure: the instance of
`NLAlib.integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow` at the two block Krylov test
matrices side by side. -/
theorem integrable_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (A : Matrix m n ℝ) (hX₁ : AEMeasurable X₁ μ) (hX₂ : AEMeasurable X₂ μ)
    (q₁ q₂ k : ℕ) :
    Integrable (fun ω => schattenNorm p (A - A * rangeProjector
      (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal) μ :=
  integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow p A
    ((measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable (hX₁.prodMk hX₂)) k

/-! ### Frobenius norm, in expectation -/

omit [DecidableEq m] in
/-- **The expected Frobenius error of a sketch containing two Gaussian block Krylov sketches**:
let $\mathbf{A}$ be a real matrix, $\mathbf{X}_1$ and $\mathbf{X}_2$ standard Gaussian
$n \times \ell_1$ and $n \times \ell_2$ test matrices (independent standard normal entries; the
two matrices need not be independent of each other), $k + 2 \le \ell_1$,
$k + j + 2 \le \ell_2$, $q_1, q_2 \ge 1$ and $0 < \gamma \le 1$, and let $\mathbf{Y}$ be an
almost everywhere measurable random test matrix such that, at every sample point, the range of
$\mathbf{A}\mathbf{Y}$ contains the ranges of
$\mathbf{A}\mathbf{K}_{q_1}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_1)$ and of
$\mathbf{A}\mathbf{K}_{q_2}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_2)$. Then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k
\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{2k\gamma}{j + 1} +
4k\,e^{-2\sqrt{2}(q_1-1)\sqrt{\gamma}}\,\frac{k}{\ell_1 - k - 1} +
4e^{-3(q_2-1)}\,\frac{k + j}{\ell_2 - k - j - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
[BakshiClarksonWoodruff2022, Theorem 3.1]; there at $p = 2$ for an algorithm that selects one of
the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants;
here in expectation, for any sketch containing both block Krylov sketches, with oversampled
blocks and explicit constants.
Result: rbki-sum-frobenius-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (Y ω)) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX₁.isProbabilityMeasure
  obtain ⟨Z₁, hZ₁, hAZ₁, hrk₁, hRi₁, hR₁⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX₁ hl₁
  obtain ⟨Z₂, hZ₂, hAZ₂, hrk₂, hRi₂, hR₂⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix
      A hX₂ (k := k + j) hl₂
  set c₁ := 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ)
  set c₂ := 4 * Real.exp (-3 * ((q₂ : ℝ) - 1))
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hI₁ : Integrable (fun ω => (1 + 2 * k * γ / ((j : ℝ) + 1)) *
      frobNorm (A - truncatedSVD A k) ^ 2 +
      c₁ * frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω)) ^ 2) μ :=
    (integrable_const _).add (hRi₁.const_mul c₁)
  have hI : Integrable (fun ω => (1 + 2 * k * γ / ((j : ℝ) + 1)) *
      frobNorm (A - truncatedSVD A k) ^ 2 +
      c₁ * frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω)) ^ 2 +
      c₂ * frobNorm ((A - truncatedSVD A (k + j)) * X₂ ω * pinv (Z₂ᴴ * X₂ ω)) ^ 2) μ :=
    hI₁.add (hRi₂.const_mul c₂)
  refine (integral_mono_ae (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hY k) hI ?_).trans ?_
  · filter_upwards [hrk₁, hrk₂] with ω hω₁ hω₂
    have h := hZ₁.frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le hZ₂ hω₁ hω₂ hAZ₁ hAZ₂ hq₁ hq₂
      hγ hγ1 (h₁ ω) (h₂ ω)
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (specNorm_nonneg _)
      (specNorm_le_frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω))) 2) hc₁
    linarith
  · rw [integral_add hI₁ (hRi₂.const_mul c₂),
      integral_add (integrable_const _) (hRi₁.const_mul c₁), integral_const, probReal_univ,
      one_smul, integral_const_mul, integral_const_mul]
    have hl : (k : ℝ) + j + 2 ≤ Fintype.card l₂ := by exact_mod_cast hl₂
    have hr₂ : 0 ≤ ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1) :=
      div_nonneg (by positivity) (by linarith)
    have hopt : frobNorm (A - truncatedSVD A (k + j)) ^ 2 ≤ frobNorm (A - truncatedSVD A k) ^ 2 :=
      pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_sub_truncatedSVD_le_of_rank_le A
        ((rank_truncatedSVD_le A k).trans (Nat.le_add_right k j))) 2
    have e₁ := mul_le_mul_of_nonneg_left hR₁ hc₁
    have hR₂' : ∫ ω, frobNorm ((A - truncatedSVD A (k + j)) * X₂ ω * pinv (Z₂ᴴ * X₂ ω)) ^ 2 ∂μ ≤
        ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1) *
          frobNorm (A - truncatedSVD A (k + j)) ^ 2 :=
      hR₂.trans_eq (by push_cast; ring)
    have e₂ := mul_le_mul_of_nonneg_left hR₂' hc₂
    have e₃ := mul_le_mul_of_nonneg_left hopt (mul_nonneg hc₂ hr₂)
    linarith

omit [DecidableEq m] in
/-- **The expected Frobenius error of block Krylov iteration on the sum of two Gaussian block
Krylov spaces**: let $\mathbf{A}$ be a real matrix, $\mathbf{X}_1$ and $\mathbf{X}_2$ standard
Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices (independent standard normal
entries; the two matrices need not be independent of each other), $k + 2 \le \ell_1$,
$k + j + 2 \le \ell_2$, $q_1, q_2 \ge 1$ and $0 < \gamma \le 1$. Then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{2k\gamma}{j + 1} +
4k\,e^{-2\sqrt{2}(q_1-1)\sqrt{\gamma}}\,\frac{k}{\ell_1 - k - 1} +
4e^{-3(q_2-1)}\,\frac{k + j}{\ell_2 - k - j - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The instance of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix` at
the two block Krylov test matrices side by side. Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there at $p = 2$ for an algorithm that selects one of
the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants;
here in expectation, for the projection onto the sum of the two spaces, with oversampled blocks
and explicit constants.
Result: rbki-sum-frobenius-error -/
theorem integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hY := (measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable
    (hX₁.aemeasurable.prodMk hX₂.aemeasurable)
  simp only [rbkiSum_def]
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix A hX₁
    hX₂ hl₁ hl₂ hq₁ hq₂ hγ hγ1 hY
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_left A (X₁ ω) (X₂ ω) q₁ q₂)
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_right A (X₁ ω) (X₂ ω) q₁ q₂)

/-! ### Schatten norms, $1 \le p \le 2$, in expectation -/

omit [DecidableEq m] in
/-- **The expected Schatten error of a sketch containing two Gaussian block Krylov sketches,
$1 \le p \le 2$, two-sided output**: let $\mathbf{A}$ be a real matrix, $\mathbf{X}_1$ and
$\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices
(independent standard normal entries; the two matrices need not be independent of each other),
$k + 2 \le \ell_1$, $k + j + 2 \le \ell_2$, $q_1, q_2 \ge 1$ and $0 < \gamma \le 1$, and let
$\mathbf{Y}$ be an almost everywhere measurable random test matrix such that, at every sample
point, the range of $\mathbf{A}\mathbf{Y}$ contains the ranges of
$\mathbf{A}\mathbf{K}_{q_1}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_1)$ and of
$\mathbf{A}\mathbf{K}_{q_2}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_2)$. Write
$\mathbf{B} = \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k$ and
$\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ for the projector onto its row space. Then
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
\Bigl(1 + \frac{2k\gamma}{j + 1} +
4k\,e^{-2\sqrt{2}(q_1-1)\sqrt{\gamma}}\,\frac{k}{\ell_1 - k - 1} +
4e^{-3(q_2-1)}\,\frac{k + j}{\ell_2 - k - j - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here in
expectation of the $p$-th power, for $1 \le p \le 2$ and any sketch containing both block Krylov
sketches, with oversampled blocks and explicit constants.
Result: rbki-sum-schatten-error -/
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rsvd A (Y ω)) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have := hX₁.isProbabilityMeasure
  obtain ⟨Z₁, hZ₁, hAZ₁, hrk₁, hRi₁, hR₁⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX₁ hl₁
  obtain ⟨Z₂, hZ₂, hAZ₂, hrk₂, hRi₂, hR₂⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix
      A hX₂ (k := k + j) hl₂
  set c₁ := 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ)
  set c₂ := 4 * Real.exp (-3 * ((q₂ : ℝ) - 1))
  set s := singularValues A k ^ (p.toReal - 2)
  set S := schattenNorm p (A - truncatedSVD A k) ^ p.toReal
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hs : 0 ≤ s := Real.rpow_nonneg (singularValues_nonneg A k) _
  have hI₁ : Integrable (fun ω => (1 + 2 * k * γ / ((j : ℝ) + 1)) * S +
      s * c₁ * frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω)) ^ 2) μ :=
    (integrable_const _).add (hRi₁.const_mul (s * c₁))
  have hI : Integrable (fun ω => (1 + 2 * k * γ / ((j : ℝ) + 1)) * S +
      s * c₁ * frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω)) ^ 2 +
      s * c₂ * frobNorm ((A - truncatedSVD A (k + j)) * X₂ ω * pinv (Z₂ᴴ * X₂ ω)) ^ 2) μ :=
    hI₁.add (hRi₂.const_mul (s * c₂))
  refine (integral_mono_ae
    (integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow p A hY k) hI ?_).trans ?_
  · filter_upwards [hrk₁, hrk₂] with ω hω₁ hω₂
    have h := hZ₁.schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le hp1 hp2 hZ₂ hω₁
      hω₂ hAZ₁ hAZ₂ hq₁ hq₂ hγ hγ1 (h₁ ω) (h₂ ω)
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (specNorm_nonneg _)
      (specNorm_le_frobNorm ((A - truncatedSVD A k) * X₁ ω * pinv (Z₁ᴴ * X₁ ω))) 2)
      (mul_nonneg hs hc₁)
    linarith
  · rw [integral_add hI₁ (hRi₂.const_mul (s * c₂)),
      integral_add (integrable_const _) (hRi₁.const_mul (s * c₁)), integral_const, probReal_univ,
      one_smul, integral_const_mul, integral_const_mul]
    have hl : (k : ℝ) + j + 2 ≤ Fintype.card l₂ := by exact_mod_cast hl₂
    have hl' : (k : ℝ) + 2 ≤ Fintype.card l₁ := by exact_mod_cast hl₁
    have hr₁ : 0 ≤ (k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1) :=
      div_nonneg (by positivity) (by linarith)
    have hr₂ : 0 ≤ ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1) :=
      div_nonneg (by positivity) (by linarith)
    have hopt : frobNorm (A - truncatedSVD A (k + j)) ^ 2 ≤ frobNorm (A - truncatedSVD A k) ^ 2 :=
      pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_sub_truncatedSVD_le_of_rank_le A
        ((rank_truncatedSVD_le A k).trans (Nat.le_add_right k j))) 2
    have hSV : s * frobNorm (A - truncatedSVD A k) ^ 2 ≤ S :=
      singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le hp1 hp2 A k
    have e₁ := mul_le_mul_of_nonneg_left hR₁ (mul_nonneg hs hc₁)
    have hR₂' : ∫ ω, frobNorm ((A - truncatedSVD A (k + j)) * X₂ ω * pinv (Z₂ᴴ * X₂ ω)) ^ 2 ∂μ ≤
        ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1) *
          frobNorm (A - truncatedSVD A (k + j)) ^ 2 :=
      hR₂.trans_eq (by push_cast; ring)
    have e₂ := mul_le_mul_of_nonneg_left hR₂' (mul_nonneg hs hc₂)
    have e₃ := mul_le_mul_of_nonneg_left hopt (mul_nonneg (mul_nonneg hs hc₂) hr₂)
    have e₄ := mul_le_mul_of_nonneg_left hSV (mul_nonneg hc₁ hr₁)
    have e₅ := mul_le_mul_of_nonneg_left hSV (mul_nonneg hc₂ hr₂)
    linarith

-- A declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
omit [DecidableEq m] in
/-- **The expected Schatten error of block Krylov iteration on the sum of two Gaussian block
Krylov spaces, $1 \le p \le 2$, two-sided output**: let $\mathbf{A}$ be a real matrix,
$\mathbf{X}_1$ and $\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test
matrices (independent standard normal entries; the two matrices need not be independent of each
other), $k + 2 \le \ell_1$, $k + j + 2 \le \ell_2$, $q_1, q_2 \ge 1$ and $0 < \gamma \le 1$.
Write $\mathbf{B} = \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1,
q_2)\rrbracket_k$ and $\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ for the projector onto its row
space. Then
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
\Bigl(1 + \frac{2k\gamma}{j + 1} +
4k\,e^{-2\sqrt{2}(q_1-1)\sqrt{\gamma}}\,\frac{k}{\ell_1 - k - 1} +
4e^{-3(q_2-1)}\,\frac{k + j}{\ell_2 - k - j - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here in
expectation of the $p$-th power, for $1 \le p \le 2$ and the projection onto the sum of the two
spaces, with oversampled blocks and explicit constants.
Result: rbki-sum-schatten-error -/
theorem integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have hY := (measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable
    (hX₁.aemeasurable.prodMk hX₂.aemeasurable)
  simp only [rbkiSum_def]
  exact
    integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    hp1 hp2 A hX₁ hX₂ hl₁ hl₂ hq₁ hq₂ hγ hγ1 hY
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_left A (X₁ ω) (X₂ ω) q₁ q₂)
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_right A (X₁ ω) (X₂ ω) q₁ q₂)

/-- The scalar bookkeeping of the headlines: under their thresholds on $j$, $q_1$ and $q_2$,
both depths are at least $1$ and, at $\gamma = \varepsilon^{2/3}$, the factor of the general
bounds is at most $1 + \varepsilon$, each of its three error terms being at most
$\varepsilon/3$. -/
private theorem one_le_and_one_le_and_factor_le_one_add {k j q₁ q₂ c₁ c₂ : ℕ} (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₁ : 2 * k + 1 ≤ c₁) (hc₂ : 2 * (k + j) + 1 ≤ c₂)
    (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
    1 ≤ q₁ ∧ 1 ≤ q₂ ∧ 1 + 2 * k * (ε ^ (3 : ℝ)⁻¹) ^ 2 / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt ((ε ^ (3 : ℝ)⁻¹) ^ 2)) *
          ((k : ℝ) / ((c₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) * (((k : ℝ) + j) / ((c₂ : ℝ) - k - j - 1)) ≤
      1 + ε := by
  set t := ε ^ (3 : ℝ)⁻¹ with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hε _
  have ht1 : t ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have ht3 : t ^ 3 = ε := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL₁ : (1 : ℝ) ≤ 12 * k / ε := (one_le_div hε).2 (by linarith)
  have hL₂ : (1 : ℝ) ≤ 12 / ε := (one_le_div hε).2 (by linarith)
  have hq₁' : 1 ≤ q₁ := by
    have : 0 ≤ Real.log (12 * k / ε) / (2 * Real.sqrt 2 * t) :=
      div_nonneg (Real.log_nonneg hL₁) (by positivity)
    exact_mod_cast (show (1 : ℝ) ≤ q₁ by linarith)
  have hq₂' : 1 ≤ q₂ := by
    have : 0 ≤ Real.log (12 / ε) / 3 := div_nonneg (Real.log_nonneg hL₂) (by norm_num)
    exact_mod_cast (show (1 : ℝ) ≤ q₂ by linarith)
  refine ⟨hq₁', hq₂', ?_⟩
  rw [Real.sqrt_sq ht0.le]
  have hj0 : (0 : ℝ) < j + 1 := by positivity
  -- the first term: `2kγ/(j + 1) ≤ ε/3`
  have e₁ : 2 * k * t ^ 2 / ((j : ℝ) + 1) ≤ ε / 3 := by
    rw [div_le_iff₀ hj0]
    have : 6 * k ≤ ((j : ℝ) + 1) * t := (div_le_iff₀ ht0).1 hj
    nlinarith [sq_nonneg t]
  -- the second term: `e^{-2√2 (q₁-1) √γ} ≤ ε/(12k)`
  have e₂ : Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t) ≤ ε / (12 * k) := by
    have hlog : Real.log (12 * k / ε) ≤ 2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2 * t)).1
        (by linarith : Real.log (12 * k / ε) / (2 * Real.sqrt 2 * t) ≤ (q₁ : ℝ) - 1)
      linarith
    calc Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t)
        ≤ Real.exp (-Real.log (12 * k / ε)) := Real.exp_le_exp.2 (by linarith)
      _ = ε / (12 * k) := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  -- the third term: `e^{-3(q₂-1)} ≤ ε/12`
  have e₃ : Real.exp (-3 * ((q₂ : ℝ) - 1)) ≤ ε / 12 := by
    calc Real.exp (-3 * ((q₂ : ℝ) - 1))
        ≤ Real.exp (-Real.log (12 / ε)) := Real.exp_le_exp.2 (by linarith)
      _ = ε / 12 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hr₁ : (k : ℝ) / ((c₁ : ℝ) - k - 1) ≤ 1 := by
    have : (2 * k + 1 : ℝ) ≤ c₁ := by exact_mod_cast hc₁
    rw [div_le_one (by linarith)]
    linarith
  have hr₂ : ((k : ℝ) + j) / ((c₂ : ℝ) - k - j - 1) ≤ 1 := by
    have : (2 * ((k : ℝ) + j) + 1) ≤ c₂ := by exact_mod_cast hc₂
    rw [div_le_one (by linarith)]
    linarith
  have e₂' : 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t) ≤ ε / 3 := by
    calc 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t)
        ≤ 4 * k * (ε / (12 * k)) := by gcongr
      _ = ε / 3 := by field_simp; ring
  have e₄ := mul_le_mul_of_nonneg_left hr₁
    (by positivity : 0 ≤ 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * t))
  have e₅ := mul_le_mul_of_nonneg_left hr₂
    (by positivity : 0 ≤ 4 * Real.exp (-3 * ((q₂ : ℝ) - 1)))
  linarith

omit [DecidableEq m] in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Frobenius norm, any block sizes**: let $\mathbf{A}$ be a real matrix, $\mathbf{X}_1$ and
$\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices
(independent standard normal entries; the two matrices need not be independent of each other),
$k \ge 1$, $0 < \varepsilon \le 1$, $\ell_1 \ge 2k + 1$ and $\ell_2 \ge 2(k + j) + 1$. If
$j + 1 \ge 6k/\varepsilon^{1/3}$,
$q_1 \ge 1 + \log(12k/\varepsilon)/(2\sqrt{2}\,\varepsilon^{1/3})$ and
$q_2 \ge 1 + \log(12/\varepsilon)/3$, then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
At $\gamma = \varepsilon^{2/3}$ the three error terms of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix` are each at
most $\varepsilon/3$. The headline at the smallest block sizes is
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there at $p = 2$ for an algorithm that selects one of
the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants;
here in expectation, for the projection onto the sum of the two spaces, with blocks of at least
$2k + 1$ and $2(k + j) + 1$ columns and explicit constants.
Result: rbki-sum-frobenius-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl₁ : 2 * k + 1 ≤ Fintype.card l₁)
    (hl₂ : 2 * (k + j) + 1 ≤ Fintype.card l₂) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  obtain ⟨hq₁', hq₂', hf⟩ := one_le_and_one_le_and_factor_le_one_add hk hε hε1 hl₁ hl₂ hj hq₁ hq₂
  have ht0 : 0 < ε ^ (3 : ℝ)⁻¹ := Real.rpow_pos_of_pos hε _
  exact (integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix A hX₁ hX₂
    (k := k) (j := j) (by omega) (by omega) hq₁' hq₂' (γ := (ε ^ (3 : ℝ)⁻¹) ^ 2) (by positivity)
    (pow_le_one₀ ht0.le (Real.rpow_le_one hε.le hε1 (by norm_num)))).trans
    (mul_le_mul_of_nonneg_right hf (sq_nonneg _))

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
omit [DecidableEq m] in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Schatten norms with $1 \le p \le 2$, any block sizes**: let $1 \le p \le 2$, let $\mathbf{A}$
be a real matrix, $\mathbf{X}_1$ and $\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and
$n \times \ell_2$ test matrices (independent standard normal entries; the two matrices need not
be independent of each other), $k \ge 1$, $0 < \varepsilon \le 1$, $\ell_1 \ge 2k + 1$ and
$\ell_2 \ge 2(k + j) + 1$. Write $\mathbf{B} = \llbracket\mathsf{rbkiSum}(\mathbf{A},
\mathbf{X}_1, \mathbf{X}_2, q_1, q_2)\rrbracket_k$ and $\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$
for the projector onto its row space. If $j + 1 \ge 6k/\varepsilon^{1/3}$,
$q_1 \ge 1 + \log(12k/\varepsilon)/(2\sqrt{2}\,\varepsilon^{1/3})$ and
$q_2 \ge 1 + \log(12/\varepsilon)/3$, then
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
At $\gamma = \varepsilon^{2/3}$ the three error terms of
`NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`
are each at most $\varepsilon/3$. The headline at the smallest block sizes is
`NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here in
expectation of the $p$-th power, for $1 \le p \le 2$ and the projection onto the sum of the two
spaces, with blocks of at least $2k + 1$ and $2(k + j) + 1$ columns and explicit constants.
Result: rbki-sum-schatten-error -/
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl₁ : 2 * k + 1 ≤ Fintype.card l₁)
    (hl₂ : 2 * (k + j) + 1 ≤ Fintype.card l₂) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  obtain ⟨hq₁', hq₂', hf⟩ := one_le_and_one_le_and_factor_le_one_add hk hε hε1 hl₁ hl₂ hj hq₁ hq₂
  have ht0 : 0 < ε ^ (3 : ℝ)⁻¹ := Real.rpow_pos_of_pos hε _
  exact (integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix hp1
    hp2 A hX₁ hX₂ (k := k) (j := j) (by omega) (by omega) hq₁' hq₂' (γ := (ε ^ (3 : ℝ)⁻¹) ^ 2)
    (by positivity) (pow_le_one₀ ht0.le (Real.rpow_le_one hε.le hε1 (by norm_num)))).trans
    (mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg (schattenNorm_nonneg _ _) _))

end Expectation

/-! ### Headlines at natural-number sizes -/

/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Frobenius norm.** Let $\mathbf{A}$ be a real $m \times n$ matrix, $\mathbf{X}_1$ a standard
Gaussian $n \times (2k + 1)$ test matrix and $\mathbf{X}_2$ a standard Gaussian
$n \times (2(k + j) + 1)$ test matrix (each with independent standard normal entries; the two
need not be independent of each other), $k \ge 1$ and $0 < \varepsilon \le 1$. If
$j + 1 \ge C_1 k/\varepsilon^{1/3}$,
$q_1 \ge 1 + \log(C_2 k/\varepsilon)/(c_1\varepsilon^{1/3})$ and
$q_2 \ge 1 + \log(C_2/\varepsilon)/c_2$, then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Here $C_1 = 6$, $C_2 = 12$, $c_1 = 2\sqrt{2}$ and $c_2 = 3$.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there at $p = 2$ for an algorithm that selects one of
the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants;
here in expectation, for the projection onto the sum of the two spaces, with oversampled blocks
and explicit constants.

Note: the three error terms of the general bound are each at most $\varepsilon/3$, at
$\gamma = \varepsilon^{2/3}$. General form:
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`; the
$O(\cdot)$ reading is
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`.
At the smallest admissible $j$, $q_1$ and $q_2$ the two runs use
$O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products with $\mathbf{A}$ or
$\mathbf{A}^{\mathsf{H}}$.
Result: rbki-sum-frobenius-error -/
theorem integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n k j q₁ q₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 :=
  integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    A hX₁ hX₂ hk hε hε1 (by simp) (by simp) hj hq₁ hq₂

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Schatten norms with $1 \le p \le 2$.** Let $1 \le p \le 2$, let $\mathbf{A}$ be a real
$m \times n$ matrix, $\mathbf{X}_1$ a standard Gaussian $n \times (2k + 1)$ test matrix and
$\mathbf{X}_2$ a standard Gaussian $n \times (2(k + j) + 1)$ test matrix (each with independent
standard normal entries; the two need not be independent of each other), $k \ge 1$ and
$0 < \varepsilon \le 1$. Write $\mathbf{B} = \llbracket\mathsf{rbkiSum}(\mathbf{A},
\mathbf{X}_1, \mathbf{X}_2, q_1, q_2)\rrbracket_k$ and $\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$
for the projector onto its row space. If $j + 1 \ge C_1 k/\varepsilon^{1/3}$,
$q_1 \ge 1 + \log(C_2 k/\varepsilon)/(c_1\varepsilon^{1/3})$ and
$q_2 \ge 1 + \log(C_2/\varepsilon)/c_2$, then
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
Here $C_1 = 6$, $C_2 = 12$, $c_1 = 2\sqrt{2}$ and $c_2 = 3$.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here in
expectation of the $p$-th power, for $1 \le p \le 2$ and the projection onto the sum of the two
spaces, with oversampled blocks and explicit constants.

Note: the output $\mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ has rank at most $k$; for
$p < 2$ the bound is for this two-sided output, not for $\mathbf{B}$. General form:
`NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`;
the $O(\cdot)$ reading is
`NLAlib.exists_forall_integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`.
Result: rbki-sum-schatten-error -/
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n k j q₁ q₂ : ℕ} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix (Fin m) (Fin n) ℝ) {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal :=
  integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    hp1 hp2 A hX₁ hX₂ hk hε hε1 (by simp) (by simp) hj hq₁ hq₂

/-! ### Asymptotic forms -/

/-- The scalar bookkeeping of the asymptotic forms: for $k \ge 1$,
$0 < \varepsilon \le e^{-1}$, $\ell_2 \ge 14k/\varepsilon^{1/3}$,
$q_1 \ge 14\log(k/\varepsilon)/\varepsilon^{1/3}$ and $q_2 \ge 14\log(1/\varepsilon)$, the
block $j = \lfloor(\ell_2 - 1)/2\rfloor - k$ and the depths meet the thresholds of the
headlines. -/
private theorem le_one_and_exists_thresholds {k q₁ q₂ c : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε)
    (hε₀ : ε ≤ Real.exp (-1)) (hc : 14 * (k / ε ^ (3 : ℝ)⁻¹) ≤ (c : ℝ))
    (hq₁ : 14 * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁) (hq₂ : 14 * Real.log (1 / ε) ≤ q₂) :
    ε ≤ 1 ∧ ∃ j : ℕ, 2 * (k + j) + 1 ≤ c ∧ 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1 ∧
      1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁ ∧
      1 + Real.log (12 / ε) / 3 ≤ q₂ := by
  set t := ε ^ (3 : ℝ)⁻¹
  have hε1 : ε ≤ 1 := hε₀.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have ht0 : 0 < t := Real.rpow_pos_of_pos hε _
  have ht1 : t ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- `M = log(1/ε) ≥ 1` and `L = log(k/ε) ≥ M`
  have hM : 1 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, le_neg]
    exact (Real.log_le_log hε hε₀).trans_eq (Real.log_exp _)
  have hL : Real.log (1 / ε) ≤ Real.log (k / ε) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hkR hε.le)
  have hlog12 : Real.log 12 ≤ 11 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hLt : Real.log (k / ε) ≤ Real.log (k / ε) / t := le_div_self (by linarith) ht0 ht1
  -- the wide block: `j = ⌊(ℓ₂ - 1)/2⌋ - k`
  have hkt : (k : ℝ) ≤ k / t := le_div_self (by linarith) ht0 ht1
  have hc' : 14 * k ≤ c := by exact_mod_cast (show (14 : ℝ) * k ≤ c by linarith)
  set j := (c - 1) / 2 - k
  have hjc : c ≤ 2 * j + 2 * k + 2 := by omega
  have hjcR : (c : ℝ) ≤ 2 * j + 2 * k + 2 := by exact_mod_cast hjc
  refine ⟨hε1, j, by omega, ?_, ?_, ?_⟩
  · rw [mul_div_assoc]
    linarith
  · have h12 : Real.log (12 * k / ε) = Real.log 12 + Real.log (k / ε) := by
      rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
    have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
      simp
    have h := div_le_div₀ (by linarith) (show Real.log (12 * k / ε) ≤ 12 * Real.log (k / ε) by
      rw [h12]; linarith) (by positivity : (0 : ℝ) < 2 * t)
      (by nlinarith : 2 * t ≤ 2 * Real.sqrt 2 * t)
    have h6 : 12 * Real.log (k / ε) / (2 * t) = 6 * (Real.log (k / ε) / t) := by
      field_simp; ring
    linarith
  · have h12 : Real.log (12 / ε) = Real.log 12 + Real.log (1 / ε) := by
      rw [← Real.log_mul (by norm_num) (by positivity), mul_one_div]
    linarith

/-- **$O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products suffice for a $(1 + \varepsilon)$
rank-$k$ approximation in the Frobenius norm**: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a real matrix $\mathbf{A}$, standard Gaussian
$n \times \ell_1$ and $n \times \ell_2$ test matrices $\mathbf{X}_1$ and $\mathbf{X}_2$
(independent standard normal entries; the two matrices need not be independent of each other),
$k \ge 1$, $0 < \varepsilon \le \varepsilon_0$, blocks $\ell_1 \ge 2k + 1$ and
$\ell_2 \ge Ck/\varepsilon^{1/3}$, and depths
$q_1 \ge C\log(k/\varepsilon)/\varepsilon^{1/3}$ and $q_2 \ge C\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
With $\ell_1 = O(k)$ and $\ell_2 = O(k\varepsilon^{-1/3})$ the two runs use
$O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products with $\mathbf{A}$ or
$\mathbf{A}^{\mathsf{H}}$. The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 1.1]; there with $\log(d/\varepsilon)$ in place of
$\log(k/\varepsilon)$, probability $99/100$ and an algorithm that selects one of two runs; here
in expectation, for the projection onto the sum of the two spaces.
Asymptotic: NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix
Result: rbki-sum-frobenius-error -/
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 0 < k → 0 < ε →
      ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ → C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (1 / ε) ≤ q₂ →
      ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨14, Real.exp (-1), by norm_num, Real.exp_pos _, ?_⟩
  intro Ω m n l₁ l₂ _ _ _ _ _ _ μ A X₁ X₂ k q₁ q₂ ε hX₁ hX₂ hk hε hε₀ hl₁ hl₂ hq₁ hq₂
  obtain ⟨hε1, j, hj₂, hj, hq₁', hq₂'⟩ := le_one_and_exists_thresholds hk hε hε₀ hl₂ hq₁ hq₂
  exact
    integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    A hX₁ hX₂ hk hε hε1 hl₁ hj₂ hj hq₁' hq₂'

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products suffice for a $(1 + \varepsilon)$
rank-$k$ approximation in Schatten norms with $1 \le p \le 2$**: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a real matrix $\mathbf{A}$, standard Gaussian
$n \times \ell_1$ and $n \times \ell_2$ test matrices $\mathbf{X}_1$ and $\mathbf{X}_2$
(independent standard normal entries; the two matrices need not be independent of each other),
$1 \le p \le 2$, $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$, blocks $\ell_1 \ge 2k + 1$ and
$\ell_2 \ge Ck/\varepsilon^{1/3}$, and depths
$q_1 \ge C\log(k/\varepsilon)/\varepsilon^{1/3}$ and $q_2 \ge C\log(1/\varepsilon)$, with
$\mathbf{B} = \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1,
q_2)\rrbracket_k$ and $\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ the projector onto its row space,
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
The constants do not depend on $p$. The asymptotic form of
`NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 1.1]; there with $\log(d/\varepsilon)$ in place of
$\log(k/\varepsilon)$, probability $99/100$ and an algorithm that selects one of two runs; here
in expectation of the $p$-th power, for the projection onto the sum of the two spaces.
Asymptotic:
NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix
Result: rbki-sum-schatten-error -/
theorem
    exists_forall_integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ)
      (p : ℝ≥0∞),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 1 ≤ p → p ≤ 2 →
      0 < k → 0 < ε → ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ →
      C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (1 / ε) ≤ q₂ →
      ∫ ω, schattenNorm p (A - A * rangeProjector
          (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  refine ⟨14, Real.exp (-1), by norm_num, Real.exp_pos _, ?_⟩
  intro Ω m n l₁ l₂ _ _ _ _ _ _ _ μ A X₁ X₂ k q₁ q₂ ε p hX₁ hX₂ hp1 hp2 hk hε hε₀ hl₁ hl₂ hq₁ hq₂
  obtain ⟨hε1, j, hj₂, hj, hq₁', hq₂'⟩ := le_one_and_exists_thresholds hk hε hε₀ hl₂ hq₁ hq₂
  exact
    integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_le_card_of_hasLaw_gaussianMatrix
    hp1 hp2 A hX₁ hX₂ hk hε hε1 hl₁ hj₂ hj hq₁' hq₂'

end NLAlib
