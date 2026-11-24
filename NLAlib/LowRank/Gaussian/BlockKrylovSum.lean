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
the $p$-th power of the Schatten $p$-norm, $1 \le p \le 2$, of the two-sided output, and a tail
bound holds for $2 \le p < \infty$. This is the rate of [BakshiClarksonWoodruff2022], for the
projection onto the sum of the two Krylov spaces instead of a selection between two runs, with
oversampled blocks, in expectation and with explicit constants.

The bounds in expectation are stated for $\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})$ at any
measurable test matrix $\mathbf{Y}$ whose sketch contains both block Krylov sketches; no
independence between $\mathbf{X}_1$ and $\mathbf{X}_2$ is used anywhere. The deterministic
content is in `NLAlib.LowRank.Structural.BlockKrylovSum`.

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix`: one
  run, Frobenius norm, per-rank form.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix`: the
  Frobenius error in expectation.
* the Schatten error of the two-sided output in expectation, $1 \le p \le 2$:
  `NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`
  and its general form with `_rsvd_rpow_le_of_range_le_` in place of `_rbkiSum_rpow_le_`.
* `NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`: the
  tail bound for $2 \le p < \infty$, one-sided output.
* the same tail bound for the two-sided output, named with `_sub_mul_rangeProjector_rbkiSum_gt_le_`
  in place of `_sub_truncatedSVD_rbkiSum_gt_le_`.
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
/-- A Gaussian block against a frame of top right singular vectors: for $k + 2 \le \ell$ there
is a frame $\mathbf{Z}$ of $\min(k, \lvert n \rvert)$ orthonormal columns with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$, almost
surely $\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
and the sketch residual
$(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{X}(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$
is square integrable with
$\mathbb{E}\|\cdot\|_{\mathsf{F}}^2 \le (k/(\ell - k - 1))
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$. -/
private theorem exists_frame_residual (A : Matrix m n ℝ) {X : Ω → Matrix n l ℝ}
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∃ Z : Matrix n (Fin (min k (Fintype.card n))) ℝ, HasOrthonormalCols Z ∧
      A * Z * Zᴴ = truncatedSVD A k ∧ (∀ᵐ ω ∂μ, ((X ω)ᴴ * Z).rank = Z.rank) ∧
      Integrable (fun ω => frobNorm ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)) ^ 2) μ ∧
      ∫ ω, frobNorm ((A - truncatedSVD A k) * X ω * pinv (Zᴴ * X ω)) ^ 2 ∂μ ≤
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  obtain ⟨Z, -, hZ, -, -, -, -, -, hpre⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A
      (min_le_right k (Fintype.card n))
  have hT : truncatedSVD A (min k (Fintype.card n)) = truncatedSVD A k := by
    rcases le_total k (Fintype.card n) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, truncatedSVD_of_rank_le A A.rank_le_card_width,
        truncatedSVD_of_rank_le A (A.rank_le_card_width.trans h)]
  have hAZ : A * Z * Zᴴ = truncatedSVD A k := by
    have h := hpre _ le_rfl
    rw [Fin.castLE_rfl, Matrix.submatrix_id_id] at h
    rw [h, hT]
  have hs : Fintype.card (Fin (min k (Fintype.card n))) + 2 ≤ Fintype.card l := by
    rw [Fintype.card_fin]
    omega
  have hE : A - truncatedSVD A k = A - A * Z * Zᴴ := by rw [hAZ]
  refine ⟨Z, hZ, hAZ, ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
      (by rw [hZ.rank_eq, Fintype.card_fin]; omega), ?_, ?_⟩
  · rw [hE]
    exact integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix A hX hZ hs
  · rw [hE, integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix A hX hZ hs,
      Fintype.card_fin, mul_div_assoc, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hkl : (k : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hk
    have htk : ((min k (Fintype.card n) : ℕ) : ℝ) ≤ k := Nat.cast_le.mpr (min_le_left _ _)
    exact div_le_div₀ (Nat.cast_nonneg _) htk (by linarith) (by linarith)

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
  obtain ⟨Z, hZ, hAZ, hrk, hRi, hR⟩ := exists_frame_residual A hX hk
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
  obtain ⟨Z₁, hZ₁, hAZ₁, hrk₁, hRi₁, hR₁⟩ := exists_frame_residual A hX₁ hl₁
  obtain ⟨Z₂, hZ₂, hAZ₂, hrk₂, hRi₂, hR₂⟩ := exists_frame_residual A hX₂ (k := k + j) hl₂
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
        frobNorm (A - truncatedSVD A k) ^ 2 := sorry

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
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

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
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

/-! ### Schatten norms, $2 \le p < \infty$, tail form -/

-- A declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
omit [DecidableEq m] in
/-- **The tail bound for block Krylov iteration on the sum of two Gaussian block Krylov spaces,
$2 \le p < \infty$**: let $\mathbf{A}$ be a real $m \times n$ matrix, $N = \min(m, n)$,
$\mathbf{X}_1$ and $\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test
matrices (independent standard normal entries; the two matrices need not be independent of each
other), $k \ge 1$, $k + 2 \le \ell_1$, $k + j + 2 \le \ell_2$, $0 < \varepsilon \le 1$ and
$\delta > 0$. If $j + 1 \ge e^2 k/(\varepsilon p)^{1/3}$,
$$q_1 \ge 1 + \Bigl(\frac{p^{1/6}}{2\varepsilon^{1/3}} + \frac{\sqrt{4p + 1}}{8}\Bigr)
\log\frac{256\,k^3 (p + 1) N}{\varepsilon^2\delta}
\qquad\text{and}\qquad
q_2 \ge 1 + \frac{\sqrt{4p + 1}}{8}\,
\log\frac{256\,k^2 (k + j)(p + 1) N}{\varepsilon^2\delta}\,,$$
then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1,
\mathbf{X}_2, q_1, q_2)\rrbracket_k\|_{S_p} >
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\Bigr] \le \delta\,.$$
The dimension $N$ enters because for $p > 2$ the Frobenius norm of the residuals is not
controlled by the optimal Schatten error. The two-sided output has the same bound:
`NLAlib.measureReal_schattenNorm_sub_mul_rangeProjector_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here
for $2 \le p < \infty$ and the projection onto the sum of the two spaces, a tail bound for every
$\delta$ with oversampled blocks and explicit constants.
Result: rbki-sum-schatten-tail -/
theorem measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
      Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₁)
    (hq₂ : 1 + Real.sqrt (4 * p.toReal + 1) / 8 *
      Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
      schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := sorry

omit [DecidableEq m] in
/-- **The tail bound for the two-sided output of block Krylov iteration on the sum of two
Gaussian block Krylov spaces, $2 \le p < \infty$**: let $\mathbf{A}$ be a real $m \times n$
matrix, $N = \min(m, n)$, $\mathbf{X}_1$ and $\mathbf{X}_2$ standard Gaussian $n \times \ell_1$
and $n \times \ell_2$ test matrices (independent standard normal entries; the two matrices need
not be independent of each other), $k \ge 1$, $k + 2 \le \ell_1$, $k + j + 2 \le \ell_2$,
$0 < \varepsilon \le 1$ and $\delta > 0$. Write $\mathbf{B} =
\llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)\rrbracket_k$ and
$\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ for the projector onto its row space. If
$j + 1 \ge e^2 k/(\varepsilon p)^{1/3}$,
$$q_1 \ge 1 + \Bigl(\frac{p^{1/6}}{2\varepsilon^{1/3}} + \frac{\sqrt{4p + 1}}{8}\Bigr)
\log\frac{256\,k^3 (p + 1) N}{\varepsilon^2\delta}
\qquad\text{and}\qquad
q_2 \ge 1 + \frac{\sqrt{4p + 1}}{8}\,
\log\frac{256\,k^2 (k + j)(p + 1) N}{\varepsilon^2\delta}\,,$$
then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p} >
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\Bigr] \le \delta\,.$$
The two-sided error is at most the one-sided error
(`IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul`), so this follows from
`NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 3.1]; the output $\mathbf{A}(\mathbf{I} -
\mathbf{Z}\mathbf{Z}^{\mathsf{T}})$ of the theorem there, for an algorithm that selects one of
the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants;
here for $2 \le p < \infty$ and the projection onto the sum of the two spaces, a tail bound for
every $\delta$ with oversampled blocks and explicit constants.
Result: rbki-sum-schatten-tail -/
theorem measureReal_schattenNorm_sub_mul_rangeProjector_rbkiSum_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
      Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₁)
    (hq₂ : 1 + Real.sqrt (4 * p.toReal + 1) / 8 *
      Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
      schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ)} ≤ δ := sorry

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
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

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
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

/-! ### Asymptotic forms -/

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
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

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
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

/-- **$O(k(p^{1/6}\varepsilon^{-1/3} + \sqrt{p})\log(\ell_2 p\lvert n \rvert/
(\varepsilon\delta)))$ products suffice for a $(1 + \varepsilon)$ rank-$k$ approximation in
Schatten norms with $2 \le p < \infty$**: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a real matrix $\mathbf{A}$ with columns indexed by $n$,
standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices $\mathbf{X}_1$ and
$\mathbf{X}_2$ (independent standard normal entries; the two matrices need not be independent
of each other), $2 \le p < \infty$, $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$,
$\delta > 0$, blocks $\ell_1 \ge k + 2$ and $\ell_2 \ge C(k + k/(\varepsilon p)^{1/3})$, and
depths
$$q_1 \ge C\Bigl(\frac{p^{1/6}}{\varepsilon^{1/3}} + \sqrt{p}\Bigr)
\log\frac{\ell_2\,p\,\lvert n \rvert}{\varepsilon\delta}
\qquad\text{and}\qquad
q_2 \ge C\sqrt{p}\,\log\frac{\ell_2\,p\,\lvert n \rvert}{\varepsilon\delta}\,,$$
the tail bound
$$\mathbb{P}\Bigl[\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1,
\mathbf{X}_2, q_1, q_2)\rrbracket_k\|_{S_p} >
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\Bigr] \le \delta$$
holds. The asymptotic form of
`NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 1.1]; there with probability $99/100$ and an algorithm that
selects one of two runs; here a tail bound for every $\delta$, for the projection onto the sum
of the two spaces.
Asymptotic:
NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix
Result: rbki-sum-schatten-tail -/
theorem
    exists_forall_measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ)
      (ε δ : ℝ) (p : ℝ≥0∞),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 2 ≤ p → p ≠ ⊤ →
      0 < k → 0 < ε → ε ≤ ε₀ → 0 < δ → k + 2 ≤ Fintype.card l₁ →
      C * (k + k / (ε * p.toReal) ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * ((p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ + Real.sqrt p.toReal) *
        Real.log (Fintype.card l₂ * p.toReal * Fintype.card n / (ε * δ))) ≤ q₁ →
      C * (Real.sqrt p.toReal *
        Real.log (Fintype.card l₂ * p.toReal * Fintype.card n / (ε * δ))) ≤ q₂ →
      μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
        schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := sorry

end NLAlib
