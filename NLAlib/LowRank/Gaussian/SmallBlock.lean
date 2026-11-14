/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylov
public import NLAlib.Probability.Distributions.GaussianLogOverlap

/-!
# Randomized block Krylov iteration with a small block

Tail bounds for randomized block Krylov iteration
$\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)$ started from one standard Gaussian vector
$\mathbf{x}$, and, by monotonicity in the block, from a standard Gaussian block of any size. The
existing bounds (`NLAlib.LowRank.Gaussian.BlockKrylov`) need a block of at least $t + 2$ columns
for a tail index $t$. Here the first $t$ Krylov vectors
$[\mathbf{x}, \mathbf{H}\mathbf{x}, \dots, \mathbf{H}^{t-1}\mathbf{x}]$,
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, play the part of the block, and the remaining
depth $q - t$ carries the Chebyshev filter
(`NLAlib.exists_degree_lt_div_sq_le_exp_singularGapRatio`). The price is a gap hypothesis on the
top $t$ singular values, $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for $i + 1 < t$: the
coordinates of the simulated block in the top $t$ right singular vectors are
$\operatorname{diag}(\mathbf{g})$ times a Vandermonde matrix in $\sigma_0^2, \dots,
\sigma_{t-1}^2$, with $\mathbf{g}$ the coordinates of $\mathbf{x}$, and its inverse costs
$\Delta^{-2(t-1)}\sum_{i<t} g_i^{-2}$. With probability at least $1 - \delta$,
$$\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 \le \sigma_r(\mathbf{A})^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\gamma = (\sigma_{r-1} - \sigma_t)/(\sigma_{r-1} + \sigma_t)$. Since
$\mathbb{E}\,g_i^{-2} = \infty$ the route bounds no expectation of the error; the two forms stated
are the tail bound and the expectation restricted to the event that every head coordinate
exceeds $\delta/t$ in absolute value.

No positivity of the head singular values is assumed in the probabilistic statements: when
$\operatorname{rank}\mathbf{A} < t$ the gap hypothesis makes the positive singular values
distinct, the Krylov space of depth $q \ge t$ of almost every start vector contains the row
space of $\mathbf{A}$, and the error vanishes almost surely.

## Main results

* `NLAlib.measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector`,
  `NLAlib.sum_inv_sq_le_card_div_sq_of_forall_le_abs`: the head coordinates.
* `NLAlib.measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector`: the tail energy.
* `NLAlib.measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`,
  `NLAlib.measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`,
  `NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector`: the
  gapped tail bounds for one start vector.
* `NLAlib.setIntegral_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianVector`: the expectation on the
  head event.
*
`NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianVector`:
  the gapless $(1 + \varepsilon)$ tail bound for one start vector.
* `NLAlib.measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix`,
`NLAlib.measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianMatrix`:
  the same bounds for a Gaussian block of any size.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l k : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype k] [DecidableEq n] {x : Ω → n → ℝ} {X : Ω → Matrix n l ℝ}

/-! ### The head coordinates and the tail energy -/

omit [DecidableEq n] in
/-- The head event of a Gaussian start vector: for a standard Gaussian vector $\mathbf{x}$ in
$\mathbb{R}^n$ (independent standard normal entries), a real matrix $\mathbf{Z}$ with orthonormal
columns indexed by $k$, and $a \ge 0$,
$$\mathbb{P}\bigl[\exists i,\ \lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert \le a\bigr] \le
\lvert k \rvert\, a\,.$$
Each coordinate $(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i$ is a standard normal variable, so the
small-ball bound `NLAlib.gaussianReal_abs_le_le` and a union bound apply; independence of the
coordinates is not used. For $\lvert k \rvert = t$ the threshold $a = \delta/(2t)$ gives
probability at most $\delta/2$ and $a = \delta/t$ gives $\delta$. -/
theorem measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector
    [DecidableEq k] (hx : HasLaw x (gaussianVector n) μ) {Z : Matrix n k ℝ}
    (hZ : HasOrthonormalCols Z) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ a} ≤ Fintype.card k * a := by
  have := hx.isProbabilityMeasure
  have hset : {ω | ∃ i, |(Zᴴ *ᵥ x ω) i| ≤ a} = ⋃ i, {ω | |(Zᴴ *ᵥ x ω) i| ≤ a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  have hi : ∀ i, μ.real {ω | |(Zᴴ *ᵥ x ω) i| ≤ a} ≤ a := fun i => by
    have h := hasLaw_dotProduct_of_hasLaw_gaussianVector hx (Z.col i)
    have hv : ‖WithLp.toLp 2 (Z.col i)‖₊ ^ 2 = 1 := by
      rw [← NNReal.coe_inj, NNReal.coe_pow, coe_nnnorm, hZ.norm_toLp_col, one_pow, NNReal.coe_one]
    rw [hv] at h
    have he := h.measureReal_eq (p := fun y : ℝ => |y| ≤ a)
      (isClosed_le continuous_abs continuous_const).measurableSet
    have hcoord : ∀ ω, (Zᴴ *ᵥ x ω) i = Z.col i ⬝ᵥ x ω := fun ω => by
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    simp only [hcoord]
    rw [he]
    exact ENNReal.toReal_le_of_le_ofReal ha (gaussianReal_abs_le_le a)
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ a fun i _ => hi i).trans (le_of_eq ?_)
  rw [Finset.card_univ, nsmul_eq_mul]

/-- Off the head event the inverse head coordinates are bounded: for real numbers $g_i$, $i$ in a
finite type $\iota$, with $\lvert g_i \rvert \ge a > 0$ for every $i$,
$$\sum_i g_i^{-2} \le \frac{\lvert\iota\rvert}{a^2}\,.$$
For $\lvert\iota\rvert = t$ the threshold $a = \delta/(2t)$ gives $4t^3/\delta^2$ and
$a = \delta/t$ gives $t^3/\delta^2$. -/
theorem sum_inv_sq_le_card_div_sq_of_forall_le_abs {ι : Type*} [Fintype ι] {g : ι → ℝ} {a : ℝ}
    (ha : 0 < a) (hg : ∀ i, a ≤ |g i|) : ∑ i, (g i)⁻¹ ^ 2 ≤ Fintype.card ι / a ^ 2 := by
  have h : ∀ i ∈ Finset.univ, (g i)⁻¹ ^ 2 ≤ 1 / a ^ 2 := fun i _ => by
    rw [inv_pow, ← sq_abs (g i), ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le (hg i) 2)
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans (le_of_eq ?_)
  rw [Finset.card_univ, nsmul_eq_mul, mul_one_div]

/-- The tail energy of a Gaussian start vector: for a standard Gaussian vector $\mathbf{x}$ in
$\mathbb{R}^n$ (independent standard normal entries), a real matrix $\mathbf{M}$ and $\eta > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{M}\mathbf{x}\|_2^2 >
\frac{\|\mathbf{M}\|_{\mathsf{F}}^2}{\eta}\Bigr] \le \eta\,.$$
Markov's inequality for
$\mathbb{E}\|\mathbf{M}\mathbf{x}\|_2^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$
(`NLAlib.IsIsotropic.integral_norm_mulVec_sq`); when $\mathbf{M} = 0$ the event is null. -/
theorem measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector
    (hx : HasLaw x (gaussianVector n) μ) (M : Matrix m n ℝ) {η : ℝ} (hη : 0 < η) :
    μ.real {ω | frobNorm M ^ 2 / η < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2} ≤ η := by
  have := hx.isProbabilityMeasure
  have hiso := isIsotropic_of_hasLaw_gaussianVector hx
  have hint := hiso.integrable_norm_mulVec_sq M
  have hE := hiso.integral_norm_mulVec_sq M
  rcases (sq_nonneg (frobNorm M)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_div]
    have hae : (fun ω => ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 (hE.trans h0.symm)
    have hnull : μ {ω | 0 < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2} = 0 :=
      measure_mono_null (fun ω (hω : 0 < ‖WithLp.toLp 2 (M *ᵥ x ω)‖ ^ 2) => hω.ne') hae
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hη.le
  · have hmk := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖WithLp.toLp 2 (M *ᵥ x ω)‖) hint
      (frobNorm M ^ 2 / η)
    rw [hE, div_mul_eq_mul_div, div_le_iff₀ hη] at hmk
    refine (measureReal_mono fun ω (hω : frobNorm M ^ 2 / η < _) => hω.le).trans ?_
    exact le_of_mul_le_mul_left hmk hpos

/-! ### One Gaussian start vector, gapped -/

/-- The gapped tail bound for randomized block Krylov iteration from one start vector, spectral
norm: for a real matrix $\mathbf{A}$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, a
standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$ (independent standard normal entries), a
head of $r = h + 1$ singular values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. The first $t$ Krylov
vectors act as a block of $t$ columns and the Chebyshev filter has degree $q - t$. No positivity
of $\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the gap hypothesis makes
the positive singular values distinct and the error is zero almost surely. No gap between
$\sigma_{t-1}$ and $\sigma_t$ is assumed. -/
theorem measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2} ≤ δ := by
  -- If `1 ≤ δ` the bound is trivial. If `singularValues A (t - 1) = 0`: almost surely every
  -- coordinate of `x` along the right singular vectors of the positive singular values is nonzero
  -- (`ae_dotProduct_ne_zero_of_hasLaw_gaussianVector`), these are distinct by `hgap`, so the range
  -- of `A * blockKrylovMatrix (Aᴴ * A) _ q` is the range of `A` (Vandermonde, `q ≥ t > rank A`)
  -- and the error is zero. Otherwise take the frame `Z` of the top `t` right singular vectors and
  -- the filter of `exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - t)`; the
  -- deterministic single-vector bound (`specNorm_sub_rbki_replicateCol_sq_le`, planned in
  -- `NLAlib.LowRank.Structural.SmallBlock`) holds off the union of the head event at
  -- `a = δ / (2 * t)`
  -- (`measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector`,
  -- `sum_inv_sq_le_card_div_sq_of_forall_le_abs`) and the tail event at `η = δ / 2` for
  -- `M = A - A * Z * Zᴴ` (`measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector`), whose
  -- Frobenius norm is that of `A - truncatedSVD A t`; `4 * 4 * 2 = 32`.
  sorry

/-- The gapped tail bound for randomized block Krylov iteration from one start vector, Frobenius
norm: for a real matrix $\mathbf{A}$ with singular values $\sigma_0 \ge \sigma_1 \ge \dots$, a
standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$ (independent standard normal entries), a
head of $r = h + 1$ singular values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_{\mathsf{F}}^2 >
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No positivity of
$\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the error is zero almost
surely. -/
theorem measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | frobNorm (A - truncatedSVD A r) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        frobNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2} ≤ δ := by
  -- As `measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`, with the Frobenius
  -- twin of the deterministic single-vector bound (the structural filter bound
  -- `HasOrthonormalCols.frobNorm_sub_rsvd_cfc_sq_le` at the simulated block); the events and the
  -- rank-deficient case are the same.
  sorry

/-- The gapped tail bound for truncated randomized block Krylov iteration from one start vector,
spectral norm: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), a head of $r = h + 1$ singular values, a tail index
$t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right
side of the untruncated form,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\rrbracket_r\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No positivity of
$\sigma_{t-1}$ is assumed: when $\operatorname{rank}\mathbf{A} < t$ the output is $\mathbf{A}$
almost surely. -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector
    (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Matrix.replicateCol Unit (x ω)) q) r) ^ 2} ≤ δ := by
  -- Pointwise, with `Y` the Krylov matrix and `P` the range projector of the filtered simulated
  -- sketch: reverse Eckart–Young
  -- (`IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le`) and Gu's projected
  -- form (`frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`) reduce the
  -- error to `frobNorm ((1 - P) * truncatedSVD A r) ^ 2`, monotone in the range
  -- (`singularValues_one_sub_rangeProjector_mul_le_of_range_le`), and head capture
  -- (`HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le`) bounds it by the same
  -- residual as in the untruncated proof. Events and the rank-deficient case as there (the output
  -- is then `A` and the truncated error is `singularValues A r`).
  sorry

/-- The expectation of the error of randomized block Krylov iteration from one start vector on
the head event: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), an orthonormal frame $\mathbf{Z}$ of $t$ columns with
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_0^2, \dots, \sigma_{t-1}^2)$, a head of $r = h + 1$
singular values, $r \le t \le q$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, $\delta > 0$,
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, and the event
$E = \{\lvert(\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i\rvert > \delta/t \text{ for every } i\}$,
$$\mathbb{E}\bigl[\mathbf{1}_E\,
\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\|_2^2\bigr] \le
\sigma_r^2 + 4e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The complement of $E$ has probability at most $\delta$
(`NLAlib.measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector` at
$a = \delta/t$). On $E$ the sum $\sum_i (\mathbf{Z}^{\mathsf{H}}\mathbf{x})_i^{-2}$ is at most
$t^3/\delta^2$, and the tail energy is integrated over the whole space, so the independence of
the head and tail coordinates is not used. -/
theorem setIntegral_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} {Z : Matrix n (Fin t) ℝ}
    (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i : Fin t => singularValues A i ^ 2)
    (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    ∫ ω in {ω | ∀ i, δ / t < |(Zᴴ *ᵥ x ω) i|},
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 2) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  -- On the event every head coordinate is nonzero. If `singularValues A (t - 1) = 0` the error
  -- vanishes there (the Krylov space contains the row space, as in the tail bound). Otherwise the
  -- deterministic single-vector bound with the filter of
  -- `exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - t)` and
  -- `sum_inv_sq_le_card_div_sq_of_forall_le_abs` at `a = δ / t` bounds the integrand by
  -- `singularValues A r ^ 2 + 4 * exp _ * Δ⁻¹ ^ _ * (t ^ 3 / δ ^ 2) * N ω ^ 2`, `N ω` the
  -- Euclidean norm of `(A - A * Z * Zᴴ) *ᵥ x ω`;
  -- `setIntegral_mono_on`, `setIntegral_le_integral` and `IsIsotropic.integral_norm_mulVec_sq`
  -- finish, with `frobNorm (A - A * Z * Zᴴ) = frobNorm (A - truncatedSVD A t)` from `hAZ`.
  -- Integrability: `integrable_specNorm_sub_rbki_sq`.
  sorry

/-! ### One Gaussian start vector, gapless -/

/-- The gapless tail bound for truncated randomized block Krylov iteration from one start vector,
$(1 + \varepsilon)$ form: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian vector $\mathbf{x}$ in $\mathbb{R}^n$
(independent standard normal entries), a target rank $r$, depth $q \ge r$, a gap $\Delta > 0$
with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < r$, $\delta > 0$ and
$\varepsilon > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{x}, q)\rrbracket_r\|_2^2 >
(1 + \varepsilon)^2\sigma_r^2 +
32e^{-8(q-r)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\Delta^{-2(r-1)}\,\frac{r^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The start vector is the one-column block `Matrix.replicateCol Unit (x ω)`. No gap between
$\sigma_{r-1}$ and $\sigma_r$ is assumed; the gap $\Delta$ among the top $r$ singular values is
the price of the single start vector. -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianVector
    (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ) {r q : ℕ} (hq : r ≤ q)
    {Δ δ ε : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i, i + 1 < r → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) *
          Δ⁻¹ ^ (2 * (r - 1)) * ((r : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (Matrix.replicateCol Unit (x ω)) q) r) ^ 2} ≤ δ := by
  -- Musco and Musco's case split (`singularValues_zero_le_or_exists_singularGapRatio`, private in
  -- `NLAlib.LowRank.Gaussian.BlockKrylovGapless`; to be made public) is deterministic in `A`.
  -- Either `specNorm A ≤ (1 + ε) * singularValues A r` and the event is empty
  -- (`singularValues_sub_truncatedSVD_rsvd_le_of_le` at truncation `0`), or there is a head
  -- `h + 1 ≤ r` with `singularValues A (h + 1) ≤ (1 + ε) * singularValues A r` and gap ratio at
  -- least `ε / (2 + ε)` (or a zero tail): apply
  -- `measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector` at head
  -- `h + 1`, tail index `t = r` (so `hgap` is used as stated and the simulated block has `r`
  -- columns), truncate at `h + 1 ≤ r` (`singularValues_sub_truncatedSVD_rsvd_le_of_le`), and use
  -- that the exponential is antitone in the gap since `r ≤ q`; `measureReal_mono`.
  sorry

/-! ### A Gaussian block of any size -/

/-- The gapped tail bound for randomized block Krylov iteration with a block of any size,
spectral norm: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The block does at least as well as its first
column at the same depth, so the bound does not improve with $\ell$; for $t + 2 \le \ell$ the
bound in expectation
`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix` needs no gap
$\Delta$. -/
theorem measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix [Nonempty l]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - rbki A (X ω) q) ^ 2} ≤ δ := by
  -- Fix a column `j`; `fun ω i => X ω i j` is a standard Gaussian vector
  -- (`hasLaw_col_of_hasLaw_gaussianMatrix`) and the range of `Matrix.replicateCol Unit` of it is
  -- contained in the range of `X ω`, so `singularValues_sub_rbki_le_of_range_le` (planned in
  -- `NLAlib.LowRank.Structural.BlockKrylov`) at index `0` with `singularValues_zero_eq_specNorm`
  -- gives an inclusion of events; `measureReal_mono` and
  -- `measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector`.
  sorry

/-- The gapped tail bound for randomized block Krylov iteration with a block of any size,
Frobenius norm: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_{\mathsf{F}}^2 >
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The block does at least as well as its first
column at the same depth. -/
theorem measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix [Nonempty l]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | frobNorm (A - truncatedSVD A r) ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        frobNorm (A - rbki A (X ω) q) ^ 2} ≤ δ := by
  -- As the spectral form: a column of `X` is a standard Gaussian vector, the comparison
  -- `singularValues_sub_rbki_le_of_range_le` (planned) holds for every singular value, hence for
  -- the Frobenius norm (`(lpGauge 2).matrixNorm_le_of_singularValues_le`), and
  -- `measureReal_frobNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianVector` applies.
  sorry

/-- The gapped tail bound for truncated randomized block Krylov iteration with a block of any
size, spectral norm: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, and $\delta > 0$, with
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 >
\sigma_r^2 + 32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. The truncated error is not monotone in the
block, so this is not a comparison of outputs: the bound for one column is proved through a
quantity that is monotone in the range of the sketch. -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix
    [Nonempty l] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2} ≤ δ := by
  -- Not by comparing outputs. Repeat the proof of
  -- `measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianVector` for the column
  -- `fun ω i => X ω i j` (`hasLaw_col_of_hasLaw_gaussianMatrix`): reverse Eckart–Young and Gu's
  -- projected form are applied to `rbki A (X ω) q` itself, and the range of the filtered
  -- simulated sketch of the column is contained in the range of
  -- `A * blockKrylovMatrix (Aᴴ * A) (X ω) q` (`blockKrylovSpace_le_of_range_le`), which is all
  -- `singularValues_one_sub_rangeProjector_mul_le_of_range_le` needs. A shared private lemma with
  -- a range hypothesis, as `integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le` in
  -- `NLAlib.LowRank.Gaussian.BlockKrylov`, serves both.
  sorry

/-- The gapless tail bound for truncated randomized block Krylov iteration with a block of any
size, $(1 + \varepsilon)$ form: for a real matrix $\mathbf{A}$ with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$
(independent standard normal entries) with $\ell \ge 1$ columns, a target rank $r$, depth
$q \ge r$, a gap $\Delta > 0$ with $\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every
$i + 1 < r$, $\delta > 0$ and $\varepsilon > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A} -
\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 >
(1 + \varepsilon)^2\sigma_r^2 +
32e^{-8(q-r)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\Delta^{-2(r-1)}\,\frac{r^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\Bigr] \le \delta\,.$$
The index type of the columns is assumed nonempty. For $r + 2 \le \ell$ the bound in expectation
`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`
needs no gap $\Delta$. -/
theorem measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianMatrix
    [Nonempty l] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hq : r ≤ q) {Δ δ ε : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i, i + 1 < r → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | (1 + ε) ^ 2 * singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - r) * Real.sqrt (ε / (2 + ε))) *
          Δ⁻¹ ^ (2 * (r - 1)) * ((r : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A r) ^ 2 <
        specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2} ≤ δ := by
  -- The case split of
  -- `measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_one_add_sq_mul_le_of_hasLaw_gaussianVector`
  -- with `measureReal_specNorm_sub_truncatedSVD_rbki_sq_gt_le_of_hasLaw_gaussianMatrix` at head
  -- `h + 1`, tail index `r`, in place of the single-vector gapped bound; the other steps are
  -- deterministic and hold for every test matrix.
  sorry

end NLAlib
