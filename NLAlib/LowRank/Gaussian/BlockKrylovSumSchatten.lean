/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylovSum
public import NLAlib.LowRank.Gaussian.RitzValues
public import NLAlib.Probability.Tail

/-!
# Two block Krylov spaces with Gaussian start blocks, Schatten norms with $p \ge 2$

For $2 \le p < \infty$, bounds on the $p$-th power of the Schatten $p$-norm error of the
truncated one-sided output
$\llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)\rrbracket_k$
(`NLAlib.rbkiSum`), for standard Gaussian test matrices $\mathbf{X}_1$ and $\mathbf{X}_2$, in
expectation and as a tail bound, with no factor of the dimension. With $\ell_1 = 2k + 1$,
$\ell_2 = 2(k + j) + 1$, $r = \lceil (p - 2)/4 \rceil$, $j + 1 \ge 2ek\varepsilon^{-1/3}$,
$q_1 \ge 1 + r + \sqrt{p}\log(14pk/\varepsilon)/(2\varepsilon^{1/3})$ and
$q_2 \ge 1 + r + \sqrt{p}\log(8pk/\varepsilon)/2$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
The filters carry the weight $x^r$ of [BakshiNarayanan2023], which makes the energy they leave on
the tail a Schatten-$p$ quantity (`NLAlib.frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow`);
the case analysis is that of [BakshiClarksonWoodruff2022]. The tail bounds of
`NLAlib.LowRank.Gaussian.BlockKrylovSumTail` for the same output have a factor
$\log\min(m, n)$ in the depths; these have none.

## Main results

* weighted deficits of one run in expectation, without a gap,
  `integral_max_singularValues_sq_sub_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix`,
  and with a gap, its sibling that starts `integral_singularValues_rpow_mul_`.
* the error in expectation for any sketch containing both block Krylov sketches,
  `integral_schattenNorm_sub_truncatedSVD_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix`.
* the headlines in expectation and as a tail bound,
  `integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix`
  and `measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_gt_le_of_hasLaw_gaussianMatrix`,
  and the asymptotic form, named `exists_forall_` followed by the explicit name.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n l₁ l₂ : Type*}
  [Fintype l] [Fintype m] [Fintype n] [Fintype l₁] [Fintype l₂] [DecidableEq n]
  {X : Ω → Matrix n l ℝ} {X₁ : Ω → Matrix n l₁ ℝ} {X₂ : Ω → Matrix n l₂ ℝ}

/-- A relative bound in squares changes every power up to `P` by at most $\sqrt{e}$. -/
private theorem rpow_le_sqrt_exp_mul {x y P α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hP : 0 < P) (hα : 0 ≤ α) (hαP : α ≤ P) (hxy : x ^ 2 ≤ (1 + 1 / P) * y ^ 2) :
    x ^ α ≤ Real.sqrt (Real.exp 1) * y ^ α := by
  have hpow (z : ℝ) (hz : 0 ≤ z) : (z ^ 2) ^ (α / 2) = z ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
    congr 1
    ring
  have he : (1 + 1 / P) ^ (α / 2) ≤ Real.sqrt (Real.exp 1) := by
    calc _ ≤ (1 + 1 / P) ^ (P / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by
            have := one_div_pos.mpr hP
            linarith) (by linarith)
      _ = Real.sqrt ((1 + 1 / P) ^ P) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1
          ring
      _ ≤ _ := Real.sqrt_le_sqrt (Real.one_add_one_div_rpow_le_exp_one hP)
  have h := Real.rpow_le_rpow (sq_nonneg x) hxy (show 0 ≤ α / 2 by positivity)
  rw [hpow x hx, Real.mul_rpow (by positivity) (sq_nonneg y), hpow y hy] at h
  exact h.trans (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hy _))

omit [DecidableEq n] in
/-- In the middle, heavy-tail regime the weights cost $\sqrt{e}$;
the relative error is controlled by the spectral tail count. -/
private theorem middle_weights_le {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) {k j i : ℕ} (hk : 0 < singularValues A k) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmid : singularValues A i ^ 2 ≤ (1 + p.toReal⁻¹) * singularValues A k ^ 2)
    (htail : singularValues A k ^ 2 ≤ (1 + p.toReal⁻¹) * singularValues A (k + j) ^ 2) :
    singularValues A i ^ (p.toReal - 2) * singularValues A k ^ (2 - p.toReal) ≤
        Real.sqrt (Real.exp 1) ∧
      singularValues A i ^ (p.toReal - 2) * γ * singularValues A k ^ 2 ≤
        Real.exp 1 * γ / ((j : ℝ) + 1) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hw := rpow_le_sqrt_exp_mul (singularValues_nonneg A i) hk.le
    (by linarith : 0 < p.toReal) (by linarith : 0 ≤ p.toReal - 2)
    (by linarith : p.toReal - 2 ≤ p.toReal) (by simpa only [one_div] using hmid)
  have ht := rpow_le_sqrt_exp_mul hk.le (singularValues_nonneg A (k + j))
    (by linarith : 0 < p.toReal) (by linarith : 0 ≤ p.toReal) le_rfl
    (by simpa only [one_div] using htail)
  have hc : singularValues A k ^ (p.toReal - 2) * singularValues A k ^ (2 - p.toReal) = 1 := by
    rw [← Real.rpow_add hk, sub_add_sub_cancel, sub_self, Real.rpow_zero]
  have hc2 : singularValues A k ^ (p.toReal - 2) * singularValues A k ^ 2 =
      singularValues A k ^ p.toReal := by
    rw [← Real.rpow_two, ← Real.rpow_add hk, sub_add_cancel]
  constructor
  · have h := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hk.le (2 - p.toReal))
    calc _ ≤ Real.sqrt (Real.exp 1) *
          (singularValues A k ^ (p.toReal - 2) * singularValues A k ^ (2 - p.toReal)) := by
          nlinarith
      _ = _ := by rw [hc, mul_one]
  · have hwk : singularValues A i ^ (p.toReal - 2) * singularValues A k ^ 2 ≤
        Real.exp 1 * singularValues A (k + j) ^ p.toReal := by
      have h1 := mul_le_mul_of_nonneg_right hw (sq_nonneg (singularValues A k))
      have h2 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (Real.exp 1))
      rw [mul_assoc, hc2] at h1
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Real.exp_nonneg 1)] at h2
      exact h1.trans h2
    have hcount := mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow hp0 hp A k j
    have h1 := mul_le_mul_of_nonneg_left hwk
      (show 0 ≤ γ * ((j : ℝ) + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcount
      (show 0 ≤ Real.exp 1 * γ by positivity)
    have hbound : singularValues A i ^ (p.toReal - 2) * γ * singularValues A k ^ 2 ≤
        (Real.exp 1 * γ * schattenNorm p (A - truncatedSVD A k) ^ p.toReal) /
          ((j : ℝ) + 1) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    exact hbound.trans_eq (by ring)

omit [DecidableEq n] in
/-- Weighted compression deficits and their positive parts are integrable. -/
private theorem integrable_max_weighted_deficit [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ) (i : ℕ) (P d : ℝ) :
    Integrable (fun ω => max 0 (singularValues A i ^ (P - 2) *
      (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) - d)) μ := by
  classical
  have h := integrable_singularValues_rbki_sq A hY 1 i
  rw [show (fun ω => singularValues (rbki A (Y ω) 1) i ^ 2) =
    (fun ω => singularValues (rsvd A (Y ω)) i ^ 2) by simp only [rbki_one]] at h
  exact (integrable_const (0 : ℝ)).sup
    ((((integrable_const _).sub h).const_mul _).sub (integrable_const d))

-- The cited weighted-deficit declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- A containing sketch inherits the moment of a gapped weighted deficit. -/
private theorem integral_max_weighted_deficit_le_of_gap {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    {X : Ω → Matrix n l₁ ℝ} (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l₁) μ) {t r q i : ℕ}
    (hl : t + 2 ≤ Fintype.card l₁) (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hit : i < t)
    {θ d : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hd : 0 ≤ d)
    (hgap : (1 + θ) * singularValues A t ^ 2 ≤ singularValues A i ^ 2)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (hinc : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X ω) q).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, max 0 (singularValues A i ^ (p.toReal - 2) *
      (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) - d) ∂μ ≤
      4 * Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) * Real.sqrt θ) *
        ((t : ℝ) / ((Fintype.card l₁ : ℝ) - t - 1)) *
          schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
  classical
  have := hX.isProbabilityMeasure
  have hw := Real.rpow_nonneg (singularValues_nonneg A i) (p.toReal - 2)
  have hi := ((integrable_const (singularValues A i ^ 2)).sub
    (integrable_singularValues_rbki_sq A hX.aemeasurable q i)).const_mul
      (singularValues A i ^ (p.toReal - 2))
  refine (integral_mono (integrable_max_weighted_deficit A hY i p.toReal d) hi
    (fun ω => ?_)).trans
      (integral_singularValues_rpow_mul_singularValues_sq_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix
        hp2 hp A hX hl hr hq hit hθ hθ1 hgap)
  have hσ := singularValues_rangeProjector_mul_le_of_range_le (hinc ω) A i
  change singularValues (rbki A (X ω) q) i ≤ singularValues (rsvd A (Y ω)) i at hσ
  have hσ2 := pow_le_pow_left₀ (singularValues_nonneg _ _) hσ 2
  have hle := (isStarProjection_rangeProjector
    (A * blockKrylovMatrix (Aᴴ * A) (X ω) q)).singularValues_mul_le A i
  have hnon : 0 ≤ singularValues A i ^ (p.toReal - 2) *
      (singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2) :=
    mul_nonneg hw (sub_nonneg.mpr (pow_le_pow_left₀ (singularValues_nonneg _ _) hle 2))
  apply max_le hnon
  nlinarith [mul_le_mul_of_nonneg_left hσ2 hw]

/-- A containing sketch inherits a centered gapless deficit moment. -/
private theorem integral_max_weighted_deficit_le_of_cut {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    {X : Ω → Matrix n l₁ ℝ} (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l₁) μ) {k r q i : ℕ}
    (hl : k + 2 ≤ Fintype.card l₁) (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hik : i < k)
    {γ d : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hd : singularValues A i ^ (p.toReal - 2) * γ * singularValues A k ^ 2 ≤ d)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (hinc : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X ω) q).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, max 0 (singularValues A i ^ (p.toReal - 2) *
      (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) - d) ∂μ ≤
      singularValues A i ^ (p.toReal - 2) *
        (4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1 - r) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) * singularValues A k ^ (2 - p.toReal) *
            schattenNorm p (A - truncatedSVD A k) ^ p.toReal) := by
  classical
  have := hX.isProbabilityMeasure
  have hw := Real.rpow_nonneg (singularValues_nonneg A i) (p.toReal - 2)
  have hi := (integrable_const (0 : ℝ)).sup
    ((integrable_const (singularValues A i ^ 2 - γ * singularValues A k ^ 2)).sub
      (integrable_singularValues_rbki_sq A hX.aemeasurable q i))
  have hmono := integral_mono (integrable_max_weighted_deficit A hY i p.toReal d)
    (hi.const_mul (singularValues A i ^ (p.toReal - 2))) (fun ω => ?_)
  · refine hmono.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_max_singularValues_sq_sub_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix
        hp2 hp A hX hl hr hq hik hγ hγ1) hw
  · have hσ := pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_rangeProjector_mul_le_of_range_le (hinc ω) A i) 2
    change singularValues (rbki A (X ω) q) i ^ 2 ≤
      singularValues (rsvd A (Y ω)) i ^ 2 at hσ
    apply max_le (mul_nonneg hw (le_max_left _ _))
    simp only [Pi.sub_apply]
    have hmax := le_max_right 0
      (singularValues A i ^ 2 - γ * singularValues A k ^ 2 - singularValues (rbki A (X ω) q) i ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left hmax hw, mul_le_mul_of_nonneg_left hσ hw]

/-- The three spectral regimes give one centered deficit estimate for every head index. -/
private theorem integral_max_weighted_deficit_le {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j r q₁ q₂ i : ℕ} (hik : i < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂)
    (hr : p.toReal ≤ 4 * r + 2) (hq₁ : r + 1 ≤ q₁) (hq₂ : r + 1 ≤ q₂) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, max 0 (singularValues A i ^ (p.toReal - 2) *
      (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) -
        Real.exp 1 * γ / ((j : ℝ) + 1) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal) ∂μ ≤
      (4 * Real.sqrt (Real.exp 1) *
          Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ) *
            ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
            schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp2).ne'
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hθ : 0 < p.toReal⁻¹ := inv_pos.mpr (by linarith)
  have hθ1 : p.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  set O := schattenNorm p (A - truncatedSVD A k) ^ p.toReal
  have hO : 0 ≤ O := Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  set R₁ := (k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)
  set R₂ := ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1)
  have hR₁ : 0 ≤ R₁ := by
    have h : (k : ℝ) + 2 ≤ Fintype.card l₁ := by exact_mod_cast hl₁
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hR₂ : 0 ≤ R₂ := by
    have h : (k : ℝ) + j + 2 ≤ Fintype.card l₂ := by exact_mod_cast hl₂
    exact div_nonneg (by positivity) (by linarith)
  set E₀ := Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ)
  set E₁ := Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal)
  set E₂ := Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal)
  have hE₀ : 0 ≤ E₀ := Real.exp_nonneg _
  have hE₁ : 0 ≤ E₁ := Real.exp_nonneg _
  have hE₂ : 0 ≤ E₂ := Real.exp_nonneg _
  have hd : 0 ≤ Real.exp 1 * γ / ((j : ℝ) + 1) * O := by positivity
  have hB₀ : 0 ≤ 4 * Real.sqrt (Real.exp 1) * E₀ * R₁ * O := by positivity
  have hB₁ : 0 ≤ 4 * E₁ * R₁ * O := by positivity
  have hB₂ : 0 ≤ 4 * E₂ * R₂ * O := by positivity
  change _ ≤ (4 * Real.sqrt (Real.exp 1) * E₀ * R₁ + 4 * E₁ * R₁ + 4 * E₂ * R₂) * O
  have heq (q : ℕ) : Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) * Real.sqrt p.toReal⁻¹) =
      Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) / Real.sqrt p.toReal) := by
    simp only [Real.sqrt_inv, div_eq_mul_inv]
  by_cases hhigh : (1 + p.toReal⁻¹) * singularValues A k ^ 2 ≤ singularValues A i ^ 2
  · have h := integral_max_weighted_deficit_le_of_gap hp2 hp A hX₁ hl₁ hr hq₁ hik
      hθ hθ1 hd hhigh hY h₁
    rw [heq] at h
    exact h.trans (by
      change 4 * E₁ * R₁ * O ≤ _
      nlinarith only [hB₀, hB₂])
  have hkpos : 0 < singularValues A k := by
    by_contra h
    have hz : singularValues A k = 0 := le_antisymm (le_of_not_gt h) (singularValues_nonneg _ _)
    simp only [hz, zero_pow two_ne_zero, mul_zero, not_le] at hhigh
    nlinarith [sq_nonneg (singularValues A i)]
  by_cases hheavy : singularValues A k ^ 2 ≤ (1 + p.toReal⁻¹) * singularValues A (k + j) ^ 2
  · have hw := middle_weights_le hp2 hp A hkpos hγ.le (le_of_not_ge hhigh) hheavy
    have h := integral_max_weighted_deficit_le_of_cut hp2 hp A hX₁ hl₁ hr hq₁ hik
      hγ hγ1 hw.2 hY h₁
    have hscale := mul_le_mul_of_nonneg_right hw.1
      (show 0 ≤ 4 * E₀ * R₁ * O by positivity)
    exact h.trans (by
      change singularValues A i ^ (p.toReal - 2) *
        (4 * E₀ * R₁ * singularValues A k ^ (2 - p.toReal) * O) ≤ _
      nlinarith only [hscale, hB₁, hB₂])
  · have hgap : (1 + p.toReal⁻¹) * singularValues A (k + j) ^ 2 ≤ singularValues A i ^ 2 :=
      (le_of_not_ge hheavy).trans (pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_antitone A hik.le) 2)
    have h := integral_max_weighted_deficit_le_of_gap hp2 hp A hX₂ hl₂ hr hq₂
      (show i < k + j by omega) hθ hθ1 hd hgap hY h₂
    rw [heq] at h
    push_cast at h
    simp only [sub_add_eq_sub_sub] at h
    have : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2⟩
    have hopt := (lpGauge p).matrixNorm_sub_truncatedSVD_le_of_rank_le A
      ((rank_truncatedSVD_le A k).trans (Nat.le_add_right k j))
    rw [lpGauge_matrixNorm, lpGauge_matrixNorm] at hopt
    have hopt' : schattenNorm p (A - truncatedSVD A (k + j)) ^ p.toReal ≤ O :=
      Real.rpow_le_rpow (schattenNorm_nonneg _ _) hopt ENNReal.toReal_nonneg
    have hscale := mul_le_mul_of_nonneg_left hopt' (show 0 ≤ 4 * E₂ * R₂ by positivity)
    exact h.trans (by
      change 4 * E₂ * R₂ * schattenNorm p (A - truncatedSVD A (k + j)) ^ p.toReal ≤ _
      nlinarith only [hscale, hB₀, hB₁])

/-- The error is a deterministic tail-count term plus an integrable nonnegative remainder. -/
private theorem exists_integrable_remainder
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ) (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ)
    {k j r q₁ q₂ : ℕ} (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂)
    (hr : p.toReal ≤ 4 * r + 2) (hq₁ : r + 1 ≤ q₁) (hq₂ : r + 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∃ W : Ω → ℝ, Integrable W μ ∧ (∀ ω, 0 ≤ W ω) ∧
      (∀ ω, schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal ≤
        (1 + k * p.toReal * Real.exp 1 * γ / (2 * ((j : ℝ) + 1))) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal + W ω) ∧
      ∫ ω, W ω ∂μ ≤
        k * p.toReal * (2 * Real.sqrt (Real.exp 1) *
          Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ) *
            ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
          2 * Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
            ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
          2 * Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
            (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  classical
  have := hX₁.isProbabilityMeasure
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  set O := schattenNorm p (A - truncatedSVD A k) ^ p.toReal
  set d := Real.exp 1 * γ / ((j : ℝ) + 1) * O
  set f := fun i ω => max 0 (singularValues A i ^ (p.toReal - 2) *
    (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) - d)
  set W := fun ω => p.toReal / 2 * ∑ i ∈ Finset.range k, f i ω
  have hi (i : ℕ) : Integrable (f i) μ := integrable_max_weighted_deficit A hY i p.toReal d
  refine ⟨W, (integrable_finsetSum _ (fun i _ => hi i)).const_mul _, ?_, ?_, ?_⟩
  · intro ω
    exact mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => le_max_left _ _)
  · intro ω
    have hP := isStarProjection_rangeProjector (A * Y ω)
    have h := hP.schattenNorm_sub_truncatedSVD_mul_rpow_le_add_sum_mul hp2 hp A k
    have hsum := Finset.sum_le_sum (s := Finset.range k) fun i _ =>
      le_max_right 0 (singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) - d)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hscale := mul_le_mul_of_nonneg_left hsum (show 0 ≤ p.toReal / 2 by linarith)
    have hsum' : (∑ i ∈ Finset.range k, p.toReal / 2 * singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2)) =
        p.toReal / 2 * ∑ i ∈ Finset.range k, singularValues A i ^ (p.toReal - 2) *
          (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    change schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal ≤ O +
      ∑ i ∈ Finset.range k, p.toReal / 2 * singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (rsvd A (Y ω)) i ^ 2) at h
    rw [hsum'] at h
    have heq : O + p.toReal / 2 * k * d =
        (1 + k * p.toReal * Real.exp 1 * γ / (2 * ((j : ℝ) + 1))) * O := by
      dsimp [d]
      field_simp
    change schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal ≤ _
    dsimp only [W]
    rw [← heq]
    nlinarith only [h, hscale]
  · change ∫ ω, p.toReal / 2 * ∑ i ∈ Finset.range k, f i ω ∂μ ≤ _
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
    have hsum := Finset.sum_le_sum (s := Finset.range k) fun i hi =>
      integral_max_weighted_deficit_le hp2 hp A hX₁ hX₂ (Finset.mem_range.mp hi)
        hl₁ hl₂ hr hq₁ hq₂ hγ hγ1 hY h₁ h₂
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hscale := mul_le_mul_of_nonneg_left hsum (show 0 ≤ p.toReal / 2 by linarith)
    exact hscale.trans_eq (by ring)

/-! ### The error in expectation -/

/-- **The expected Schatten error, $2 \le p < \infty$, of a sketch containing two Gaussian block
Krylov sketches**: let $2 \le p < \infty$, $\mathbf{A}$ a real matrix, $\mathbf{X}_1$ and
$\mathbf{X}_2$ standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices
(independent standard normal entries; the two matrices need not be independent of each other),
$k + 2 \le \ell_1$, $k + j + 2 \le \ell_2$, $r$ with $p \le 4r + 2$, $q_1, q_2 \ge r + 1$ and
$0 < \gamma \le 1$, and let $\mathbf{Y}$ be an almost everywhere measurable random test matrix
such that, at every sample point, the range of $\mathbf{A}\mathbf{Y}$ contains the ranges of
$\mathbf{A}\mathbf{K}_{q_1}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_1)$ and of
$\mathbf{A}\mathbf{K}_{q_2}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{X}_2)$. Then
$$\begin{aligned}
\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k\|_{S_p}^p
\le \Bigl(1 + kp\Bigl(&\frac{e\gamma}{2(j + 1)} +
2\sqrt{e}\,e^{-2\sqrt{2}(q_1-1-r)\sqrt{\gamma}}\,\frac{k}{\ell_1 - k - 1} \\
&+ 2e^{-\frac{8}{3}(q_1-1-r)/\sqrt{p}}\,\frac{k}{\ell_1 - k - 1} +
2e^{-\frac{8}{3}(q_2-1-r)/\sqrt{p}}\,\frac{k + j}{\ell_2 - k - j - 1}\Bigr)\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.
\end{aligned}$$
No factor of the dimension appears. [BakshiClarksonWoodruff2022, Theorem 3.1]; there for an
algorithm that selects one of the two runs, with blocks of $k$ and $s$ columns, probability
$9/10$ and unspecified constants; here in expectation of the $p$-th power, for any sketch
containing both block Krylov sketches, with oversampled blocks, explicit constants and the filter
weight of [BakshiNarayanan2023, proof of Lemma 7.6]. -/
theorem integral_schattenNorm_sub_truncatedSVD_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ) (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ)
    {k j r q₁ q₂ : ℕ} (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂)
    (hr : p.toReal ≤ 4 * r + 2) (hq₁ : r + 1 ≤ q₁) (hq₂ : r + 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal ∂μ ≤
      (1 + k * p.toReal * (Real.exp 1 * γ / (2 * ((j : ℝ) + 1)) +
        2 * Real.sqrt (Real.exp 1) *
          Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        2 * Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        2 * Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1)))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have := hX₁.isProbabilityMeasure
  obtain ⟨W, hW, -, hbound, hmoment⟩ := exists_integrable_remainder
    hp2 hp A hX₁ hX₂ hl₁ hl₂ hr hq₁ hq₂ hγ hγ1 hY h₁ h₂
  have h := integral_mono (integrable_schattenNorm_sub_truncatedSVD_rsvd_rpow p A hY k)
    ((integrable_const _).add hW) hbound
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hW, integral_const, probReal_univ, one_smul] at h
  have heq : (1 + k * p.toReal * Real.exp 1 * γ / (2 * ((j : ℝ) + 1))) =
      1 + k * p.toReal * (Real.exp 1 * γ / (2 * ((j : ℝ) + 1))) := by ring
  rw [heq] at h
  nlinarith only [h, hmoment]


/-- The stated logarithmic depths bound each exponential by its reciprocal log argument. -/
private theorem schatten_thresholds {P ε δ a b : ℝ} {k r q₁ q₂ : ℕ}
    (hP : 2 ≤ P) (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hq₁ : 1 + r + Real.sqrt P * Real.log (a * P * k / (ε * δ)) /
      (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + r + Real.sqrt P * Real.log (b * P * k / (ε * δ)) / 2 ≤ q₂) :
    let u := ε ^ (3 : ℝ)⁻¹
    let γ := u ^ 2 / P
    0 < u ∧ u ≤ 1 ∧ u ^ 3 = ε ∧ 0 < γ ∧ γ ≤ 1 ∧ r + 1 ≤ q₁ ∧ r + 1 ≤ q₂ ∧
      Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ) ≤ ε * δ / (a * P * k) ∧
      Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt P) ≤ ε * δ / (a * P * k) ∧
      Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt P) ≤ ε * δ / (b * P * k) := by
  let u := ε ^ (3 : ℝ)⁻¹
  let γ := u ^ 2 / P
  have hu : 0 < u := Real.rpow_pos_of_pos hε _
  change 1 + (r : ℝ) + Real.sqrt P * Real.log (a * P * k / (ε * δ)) / (2 * u) ≤ q₁ at hq₁
  have hu1 : u ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hu3 : u ^ 3 = ε := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hP0 : 0 < P := by linarith
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP0
  have hγ : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := (div_le_one hP0).mpr (by nlinarith)
  have hsg : Real.sqrt γ = u / Real.sqrt P := by
    dsimp [γ]
    rw [Real.sqrt_div (sq_nonneg u), Real.sqrt_sq hu.le]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog (c : ℝ) (hc : 1 ≤ c) : 0 ≤ Real.log (c * P * k / (ε * δ)) := by
    apply Real.log_nonneg
    apply (one_le_div (mul_pos hε hδ)).mpr
    have hcp : P ≤ c * P := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hk1 (show 0 ≤ c * P by positivity)
    have hed := mul_le_mul_of_nonneg_left hδ1 hε.le
    nlinarith
  have hL₁ := hlog a ha
  have hL₂ := hlog b hb
  have hd₁ : (0 : ℝ) ≤ q₁ - 1 - r := by
    have hnon : 0 ≤ Real.sqrt P * Real.log (a * P * k / (ε * δ)) / (2 * u) := by positivity
    linarith
  have hd₂ : (0 : ℝ) ≤ q₂ - 1 - r := by
    have hnon : 0 ≤ Real.sqrt P * Real.log (b * P * k / (ε * δ)) / 2 := by positivity
    linarith
  have hm₁ : Real.sqrt P * Real.log (a * P * k / (ε * δ)) ≤
      ((q₁ : ℝ) - 1 - r) * (2 * u) :=
    (div_le_iff₀ (by positivity)).mp (show Real.sqrt P *
      Real.log (a * P * k / (ε * δ)) / (2 * u) ≤ (q₁ : ℝ) - 1 - r by linarith)
  have hm₂ : Real.sqrt P * Real.log (b * P * k / (ε * δ)) ≤
      ((q₂ : ℝ) - 1 - r) * 2 :=
    (div_le_iff₀ (by norm_num)).mp (by linarith)
  have hexp (c z : ℝ) (hc : 1 ≤ c) (hz : Real.log (c * P * k / (ε * δ)) ≤ z) :
      Real.exp (-z) ≤ ε * δ / (c * P * k) := by
    calc _ ≤ Real.exp (-Real.log (c * P * k / (ε * δ))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  refine ⟨hu, hu1, hu3, hγ, hγ1, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (r : ℝ) + 1 ≤ q₁ by linarith)
  · exact_mod_cast (show (r : ℝ) + 1 ≤ q₂ by linarith)
  · have hs2 : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hz : Real.log (a * P * k / (ε * δ)) ≤
        2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ := by
      rw [hsg, ← mul_div_assoc]
      apply (le_div_iff₀ hsP).mpr
      nlinarith [mul_le_mul_of_nonneg_right hs2
        (show 0 ≤ 2 * ((q₁ : ℝ) - 1 - r) * u by positivity)]
    simpa only [neg_mul] using hexp a _ ha hz
  · have hz : Real.log (a * P * k / (ε * δ)) ≤
        (8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt P := by
      apply (le_div_iff₀ hsP).mpr
      nlinarith [mul_le_mul_of_nonneg_right hu1 hd₁]
    simpa only [neg_mul, neg_div] using hexp a _ ha hz
  · have hz : Real.log (b * P * k / (ε * δ)) ≤
        (8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt P := by
      apply (le_div_iff₀ hsP).mpr
      nlinarith
    simpa only [neg_mul, neg_div] using hexp b _ hb hz

/-- Three bounded exponential factors give the required remainder budget. -/
private theorem remainder_coefficient_le {K ε δ a b x y z R S : ℝ}
    (hK : 0 < K) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hR : R ≤ 1) (hS : S ≤ 1)
    (hxb : x ≤ ε * δ / (a * K)) (hyb : y ≤ ε * δ / (a * K))
    (hzb : z ≤ ε * δ / (b * K)) :
    K * (2 * Real.sqrt (Real.exp 1) * x * R + 2 * y * R + 2 * z * S) ≤
      (6 / a + 2 / b) * ε * δ := by
  have hs : Real.sqrt (Real.exp 1) ≤ 2 := by
    nlinarith [Real.sq_sqrt (Real.exp_nonneg 1), Real.exp_one_lt_three]
  have h0 : x * R ≤ ε * δ / (a * K) :=
    (mul_le_of_le_one_right hx hR).trans hxb
  have h1 : y * R ≤ ε * δ / (a * K) :=
    (mul_le_of_le_one_right hy hR).trans hyb
  have h2 : z * S ≤ ε * δ / (b * K) :=
    (mul_le_of_le_one_right hz hS).trans hzb
  have h0' := mul_le_mul_of_nonneg_left h0
    (show 0 ≤ 2 * Real.sqrt (Real.exp 1) by positivity)
  have hs' := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ 2 * (ε * δ / (a * K)) by positivity)
  have hsum : 2 * Real.sqrt (Real.exp 1) * x * R + 2 * y * R + 2 * z * S ≤
      6 * (ε * δ / (a * K)) + 2 * (ε * δ / (b * K)) := by nlinarith only [h0', hs', h1, h2]
  calc _ ≤ K * (6 * (ε * δ / (a * K)) + 2 * (ε * δ / (b * K))) :=
        mul_le_mul_of_nonneg_left hsum hK.le
    _ = _ := by field_simp

/-- The wide block pays for the deterministic relative part of the deficits. -/
private theorem relative_coefficient_le {P ε u c : ℝ} {k j : ℕ}
    (hP : 0 < P) (hu : 0 < u) (hc : 0 < c) (hu3 : u ^ 3 = ε)
    (hj : c * Real.exp 1 * k / u ≤ (j : ℝ) + 1) :
    k * P * Real.exp 1 * (u ^ 2 / P) / (2 * ((j : ℝ) + 1)) ≤ ε / (2 * c) := by
  have hj' := (div_le_iff₀ hu).mp hj
  have hmul := mul_le_mul_of_nonneg_right hj' (sq_nonneg u)
  have hu3' := congrArg (fun x : ℝ => ((j : ℝ) + 1) * x) hu3
  have hnum : (k : ℝ) * P * Real.exp 1 * (u ^ 2 / P) = k * Real.exp 1 * u ^ 2 := by
    field_simp
  rw [hnum]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((j : ℝ) + 1))
    (by positivity : (0 : ℝ) < 2 * c)).mpr
  nlinarith only [hmul, hu3']

/-- The explicit logarithmic depths suffice with any blocks at least twice their target ranks. -/
private theorem integral_error_le_of_thresholds {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j r q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : 2 * k + 1 ≤ Fintype.card l₁) (hl₂ : 2 * (k + j) + 1 ≤ Fintype.card l₂)
    (hr : p.toReal ≤ 4 * r + 2) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hj : 2 * Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + r + Real.sqrt p.toReal * Real.log (14 * p.toReal * k / ε) /
      (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + r + Real.sqrt p.toReal * Real.log (8 * p.toReal * k / ε) / 2 ≤ q₂) :
    ∫ ω, schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  obtain ⟨hu, hu1, hu3, hγ, hγ1, hn₁, hn₂, he₀, he₁, he₂⟩ :=
    schatten_thresholds hP hk hε hε1 zero_lt_one le_rfl
      (by norm_num : (1 : ℝ) ≤ 14) (by norm_num : (1 : ℝ) ≤ 8)
      (by simpa only [mul_one] using hq₁) (by simpa only [mul_one] using hq₂)
  have hlr₁ : (2 : ℝ) * k + 1 ≤ Fintype.card l₁ := by exact_mod_cast hl₁
  have hlr₂ : (2 : ℝ) * (k + j) + 1 ≤ Fintype.card l₂ := by exact_mod_cast hl₂
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hR₁ : (k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hR₂ : ((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hD := relative_coefficient_le (by linarith : 0 < p.toReal) hu
    (by norm_num : (0 : ℝ) < 2) hu3 hj
  have hC := remainder_coefficient_le
    (x := Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) *
      Real.sqrt ((ε ^ (3 : ℝ)⁻¹) ^ 2 / p.toReal)))
    (y := Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal))
    (z := Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal))
    (show 0 < (k : ℝ) * p.toReal by positivity)
    hε.le (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 14)
    (by norm_num : (0 : ℝ) < 8) (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hR₁ hR₂
    (by simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using he₀)
    (by simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using he₁)
    (by simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using he₂)
  have hY := (measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable
    (hX₁.aemeasurable.prodMk hX₂.aemeasurable)
  have h := integral_schattenNorm_sub_truncatedSVD_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    hp2 hp A hX₁ hX₂ (k := k) (j := j) (r := r) (by omega) (by omega) hr hn₁ hn₂ hγ hγ1 hY
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_left A (X₁ ω) (X₂ ω) q₁ q₂)
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_right A (X₁ ω) (X₂ ω) q₁ q₂)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (schattenNorm_nonneg _ _) _))
  have hD' : (k : ℝ) * p.toReal *
      (Real.exp 1 * ((ε ^ (3 : ℝ)⁻¹) ^ 2 / p.toReal) / (2 * ((j : ℝ) + 1))) ≤ ε / 4 := by
    convert hD using 1 <;> ring
  nlinarith only [hD', hC, hε.le]

/-! ### Headlines at natural-number sizes -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Schatten norms with $2 \le p < \infty$.** Let $2 \le p < \infty$, let $\mathbf{A}$ be a real
$m \times n$ matrix, $\mathbf{X}_1$ a standard Gaussian $n \times (2k + 1)$ test matrix and
$\mathbf{X}_2$ a standard Gaussian $n \times (2(k + j) + 1)$ test matrix (each with independent
standard normal entries; the two need not be independent of each other), $k \ge 1$ and
$0 < \varepsilon \le 1$, and let $r = \lceil (p - 2)/4 \rceil$. If
$j + 1 \ge C_1 k/\varepsilon^{1/3}$,
$q_1 \ge 1 + r + \sqrt{p}\log(C_2 pk/\varepsilon)/(c\,\varepsilon^{1/3})$ and
$q_2 \ge 1 + r + \sqrt{p}\log(C_3 pk/\varepsilon)/c$, then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
Here $C_1 = 2e$, $C_2 = 14$, $C_3 = 8$ and $c = 2$.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants, here in
expectation of the $p$-th power, for the projection onto the sum of the two spaces, with
oversampled blocks and explicit constants; [BakshiNarayanan2023, Theorem 7.1]; there for rank
one and one Gaussian start vector, here for every $k$.

Note: the general form
`NLAlib.integral_schattenNorm_sub_truncatedSVD_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix`
at $\gamma = \varepsilon^{2/3}/p$; its four error terms are each at most $\varepsilon/4$. No
factor of the dimension appears, unlike the tail bound
`NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`. For
the norm itself, $\varepsilon = p\varepsilon'$ gives the factor
$(1 + p\varepsilon')^{1/p} \le e^{\varepsilon'}$; since $\varepsilon \le 1$ this covers only
$\varepsilon' \le 1/p$. At $p = 2$ ($r = 0$) it is a Frobenius bound of the shape of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`,
with other constants. Asymptotic form:
`NLAlib.exists_forall_integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix`.
Result: rbki-sum-schatten-large-p-error -/
theorem integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {m n k j q₁ q₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 2 * Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (14 * p.toReal * k / ε) / (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (8 * p.toReal * k / ε) / 2 ≤ q₂) :
    ∫ ω, schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  have hr : p.toReal ≤ 4 * (⌈(p.toReal - 2) / 4⌉₊ : ℝ) + 2 := by
    have h := Nat.le_ceil ((p.toReal - 2) / 4)
    linarith
  exact integral_error_le_of_thresholds hp2 hp A hX₁ hX₂ hk
    (by simp) (by simp) hr hε hε1 hj hq₁ hq₂


/-- Markov's inequality for an error bounded by a relative term and a nonnegative remainder. -/
private theorem measureReal_error_gt_le_of_remainder [IsFiniteMeasure μ] {ε δ O : ℝ} {f W : Ω → ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hO : 0 ≤ O) (hW : Integrable W μ) (hW0 : ∀ ω, 0 ≤ W ω)
    (hgood : ∀ ω, f ω ≤ (1 + ε / 2) * O + W ω)
    (hmoment : ∫ ω, W ω ∂μ ≤ ε * δ / 2 * O) :
    μ.real {ω | (1 + ε) * O < f ω} ≤ δ := by
  rcases hO.eq_or_lt with hO0 | hOpos
  · have hae : W =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hW0 hW).mp
      (le_antisymm (by simpa only [← hO0, mul_zero] using hmoment) (integral_nonneg hW0))
    have hnull : μ {ω | (1 + ε) * O < f ω} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) hae
      change W ω ≠ 0
      intro hz
      have h := hgood ω
      simp only [← hO0, mul_zero, hz, add_zero] at h hω
      exact (not_lt_of_ge h) hω
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact hδ.le
  · have hsub : {ω | (1 + ε) * O < f ω} ⊆ {ω | ε / 2 * O ≤ W ω} := by
      intro ω hω
      have h := hgood ω
      change ε / 2 * O ≤ W ω
      change (1 + ε) * O < f ω at hω
      linarith
    refine (measureReal_mono hsub).trans
      ((measureReal_ge_le_integral_div (ae_of_all _ hW0) hW
        (by positivity : 0 < ε / 2 * O)).trans ?_)
    apply (div_le_iff₀ (by positivity : 0 < ε / 2 * O)).mpr
    nlinarith only [hmoment]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from two Gaussian block Krylov spaces,
Schatten norms with $2 \le p < \infty$, tail bound.** Let $2 \le p < \infty$, let $\mathbf{A}$ be
a real $m \times n$ matrix, $\mathbf{X}_1$ a standard Gaussian $n \times (2k + 1)$ test matrix and
$\mathbf{X}_2$ a standard Gaussian $n \times (2(k + j) + 1)$ test matrix (each with independent
standard normal entries; the two need not be independent of each other), $k \ge 1$,
$0 < \varepsilon \le 1$ and $\delta > 0$, and let $r = \lceil (p - 2)/4 \rceil$. If
$j + 1 \ge C_1 k/\varepsilon^{1/3}$,
$q_1 \ge 1 + r + \sqrt{p}\log(C_2 pk/(\varepsilon\delta))/(c\,\varepsilon^{1/3})$ and
$q_2 \ge 1 + r + \sqrt{p}\log(C_3 pk/(\varepsilon\delta))/c$, then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1,
\mathbf{X}_2, q_1, q_2)\rrbracket_k\|_{S_p}^p >
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\Bigr] \le
\delta\,.$$
Here $C_1 = e$, $C_2 = 20$, $C_3 = 12$ and $c = 2$.
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants, here as a
tail bound in $p$-th powers, for the projection onto the sum of the two spaces, with
oversampled blocks, explicit constants and $\delta$ only inside the logarithms.

Note: the relative part of the deficits costs at most $\varepsilon/2$ deterministically; the
rest is Markov's inequality on the positive parts of the weighted deficits
(`NLAlib.integral_max_singularValues_sq_sub_sub_singularValues_rbki_sq_le_of_hasLaw_gaussianMatrix`).
No factor of the dimension appears, unlike
`NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`, which
bounds the norm.
Result: rbki-sum-schatten-large-p-tail -/
theorem measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {m n k j q₁ q₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (20 * p.toReal * k / (ε * δ)) / (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (12 * p.toReal * k / (ε * δ)) / 2 ≤ q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal <
      schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal} ≤ δ := by
  have := hX₁.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  let r := ⌈(p.toReal - 2) / 4⌉₊
  have hr : p.toReal ≤ 4 * (r : ℝ) + 2 := by
    have h := Nat.le_ceil ((p.toReal - 2) / 4)
    change (p.toReal - 2) / 4 ≤ (r : ℝ) at h
    linarith
  obtain ⟨hu, hu1, hu3, hγ, hγ1, hn₁, hn₂, he₀, he₁, he₂⟩ :=
    schatten_thresholds hP hk hε hε1 hδ hδ1.le
      (by norm_num : (1 : ℝ) ≤ 20) (by norm_num : (1 : ℝ) ≤ 12) hq₁ hq₂
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlr₁ : (2 : ℝ) * k + 1 ≤ Fintype.card (Fin (2 * k + 1)) := by simp
  have hlr₂ : (2 : ℝ) * (k + j) + 1 ≤ Fintype.card (Fin (2 * (k + j) + 1)) := by simp
  have hR₁ : (k : ℝ) / ((Fintype.card (Fin (2 * k + 1)) : ℝ) - k - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hR₂ : ((k : ℝ) + j) /
      ((Fintype.card (Fin (2 * (k + j) + 1)) : ℝ) - k - j - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hD := relative_coefficient_le (by linarith : 0 < p.toReal) hu
    (by norm_num : (0 : ℝ) < 1) hu3 (by simpa only [one_mul] using hj)
  have hC := remainder_coefficient_le
    (x := Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) *
      Real.sqrt ((ε ^ (3 : ℝ)⁻¹) ^ 2 / p.toReal)))
    (y := Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal))
    (z := Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal))
    (show 0 < (k : ℝ) * p.toReal by positivity)
    hε.le hδ.le (by norm_num : (0 : ℝ) < 20) (by norm_num : (0 : ℝ) < 12)
    (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _) hR₁ hR₂
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using he₀)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using he₁)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using he₂)
  have hY := (measurable_fromCols_blockKrylovMatrix (Aᴴ * A) q₁ q₂).comp_aemeasurable
    (hX₁.aemeasurable.prodMk hX₂.aemeasurable)
  obtain ⟨W, hW, hW0, hbound, hmoment⟩ := exists_integrable_remainder hp2 hp A hX₁ hX₂
    (k := k) (j := j) (r := r) (by simp; omega) (by simp; omega) hr hn₁ hn₂ hγ hγ1 hY
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_left A (X₁ ω) (X₂ ω) q₁ q₂)
    (fun ω => range_mul_blockKrylovMatrix_le_range_mul_fromCols_right A (X₁ ω) (X₂ ω) q₁ q₂)
  set O := schattenNorm p (A - truncatedSVD A k) ^ p.toReal
  have hO : 0 ≤ O := Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have hmoment' : ∫ ω, W ω ∂μ ≤ ε * δ / 2 * O := by
    refine hmoment.trans (mul_le_mul_of_nonneg_right ?_ hO)
    nlinarith only [hC, mul_nonneg hε.le hδ.le]
  have hgood (ω : Ω) : schattenNorm p
      (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ≤
      (1 + ε / 2) * O + W ω := by
    have h := mul_le_mul_of_nonneg_right hD hO
    have hω := hbound ω
    change schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^
      p.toReal ≤ (1 + k * p.toReal * Real.exp 1 *
        ((ε ^ (3 : ℝ)⁻¹) ^ 2 / p.toReal) / (2 * ((j : ℝ) + 1))) * O + W ω at hω
    nlinarith only [h, hω]
  exact measureReal_error_gt_le_of_remainder hε hδ hO hW hW0 hgood hmoment'

end Gaussian

/-- Absolute depth and block-size constants imply the explicit Schatten thresholds. -/
private theorem schatten_asymptotic_thresholds {P ε : ℝ} {k c q₁ q₂ : ℕ}
    (hP : 2 ≤ P) (hk : 0 < k) (hε : 0 < ε) (hε0 : ε ≤ Real.exp (-1))
    (hc : 1000 * (k / ε ^ (3 : ℝ)⁻¹) ≤ (c : ℝ))
    (hq₁ : 1000 * (P + Real.sqrt P * Real.log (P * k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1000 * (P + Real.sqrt P * Real.log (P * k / ε)) ≤ q₂) :
    ε ≤ 1 ∧ ∃ j : ℕ, 2 * (k + j) + 1 ≤ c ∧
      2 * Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1 ∧
      1 + ⌈(P - 2) / 4⌉₊ + Real.sqrt P * Real.log (14 * P * k / ε) /
        (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁ ∧
      1 + ⌈(P - 2) / 4⌉₊ + Real.sqrt P * Real.log (8 * P * k / ε) / 2 ≤ q₂ := by
  let u := ε ^ (3 : ℝ)⁻¹
  change 1000 * (k / u) ≤ (c : ℝ) at hc
  change 1000 * (P + Real.sqrt P * Real.log (P * k / ε) / u) ≤ q₁ at hq₁
  have hε1 : ε ≤ 1 := hε0.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hu : 0 < u := Real.rpow_pos_of_pos hε _
  have hu1 : u ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hku : (k : ℝ) ≤ k / u := le_div_self (by linarith) hu hu1
  have hc' : 1000 * k ≤ c := by exact_mod_cast (show (1000 : ℝ) * k ≤ c by linarith)
  let j := (c - 1) / 2 - k
  have hjc : c ≤ 2 * j + 2 * k + 2 := by dsimp [j]; omega
  have hjcR : (c : ℝ) ≤ 2 * j + 2 * k + 2 := by exact_mod_cast hjc
  have hL : 1 ≤ Real.log (P * k / ε) := by
    have hM : 1 ≤ Real.log (1 / ε) := by
      rw [one_div, Real.log_inv, le_neg]
      exact (Real.log_le_log hε hε0).trans_eq (Real.log_exp _)
    refine hM.trans (Real.log_le_log (by positivity) ?_)
    apply div_le_div_of_nonneg_right _ hε.le
    nlinarith
  have hlog (a : ℝ) (ha : 1 ≤ a) : Real.log (a * P * k / ε) ≤ a * Real.log (P * k / ε) := by
    rw [show a * P * k / ε = a * (P * k / ε) by ring,
      Real.log_mul (by linarith) (by positivity)]
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < a)
    nlinarith
  have hr : 1 + (⌈(P - 2) / 4⌉₊ : ℝ) ≤ 2 * P := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (P - 2) / 4 by linarith)
    linarith
  refine ⟨hε1, j, by dsimp [j]; omega, ?_, ?_, ?_⟩
  · have he := mul_le_mul_of_nonneg_right
      (show 2 * Real.exp 1 ≤ 6 by linarith [Real.exp_one_lt_three])
      (show 0 ≤ (k : ℝ) / u by positivity)
    change 2 * Real.exp 1 * k / u ≤ _
    rw [mul_div_assoc]
    linarith only [hc, hjcR, hku, he]
  · have hlog' := mul_le_mul_of_nonneg_left (hlog 14 (by norm_num)) (Real.sqrt_nonneg P)
    have hterm : Real.sqrt P * Real.log (14 * P * k / ε) / (2 * u) ≤
        7 * (Real.sqrt P * Real.log (P * k / ε) / u) := by
      have h := div_le_div_of_nonneg_right hlog' (show 0 ≤ 2 * u by positivity)
      exact h.trans_eq (by ring)
    have hn : 0 ≤ Real.sqrt P * Real.log (P * k / ε) / u := by positivity
    change 1 + (⌈(P - 2) / 4⌉₊ : ℝ) + _ / (2 * u) ≤ _
    linarith
  · have hlog' := mul_le_mul_of_nonneg_left (hlog 8 (by norm_num)) (Real.sqrt_nonneg P)
    have hterm : Real.sqrt P * Real.log (8 * P * k / ε) / 2 ≤
        4 * (Real.sqrt P * Real.log (P * k / ε)) := by linarith
    have hn : 0 ≤ Real.sqrt P * Real.log (P * k / ε) := by positivity
    linarith

/-! ### Asymptotic form -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(p + \sqrt{p}\,\varepsilon^{-1/3}\log(pk/\varepsilon))$ depth suffices for a
$(1 + \varepsilon)$ rank-$k$ approximation in Schatten norms with $2 \le p < \infty$**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for $2 \le p < \infty$, a real matrix
$\mathbf{A}$, standard Gaussian $n \times \ell_1$ and $n \times \ell_2$ test matrices
$\mathbf{X}_1$ and $\mathbf{X}_2$ (independent standard normal entries; the two matrices need
not be independent of each other), $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$, blocks
$\ell_1 \ge 2k + 1$ and $\ell_2 \ge Ck/\varepsilon^{1/3}$, and depths
$q_1 \ge C(p + \sqrt{p}\log(pk/\varepsilon)/\varepsilon^{1/3})$ and
$q_2 \ge C(p + \sqrt{p}\log(pk/\varepsilon))$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2,
q_1, q_2)\rrbracket_k\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
The constants do not depend on $p$, and no factor of the dimension appears. The asymptotic form
of
`NLAlib.integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix`.
[BakshiClarksonWoodruff2022, Theorem 1.1]; there with $\log(d/\varepsilon)$ in place of
$\log(pk/\varepsilon)$, probability $99/100$ and an algorithm that selects one of two runs; here
in expectation of the $p$-th power, for the projection onto the sum of the two spaces.
Asymptotic:
NLAlib.integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: rbki-sum-schatten-large-p-error -/
theorem
    exists_forall_integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω) (p : ℝ≥0∞)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ),
      2 ≤ p → p ≠ ⊤ → HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ →
      0 < k → 0 < ε → ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ →
      C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (p.toReal + Real.sqrt p.toReal * Real.log (p.toReal * k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ →
      C * (p.toReal + Real.sqrt p.toReal * Real.log (p.toReal * k / ε)) ≤ q₂ →
      ∫ ω, schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ∂μ ≤
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  refine ⟨1000, Real.exp (-1), by norm_num, Real.exp_pos _, ?_⟩
  intro Ω m n l₁ l₂ _ _ _ _ _ _ μ p A X₁ X₂ k q₁ q₂ ε hp2 hp hX₁ hX₂ hk hε hε0 hl₁ hl₂ hq₁ hq₂
  have hP : 2 ≤ p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  obtain ⟨hε1, j, hj₂, hj, hq₁', hq₂'⟩ :=
    schatten_asymptotic_thresholds hP hk hε hε0 hl₂ hq₁ hq₂
  have hr : p.toReal ≤ 4 * (⌈(p.toReal - 2) / 4⌉₊ : ℝ) + 2 := by
    have h := Nat.le_ceil ((p.toReal - 2) / 4)
    linarith
  exact integral_error_le_of_thresholds hp2 hp A hX₁ hX₂ hk hl₁ hj₂ hr hε hε1 hj hq₁' hq₂'


end NLAlib
