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
public import NLAlib.Probability.Tail

/-!
# Two Gaussian block Krylov spaces: Schatten tail bounds, $2 \le p < \infty$

Tail bounds for block Krylov iteration on the sum of two block Krylov spaces,
$\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1, \mathbf{X}_2, q_1, q_2)$ (`NLAlib.rbkiSum`), in the
Schatten $p$-norm for $2 \le p < \infty$, with standard Gaussian test matrices $\mathbf{X}_1$
($n \times \ell_1$) and $\mathbf{X}_2$ ($n \times \ell_2$). With $N = \min(m, n)$,
$j + 1 \ge e^2 k/(\varepsilon p)^{1/3}$ for $\ell_2 = k + j + 2$ and depths $q_1$, $q_2$ of
order $(p^{1/6}\varepsilon^{-1/3} + \sqrt{p})\log(kpN/(\varepsilon\delta))$ and
$\sqrt{p}\log(kpN/(\varepsilon\delta))$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{X}_1,
\mathbf{X}_2, q_1, q_2)\rrbracket_k\|_{S_p} >
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}\Bigr] \le \delta\,,$$
and the same for the two-sided output. This is the regime $p > 2$ of
[BakshiClarksonWoodruff2022], for the projection onto the sum of the two Krylov spaces instead
of a selection between two runs, as a tail bound for every $\delta$ and with explicit constants.
On the good event of two Markov bounds for the sketch residuals, the deficits of the leading
singular values are bounded per index (`NLAlib.LowRank.Structural.RitzValues`), with a gap or
without, and the one-sided tail-count form
(`NLAlib.schattenNorm_sub_truncatedSVD_rsvd_le_mul_of_singularValues_le_mul`) turns them into
the error. The bounds in expectation, $1 \le p \le 2$ and Frobenius, are in
`NLAlib.LowRank.Gaussian.BlockKrylovSum`.

## Main results

* `NLAlib.measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`: the
  tail bound, one-sided output.
* `NLAlib.measureReal_schattenNorm_sub_mul_rangeProjector_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`:
  the same bound for the two-sided output.
* the asymptotic form of the first, named `exists_forall_` followed by its name.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Tail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n l₁ l₂ : Type*}
  [Fintype l] [Fintype m] [Fintype n] [Fintype l₁] [Fintype l₂] [DecidableEq m]
  [DecidableEq n] {X₁ : Ω → Matrix n l₁ ℝ} {X₂ : Ω → Matrix n l₂ ℝ}

/-! ### On the good event -/

omit [DecidableEq m] [DecidableEq n] in
/-- On the good event of the Markov bound for a top-$t$ frame of $\min(t, \lvert n \rvert)$
columns and a block of $\ell \ge t + 2$ columns, the squared spectral norm of the sketch residual
is at most $\tau\,t\,\min(\lvert m \rvert, \lvert n \rvert)\,\sigma_t^2$. -/
private theorem specNorm_residual_sq_le_of_frobNorm_sq_le {A : Matrix m n ℝ} {X : Matrix n l ℝ}
    {t : ℕ} {Z : Matrix n (Fin (min t (Fintype.card n))) ℝ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) (hl : t + 2 ≤ Fintype.card l) {τ : ℝ} (hτ : 0 ≤ τ)
    (hgood : frobNorm ((A - A * Z * Zᴴ) * X * pinv (Zᴴ * X)) ^ 2 ≤
      τ * (frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card (Fin (min t (Fintype.card n))) /
        ((Fintype.card l : ℝ) - Fintype.card (Fin (min t (Fintype.card n))) - 1))) :
    specNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)) ^ 2 ≤
      τ * t * (min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A t ^ 2 := by
  rw [hAZ, Fintype.card_fin] at hgood
  have hs : ((min t (Fintype.card n) : ℕ) : ℝ) ≤ t := by exact_mod_cast min_le_left _ _
  have hl' : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hl
  have hd : 1 ≤ (Fintype.card l : ℝ) - ((min t (Fintype.card n) : ℕ) : ℝ) - 1 := by linarith
  have hF := frobNorm_sub_truncatedSVD_sq_le_min_card_mul_sq A t
  have hr : frobNorm (A - truncatedSVD A t) ^ 2 * ((min t (Fintype.card n) : ℕ) : ℝ) /
      ((Fintype.card l : ℝ) - ((min t (Fintype.card n) : ℕ) : ℝ) - 1) ≤
      t * (min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A t ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ t * ((min (Fintype.card m) (Fintype.card n) : ℕ) : ℝ) *
        singularValues A t ^ 2 := by positivity
    calc frobNorm (A - truncatedSVD A t) ^ 2 * ((min t (Fintype.card n) : ℕ) : ℝ)
        ≤ ((min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A t ^ 2) * t :=
          mul_le_mul hF hs (Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  calc specNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)) ^ 2
      ≤ frobNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)) ^ 2 :=
        pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2
    _ ≤ _ := hgood
    _ ≤ τ * (t * (min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A t ^ 2) :=
        mul_le_mul_of_nonneg_left hr hτ
    _ = _ := by ring

/-- The logarithm in the depth thresholds of the tail bound turns the residual bound into the
head accuracy: $4e^{-\Lambda}\cdot 2TN/\delta \le \varepsilon^2/(32k^2(p + 1))$ at
$\Lambda = \log(256k^2T(p + 1)N/(\varepsilon^2\delta))$. -/
private theorem four_mul_exp_neg_log_mul_le {k T p N ε δ : ℝ} (hk : 0 < k) (hT : 0 < T)
    (hp : 0 < p) (hN : 0 ≤ N) (hε : 0 < ε) (hδ : 0 < δ) :
    4 * Real.exp (-Real.log (256 * k ^ 2 * T * (p + 1) * N / (ε ^ 2 * δ))) * (2 / δ * T * N) ≤
      ε ^ 2 / (32 * k ^ 2 * (p + 1)) := by
  rcases hN.eq_or_lt with rfl | hN
  · simp only [mul_zero]
    positivity
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  refine le_of_eq ?_
  field_simp
  ring

/-- A depth $q \ge 1 + \sqrt{4p + 1}\,\Lambda/8$ and a relative gap $g \ge 1/(4p + 1)$ give
$e^{-8(q-1)\sqrt{g}} \le e^{-\Lambda}$. -/
private theorem exp_neg_eight_mul_le_exp_neg {q Λ p g : ℝ} (hΛ : 0 ≤ Λ) (hp : 0 ≤ p)
    (hq : 1 + Real.sqrt (4 * p + 1) / 8 * Λ ≤ q) (hg : 1 / (4 * p + 1) ≤ g) :
    Real.exp (-8 * (q - 1) * Real.sqrt g) ≤ Real.exp (-Λ) := by
  refine Real.exp_le_exp.2 ?_
  have hs : 0 < Real.sqrt (4 * p + 1) := Real.sqrt_pos.2 (by linarith)
  have hsg : (Real.sqrt (4 * p + 1))⁻¹ ≤ Real.sqrt g := by
    rw [← Real.sqrt_inv, ← one_div]
    exact Real.sqrt_le_sqrt hg
  have hq1 : 0 ≤ q - 1 := by
    have : 0 ≤ Real.sqrt (4 * p + 1) / 8 * Λ := by positivity
    linarith
  have h1 := mul_le_mul_of_nonneg_left hsg (by linarith : (0 : ℝ) ≤ 8 * (q - 1))
  have h2 : Λ ≤ 8 * (q - 1) * (Real.sqrt (4 * p + 1))⁻¹ := by
    rw [le_mul_inv_iff₀ hs]
    linarith
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- A ratio $\sigma_h \ge (1 + 1/(2p))\,\sigma_t > 0$ gives the relative gap
$\operatorname{gap}(h, t) \ge 1/(4p + 1)$. -/
private theorem one_div_le_singularGapRatio {A : Matrix m n ℝ} {h t : ℕ} {p : ℝ} (hp : 0 < p)
    (hpos : 0 < singularValues A h)
    (hle : (1 + 1 / (2 * p)) * singularValues A t ≤ singularValues A h) :
    1 / (4 * p + 1) ≤ singularGapRatio A h t := by
  have ht := singularValues_nonneg A t
  rw [singularGapRatio, div_le_div_iff₀ (by linarith) (by linarith)]
  have e : 4 * p * ((1 + 1 / (2 * p)) * singularValues A t) =
      (4 * p + 2) * singularValues A t := by
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 4 * p)
  rw [e] at hm
  linarith

omit [DecidableEq m] in
/-- **A deficit from a gap, on a good event**: with a top-$t$ frame, a residual bound
$\|\mathbf{M}\|_2^2 \le c\,\sigma_t^2$, a depth $q \ge 1 + \sqrt{4p + 1}\,\Lambda/8$ with
$4e^{-\Lambda}c \le D$, and an index $h < t$ with $\sigma_h \ge (1 + 1/(2p))\,\sigma_t > 0$,
every $i \le h$ has $\sigma_i^2 - D\sigma_t^2 \le \sigma_i(\mathsf{rbki})^2$. -/
private theorem singularValues_sq_sub_le_singularValues_rbki_sq_of_gap {s : Type*} [Fintype s]
    [DecidableEq s] {A : Matrix m n ℝ} {X : Matrix n l ℝ} {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hX : (Xᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq1 : 1 ≤ q) {p Λ c D : ℝ} (hp : 0 < p)
    (hΛ : 0 ≤ Λ) (hq : 1 + Real.sqrt (4 * p + 1) / 8 * Λ ≤ q)
    (hM : specNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)) ^ 2 ≤
      c * singularValues A t ^ 2)
    (hD : 4 * Real.exp (-Λ) * c ≤ D) {h : ℕ} (hht : h < t) (hpos : 0 < singularValues A h)
    (hgap : (1 + 1 / (2 * p)) * singularValues A t ≤ singularValues A h) {i : ℕ} (hi : i ≤ h) :
    singularValues A i ^ 2 - D * singularValues A t ^ 2 ≤ singularValues (rbki A X q) i ^ 2 := by
  have h4 := hZ.singularValues_sq_sub_le_singularValues_rbki_sq_singularGapRatio hX rfl hht hAZ
    hq1 (Nat.lt_succ_of_le hi)
  have he := exp_neg_eight_mul_le_exp_neg hΛ hp.le hq (one_div_le_singularGapRatio hp hpos hgap)
  have hσ := sq_nonneg (singularValues A t)
  have hM0 := sq_nonneg (specNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)))
  have hc : 0 ≤ c * singularValues A t ^ 2 := hM0.trans hM
  have : 4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
      specNorm ((A - truncatedSVD A t) * X * pinv (Zᴴ * X)) ^ 2 ≤
      D * singularValues A t ^ 2 :=
    calc _ ≤ 4 * Real.exp (-Λ) * (c * singularValues A t ^ 2) :=
          mul_le_mul (by gcongr) hM hM0 (by positivity)
      _ = (4 * Real.exp (-Λ) * c) * singularValues A t ^ 2 := by ring
      _ ≤ D * singularValues A t ^ 2 := mul_le_mul_of_nonneg_right hD hσ
  linarith

omit [DecidableEq m] in
/-- **A deficit without a gap, on a good event**: with a top-$k$ frame, a residual bound
$\|\mathbf{M}\|_2^2 \le c\,\sigma_k^2$, $0 < w \le 1$, a depth with $\Lambda \le 2(q - 1)w$ and
$4e^{-\Lambda}c \le D \le w^2/2$, every $i < k$ has
$\sigma_i^2 - w^2\sigma_k^2 \le \sigma_i(\mathsf{rbki})^2$ (no-gap deficits at $\gamma = w^2/2$). -/
private theorem singularValues_sq_sub_le_singularValues_rbki_sq_of_noGap {s : Type*}
    [Fintype s] [DecidableEq s] {A : Matrix m n ℝ} {X : Matrix n l ℝ} {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hX : (Xᴴ * Z).rank = Z.rank) {k : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ} (hq1 : 1 ≤ q) {w Λ c D : ℝ} (hw : 0 < w)
    (hw1 : w ≤ 1) (hΛ : Λ ≤ 2 * ((q : ℝ) - 1) * w)
    (hM : specNorm ((A - truncatedSVD A k) * X * pinv (Zᴴ * X)) ^ 2 ≤
      c * singularValues A k ^ 2)
    (hD : 4 * Real.exp (-Λ) * c ≤ D) (hDw : D ≤ w ^ 2 / 2) {i : ℕ} (hi : i < k) :
    singularValues A i ^ 2 - w ^ 2 * singularValues A k ^ 2 ≤
      singularValues (rbki A X q) i ^ 2 := by
  have h3 := hZ.singularValues_sq_sub_le_singularValues_rbki_sq hX hAZ hq1 (γ := w ^ 2 / 2)
    (by positivity) (by nlinarith) hi
  have hexp : -2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (w ^ 2 / 2) =
      -2 * ((q : ℝ) - 1) * w := by
    rw [Real.sqrt_div (sq_nonneg w), Real.sqrt_sq hw.le]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hexp] at h3
  have he : Real.exp (-2 * ((q : ℝ) - 1) * w) ≤ Real.exp (-Λ) := Real.exp_le_exp.2 (by linarith)
  have hσ := sq_nonneg (singularValues A k)
  have hM0 := sq_nonneg (specNorm ((A - truncatedSVD A k) * X * pinv (Zᴴ * X)))
  have : 4 * Real.exp (-2 * ((q : ℝ) - 1) * w) *
      specNorm ((A - truncatedSVD A k) * X * pinv (Zᴴ * X)) ^ 2 ≤
      D * singularValues A k ^ 2 :=
    calc _ ≤ 4 * Real.exp (-Λ) * (c * singularValues A k ^ 2) :=
          mul_le_mul (by gcongr) hM hM0 (by positivity)
      _ = (4 * Real.exp (-Λ) * c) * singularValues A k ^ 2 := by ring
      _ ≤ D * singularValues A k ^ 2 := mul_le_mul_of_nonneg_right hD hσ
  have h5 := mul_le_mul_of_nonneg_right hDw hσ
  linarith

/-- The constant of the tail bound: with head accuracy $\varepsilon^2/(32k^2(p + 1))$ and a
middle increment $0 \le x \le p\varepsilon/2$, the coefficient
$k\sqrt{2(p + 1)\delta} + (1 + x)^{1/p}$ is at most $1 + \varepsilon$. -/
private theorem mul_sqrt_add_one_add_rpow_inv_le {r ε x : ℝ} {k : ℕ} (hr2 : 2 ≤ r) (hk : 0 < k)
    (hε : 0 < ε) (hx0 : 0 ≤ x) (hx : x ≤ r * ε / 2) :
    k * Real.sqrt (2 * (r + 1) * (ε ^ 2 / (32 * k ^ 2 * (r + 1)))) + (1 + x) ^ r⁻¹ ≤ 1 + ε := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 2 * (r + 1) * (ε ^ 2 / (32 * k ^ 2 * (r + 1))) = (ε / (4 * k)) ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_sq (by positivity)]
  have h2 := rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ x)
    (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ r)) (inv_le_one_of_one_le₀ (by linarith))
  have h3 : r⁻¹ * x ≤ ε / 2 := by
    rw [inv_mul_le_iff₀ (by linarith)]
    linarith
  have h4 : (k : ℝ) * (ε / (4 * k)) = ε / 4 := by field_simp
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail bound on the good event, flat tail**: if $\sigma_k \le (1 + 1/p)\,\sigma_{k+j}$,
$j + 1 \ge e^2k/(\varepsilon p)^{1/3}$, the large singular values have deficits at most
$\varepsilon^2/(32k^2(p + 1))\,\sigma_k^2$ and all leading ones at most
$(\varepsilon^{1/3}/p^{1/6})^2\,\sigma_k^2$, then
$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k\|_{S_p} \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}$. -/
private theorem schattenNorm_sub_truncatedSVD_rsvd_le_one_add_mul_of_flat {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {A : Matrix m n ℝ} {Y : Matrix n l ℝ} {k j : ℕ} (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (htail : singularValues A k ≤ (1 + 1 / p.toReal) * singularValues A (k + j))
    (hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - ε ^ 2 / (32 * k ^ 2 * (p.toReal + 1)) * singularValues A k ^ 2 ≤
        singularValues (rsvd A Y) i ^ 2)
    (hritz : ∀ i < k, singularValues A i ^ 2 -
      (ε ^ (3 : ℝ)⁻¹ / p.toReal ^ (6 : ℝ)⁻¹) ^ 2 * singularValues A k ^ 2 ≤
        singularValues (rsvd A Y) i ^ 2) :
    schattenNorm p (A - truncatedSVD (rsvd A Y) k) ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) := by
  have hr2 : 2 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hr : 0 < p.toReal := by linarith
  have ha : 0 < ε ^ (3 : ℝ)⁻¹ := Real.rpow_pos_of_pos hε _
  have hb : 0 < p.toReal ^ (6 : ℝ)⁻¹ := Real.rpow_pos_of_pos hr _
  have ha3 : (ε ^ (3 : ℝ)⁻¹) ^ 3 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hεr : (ε * p.toReal) ^ (3 : ℝ)⁻¹ = ε ^ (3 : ℝ)⁻¹ * (p.toReal ^ (6 : ℝ)⁻¹) ^ 2 := by
    rw [Real.mul_rpow hε.le hr.le, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  set a := ε ^ (3 : ℝ)⁻¹
  set b := p.toReal ^ (6 : ℝ)⁻¹
  have hκ : (1 + 1 / p.toReal) ^ p.toReal ≤ Real.exp 1 := Real.one_add_one_div_rpow_le_exp_one hr
  have hj0 : (0 : ℝ) < j + 1 := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hεr, div_le_iff₀ (by positivity)] at hj
  have h := schattenNorm_sub_truncatedSVD_rsvd_le_mul_of_singularValues_le_mul hp2 hp A Y
    (by positivity) (sq_nonneg (a / b)) (by positivity : (0 : ℝ) ≤ 1 + 1 / p.toReal) htail hhead
    hritz
  refine h.trans (mul_le_mul_of_nonneg_right
    (mul_sqrt_add_one_add_rpow_inv_le hr2 hk hε (by positivity) ?_) (schattenNorm_nonneg _ _))
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [div_le_iff₀ hj0]
  calc Real.exp 1 * (p.toReal / 2) * k * (a / b) ^ 2 * (1 + 1 / p.toReal) ^ p.toReal
      ≤ Real.exp 1 * (p.toReal / 2) * k * (a / b) ^ 2 * Real.exp 1 := by gcongr
    _ = p.toReal / 2 * (a / b) ^ 2 * (Real.exp 2 * k) := by rw [he2]; ring
    _ ≤ p.toReal / 2 * (a / b) ^ 2 * (((j : ℝ) + 1) * (a * b ^ 2)) := by gcongr
    _ = p.toReal * ε / 2 * ((j : ℝ) + 1) := by
        rw [← ha3]
        field_simp

omit [DecidableEq m] [DecidableEq n] in
/-- **The tail bound on the good event, spectral drop**: if every leading singular value has
deficit at most $\varepsilon^2/(32k^2(p + 1))\,\sigma_k^2$, $k \ge 1$, $p \ge 2$ and
$0 < \varepsilon \le 1$, then
$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{Y})\rrbracket_k\|_{S_p} \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}$. -/
private theorem schattenNorm_sub_truncatedSVD_rsvd_le_one_add_mul_of_drop {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {A : Matrix m n ℝ} {Y : Matrix n l ℝ} {k : ℕ} (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hritz : ∀ i < k, singularValues A i ^ 2 -
      ε ^ 2 / (32 * k ^ 2 * (p.toReal + 1)) * singularValues A k ^ 2 ≤
        singularValues (rsvd A Y) i ^ 2) :
    schattenNorm p (A - truncatedSVD (rsvd A Y) k) ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) := by
  have hr2 : 2 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have he0 := Real.exp_pos 1
  have hΔ : ε ^ 2 / (32 * k ^ 2 * (p.toReal + 1)) ≤ ε / (Real.exp 1 * k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ε ^ 2 * (Real.exp 1 * k) ≤ ε * (Real.exp 1 * k) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have h2 : ε * (Real.exp 1 * k) ≤ ε * (32 * k ^ 2 * (p.toReal + 1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hε.le
    linarith
  have h := schattenNorm_sub_truncatedSVD_rsvd_le_mul_of_singularValues_le_mul hp2 hp A Y (j := 0)
    (κ := 1) (by positivity) (by positivity : 0 ≤ ε / (Real.exp 1 * k)) zero_le_one (by simp)
    (fun i hi _ => hritz i hi) fun i hi => (hritz i hi).trans' (sub_le_sub_left
      (mul_le_mul_of_nonneg_right hΔ (sq_nonneg _)) _)
  refine h.trans (mul_le_mul_of_nonneg_right
    (mul_sqrt_add_one_add_rpow_inv_le hr2 hk hε (by positivity) (le_of_eq ?_))
    (schattenNorm_nonneg _ _))
  rw [Real.one_rpow, Nat.cast_zero, zero_add]
  field_simp

/-- The no-gap parameter of the tail bound, $w = \varepsilon^{1/3}/p^{1/6}$ for
$0 < \varepsilon \le 1$ and $p \ge 2$: $w \le 1$ and the head accuracy
$\varepsilon^2/(32k^2(p + 1))$ is at most $w^2/2$. -/
private theorem div_rpow_le_one_and_le_sq_div_two {k : ℕ} (hk : 0 < k) {ε r : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hr2 : 2 ≤ r) :
    ε ^ (3 : ℝ)⁻¹ / r ^ (6 : ℝ)⁻¹ ≤ 1 ∧
      ε ^ 2 / (32 * k ^ 2 * (r + 1)) ≤ (ε ^ (3 : ℝ)⁻¹ / r ^ (6 : ℝ)⁻¹) ^ 2 / 2 := by
  have hr : 0 < r := by linarith
  have ha : 0 < ε ^ (3 : ℝ)⁻¹ := Real.rpow_pos_of_pos hε _
  have hb : 0 < r ^ (6 : ℝ)⁻¹ := Real.rpow_pos_of_pos hr _
  have ha3 : (ε ^ (3 : ℝ)⁻¹) ^ 3 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hb6 : (r ^ (6 : ℝ)⁻¹) ^ 6 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hw1 : ε ^ (3 : ℝ)⁻¹ / r ^ (6 : ℝ)⁻¹ ≤ 1 := by
    rw [div_le_one hb]
    exact (Real.rpow_le_one hε.le hε1 (by norm_num)).trans
      (Real.one_le_rpow (by linarith) (by norm_num))
  refine ⟨hw1, ?_⟩
  set a := ε ^ (3 : ℝ)⁻¹
  set b := r ^ (6 : ℝ)⁻¹
  have hw6 : (a / b) ^ 6 = ε ^ 2 / r := by
    rw [div_pow, hb6, show a ^ 6 = (a ^ 3) ^ 2 by ring, ha3]
  have h62 : (a / b) ^ 6 ≤ (a / b) ^ 2 := pow_le_pow_of_le_one (by positivity) hw1 (by norm_num)
  have h1 : ε ^ 2 / (32 * k ^ 2 * (r + 1)) ≤ ε ^ 2 / (2 * r) :=
    div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity) (by
      have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hk)
      nlinarith)
  have h2 : ε ^ 2 / (2 * r) = (a / b) ^ 6 / 2 := by rw [hw6]; ring
  linarith

omit [DecidableEq m] in
/-- **The tail bound on the good event**: for top-$k$ and top-$(k + j)$ frames $\mathbf{Z}_1$,
$\mathbf{Z}_2$ in general position against $\mathbf{\Omega}_1$, $\mathbf{\Omega}_2$, the
thresholds of the tail bound, and sketch residuals with
$\|\mathbf{M}_1\|_2^2 \le (2/\delta)kN\sigma_k^2$ and
$\|\mathbf{M}_2\|_2^2 \le (2/\delta)(k + j)N\sigma_{k+j}^2$,
$\|\mathbf{A} - \llbracket\mathsf{rbkiSum}(\mathbf{A}, \mathbf{\Omega}_1, \mathbf{\Omega}_2,
q_1, q_2)\rrbracket_k\|_{S_p} \le (1 + \varepsilon)\,\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{S_p}$. A flat tail uses the no-gap deficits of the first
run; a spectral drop $\sigma_k > (1 + 1/p)\,\sigma_{k+j}$ the gap deficits of the second. -/
private theorem schattenNorm_sub_truncatedSVD_rbkiSum_le_of_specNorm_sq_le {s₁ s₂ : Type*}
    [Fintype s₁] [Fintype s₂] [DecidableEq s₁] [DecidableEq s₂] {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hp : p ≠ ⊤) {A : Matrix m n ℝ} {Ω₁ : Matrix n l₁ ℝ} {Ω₂ : Matrix n l₂ ℝ}
    {Z₁ : Matrix n s₁ ℝ} {Z₂ : Matrix n s₂ ℝ} (hZ₁ : HasOrthonormalCols Z₁)
    (hZ₂ : HasOrthonormalCols Z₂) (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank)
    (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
      Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₁)
    (hq₂ : 1 + Real.sqrt (4 * p.toReal + 1) / 8 *
      Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₂)
    (hΛ₁ : 0 ≤ Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)))
    (hΛ₂ : 0 ≤ Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)))
    (hM₁ : specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 ≤
      2 / δ * k * (min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A k ^ 2)
    (hM₂ : specNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 ≤
      2 / δ * ((k + j : ℕ) : ℝ) * (min (Fintype.card m) (Fintype.card n) : ℕ) *
        singularValues A (k + j) ^ 2) :
    schattenNorm p (A - truncatedSVD (rbkiSum A Ω₁ Ω₂ q₁ q₂) k) ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) := by
  have hr2 : 2 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hr : 0 < p.toReal := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 ≤ Real.sqrt (4 * p.toReal + 1) / 8 := by positivity
  have hb2a : 0 ≤ p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) := by positivity
  have hq₁a := mul_nonneg hb2a hΛ₁
  have hq₁s := mul_nonneg hs hΛ₁
  have hq₁' : 1 ≤ q₁ := by exact_mod_cast (show (1 : ℝ) ≤ q₁ by nlinarith)
  have hq₂' : 1 ≤ q₂ := by
    have := mul_nonneg hs hΛ₂
    exact_mod_cast (show (1 : ℝ) ≤ q₂ by linarith)
  have hD₁ := four_mul_exp_neg_log_mul_le hkR hkR hr
    (Nat.cast_nonneg (min (Fintype.card m) (Fintype.card n))) hε hδ
  rw [show (256 : ℝ) * k ^ 2 * k = 256 * k ^ 3 by ring] at hD₁
  have hD₂ := four_mul_exp_neg_log_mul_le hkR (by positivity : (0 : ℝ) < k + j) hr
    (Nat.cast_nonneg (min (Fintype.card m) (Fintype.card n))) hε hδ
  rw [Nat.cast_add] at hM₂
  -- the large singular values, from the first run
  have hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - ε ^ 2 / (32 * k ^ 2 * (p.toReal + 1)) * singularValues A k ^ 2 ≤
        singularValues (rbkiSum A Ω₁ Ω₂ q₁ q₂) i ^ 2 := fun i hi hbig =>
    (singularValues_sq_sub_le_singularValues_rbki_sq_of_gap hZ₁ hΩ₁ hAZ₁ hq₁' hr hΛ₁
      (by linarith) hM₁ hD₁ hi
      (lt_of_le_of_lt (mul_nonneg (by positivity) (singularValues_nonneg _ _)) hbig) hbig.le
      le_rfl).trans
      (pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_rbki_le_singularValues_rbkiSum_left A Ω₁ Ω₂ q₁ q₂ i) 2)
  by_cases hflat : singularValues A k ≤ (1 + 1 / p.toReal) * singularValues A (k + j)
  · -- a flat tail: no-gap deficits of the first run at `w = ε^{1/3}/p^{1/6}`
    have ha : 0 < ε ^ (3 : ℝ)⁻¹ := Real.rpow_pos_of_pos hε _
    have hb : 0 < p.toReal ^ (6 : ℝ)⁻¹ := Real.rpow_pos_of_pos hr _
    obtain ⟨hw1, hDw⟩ := div_rpow_le_one_and_le_sq_div_two hk hε hε1 hr2
    set a := ε ^ (3 : ℝ)⁻¹
    set b := p.toReal ^ (6 : ℝ)⁻¹
    have hΛw : Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤
        2 * ((q₁ : ℝ) - 1) * (a / b) := by
      calc _ = 2 * (b / (2 * a) * Real.log (256 * k ^ 3 * (p.toReal + 1) *
            (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ))) * (a / b) := by
            field_simp
        _ ≤ 2 * ((q₁ : ℝ) - 1) * (a / b) := by gcongr; linarith
    exact schattenNorm_sub_truncatedSVD_rsvd_le_one_add_mul_of_flat hp2 hp hk hε hj hflat hhead
      fun i hi => (singularValues_sq_sub_le_singularValues_rbki_sq_of_noGap hZ₁ hΩ₁ hAZ₁ hq₁'
        (by positivity) hw1 hΛw hM₁ hD₁ hDw hi).trans (pow_le_pow_left₀ (singularValues_nonneg _ _)
          (singularValues_rbki_le_singularValues_rbkiSum_left A Ω₁ Ω₂ q₁ q₂ i) 2)
  · -- a spectral drop: gap deficits of the second run
    replace hflat := not_le.1 hflat
    have hk0 : 0 < singularValues A k :=
      lt_of_le_of_lt (mul_nonneg (by positivity) (singularValues_nonneg _ _)) hflat
    have hle : singularValues A k ≤ singularValues A (k - 1) :=
      singularValues_antitone A (Nat.sub_le k 1)
    have hgap : (1 + 1 / (2 * p.toReal)) * singularValues A (k + j) ≤
        singularValues A (k - 1) := by
      have : 1 / (2 * p.toReal) ≤ 1 / p.toReal :=
        one_div_le_one_div_of_le hr (by linarith)
      nlinarith [singularValues_nonneg A (k + j)]
    have hσ : singularValues A (k + j) ^ 2 ≤ singularValues A k ^ 2 :=
      pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_antitone A (Nat.le_add_right k j)) 2
    refine schattenNorm_sub_truncatedSVD_rsvd_le_one_add_mul_of_drop hp2 hp hk hε hε1
      fun i hi => ?_
    have h := singularValues_sq_sub_le_singularValues_rbki_sq_of_gap hZ₂ hΩ₂ hAZ₂ hq₂' hr hΛ₂
      hq₂ hM₂ hD₂ (by omega : k - 1 < k + j) (hk0.trans_le hle) hgap (by omega : i ≤ k - 1)
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hσ (by positivity)) _).trans
      (h.trans (pow_le_pow_left₀ (singularValues_nonneg _ _)
        (singularValues_rbki_le_singularValues_rbkiSum_right A Ω₁ Ω₂ q₁ q₂ i) 2))

/-! ### The tail bound -/

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
[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two
runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here
for $2 \le p < \infty$ and the projection onto the sum of the two spaces, a tail bound for every
$\delta$ with oversampled blocks and explicit constants.

Note: the dimension $N$ enters because for $p > 2$ the Frobenius norm of the residuals is not
controlled by the optimal Schatten error. The two-sided output has the same bound:
`NLAlib.measureReal_schattenNorm_sub_mul_rangeProjector_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
The $O(\cdot)$ reading is
`NLAlib.exists_forall_measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`.
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
      schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := by
  have := hX₁.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rcases Nat.eq_zero_or_pos (min (Fintype.card m) (Fintype.card n)) with hN | hN
  · -- an empty matrix: the event is empty
    simp only [schattenNorm_eq_zero_of_min_card_eq_zero _ hN, mul_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty]
    exact hδ.le
  obtain ⟨Z₁, hZ₁, hAZ₁, hrk₁, -, -⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix A hX₁ hl₁
  obtain ⟨Z₂, hZ₂, hAZ₂, hrk₂, -, -⟩ :=
    exists_integral_frobNorm_sub_truncatedSVD_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix
      A hX₂ (k := k + j) hl₂
  have hτ : (0 : ℝ) < 2 / δ := by positivity
  have hE₁ := measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix A hX₁ hZ₁
    (by rw [Fintype.card_fin]; omega) hτ
  have hE₂ := measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix A hX₂ hZ₂
    (by rw [Fintype.card_fin]; omega) hτ
  -- the logarithms of the depth thresholds are nonnegative
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN1 : (1 : ℝ) ≤ (min (Fintype.card m) (Fintype.card n) : ℕ) := by exact_mod_cast hN
  have hr2 : 2 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have harg : ∀ T : ℝ, 1 ≤ T → 1 ≤ 256 * k ^ 2 * T * (p.toReal + 1) *
      (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ) := fun T hT => by
    have hk2 : (1 : ℝ) ≤ k ^ 2 := one_le_pow₀ hkR
    have h1 : (1 : ℝ) ≤ 256 * k ^ 2 * T * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) :=
      calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    have hden : ε ^ 2 * δ ≤ 1 := mul_le_one₀ (pow_le_one₀ hε.le hε1) hδ.le hδ1.le
    rw [one_le_div (by positivity)]
    linarith
  have hΛ₁ : 0 ≤ Real.log (256 * k ^ 3 * (p.toReal + 1) *
      (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) := by
    rw [show (256 : ℝ) * k ^ 3 = 256 * k ^ 2 * k by ring]
    exact Real.log_nonneg (harg k hkR)
  have hΛ₂ := Real.log_nonneg (harg ((k : ℝ) + j) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))
  refine (measureReal_le_add_of_ae_imp hE₁ hE₂ ?_).trans_eq (by rw [inv_div]; ring)
  filter_upwards [hrk₁, hrk₂] with ω hr₁ hr₂ hω
  by_contra hc
  simp only [not_or, not_lt] at hc
  exact (not_le.2 hω) (schattenNorm_sub_truncatedSVD_rbkiSum_le_of_specNorm_sq_le hp2 hp hZ₁ hZ₂
    hr₁ hr₂ hk hAZ₁ hAZ₂ hε hε1 hδ hj hq₁ hq₂ hΛ₁ hΛ₂
    (specNorm_residual_sq_le_of_frobNorm_sq_le hAZ₁ (by omega) hτ.le hc.1)
    (specNorm_residual_sq_le_of_frobNorm_sq_le hAZ₂ hl₂ hτ.le hc.2))

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
[BakshiClarksonWoodruff2022, Theorem 3.1]; there the error
$\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ of the two-sided output, for an
algorithm that selects one of the two runs, with blocks of $k$ and $s$ columns, probability
$9/10$ and unspecified constants; here for $2 \le p < \infty$ and the projection onto the sum of
the two spaces, a tail bound for every $\delta$ with oversampled blocks and explicit constants.
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
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ)} ≤ δ := by
  have := hX₁.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix hp2 hp A hX₁
      hX₂ hk hl₁ hl₂ hε hε1 hδ hj hq₁ hq₂)
  exact lt_of_lt_of_le hω (schattenNorm_sub_mul_rangeProjector_le_schattenNorm_sub_truncatedSVD_rsvd
    (one_le_two.trans hp2) A _ k)

end Tail

/-! ### Asymptotic form -/

/-- The logarithms of the depth thresholds of the tail bound are at most nine times the
logarithm of the asymptotic form: for $1 \le k, T \le \ell$, $\ell \ge 3$, $p \ge 2$,
$1 \le N \le M$ and $\varepsilon, \delta \in (0, 1]$,
$\log(256k^2T(p + 1)N/(\varepsilon^2\delta)) \le 9\log(\ell pM/(\varepsilon\delta))$. -/
private theorem log_le_nine_mul_log {k T X P M N ε δ : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X)
    (hT : 1 ≤ T) (hTX : T ≤ X) (hX : 3 ≤ X) (hP : 2 ≤ P) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (256 * k ^ 2 * T * (P + 1) * N / (ε ^ 2 * δ)) ≤
      9 * Real.log (X * P * M / (ε * δ)) := by
  have hM : 1 ≤ M := hN.trans hNM
  have h9 : (9 : ℝ) = ((9 : ℕ) : ℝ) := by norm_num
  rw [h9, ← Real.log_pow]
  refine Real.log_le_log (by positivity) ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h256 : (256 : ℝ) ≤ X ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num) hX 6]
  have hP9 : P + 1 ≤ P ^ 9 := by
    have : P ^ 2 ≤ P ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hM9 : N ≤ M ^ 9 := hNM.trans (by simpa using pow_le_pow_right₀ hM (by norm_num : 1 ≤ 9))
  have hA : 256 * k ^ 2 * T * (P + 1) * N ≤ (X * P * M) ^ 9 :=
    calc 256 * k ^ 2 * T * (P + 1) * N ≤ X ^ 6 * X ^ 2 * X * P ^ 9 * M ^ 9 := by gcongr
      _ = (X * P * M) ^ 9 := by ring
  have hB : (ε * δ) ^ 9 ≤ ε ^ 2 * δ := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_of_le_one hε.le hε1 (by norm_num))
      (by simpa using pow_le_pow_of_le_one hδ.le hδ1 (by norm_num : 1 ≤ 9)) (by positivity)
      (by positivity)
  exact mul_le_mul hA hB (by positivity) (by positivity)

/-- **$O(k(p^{1/6}\varepsilon^{-1/3} + \sqrt{p})\log(\ell_2 p\lvert n \rvert/(\varepsilon\delta)))$
products suffice for a $(1 + \varepsilon)$ rank-$k$ approximation in
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
        schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := by
  refine ⟨10, 1, by norm_num, by norm_num, ?_⟩
  intro Ω m n l₁ l₂ _ _ _ _ _ _ _ μ A X₁ X₂ k q₁ q₂ ε δ p hX₁ hX₂ hp2 hp hk hε hε1 hδ hl₁ hl₂
    hq₁ hq₂
  have := hX₁.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rcases Nat.eq_zero_or_pos (min (Fintype.card m) (Fintype.card n)) with hN | hN
  · simp only [schattenNorm_eq_zero_of_min_card_eq_zero _ hN, mul_zero, lt_self_iff_false,
      Set.ofPred_false, measureReal_empty]
    exact hδ.le
  have hr2 : 2 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hp hp2
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : 0 ≤ k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ := by positivity
  have hc : (k : ℝ) + 2 ≤ Fintype.card l₂ := by linarith
  have hcN : k + 2 ≤ Fintype.card l₂ := by exact_mod_cast hc
  have hjR : ((Fintype.card l₂ - k - 2 : ℕ) : ℝ) + 1 = Fintype.card l₂ - k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  -- the logarithms
  have hN1 : (1 : ℝ) ≤ (min (Fintype.card m) (Fintype.card n) : ℕ) := by exact_mod_cast hN
  have hNM : ((min (Fintype.card m) (Fintype.card n) : ℕ) : ℝ) ≤ Fintype.card n :=
    by exact_mod_cast min_le_right _ _
  set L := Real.log (Fintype.card l₂ * p.toReal * Fintype.card n / (ε * δ))
  have h6 : (6 : ℝ) ≤ Fintype.card l₂ * p.toReal * Fintype.card n := by
    have h1 : (1 : ℝ) ≤ Fintype.card n := hN1.trans hNM
    calc (6 : ℝ) = 3 * 2 * 1 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hL1 : 1 ≤ L := by
    have hed : ε * δ ≤ 1 := mul_le_one₀ hε1 hδ.le hδ1.le
    have hed0 : 0 < ε * δ := mul_pos hε hδ
    rw [Real.le_log_iff_exp_le (div_pos (by linarith) hed0), le_div_iff₀ hed0]
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith [Real.exp_pos 1]
  have hΛ₁ := log_le_nine_mul_log (X := (Fintype.card l₂ : ℝ)) hkR (by linarith) hkR
    (by linarith) (by linarith) hr2 hN1 hNM hε hε1 hδ hδ1.le
  rw [show (256 : ℝ) * k ^ 2 * k = 256 * k ^ 3 by ring] at hΛ₁
  have hΛ₂ := log_le_nine_mul_log (T := (k : ℝ) + (Fintype.card l₂ - k - 2 : ℕ))
    (X := (Fintype.card l₂ : ℝ)) hkR
    (by linarith) (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (Fintype.card l₂ - k - 2 : ℕ))])
    (by linarith) (by linarith) hr2 hN1 hNM hε hε1 hδ hδ1.le
  -- `√(4p + 1) ≤ 3√p` and `1 ≤ √p`
  have hs3 : Real.sqrt (4 * p.toReal + 1) ≤ 3 * Real.sqrt p.toReal := by
    have h9 : Real.sqrt (9 * p.toReal) = 3 * Real.sqrt p.toReal := by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h9]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsp : 1 ≤ Real.sqrt p.toReal := by simpa using Real.sqrt_le_sqrt (by linarith : 1 ≤ p.toReal)
  have hLs := one_le_mul_of_one_le_of_one_le hL1 hsp
  have hu : 0 ≤ p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ := by positivity
  refine measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix hp2 hp A
    hX₁ hX₂ (j := Fintype.card l₂ - k - 2) hk hl₁ (by omega) hε hε1 hδ ?_ ?_ ?_
  · rw [hjR, mul_div_assoc]
    have he2 : Real.exp 2 ≤ 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      nlinarith [Real.exp_pos 1]
    nlinarith
  · have hK : 0 ≤ p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8 :=
      by positivity
    have hh : p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) =
        p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ / 2 := by ring
    calc _ ≤ 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
          (9 * L) := by gcongr
      _ ≤ 1 + (p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ / 2 + 3 * Real.sqrt p.toReal / 8) *
          (9 * L) := by rw [hh]; gcongr
      _ ≤ 10 * ((p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ + Real.sqrt p.toReal) * L) := by
          nlinarith [mul_nonneg hu (by linarith : (0 : ℝ) ≤ L)]
      _ ≤ q₁ := hq₁
  · push_cast at hΛ₂ ⊢
    calc _ ≤ 1 + Real.sqrt (4 * p.toReal + 1) / 8 * (9 * L) := by gcongr
      _ ≤ 1 + 3 * Real.sqrt p.toReal / 8 * (9 * L) := by gcongr
      _ ≤ 10 * (Real.sqrt p.toReal * L) := by nlinarith
      _ ≤ q₂ := hq₂

end NLAlib
