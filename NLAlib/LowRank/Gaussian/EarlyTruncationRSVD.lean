/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.EarlyTruncation
public import NLAlib.RandomMatrix.Gaussian.ClippedInverseMoments
public import NLAlib.Sketching.Gaussian.Gaussian
public import NLAlib.Regression.SketchAndSolve
public import NLAlib.Sketching.Properties.MatrixMultiplication

public import NLAlib.ForMathlib.Analysis.Real.Sqrt

/-!
# Early-truncated randomized SVD with Gaussian test matrices

Expected squared Frobenius error for Gaussian early truncation, with a free Young parameter
and its optimized factor. Relative error $1+\varepsilon$ follows at
$\ell\ge\max\{900,400k/\varepsilon^2\}$; the previous $900k/\varepsilon^2$ form remains available.
Gaussian completion to generalized Nyström is in the Gaussian EarlyTruncation module.
Design: docs/design/research/Nystrom-Constants.md.

## Main results

* [Free-parameter expectation](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_div_of_hasLaw_gaussianMatrix).
* [Optimized-factor expectation](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix).
* [Relative-error width](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedRSVDRelativeErrorDim_le).
* [Previous sufficient width](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-! ### The early-truncated randomized SVD factor -/

/-- **The optimized Gaussian early-truncation factor** multiplying the optimal squared
Frobenius error, for $100k\le\ell$ and $\ell\ge900$, at
present <!-- value earlyTruncatedRSVDFactor k \ell -->
$$
( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + 2( ( k/\ell)
\sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) + \sqrt{ 4( (
k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) ( ( (
1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + ( ( k/\ell) \sqrt{
1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) ) } \,.
$$
This is the minimum of the free Young-parameter estimate. The constants $10$ and $263$
come from the clipped inverse-head moments. It tends to $1$ as $k/\ell$ and $1/\ell$ tend to $0$.
The error theorems use $100k\le\ell$ and $\ell\ge900$; outside those hypotheses this definition
is only a total real expression, with inverse-of-zero interpreted as $0$. No printed source. -/
noncomputable irreducible_def earlyTruncatedRSVDFactor (k l : ℕ) : ℝ :=
  let a := (1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l)
  let b := ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
    √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l)
  a + 2 * b + √(4 * b * (a + b))

/-- **The Gaussian early-truncation factor with a free Young parameter**: for
$100k\le\ell$, $\ell\ge900$ and $0<\theta<1$, its value is at
present <!-- value earlyTruncatedRSVDYoungFactor k \ell \theta -->
$$
( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) + ( ( k/\ell)
\sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) /\theta) /(
1-\theta) \,.
$$
The error estimate is only asserted under those hypotheses; this is a total real expression
elsewhere, with inverse-of-zero interpreted as $0$. No printed source. -/
noncomputable irreducible_def earlyTruncatedRSVDYoungFactor (k l : ℕ) (θ : ℝ) : ℝ :=
  ((1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l) +
      ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
        √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l) / θ) / (1 - θ)

/-- The explicit value the documentation displays: the optimized Gaussian early-truncation factor
is at most <!-- value earlyTruncatedRSVDFactor k \ell -->
$$
( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + 2( ( k/\ell)
\sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) + \sqrt{ 4( (
k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) ( ( (
1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + ( ( k/\ell) \sqrt{
1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) ) }
$$
(at present an equality), written $a + 2b + \sqrt{4b(a + b)}$ with $a$ and $b$ its two repeated
subexpressions. -/
theorem earlyTruncatedRSVDFactor_le (k l : ℕ) :
    earlyTruncatedRSVDFactor k l ≤
      (let a := (1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l)
       let b := ((k : ℝ) / l) * √(1 + 2 / (k * l)) * √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l)
       a + 2 * b + √(4 * b * (a + b))) := by
  rw [earlyTruncatedRSVDFactor_def]

/-- The explicit value the documentation displays: the Gaussian early-truncation factor with a free
Young parameter is at most <!-- value earlyTruncatedRSVDYoungFactor k \ell \theta -->
$$
( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) + ( ( k/\ell)
\sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) /\theta) /(
1-\theta)
$$
(at present an equality). -/
theorem earlyTruncatedRSVDYoungFactor_le (k l : ℕ) (θ : ℝ) :
    earlyTruncatedRSVDYoungFactor k l θ ≤
      ((1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l) +
          ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
            √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l) / θ) / (1 - θ) := by
  rw [earlyTruncatedRSVDYoungFactor_def]

/-- The sizes in the factor: for $100k \le \ell$, $y = \sqrt{k/\ell}$ satisfies
$0 \le y \le 1/10$. -/
private theorem sqrt_div_le_tenth {k l : ℕ} (h : 100 * k ≤ l) :
    0 ≤ √((k : ℝ) / l) ∧ √((k : ℝ) / l) ≤ 1 / 10 := by
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩⟩
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [hl]
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h' : 100 * (k : ℝ) ≤ l := by exact_mod_cast h
  rw [div_le_iff₀ hl']
  linarith

/-- The optimized early-truncation factor is at least $1$ when $100k\le\ell$, at
present <!-- value earlyTruncatedRSVDFactor k \ell -->
$$
1\le ( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + 2( (
k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) +
\sqrt{ 4( ( k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{
\ell} } ) ( ( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{ \ell} ) ) + ( (
k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{ \ell} } ) ) }
\,.
$$ -/
theorem one_le_earlyTruncatedRSVDFactor {k l : ℕ} (h : 100 * k ≤ l) :
    1 ≤ earlyTruncatedRSVDFactor k l := by
  obtain ⟨hy0, hy⟩ := sqrt_div_le_tenth h
  rw [earlyTruncatedRSVDFactor_def]
  dsimp only
  have h1y : 0 < 1 - √((k : ℝ) / l) := by linarith
  have hinv : 1 ≤ ((1 - √((k : ℝ) / l)) ^ 2)⁻¹ :=
    one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h1y.le (by linarith))
  have ha : 1 ≤ (1 + √(2 * (k : ℝ) / l)) *
      (((1 - √((k : ℝ) / l)) ^ 2)⁻¹ + 10 / √(l : ℝ)) := by
    nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) / l),
      show 0 ≤ 10 / √(l : ℝ) by positivity]
  have hb : 0 ≤ ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
      √(((1 - √((k : ℝ) / l)) ^ 8)⁻¹ + 263 / √(l : ℝ)) := by positivity
  linarith [Real.sqrt_nonneg (4 * (((k : ℝ) / l) * √(1 + 2 / (k * l)) *
    √(((1 - √((k : ℝ) / l)) ^ 8)⁻¹ + 263 / √(l : ℝ))) *
    ((1 + √(2 * (k : ℝ) / l)) *
      (((1 - √((k : ℝ) / l)) ^ 2)⁻¹ + 10 / √(l : ℝ)) +
      ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
        √(((1 - √((k : ℝ) / l)) ^ 8)⁻¹ + 263 / √(l : ℝ))))]

/-! ### The early-truncated randomized SVD in expectation -/

/-- **The structural bound at the normalised sketch**, pointwise: for a frame $\mathbf{Z}$ of
$k \ge 1$ columns with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}
\rrbracket_k$, a fixed $\mathbf{\Omega}$, $c > 0$, $0 < a \le \min\{1,
c^2\sigma_{k-1}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^2\}$ and $0 < \theta < 1$, with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$ and $\mathbf{S} = c\mathbf{\Omega}$,
$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
((\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w)/(1 - \theta))a^{-1} +
(\chi^2/(\theta(1-\theta)))a^{-2}$, $w = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}
\mathbf{E}^{\mathsf{H}} - \mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$,
$\chi = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}$. The projector is
that of the unnormalised sketch, so no scale equivariance of the truncation is needed. -/
private theorem frobNorm_sub_earlyTruncatedRSVD_sq_le_inv {A : Matrix m n ℝ} {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : A * Z * Zᴴ = truncatedSVD A k) (X₀ : Matrix n l ℝ) {c a θ : ℝ} (hc : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (haσ : a ≤ c ^ 2 * singularValues (X₀ᴴ * Z) (k - 1) ^ 2)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2 ≤
      (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) *
          frobNorm ((A - truncatedSVD A k) * (c • X₀) * (c • X₀)ᴴ * (A - truncatedSVD A k)ᴴ -
            (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)) / (1 - θ) * a⁻¹ +
        frobNorm ((A - truncatedSVD A k) * (c • X₀) * (c • X₀)ᴴ * Z) ^ 2 / (θ * (1 - θ)) *
          a⁻¹ ^ 2 := by
  classical
  have hinj : IsSubspaceInjection (c • X₀)ᴴ Z a := by
    rw [hZ.isSubspaceInjection_iff_le_singularValues_sq (j := k - 1)
      (by rw [Fintype.card_fin]; omega), Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, singularValues_smul, Real.norm_of_nonneg hc.le, mul_pow]
    exact haσ
  have hP := isStarProjection_rangeProjector (truncatedSVD (A * X₀) k)
  have hPk : (rangeProjector (truncatedSVD (A * X₀) k)).rank ≤ k :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)
  have hopt : frobNorm (A * (c • X₀) - rangeProjector (truncatedSVD (A * X₀) k) *
      (A * (c • X₀))) ≤ frobNorm ((A - A * Z * Zᴴ) * (c • X₀)) := by
    have hr : (A * Z * Zᴴ * X₀).rank ≤ k :=
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
        (Matrix.rank_le_card_width _))).trans (by rw [Fintype.card_fin])
    simp only [Matrix.mul_smul, ← smul_sub, frobNorm_smul, Real.norm_of_nonneg hc.le]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    rw [rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
    exact frobNorm_sub_truncatedSVD_le_of_rank_le (A * X₀) hr
  have hEZ : (A - A * Z * Zᴴ) * Z = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), hZ.conjTranspose_mul_self, Matrix.mul_one,
      sub_self]
  have h := hinj.frobNorm_sub_mul_sq_le hZ ha ha1 hθ hθ1 hP hPk hopt
  rw [hEZ, sub_zero, hAZ] at h
  refine h.trans_eq ?_
  have h1θ : 1 - θ ≠ 0 := by linarith
  field_simp

/-- The head of a Gaussian test matrix in a frame $\mathbf{Z}$,
$\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$, is a standard Gaussian $\ell \times k$ matrix. -/
private theorem hasLaw_conjTranspose_mul_frame (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) :
    HasLaw (fun ω => (X ω)ᴴ * Z) (gaussianMatrix l (Fin k)) μ :=
  hasLaw_mul_const_of_hasLaw_gaussianMatrix (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX) hZ

/-- The clipped inverse power of the head is integrable for $2r + k \le \ell$. -/
private theorem integrable_min_one_inv_pow (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) {r : ℕ}
    (hr : 2 * r + k ≤ Fintype.card l) :
    Integrable (fun ω =>
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ r) μ :=
  integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_mul_frame hX hZ) (by rw [Fintype.card_fin]; omega)
    (by rwa [Fintype.card_fin])

/-- The clipped inverse of the head is a measurable function of the head. -/
private theorem measurable_min_one_inv {k : ℕ} (L : ℝ) :
    Measurable fun H : Matrix (Fin k) l ℝ => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹ :=
  (measurable_const.min ((((measurable_singularValues (k - 1)).comp
    (continuous_id.matrix_conjTranspose.measurable)).pow_const 2).div_const L)).inv

/-- The tail–tail term of the structural bound in expectation: with
$w = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$, $\mathbf{S} = \ell^{-1/2}\mathbf{\Omega}$, a
function of the tail block $\mathbf{V}^{\mathsf{H}}\mathbf{\Omega}$, and $u$ the clipped inverse of
the head, independent of it, $\mathbb{E}[wu] = \mathbb{E}w\,\mathbb{E}u \le
\sqrt{2/\ell}\,\|\mathbf{E}\|_{\mathsf{F}}^2\,\mathbb{E}u$ (approximate matrix multiplication at
$p = 2$). -/
private theorem integral_frobNorm_mul_inv_le {q : Type*} [Fintype q] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k)
    (hkl : 2 + k ≤ Fintype.card l) {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ}
    (hZ : HasOrthonormalCols Z) (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0)
    {E : Matrix m n ℝ} (hEV : E * V * Vᴴ = E) :
    Integrable (fun ω => frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Eᴴ - E * Eᴴ) *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹) μ ∧
    ∫ ω, frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Eᴴ - E * Eᴴ) *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ ≤
      √(2 / Fintype.card l) * frobNorm E ^ 2 *
        ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ := by
  have := hX.isProbabilityMeasure
  have hl0 : 0 < Fintype.card l := by omega
  have : Nonempty l := Fintype.card_pos_iff.1 hl0
  set L := (Fintype.card l : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast hl0
  set c := (√L)⁻¹ with hc
  set U : Matrix (Fin k) l ℝ → ℝ := fun H => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹
  set W : Matrix q l ℝ → ℝ := fun G =>
    frobNorm ((E * V) * (c • G) * ((E * V) * (c • G))ᴴ - E * Eᴴ)
  have hU : Measurable U := measurable_min_one_inv L
  have hW : Measurable W := by
    have hSG : Measurable fun G : Matrix q l ℝ => (E * V) * (c • G) :=
      measurable_const.matrix_mul (measurable_id.const_smul c)
    exact measurable_frobNorm.comp ((hSG.matrix_mul
      ((continuous_id.matrix_conjTranspose.measurable).comp hSG)).matrix_sub measurable_const)
  have hw (ω : Ω) : frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Eᴴ - E * Eᴴ) = W (Vᴴ * X ω) := by
    have e : E * (c • X ω) = (E * V) * (c • (Vᴴ * X ω)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hEV]
    simp only [W]
    rw [← e, Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  have hu (ω : Ω) : (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ = U (Zᴴ * X ω) := by
    simp only [U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hVZ : Vᴴ * Z = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Vᴴ * Z), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hZV, Matrix.conjTranspose_zero]
  have hind : IndepFun (fun ω => W (Vᴴ * X ω)) (fun ω => U (Zᴴ * X ω)) μ :=
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV hZ hVZ).comp hW hU
  have hXm := hX.aemeasurable
  have hWm : AEMeasurable (fun ω => W (Vᴴ * X ω)) μ :=
    hW.comp_aemeasurable (measurable_const.matrix_mul measurable_id |>.comp_aemeasurable hXm)
  have hUm : AEMeasurable (fun ω => U (Zᴴ * X ω)) μ :=
    hU.comp_aemeasurable (measurable_const.matrix_mul measurable_id |>.comp_aemeasurable hXm)
  -- the second moment of `w`, by approximate matrix multiplication
  have hXt := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  have hJL := hasJLMoment_of_hasLaw_gaussianMatrix hXt (ε := 1) one_pos
  have hSm : AEMeasurable (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) μ :=
    hXt.aemeasurable.const_smul ((√(Fintype.card l : ℝ))⁻¹)
  have he (ω : Ω) : frobNorm (Eᴴᴴ * ((√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ)ᴴ *
      ((√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) * Eᴴ - Eᴴᴴ * Eᴴ) ^ (2 : ℝ) =
      W (Vᴴ * X ω) ^ 2 := by
    rw [← hw, Real.rpow_two]
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hc,
      hL]
  have hint2 := hJL.integrable_frobNorm_conjTranspose_mul_sub_rpow le_rfl hSm Eᴴ Eᴴ
  have hamm := hJL.integral_frobNorm_conjTranspose_mul_sub_rpow_le zero_le_one le_rfl hSm Eᴴ Eᴴ
  simp only [he] at hint2 hamm
  have hmem : MemLp (fun ω => W (Vᴴ * X ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).2 hint2
  have hWi : Integrable (fun ω => W (Vᴴ * X ω)) μ := hmem.integrable one_le_two
  have hUi : Integrable (fun ω => U (Zᴴ * X ω)) μ := by
    have h := integrable_min_one_inv_pow hX hk hZ (r := 1) (by omega)
    simp only [pow_one] at h
    exact h.congr (ae_of_all _ fun ω => hu ω)
  have hEw : ∫ ω, W (Vᴴ * X ω) ∂μ ≤ √(2 / L) * frobNorm E ^ 2 := by
    have hvar := variance_nonneg (fun ω => W (Vᴴ * X ω)) μ
    rw [variance_eq_sub hmem] at hvar
    simp only [Pi.pow_apply] at hvar
    have h2 : ∫ ω, W (Vᴴ * X ω) ^ 2 ∂μ ≤ (√(2 / L) * frobNorm E ^ 2) ^ 2 := by
      refine hamm.trans_eq ?_
      rw [frobNorm_conjTranspose, mul_pow, Real.sq_sqrt (by positivity), Real.rpow_two]
      ring
    have h0 : 0 ≤ ∫ ω, W (Vᴴ * X ω) ∂μ ∨ ∫ ω, W (Vᴴ * X ω) ∂μ < 0 := le_or_gt _ _
    rcases h0 with h0 | h0
    · exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 (by linarith)
    · exact h0.le.trans (by positivity)
  simp only [hw, hu]
  refine ⟨hind.integrable_mul hWi hUi, ?_⟩
  rw [hind.integral_fun_mul_eq_mul_integral hWm.aestronglyMeasurable hUm.aestronglyMeasurable]
  exact mul_le_mul_of_nonneg_right hEw (integral_nonneg fun ω => inv_nonneg.2
    (le_min zero_le_one (div_nonneg (sq_nonneg _) hL0.le)))

/-- The Gaussian-product identity of `integral_frobNorm_sq_mul_inv_sq_le`: for
$\mathbf{E}\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{E}$ and $u \ge 0$,
$\|\mathbf{E}(c\mathbf{Y})(c\mathbf{Y})^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}^2u^2 =
\|\mathbf{E}\mathbf{V}(\mathbf{V}^{\mathsf{H}}\mathbf{Y})\,c^2u\,
(\mathbf{Z}^{\mathsf{H}}\mathbf{Y})^{\mathsf{H}}\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_mul_smul_mul_sq_mul_sq {q r : Type*} [Fintype q] [Fintype r]
    {E : Matrix m n ℝ} {V : Matrix n q ℝ} (hEV : E * V * Vᴴ = E) (c : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (Y : Matrix n l ℝ) (Z : Matrix n r ℝ) :
    frobNorm (E * (c • Y) * (c • Y)ᴴ * Z) ^ 2 * u ^ 2 =
      frobNorm (E * V * (Vᴴ * Y) * ((c ^ 2 * u) • (Zᴴ * Y)ᴴ)) ^ 2 := by
  have e1 : E * (c • Y) * (c • Y)ᴴ * Z = c ^ 2 • ((E * V) * (Vᴴ * Y) * (Zᴴ * Y)ᴴ) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul,
      star_trivial]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, hEV]
    ring_nf
  rw [e1, Matrix.mul_smul, frobNorm_smul, frobNorm_smul, Real.norm_of_nonneg (sq_nonneg c),
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg c) hu)]
  ring

/-- A product of squares is integrable when both fourth powers are, by
$f^2g^2 \le (f^4 + g^4)/2$. -/
private theorem integrable_sq_mul_sq_of_integrable_pow_four {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable (fun ω => f ω ^ 2) μ)
    (hg : AEStronglyMeasurable (fun ω => g ω ^ 2) μ)
    (hf4 : Integrable (fun ω => f ω ^ 4) μ) (hg4 : Integrable (fun ω => g ω ^ 4) μ) :
    Integrable (fun ω => f ω ^ 2 * g ω ^ 2) μ := by
  refine ((hf4.add hg4).div_const 2).mono' (hf.mul hg) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  change f ω ^ 2 * g ω ^ 2 ≤ (f ω ^ 4 + g ω ^ 4) / 2
  nlinarith [sq_nonneg (f ω ^ 2 - g ω ^ 2)]

/-- The tail–head term of the structural bound in expectation: with
$\chi = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}$,
$\mathbf{S} = \ell^{-1/2}\mathbf{\Omega}$, and $u$ the clipped inverse of the head
$\mathbf{G}_1 = \mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$, conditionally on $\mathbf{G}_1$ the
matrix $\ell\,u\,\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}$ is a Gaussian product, and
$\mathbb{E}[\chi^2u^2] = \ell^{-2}\|\mathbf{E}\|_{\mathsf{F}}^2\,\mathbb{E}[u^2\|\mathbf{G}_1
\|_{\mathsf{F}}^2] \le \ell^{-2}\|\mathbf{E}\|_{\mathsf{F}}^2\sqrt{(k\ell)^2 + 2k\ell}\,
(\mathbb{E}u^4)^{1/2}$. -/
private theorem integral_frobNorm_sq_mul_inv_sq_le {q : Type*} [Fintype q] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k)
    (hkl : 8 + k ≤ Fintype.card l) {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ}
    (hZ : HasOrthonormalCols Z) (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0)
    {E : Matrix m n ℝ} (hEV : E * V * Vᴴ = E) :
    Integrable (fun ω => frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Z) ^ 2 *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 2) μ ∧
    ∫ ω, frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Z) ^ 2 *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 2 ∂μ ≤
      frobNorm E ^ 2 / (Fintype.card l : ℝ) ^ 2 *
        √(((k * Fintype.card l : ℕ) : ℝ) ^ 2 + 2 * ((k * Fintype.card l : ℕ) : ℝ)) *
        √(∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 4 ∂μ) := by
  have := hX.isProbabilityMeasure
  have hl0 : 0 < Fintype.card l := by omega
  set L := (Fintype.card l : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast hl0
  set c := (√L)⁻¹ with hc
  have hc2 : c ^ 2 = L⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hL0.le]
  set U : Matrix (Fin k) l ℝ → ℝ := fun H => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹
  have hU : Measurable U := measurable_min_one_inv L
  have hU0 (H : Matrix (Fin k) l ℝ) : 0 ≤ U H :=
    inv_nonneg.2 (le_min zero_le_one (div_nonneg (sq_nonneg _) hL0.le))
  have hu (ω : Ω) : (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ = U (Zᴴ * X ω) := by
    simp only [U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set T : Matrix (Fin k) l ℝ → Matrix l (Fin k) ℝ := fun H => (c ^ 2 * U H) • Hᴴ
  have hT : Measurable T :=
    (measurable_const.mul hU).smul continuous_id.matrix_conjTranspose.measurable
  have hG₁ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hZ
  have hG₂ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV
  have hind := indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hZ hV hZV
  have hEVn : frobNorm (E * V) = frobNorm E := by
    conv_rhs => rw [← hEV]
    exact (hV.frobNorm_mul_conjTranspose_right _).symm
  -- the identity with the Gaussian product
  have hid (ω : Ω) : frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Z) ^ 2 * U (Zᴴ * X ω) ^ 2 =
      frobNorm ((fun _ : Matrix (Fin k) l ℝ => E * V) (Zᴴ * X ω) * (Vᴴ * X ω) *
        T (Zᴴ * X ω)) ^ 2 :=
    frobNorm_mul_smul_mul_sq_mul_sq hEV c (hU0 _) (X ω) Z
  have hTn (H : Matrix (Fin k) l ℝ) :
      frobNorm (E * V) ^ 2 * frobNorm (T H) ^ 2 =
        frobNorm E ^ 2 * L⁻¹ ^ 2 * (U H ^ 2 * frobNorm H ^ 2) := by
    simp only [T, frobNorm_smul, frobNorm_conjTranspose, Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg c) (hU0 H)), hEVn, ← hc2]
    ring
  -- integrability
  have hG4i := integrable_frobNorm_pow_four_of_hasLaw_gaussianMatrix hG₁
  have hG4 := integral_frobNorm_pow_four_of_hasLaw_gaussianMatrix hG₁
  have hU4i : Integrable (fun ω => U (Zᴴ * X ω) ^ 4) μ :=
    (integrable_min_one_inv_pow hX hk hZ (r := 4) (by omega)).congr
      (ae_of_all _ fun ω => congrArg (· ^ 4) (hu ω))
  have hXm := hX.aemeasurable
  have hG₁m : AEMeasurable (fun ω => Zᴴ * X ω) μ :=
    (measurable_const.matrix_mul measurable_id).comp_aemeasurable hXm
  have hUm : AEStronglyMeasurable (fun ω => U (Zᴴ * X ω) ^ 2) μ :=
    ((hU.comp_aemeasurable hG₁m).pow_const 2).aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun ω => frobNorm (Zᴴ * X ω) ^ 2) μ :=
    ((measurable_frobNorm.comp_aemeasurable hG₁m).pow_const 2).aestronglyMeasurable
  have hprod : Integrable (fun ω => U (Zᴴ * X ω) ^ 2 * frobNorm (Zᴴ * X ω) ^ 2) μ :=
    integrable_sq_mul_sq_of_integrable_pow_four (f := fun ω => U (Zᴴ * X ω))
      (g := fun ω => frobNorm (Zᴴ * X ω)) hUm hFm hU4i hG4i
  have hR : Integrable (fun ω => frobNorm ((fun _ : Matrix (Fin k) l ℝ => E * V) (Zᴴ * X ω)) ^ 2 *
      frobNorm (T (Zᴴ * X ω)) ^ 2) μ := by
    simp only [hTn]
    exact hprod.const_mul _
  have hL' := (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hG₂ hG₁m
    hind measurable_const hT).2 hR
  have hval := integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun hG₂ hG₁m hind
    (S := fun _ : Matrix (Fin k) l ℝ => E * V) measurable_const hT
  simp only [hu, hid]
  refine ⟨hL', ?_⟩
  rw [hval]
  simp only [hTn]
  rw [integral_const_mul]
  -- Cauchy–Schwarz
  have hmem1 : MemLp (fun ω => U (Zᴴ * X ω) ^ 2) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num, memLp_two_iff_integrable_sq hUm]
    simpa only [← pow_mul] using hU4i
  have hmem2 : MemLp (fun ω => frobNorm (Zᴴ * X ω) ^ 2) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num, memLp_two_iff_integrable_sq hFm]
    simpa only [← pow_mul] using hG4i
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => sq_nonneg (U (Zᴴ * X ω))) (ae_of_all _ fun ω => sq_nonneg _) hmem1 hmem2
  simp only [Real.rpow_two, ← pow_mul, ← Real.sqrt_eq_rpow, Nat.reduceMul] at hCS
  rw [hG4, Fintype.card_fin] at hCS
  have hE0 : 0 ≤ frobNorm E ^ 2 * L⁻¹ ^ 2 := by positivity
  calc frobNorm E ^ 2 * L⁻¹ ^ 2 * ∫ ω, U (Zᴴ * X ω) ^ 2 * frobNorm (Zᴴ * X ω) ^ 2 ∂μ ≤
        frobNorm E ^ 2 * L⁻¹ ^ 2 * (√(∫ ω, U (Zᴴ * X ω) ^ 4 ∂μ) *
          √(((k * Fintype.card l : ℕ) : ℝ) ^ 2 + 2 * ((k * Fintype.card l : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hCS hE0
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow]; ring

/-- The clipped inverse moments of the head at $q = 1$ and $q = 4$, with the constants of
`NLAlib.gaussianClippedInvMomentConstant_one_le_10` and
`NLAlib.gaussianClippedInvMomentConstant_four_le_263` in place. -/
private theorem integral_min_one_inv_pow_le (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l)
    {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) :
    ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ ≤
        ((1 - √((k : ℝ) / Fintype.card l)) ^ 2)⁻¹ + 10 / √(Fintype.card l : ℝ) ∧
      ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 4 ∂μ ≤
        ((1 - √((k : ℝ) / Fintype.card l)) ^ 8)⁻¹ + 263 / √(Fintype.card l : ℝ) := by
  have hY := hasLaw_conjTranspose_mul_frame hX hZ
  have hk' : k - 1 + 1 = Fintype.card (Fin k) := by rw [Fintype.card_fin]; omega
  have hn : 100 * Fintype.card (Fin k) ≤ Fintype.card l := by rwa [Fintype.card_fin]
  have h1 := integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix hY hk' hn
    hl (q := 1) (by norm_num)
  have h4 := integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix hY hk' hn
    hl (q := 4) le_rfl
  simp only [pow_one, Fintype.card_fin, Nat.reduceMul] at h1 h4
  refine ⟨h1.trans ?_, h4.trans ?_⟩
  · gcongr
    exact gaussianClippedInvMomentConstant_one_le_10
  · gcongr
    exact gaussianClippedInvMomentConstant_four_le_263

/-- Assembly of the three Gaussian early-truncation moments with a free parameter. -/
private theorem add_le_earlyTruncatedRSVDYoungFactor_mul {k l : ℕ} (hk : 1 ≤ k)
    (hkl : 100 * k ≤ l) {θ e Iu Iu4 : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (he : 0 ≤ e)
    (hIu : Iu ≤ ((1 - √((k : ℝ) / l)) ^ 2)⁻¹ + 10 / √(l : ℝ))
    (hIu4 : Iu4 ≤ ((1 - √((k : ℝ) / l)) ^ 8)⁻¹ + 263 / √(l : ℝ)) :
    e / (1 - θ) * Iu +
        √(k : ℝ) / (1 - θ) * (√(2 / (l : ℝ)) * e * Iu) +
      1 / (θ * (1 - θ)) *
        (e / (l : ℝ) ^ 2 * √(((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ)) * √Iu4) ≤
      earlyTruncatedRSVDYoungFactor k l θ * e := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hd : 0 < 1 - θ := by linarith
  have hroot : √(((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ)) =
      k * l * √(1 + 2 / (k * l)) := by
    rw [show ((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ) =
      ((k : ℝ) * l) ^ 2 * (1 + 2 / (k * l)) by push_cast; field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have h2 : √(k : ℝ) * √(2 / (l : ℝ)) = √(2 * k / l) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]; congr 1; ring
  rw [hroot, earlyTruncatedRSVDYoungFactor_def]
  have heq : e / (1 - θ) * Iu +
      √(k : ℝ) / (1 - θ) * (√(2 / (l : ℝ)) * e * Iu) +
      1 / (θ * (1 - θ)) *
        (e / (l : ℝ) ^ 2 * (k * l * √(1 + 2 / (k * l))) * √Iu4) =
      ((1 + √(2 * k / l)) * Iu +
        ((k : ℝ) / l) * √(1 + 2 / (k * l)) * √Iu4 / θ) / (1 - θ) * e := by
    rw [← h2]
    field_simp
  rw [heq]
  gcongr

/-- The main case of the expectation bound, $1 \le k \le \lvert n \rvert$, in a frame
$\mathbf{Z}$ of the top-$k$ right singular subspace and its completion $\mathbf{V}$. -/
private theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_div_of_frame {q : Type*} [Fintype q]
    [DecidableEq q] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ} (hZ : HasOrthonormalCols Z)
    (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0) (hAZ : A * Z * Zᴴ = truncatedSVD A k)
    (hEV : (A - truncatedSVD A k) * V * Vᴴ = A - truncatedSVD A k) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      earlyTruncatedRSVDYoungFactor k (Fintype.card l) θ * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  have hL0 : (0 : ℝ) < Fintype.card l := by
    have : (900 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
    linarith
  set E := A - truncatedSVD A k
  set L := (Fintype.card l : ℝ)
  set y := √((k : ℝ) / L)
  set c := (√L)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hL0)
  have hc2 : c ^ 2 = L⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hL0.le]
  have hY := hasLaw_conjTranspose_mul_frame hX hZ
  have hσ : ∀ᵐ ω ∂μ, 0 < singularValues ((X ω)ᴴ * Z) (k - 1) := by
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with ω hω
    rw [singularValues_pos_iff, hω, Fintype.card_fin, min_eq_right (by omega)]
    omega
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ≤
      frobNorm E ^ 2 / (1 - θ) *
          (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ +
        √(k : ℝ) / (1 - θ) *
          (frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Eᴴ - E * Eᴴ) *
            (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹) +
        1 / (θ * (1 - θ)) *
          (frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Z) ^ 2 *
            (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ ^ 2) := by
    filter_upwards [hσ] with ω hσω
    have h := frobNorm_sub_earlyTruncatedRSVD_sq_le_inv hk hZ hAZ (X ω) hc0
      (a := min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))
      (lt_min one_pos (div_pos (pow_pos hσω 2) hL0)) (min_le_left _ _)
      (by rw [hc2, inv_mul_eq_div]; exact min_le_right _ _) hθ0 hθ1
    refine h.trans_eq ?_
    ring
  obtain ⟨hIu, hIu4⟩ := integral_min_one_inv_pow_le hX hk hkl hl hZ
  have hu1i := integrable_min_one_inv_pow hX hk hZ (r := 1) (by omega)
  simp only [pow_one] at hu1i
  obtain ⟨hwui, hwu⟩ := integral_frobNorm_mul_inv_le hX hk (by omega) hZ hV hZV hEV
  obtain ⟨hχui, hχu⟩ := integral_frobNorm_sq_mul_inv_sq_le hX hk (by omega) hZ hV hZV hEV
  have hRi := ((hu1i.const_mul (frobNorm E ^ 2 / (1 - θ))).add
    (hwui.const_mul (√(k : ℝ) / (1 - θ)))).add
      (hχui.const_mul (1 / (θ * (1 - θ))))
  refine (integral_mono_ae (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX.aemeasurable k)
    hRi hpt).trans ?_
  rw [integral_add' (hu1i.const_mul _ |>.add (hwui.const_mul _)) (hχui.const_mul _),
    integral_add' (hu1i.const_mul _) (hwui.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  refine le_trans ?_ (add_le_earlyTruncatedRSVDYoungFactor_mul hk hkl hθ0 hθ1
    (sq_nonneg (frobNorm E)) hIu
    hIu4)
  gcongr

/-- Early-truncated randomized SVD with a free Young parameter: let $\mathbf{\Omega}$ be
a standard Gaussian $n\times\ell$ matrix, $100k\le\ell$, $\ell\ge900$, and $0<\theta<1$.
Writing $T=\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, the expected error is
at present <!-- value earlyTruncatedRSVDYoungFactor k \ell \theta -->
$$
\mathbb{ E} \|\mathbf{ A} -\mathsf{earlyTruncatedRSVD} ( \mathbf{ A} ,\mathbf{ \Omega} ,k)
\|_{ \mathsf{ F} } ^2\le ( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{
\ell} ) + ( ( k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} + 263/\sqrt{
\ell} } ) /\theta) /( 1-\theta) T\,.
$$
No printed source. The structural early-truncation inequality is integrated using the
independent Gaussian head and tail blocks and the clipped inverse-head moment bounds. -/
theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_div_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {θ : ℝ}
    (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      earlyTruncatedRSVDYoungFactor k (Fintype.card l) θ *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) : earlyTruncatedRSVD A x 0 = 0 := by
      rw [earlyTruncatedRSVD, truncatedSVD_zero, rangeProjector_zero, Matrix.zero_mul]
    have hf : 1 ≤ earlyTruncatedRSVDYoungFactor 0 (Fintype.card l) θ := by
      rw [earlyTruncatedRSVDYoungFactor_def]
      simp only [Nat.cast_zero, mul_zero, zero_div, Real.sqrt_zero, sub_zero,
        one_pow, inv_one, zero_mul, add_zero, one_mul]
      apply (le_div_iff₀ (by linarith : 0 < 1 - θ)).2
      have : 0 ≤ 10 / √(Fintype.card l : ℝ) := by positivity
      linarith
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    exact le_mul_of_one_le_left (sq_nonneg _) hf
  by_cases hkn : Fintype.card n < k
  · have hr : A.rank ≤ k := A.rank_le_card_width.trans hkn.le
    have hE : A - truncatedSVD A k = 0 := by rw [truncatedSVD_of_rank_le A hr, sub_self]
    have hae : ∀ᵐ ω ∂μ, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 = 0 := by
      filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX (by omega)] with ω hω
      rw [earlyTruncatedRSVD_of_rank_le ((Matrix.rank_mul_le_left _ _).trans hr), hω, sub_self,
        frobNorm_zero]
      norm_num
    rw [integral_congr_ae hae, hE, frobNorm_zero]
    simp
  push Not at hkn
  obtain ⟨Z, V, hZ, hV, hZV, hAZ, hEV⟩ :=
    exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion
      (p := Fin k) (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
      (by simp only [Fintype.card_fin]; omega)
  exact integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_div_of_frame A hX hk hkl hl
    hθ0 hθ1 hZ hV hZV hAZ hEV

/-- **The expected error of early-truncated randomized SVD**: let $\mathbf{\Omega}$ be a standard
Gaussian $n\times\ell$ matrix, $100k\le\ell$ and $\ell\ge900$.
Writing $T=\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, its optimized error
bound is at present <!-- value earlyTruncatedRSVDFactor k \ell -->
$$
\mathbb{ E} \|\mathbf{ A} -\mathsf{earlyTruncatedRSVD} ( \mathbf{ A} ,\mathbf{ \Omega} ,k)
\|_{ \mathsf{ F} } ^2\le\bigl( ( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} + 10/\sqrt{
\ell} ) ) + 2( ( k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} +
263/\sqrt{ \ell} } ) + \sqrt{ 4( ( k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} )
^{ -8} + 263/\sqrt{ \ell} } ) ( ( ( 1+ \sqrt{ 2k/\ell} ) ( ( 1-\sqrt{ k/\ell} ) ^{ -2} +
10/\sqrt{ \ell} ) ) + ( ( k/\ell) \sqrt{ 1+ 2/( k\ell) } \sqrt{ ( 1-\sqrt{ k/\ell} ) ^{ -8} +
263/\sqrt{ \ell} } ) ) }\bigr) T\,.
$$
Every rank and shape is allowed, including a zero optimal residual. No printed source.
The free Young-parameter Gaussian estimate is optimized by scalar algebra.
Result: etrsvd -/
theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      earlyTruncatedRSVDFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  set T := frobNorm (A - truncatedSVD A k) ^ 2
  set a := (1 + √(2 * k / (Fintype.card l : ℝ))) *
    (((1 - √((k : ℝ) / Fintype.card l)) ^ 2)⁻¹ + 10 / √(Fintype.card l : ℝ))
  set b := ((k : ℝ) / Fintype.card l) * √(1 + 2 / (k * Fintype.card l)) *
    √(((1 - √((k : ℝ) / Fintype.card l)) ^ 8)⁻¹ + 263 / √(Fintype.card l : ℝ))
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hθ : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
        (a + b / θ) / (1 - θ) * T := by
    intro θ hθ0 hθ1
    simpa only [earlyTruncatedRSVDYoungFactor_def, a, b, T] using
      (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_div_of_hasLaw_gaussianMatrix
        A hX hkl hl hθ0 hθ1)
  rcases eq_or_lt_of_le (sq_nonneg (frobNorm (A - truncatedSVD A k))) with hT | hT
  · have hh := hθ (1 / 2) (by norm_num) (by norm_num)
    change 0 = T at hT
    rw [← hT, mul_zero] at hh ⊢
    exact hh
  · have hh := Real.le_add_sqrt_of_forall_le_div_one_sub ha hb (x :=
        (∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ) / T) ?_
    · rw [div_le_iff₀ hT] at hh
      simpa only [earlyTruncatedRSVDFactor_def, a, b, T] using hh
    · intro θ hθ0 hθ1
      exact (div_le_iff₀ hT).2 (hθ θ hθ0 hθ1)


/-- The optimized factor is at most $1+20\sqrt{k/\ell}$ for $k\ge1$ and $400k\le\ell$. -/
private theorem earlyTruncatedRSVDFactor_le_one_add_twenty_mul_sqrt {k l : ℕ}
    (hk : 1 ≤ k) (hkl : 400 * k ≤ l) :
    earlyTruncatedRSVDFactor k l ≤ 1 + 20 * √((k : ℝ) / l) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  set y := √((k : ℝ) / l)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyy : y ^ 2 = (k : ℝ) / l := Real.sq_sqrt (by positivity)
  have hy : y ≤ 1 / 20 := by
    apply Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hl0]
    have hc : (400 : ℝ) * k ≤ l := by exact_mod_cast hkl
    nlinarith
  have hd : 0 < 1 - y := by linarith
  have hs : 1 / √(l : ℝ) ≤ y := by
    have hh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hk1 hl0.le)
    simpa only [Real.sqrt_div zero_le_one, Real.sqrt_one] using hh
  have hi2 : ((1 - y) ^ 2)⁻¹ ≤ 400 / 361 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 20)
      (show (19 : ℝ) / 20 ≤ 1 - y by linarith) 2
    nlinarith
  have hi1 : (1 - y)⁻¹ ≤ 20 / 19 := by
    rw [inv_le_iff_one_le_mul₀ hd]
    linarith
  set a := (1 + √(2 * k / (l : ℝ))) * (((1 - y) ^ 2)⁻¹ + 10 / √(l : ℝ))
  set b := ((k : ℝ) / l) * √(1 + 2 / (k * l)) *
    √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ))
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hr2 : √(2 * k / (l : ℝ)) ≤ 1.415 * y := by
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_div_assoc]
    nlinarith
  have ha : a ≤ 1 + 14.44 * y := by
    have hupper : a ≤ (1 + 1.415 * y) * (((1 - y) ^ 2)⁻¹ + 10 * y) := by
      apply mul_le_mul (by linarith)
        (by rw [div_eq_mul_one_div]; nlinarith) (by positivity) (by positivity)
    have he : (1 + 1.415 * y) * (((1 - y) ^ 2)⁻¹ + 10 * y) =
        1 + y * ((1.415 + 1) * ((1 - y) ^ 2)⁻¹ + (1 - y)⁻¹ + 10 + 10 * 1.415 * y) := by
      field_simp
      ring
    rw [he] at hupper
    have hh : (1.415 + 1) * ((1 - y) ^ 2)⁻¹ + (1 - y)⁻¹ + 10 +
        10 * 1.415 * y ≤ 14.44 := by nlinarith
    nlinarith
  have hkl2 : 2 / ((k : ℝ) * l) ≤ 2 * y ^ 2 := by
    rw [hyy, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < k * l) hl0).2
    have hsq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsq hl0.le
    nlinarith
  have hs2 : √(1 + 2 / ((k : ℝ) * l)) ≤ 1.0025 := by
    apply Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    have hh := pow_le_pow_left₀ hy0 hy 2
    nlinarith
  have hi8 : ((1 - y) ^ 8)⁻¹ ≤ ((20 : ℝ) / 19) ^ 8 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 20)
      (show (19 : ℝ) / 20 ≤ 1 - y by linarith) 8
    nlinarith
  have hs8 : √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) ≤ 3.829 := by
    apply Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    rw [div_eq_mul_one_div]
    nlinarith
  have hb : b ≤ 3.84 * y ^ 2 := by
    have hh := mul_le_mul hs2 hs8 (Real.sqrt_nonneg _) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg y)
    dsimp only [b]
    rw [← hyy]
    nlinarith
  have hroot : √(4 * b * (a + b)) ≤ y * (5.56 - 7.68 * y) := by
    apply Real.sqrt_le_iff.2 ⟨by nlinarith, ?_⟩
    have hp : 4 * b * (a + b) ≤ 4 * (3.84 * y ^ 2) *
        (1 + 14.44 * y + 3.84 * y ^ 2) := by gcongr
    have hh := mul_nonneg (sq_nonneg y)
      (show 0 ≤ 15.5536 - 307.2 * y by linarith)
    nlinarith
  rw [earlyTruncatedRSVDFactor_def]
  change a + 2 * b + √(4 * b * (a + b)) ≤ 1 + 20 * y
  nlinarith

/-- The optimized factor is at most $1+\varepsilon$ if $400k\le\varepsilon^2\ell$,
$k\ge1$, and $0<\varepsilon\le1$. -/
private theorem earlyTruncatedRSVDFactor_le_one_add_of_four_hundred {k l : ℕ} {ε : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : 400 * (k : ℝ) ≤ ε ^ 2 * l) : earlyTruncatedRSVDFactor k l ≤ 1 + ε := by
  have hl0 : (0 : ℝ) < l := by
    by_contra h
    have hh : (l : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [hh, mul_zero] at hl
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkl : 400 * k ≤ l := by
    have he : ε ^ 2 ≤ 1 := by nlinarith
    have hh : (400 : ℝ) * k ≤ l := by nlinarith
    exact_mod_cast hh
  have hy : √((k : ℝ) / l) ≤ ε / 20 := by
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hl0]
    nlinarith
  have hh := earlyTruncatedRSVDFactor_le_one_add_twenty_mul_sqrt hk hkl
  linarith

/-- The early-truncation factor at $900k/\varepsilon^2$ is at most $1+\varepsilon$
for $k\ge1$ and $0<\varepsilon\le1$. -/
theorem earlyTruncatedRSVDFactor_le_one_add {k l : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * l) : earlyTruncatedRSVDFactor k l ≤ 1 + ε :=
  earlyTruncatedRSVDFactor_le_one_add_of_four_hundred hk hε hε1 (by nlinarith)

/-- The sufficient Gaussian width for early-truncated randomized SVD is at
present <!-- value earlyTruncatedRSVDRelativeErrorDim k \varepsilon -->
$\max\{900,400k/\varepsilon^2\}$.
The relative-error theorem assumes $0<\varepsilon\le1$; at $\varepsilon=0$ this total
expression equals $900$ by the inverse-of-zero convention. No printed source. -/
noncomputable irreducible_def earlyTruncatedRSVDRelativeErrorDim (k : ℕ) (ε : ℝ) : ℝ :=
  max 900 (400 * (k : ℝ) / ε ^ 2)

/-- The explicit value the documentation displays: the sufficient Gaussian width is at
most <!-- value earlyTruncatedRSVDRelativeErrorDim k \varepsilon -->
$\max\{900,400k/\varepsilon^2\}$ (at present an equality). -/
theorem earlyTruncatedRSVDRelativeErrorDim_le (k : ℕ) (ε : ℝ) :
    earlyTruncatedRSVDRelativeErrorDim k ε ≤ max 900 (400 * (k : ℝ) / ε ^ 2) := by
  rw [earlyTruncatedRSVDRelativeErrorDim_def]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Early-truncated randomized SVD reaches relative error** with standard Gaussian samples:
for $0<\varepsilon\le1$ and $\ell\ge\max\{900,400k/\varepsilon^2\}$, the expected squared
Frobenius error is at most $(1+\varepsilon)$ times the optimal squared error.
$$\mathbb E\|\mathbf A-\mathsf{earlyTruncatedRSVD}(\mathbf A,\mathbf\Omega,k)
\|_{\mathsf F}^2\le(1+\varepsilon)
\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\,.$$
No printed source.
Result: etrsvd -/
theorem
    integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_earlyTruncatedRSVDRelativeErrorDim_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : earlyTruncatedRSVDRelativeErrorDim k ε ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) : earlyTruncatedRSVD A x 0 = 0 := by
      rw [earlyTruncatedRSVD, truncatedSVD_zero, rangeProjector_zero, Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  rw [earlyTruncatedRSVDRelativeErrorDim_def] at hl
  have hl900 : 900 ≤ Fintype.card l := by
    exact_mod_cast (le_trans (le_max_left _ _) hl)
  have hs : 400 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l := by
    have hh := le_trans (le_max_right (900 : ℝ) _) hl
    rw [div_le_iff₀ (sq_pos_of_pos hε)] at hh
    nlinarith
  have hkl : 100 * k ≤ Fintype.card l := by
    have he : ε ^ 2 ≤ 1 := by nlinarith
    have hh : (100 : ℝ) * k ≤ Fintype.card l := by nlinarith
    exact_mod_cast hh
  exact (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix
    A hX hkl hl900).trans (mul_le_mul_of_nonneg_right
      (earlyTruncatedRSVDFactor_le_one_add_of_four_hundred hk hε hε1 hs) (sq_nonneg _))

/-- **The early-truncated randomized SVD reaches relative error $1 + \varepsilon$** with
$\ell \ge 900k/\varepsilon^2$ standard Gaussian samples, $0 < \varepsilon \le 1$:
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
with $\ell$ products with $\mathbf{A}$, at most $k$ with $\mathbf{A}^{\mathsf{H}}$, and output
rank at most $k$. Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`.
Proved without a literature source; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1].
Result: etrsvd -/
theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) : earlyTruncatedRSVD A x 0 = 0 := by
      rw [earlyTruncatedRSVD, truncatedSVD_zero, rangeProjector_zero, Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hl900 : (900 : ℝ) * k ≤ Fintype.card l := by nlinarith
  have hkl : 100 * k ≤ Fintype.card l := by
    have : (100 : ℝ) * k ≤ Fintype.card l := by linarith
    exact_mod_cast this
  have hl' : 900 ≤ Fintype.card l := by
    have : (900 : ℝ) ≤ Fintype.card l := by linarith
    exact_mod_cast this
  exact (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix A hX hkl hl').trans
    (mul_le_mul_of_nonneg_right (earlyTruncatedRSVDFactor_le_one_add hk hε hε1 hl) (sq_nonneg _))

/-- **$O(k/\varepsilon^2)$ samples suffice for the early-truncated randomized SVD**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test
matrix $\mathbf{\Omega}$, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon^2$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`; the
proof takes $C = 900$ and $\varepsilon_0 = 1$.
Asymptotic:
NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: etrsvd -/
theorem exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε ^ 2) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨900, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ μ A X k ε hX hε hε1 hl
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hl
  exact integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix A hX hε
    hε1 (by linarith)

end NLAlib
