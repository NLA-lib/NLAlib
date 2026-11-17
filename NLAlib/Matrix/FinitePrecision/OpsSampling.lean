/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Matrix.FinitePrecision.Samples
public import NLAlib.Matrix.Norms.Spectral

/-!
# Mathematical samplers from the actual Ops scalar operations

The uniform sampler multiplies the stored scale by a rounded real seed. The Gaussian sampler
multiplies each rounded real Gaussian word by the stored square root of one half. An ideal
standard complex Gaussian already contains division by the exact square root of two, so its
real and imaginary parts are rescaled before the real-word rounding is applied.

These are mathematical functions of the same scalar machine as the program, rather than
arbitrary sampler parameters assumed to have been implemented. No old program interpretation or
scalar semantics is constructed.

## Main results

* `NLAlib.Ops.Machine.normalSample_div_sqrt_two`: the complex sampler equals the executed
  two-word scaling on its raw real Gaussian words.
* `NLAlib.Ops.StdModel.isUnifSampler_uniformSample`: the uniform accuracy contract follows
  from scalar multiplication, seed rounding, and multiplication's radius-preservation property.
* `NLAlib.Ops.StdModel.isNormalSampler_normalSample`: relative accuracy of the actual Gaussian
  normalization and scalar products, independently of the sample law.
* `NLAlib.Ops.StdModel.isAccurate_toFloatMachine`: the combined matrix-machine numerical
  interface, including explicit multiplication and QR accuracy assumptions.
* `NLAlib.Ops.StdModel.specNorm_perturbWords_sub_le`: the rounding of a Gaussian perturbation
  scaled by $\gamma/\sqrt N$ (`NLAlib.Ops.Machine.perturbWords`).
-/

@[expose] public section

namespace NLAlib

namespace Ops.Machine

variable {K : Type}

/-- The stored normalization word computed by the program, using its actual scalar machine. -/
def sqrtHalf (M : Ops.Machine K) : K := M.sqrt (M.div (M.lit 1) (M.lit 2))

/-- The actual uniform shift computation on a rounded ideal real seed. -/
def uniformSample (M : Ops.Machine K) (roundUnif : ℝ → K) (s : K) (v : ℝ) : K :=
  M.mul s (roundUnif v)

/-- Scale the two actual stored real Gaussian words by the program's stored normalization. -/
def normalWords (M : Ops.Machine K) (a b : K) : K × K :=
  (M.mul a M.sqrtHalf, M.mul b M.sqrtHalf)

/-- The sampler on an ideal standard complex Gaussian. Its components are already divided by
the exact square root of two, which is undone before rounding the raw real Gaussian words. -/
noncomputable def normalSample (M : Ops.Machine K) (roundGaussian : ℝ → K) (z : ℂ) : K × K :=
  M.normalWords (roundGaussian (√2 * z.re)) (roundGaussian (√2 * z.im))

/-- On an ideal complex sample formed from two raw standard real Gaussian values, the
mathematical sampler performs exactly the two scalar products executed on their rounded words. -/
theorem normalSample_div_sqrt_two (M : Ops.Machine K) (roundGaussian : ℝ → K) (a b : ℝ) :
    M.normalSample roundGaussian (⟨a / √2, b / √2⟩ : ℂ) =
      M.normalWords (roundGaussian a) (roundGaussian b) := by
  have htwo : (√2 : ℝ) ≠ 0 := by positivity
  have ha : √2 * (a / √2) = a := by field_simp
  have hb : √2 * (b / √2) = b := by field_simp
  simp only [normalSample, ha, hb]

/-- The mathematical machine's uniform sampler is the actual rounded seed multiplication. -/
theorem unif_toFloatMachine (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (roundUnif roundGaussian : ℝ → K)
    (s : K) (v : ℝ) :
    (M.toFloatMachine dec mm qr (M.uniformSample roundUnif) (M.normalSample roundGaussian)).unif
      s v = M.mul s (roundUnif v) := rfl

/-- The mathematical machine's complex sampler is the actual rounded two-word computation. -/
theorem normal_toFloatMachine (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (roundUnif roundGaussian : ℝ → K)
    (z : ℂ) :
    (M.toFloatMachine dec mm qr (M.uniformSample roundUnif) (M.normalSample roundGaussian)).normal
      z = M.normalWords (roundGaussian (√2 * z.re)) (roundGaussian (√2 * z.im)) := rfl

end Ops.Machine

namespace Ops.StdModel

variable {K : Type} {M : Ops.Machine K} {dec : K → ℝ} {u c : ℝ}

/-- The actual square-root-of-one-half word has relative normalization error at most
`(2+u)*u`, when literals one and two are exact and `u` is at most one tenth. Division and
square root are both charged by the standard scalar model. -/
theorem abs_mul_sqrtHalf_sub_one_le (h : Ops.StdModel u dec M) (hu : 0 ≤ u)
    (hu1 : u ≤ 1 / 10) (hlit : Ops.IsExactNatLit dec M 2) :
    |√2 * dec M.sqrtHalf - 1| ≤ (2 + u) * u := by
  have hone : dec (M.lit 1) = 1 := by simpa using hlit 1 (by omega)
  have htwo : dec (M.lit 2) = 2 := by simpa using hlit 2 le_rfl
  have hd := h.div (M.lit 1) (M.lit 2) (by rw [htwo]; norm_num)
  rw [hone, htwo] at hd
  norm_num at hd
  let x := dec (M.div (M.lit 1) (M.lit 2))
  have hx : 0 ≤ x := by have hb := abs_le.mp hd; dsimp only [x]; linarith [hb.1]
  let sigma := √2 * √x
  have hsigma0 : 0 ≤ sigma := mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg x)
  have hsigmaSq : sigma ^ 2 = 2 * x := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hx]
  have hsigma : |sigma - 1| ≤ u := by
    rw [abs_le]
    have hb := abs_le.mp hd
    change -(u * (1 / 2)) ≤ x - 1 / 2 ∧ x - 1 / 2 ≤ u * (1 / 2) at hb
    constructor <;> nlinarith [hb.1, hb.2]
  have hsqrt := h.sqrt (M.div (M.lit 1) (M.lit 2)) hx
  have hscale : |√2 * dec M.sqrtHalf - sigma| ≤ u * sigma := by
    calc |√2 * dec M.sqrtHalf - sigma| = |√2 * (dec M.sqrtHalf - √x)| := by
            congr 1
            dsimp only [sigma]
            ring
      _ = √2 * |dec M.sqrtHalf - √x| := by
            rw [abs_mul (√2) _, abs_of_nonneg (Real.sqrt_nonneg 2)]
      _ ≤ √2 * (u * √x) := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg 2)
      _ = u * sigma := by dsimp only [sigma]; ring
  calc |√2 * dec M.sqrtHalf - 1| ≤ |√2 * dec M.sqrtHalf - sigma| + |sigma - 1| :=
        abs_sub_le _ _ _
    _ ≤ u * sigma + u := add_le_add hscale hsigma
    _ ≤ (2 + u) * u := by have hb := (abs_le.mp hsigma).2; nlinarith

/-- A uniform seed rounded with relative error `c*u`, kept in the unit interval, and multiplied
by a scalar machine obeying the standard model gives sampler error `(c+1)*u`. The extra
radius-preservation assumption concerns multiplication itself, for every word of modulus at
most one; it does not assert an algorithm output or a successful execution. -/
theorem isUnifSampler_uniformSample (h : Ops.StdModel u dec M) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (roundUnif : ℝ → K)
    (hround : ∀ v : ℝ, |v| ≤ 1 → |dec (roundUnif v) - v| ≤ c * u * |v|)
    (hrange : ∀ v ∈ Set.Icc (-1 : ℝ) 1, dec (roundUnif v) ∈ Set.Icc (-1 : ℝ) 1)
    (hmul : ∀ x y : K, |dec y| ≤ 1 → |dec (M.mul x y)| ≤ |dec x|) :
    IsUnifSampler dec ((c + 1) * u) 0 (M.uniformSample roundUnif) := by
  intro s v hs hv
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  have hrabs : |dec (roundUnif v)| ≤ 1 := abs_le.mpr (hrange v hv)
  have hseed : |v - dec (roundUnif v)| ≤ c * u := by
    rw [abs_sub_comm]
    exact (hround v hvabs).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hvabs (mul_nonneg hc hu))
  have hproduct : |dec s * dec (roundUnif v)| ≤ dec s := by
    rw [abs_mul, abs_of_nonneg hs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrabs hs
  have herr := h.mul s (roundUnif v)
  have hsplit := abs_sub_le (dec s * v) (dec s * dec (roundUnif v))
    (dec (M.uniformSample roundUnif s v))
  have hfirst : |dec s * v - dec s * dec (roundUnif v)| ≤ dec s * (c * u) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hseed hs
  refine ⟨by simpa only [Ops.Machine.uniformSample, abs_of_nonneg hs] using hmul s _ hrabs, ?_⟩
  rw [max_eq_left hs]
  dsimp only [Ops.Machine.uniformSample] at hsplit ⊢
  rw [abs_sub_comm (dec s * dec (roundUnif v))] at hsplit
  nlinarith [mul_le_mul_of_nonneg_left hproduct hu]

/-- A rounded real Gaussian word multiplied by the actual normalization word approximates its
ideal complex component with relative error `2*(c+3)*u`. The normalization error is stated on
that actual word, independently of any distribution assumption. -/
theorem abs_sub_mul_sqrtHalf_le (h : Ops.StdModel u dec M) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hcu : (c + 3) * u ≤ 1 / 10) {Ω : ℝ} (roundGaussian : ℝ → K)
    (hround : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec (roundGaussian x) - x| ≤ c * u * |x|)
    (hnorm : |√2 * dec M.sqrtHalf - 1| ≤ (2 + u) * u) (w : ℝ)
    (hw : |√2 * w| ≤ 2 * Ω) :
    |w - dec (M.mul (roundGaussian (√2 * w)) M.sqrtHalf)| ≤ 2 * ((c + 3) * u) * |w| := by
  have htwo : (0 : ℝ) < √2 := by positivity
  have hu1 : u ≤ 1 / 10 := by nlinarith
  let q := dec (roundGaussian (√2 * w)) / √2
  let s := √2 * dec M.sqrtHalf
  have hq : |q - w| ≤ c * u * |w| := by
    apply (mul_le_mul_iff_right₀ htwo).mp
    have hscale : √2 * |q - w| = |dec (roundGaussian (√2 * w)) - √2 * w| := by
      have heq : √2 * (q - w) = dec (roundGaussian (√2 * w)) - √2 * w := by
        dsimp only [q]
        field_simp
      rw [← heq, abs_mul (√2) (q - w), abs_of_pos htwo]
    rw [hscale]
    have hr := hround (√2 * w) hw
    rw [abs_mul, abs_of_pos htwo] at hr
    nlinarith
  have hqabs : |q| ≤ (1 + c * u) * |w| := by
    have ht := abs_add_le (q - w) w
    rw [sub_add_cancel] at ht
    nlinarith
  change |s - 1| ≤ (2 + u) * u at hnorm
  have hsabs : |s| ≤ (1 + u) ^ 2 := by
    have ht : |s| ≤ |s - 1| + 1 := by
      simpa only [sub_add_cancel, abs_one] using abs_add_le (s - 1) 1
    nlinarith
  have htarget : dec (roundGaussian (√2 * w)) * dec M.sqrtHalf = q * s := by
    dsimp only [q, s]
    field_simp
  have hprod : |q * s - w| ≤ (c * u * (1 + u) ^ 2 + (2 + u) * u) * |w| := by
    have hdecomp : q * s - w = (q - w) * s + w * (s - 1) := by ring
    have h1 := mul_le_mul hq hsabs (abs_nonneg s) (by positivity : 0 ≤ c * u * |w|)
    have h2 := mul_le_mul_of_nonneg_left hnorm (abs_nonneg w)
    calc |q * s - w| = |(q - w) * s + w * (s - 1)| := congrArg abs hdecomp
      _ ≤ |(q - w) * s| + |w * (s - 1)| := abs_add_le _ _
      _ = |q - w| * |s| + |w| * |s - 1| := by
            rw [abs_mul (q - w) s, abs_mul w (s - 1)]
      _ ≤ c * u * |w| * (1 + u) ^ 2 + |w| * ((2 + u) * u) := add_le_add h1 h2
      _ = (c * u * (1 + u) ^ 2 + (2 + u) * u) * |w| := by ring
  have hr := h.mul (roundGaussian (√2 * w)) M.sqrtHalf
  rw [htarget] at hr
  have hprodabs : |q * s| ≤ ((1 + c * u) * (1 + u) ^ 2) * |w| := by
    rw [abs_mul q s]
    nlinarith [mul_le_mul hqabs hsabs (abs_nonneg s)
      (by positivity : 0 ≤ (1 + c * u) * |w|)]
  have htotal : |w - dec (M.mul (roundGaussian (√2 * w)) M.sqrtHalf)| ≤
      ((1 + c * u) * (1 + u) ^ 3 - 1) * |w| := by
    have ht := abs_sub_le w (q * s) (dec (M.mul (roundGaussian (√2 * w)) M.sqrtHalf))
    rw [abs_sub_comm w (q * s),
      abs_sub_comm (q * s) (dec (M.mul (roundGaussian (√2 * w)) M.sqrtHalf))] at ht
    nlinarith [mul_le_mul_of_nonneg_left hprodabs hu]
  have hpoly : (1 + c * u) * (1 + u) ^ 3 - 1 ≤ 2 * ((c + 3) * u) := by
    have hrest : 0 ≤ c * u * (1 - 3 * u - 3 * u ^ 2 - u ^ 3) :=
      mul_nonneg (mul_nonneg hc hu) (by nlinarith)
    nlinarith [mul_nonneg hu (show (0 : ℝ) ≤ 3 - 3 * u - u ^ 2 by nlinarith)]
  exact htotal.trans (mul_le_mul_of_nonneg_right hpoly (abs_nonneg w))

/-- The actual Gaussian sampler meets the complex relative-error contract with constant
`2*(c+3)` at zero floor. Raw real seed rounding has relative error `c*u` in the stated range;
the scalar machine satisfies the standard model, literals one and two are exact, and
`(c+3)*u` is at most one tenth. The probability law of the seeds is a separate theorem. -/
theorem isNormalSampler_normalSample (h : Ops.StdModel u dec M) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hcu : (c + 3) * u ≤ 1 / 10) (hlit : Ops.IsExactNatLit dec M 2) {Ω : ℝ}
    (roundGaussian : ℝ → K)
    (hround : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec (roundGaussian x) - x| ≤ c * u * |x|) :
    IsNormalSampler (decodeComplex dec) u (2 * (c + 3)) 0 Ω (M.normalSample roundGaussian) := by
  have hnorm := h.abs_mul_sqrtHalf_sub_one_le hu (by nlinarith) hlit
  intro z hz
  have hΩ : 0 ≤ Ω := (norm_nonneg z).trans hz
  have hscale (x : ℝ) (hx : |x| ≤ ‖z‖) : |√2 * x| ≤ 2 * Ω := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have htwo : √2 ≤ (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [mul_le_mul_of_nonneg_left (hx.trans hz) (Real.sqrt_nonneg 2)]
  have er := h.abs_sub_mul_sqrtHalf_le hu hc hcu roundGaussian hround hnorm z.re
    (hscale _ (Complex.abs_re_le_norm z))
  have ei := h.abs_sub_mul_sqrtHalf_le hu hc hcu roundGaussian hround hnorm z.im
    (hscale _ (Complex.abs_im_le_norm z))
  let r := M.mul (roundGaussian (√2 * z.re)) M.sqrtHalf
  let s := M.mul (roundGaussian (√2 * z.im)) M.sqrtHalf
  let A := (2 * (c + 3)) * u
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hreal : (z.re - dec r) ^ 2 ≤ (A * z.re) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_of_nonneg hA]
    simpa only [A, mul_assoc] using er
  have himag : (z.im - dec s) ^ 2 ≤ (A * z.im) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_of_nonneg hA]
    simpa only [A, mul_assoc] using ei
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hd : ‖z - (⟨dec r, dec s⟩ : ℂ)‖ ^ 2 =
      (z.re - dec r) ^ 2 + (z.im - dec s) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hbound : ‖z - (⟨dec r, dec s⟩ : ℂ)‖ ≤ A * ‖z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg z))).mp
    rw [hd]
    calc (z.re - dec r) ^ 2 + (z.im - dec s) ^ 2 ≤ (A * z.re) ^ 2 + (A * z.im) ^ 2 :=
          add_le_add hreal himag
      _ = (A * ‖z‖) ^ 2 := by rw [mul_pow A ‖z‖, hn]; ring
  rw [max_eq_left (norm_nonneg z)]
  exact hbound

/-- The actual scalar functions and implemented samplers satisfy the full mathematical
matrix-machine accuracy interface. The common allowance includes uniform seed rounding;
matrix multiplication and QR must satisfy their numerical contracts at that same allowance.
Measurability and the ideal sample law remain separate from numerical accuracy. -/
theorem isAccurate_toFloatMachine (h : Ops.StdModel u dec M) (hu : 0 ≤ u)
    {cU cG Ω : ℝ} (hcU : 0 ≤ cU) (hcG : 0 ≤ cG)
    (hsmall : (cG + 3) * u ≤ 1 / 10) (hlit : Ops.IsExactNatLit dec M 2)
    (roundUnif roundGaussian : ℝ → K)
    (hU : ∀ v : ℝ, |v| ≤ 1 → |dec (roundUnif v) - v| ≤ cU * u * |v|)
    (hUr : ∀ v ∈ Set.Icc (-1 : ℝ) 1, dec (roundUnif v) ∈ Set.Icc (-1 : ℝ) 1)
    (hmul : ∀ x y : K, |dec y| ≤ 1 → |dec (M.mul x y)| ≤ |dec x|)
    (hG : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec (roundGaussian x) - x| ≤ cG * u * |x|)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (μM μQ : ℕ → ℝ)
    (hmm : IsMatMulErr (decodeComplex dec) ((cU + 1) * u) 0 Ω μM mm)
    (hqr : IsQRErr (decodeComplex dec) ((cU + 1) * u) 0 Ω μQ qr) :
    (M.toFloatMachine dec mm qr (M.uniformSample roundUnif)
      (M.normalSample roundGaussian)).IsAccurate dec ((cU + 1) * u) 0 Ω μM μQ
        (2 * (cG + 3)) := by
  have huv : u ≤ (cU + 1) * u := by nlinarith
  refine ⟨(h.mono huv).isArithAccurate_toFloatMachine
    (by simpa using hlit 1 (by omega)) mm qr _ _ μM hmm, hqr,
    h.isUnifSampler_uniformSample hu hcU roundUnif hU hUr hmul, ?_⟩
  intro z hz
  exact (h.isNormalSampler_normalSample hu hcG hsmall hlit roundGaussian hG z hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv (by positivity))
      (le_max_of_le_left (norm_nonneg z)))

end Ops.StdModel

/-- The matrix $\mathbf{A} + \gamma' \mathbf{G}$ computed by a machine from the real Gaussian
words $x$ (column-major, real and imaginary parts adjacent): the scale
$\gamma' = \mathrm{fl}(\gamma/\mathrm{fl}(\sqrt N))$, each word multiplied by the stored
$\sqrt{1/2}$ and by $\gamma'$, and added to the entry of $\mathbf{A}$, all rounded. -/
noncomputable def Ops.Machine.perturbWords (M : Ops.Machine ℝ) {N : ℕ} (γ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    ⟨M.add (A i j).re (M.mul (M.mul (x (2 * (j * N + i))) M.sqrtHalf)
        (M.div γ (M.sqrt (M.lit (N : ℚ))))),
      M.add (A i j).im (M.mul (M.mul (x (2 * (j * N + i) + 1)) M.sqrtHalf)
        (M.div γ (M.sqrt (M.lit (N : ℚ)))))⟩

section PerturbRounding

variable {M : Ops.Machine ℝ} {u : ℝ}

/-- $\lvert\sqrt y - 1\rvert \le \lvert y - 1\rvert$ for $y \ge 0$. -/
private theorem abs_sqrt_sub_one_le {y : ℝ} (hy : 0 ≤ y) : |√y - 1| ≤ |y - 1| := by
  have hs := Real.sqrt_nonneg y
  have e : y - 1 = (√y - 1) * (√y + 1) := by
    rw [show (√y - 1) * (√y + 1) = √y ^ 2 - 1 by ring, Real.sq_sqrt hy]
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ √y + 1)]
  nlinarith [abs_nonneg (√y - 1)]

/-- The stored $\sqrt{1/2}$ of a machine with the standard model and rounded literals, at
$0 \le \boldsymbol{u} \le 1/100$: $\lvert\sqrt2\,h - 1\rvert \le 7\boldsymbol{u}$. -/
private theorem abs_sqrt_two_mul_sqrtHalf_sub_one_le (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) : |√2 * M.sqrtHalf - 1| ≤ 7 * u := by
  have h1 : |M.lit 1 - 1| ≤ u := by simpa using hM.lit 1
  have h2 : |M.lit 2 - 2| ≤ 2 * u := by
    have := hM.lit 2
    simp only [id] at this
    rw [show ((2 : ℚ) : ℝ) = 2 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    linarith
  set a := M.lit 1
  set b := M.lit 2
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  have hb : 0 < b := by linarith
  have hb0 := hb.ne'
  have hd := hM.div a b hb.ne'
  simp only [id] at hd
  set q := M.div a b
  have hab : |2 * (a / b) - 1| ≤ 3 * u := by
    rw [show 2 * (a / b) - 1 = (2 * a - b) / b by field_simp, abs_div, abs_of_pos hb,
      div_le_iff₀ hb, abs_le]
    constructor <;> nlinarith
  have hab0 : 0 ≤ a / b := div_nonneg (by linarith) hb.le
  rw [abs_of_nonneg hab0] at hd
  have hq : |2 * q - 1| ≤ 5 * u := by
    obtain ⟨hl, hr⟩ := abs_le.mp hd
    obtain ⟨hl', hr'⟩ := abs_le.mp hab
    rw [abs_le]
    constructor <;> nlinarith
  have hq0 : 0 ≤ q := by obtain ⟨hl, hr⟩ := abs_le.mp hq; linarith
  have hs := hM.sqrt q hq0
  simp only [id] at hs
  have e2 : √2 * √q = √(2 * q) := (Real.sqrt_mul (by norm_num) q).symm
  have hsq := abs_sqrt_sub_one_le (by linarith : 0 ≤ 2 * q)
  have hsq1 : √(2 * q) ≤ 1 + 5 * u := by
    have := (abs_le.mp (hsq.trans hq)).2
    linarith
  change |√2 * M.sqrt q - 1| ≤ 7 * u
  have hsc : |√2 * M.sqrt q - √(2 * q)| ≤ u * √(2 * q) := by
    rw [← e2, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √2), mul_comm u,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hs) (by positivity)
  calc |√2 * M.sqrt q - 1| ≤ |√2 * M.sqrt q - √(2 * q)| + |√(2 * q) - 1| := abs_sub_le _ _ _
    _ ≤ u * (1 + 5 * u) + 5 * u :=
        add_le_add (hsc.trans (mul_le_mul_of_nonneg_left hsq1 hu0)) (hsq.trans hq)
    _ ≤ 7 * u := by nlinarith

/-- The computed scale $\mathrm{fl}(\gamma/\mathrm{fl}(\sqrt N))$ of a machine with the standard
model at $0 \le \boldsymbol{u} \le 1/100$, for $N \ge 1$ and $\gamma \ge 0$, is within
$4\boldsymbol{u}\gamma/\sqrt N$ of $\gamma/\sqrt N$. -/
private theorem abs_div_sqrt_lit_sub_le (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) {N : ℕ} (hN : 1 ≤ N) {γ : ℝ} (hγ : 0 ≤ γ) :
    |M.div γ (M.sqrt (M.lit (N : ℚ))) - γ / √(N : ℝ)| ≤ 4 * u * (γ / √(N : ℝ)) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0' : (N : ℝ) ≠ 0 := by positivity
  have hl := hM.lit (N : ℚ)
  simp only [id, Rat.cast_natCast] at hl
  rw [abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] at hl
  set ℓ := M.lit (N : ℚ)
  obtain ⟨hll, hlr⟩ := abs_le.mp hl
  have hℓ0 : 0 ≤ ℓ := by nlinarith
  have hs := hM.sqrt ℓ hℓ0
  simp only [id] at hs
  set s := M.sqrt ℓ
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hr : |ℓ / N - 1| ≤ u := by
    rw [show ℓ / N - 1 = (ℓ - N) / N by field_simp, abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < N), div_le_iff₀ (by linarith)]
    exact hl
  have hr0 : 0 ≤ ℓ / N := div_nonneg hℓ0 (by linarith)
  have hρ := (abs_sqrt_sub_one_le hr0).trans hr
  set ρ := √(ℓ / N)
  have eρ : √ℓ = ρ * √(N : ℝ) := by
    rw [← Real.sqrt_mul hr0, div_mul_cancel₀ _ hN0']
  obtain ⟨hρl, hρr⟩ := abs_le.mp hρ
  obtain ⟨hsl, hsr⟩ := abs_le.mp hs
  rw [eρ] at hsl hsr
  set t := s / √(N : ℝ)
  have es : s = t * √(N : ℝ) := by simp only [t]; field_simp
  rw [es] at hsl hsr
  have htl : ρ * (1 - u) ≤ t := by
    have : ρ * (1 - u) * √(N : ℝ) ≤ t * √(N : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right this hsN
  have htr : t ≤ ρ * (1 + u) := by
    have : t * √(N : ℝ) ≤ ρ * (1 + u) * √(N : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right this hsN
  have ht : |t - 1| ≤ 21 / 10 * u := by
    rw [abs_le]
    constructor <;> nlinarith
  have ht0 : 0 < t := by nlinarith
  have hs0 : 0 < s := by rw [es]; positivity
  have hd := hM.div γ s hs0.ne'
  simp only [id] at hd
  set β := γ / √(N : ℝ)
  have hβ : 0 ≤ β := div_nonneg hγ hsN.le
  have eγ : γ / s = β / t := by
    rw [es]
    simp only [β]
    field_simp
  rw [eγ, abs_of_nonneg (div_nonneg hβ ht0.le)] at hd
  have hbt : |β / t - β| ≤ 22 / 10 * u * β := by
    rw [show β / t - β = β * (1 - t) / t by field_simp, abs_div, abs_mul, abs_of_nonneg hβ,
      abs_of_pos ht0, div_le_iff₀ ht0, abs_sub_comm]
    nlinarith [mul_le_mul_of_nonneg_left ht hβ,
      mul_nonneg (mul_nonneg hβ hu0) (by nlinarith : (0 : ℝ) ≤ t - 979 / 1000)]
  have hbt' : β / t ≤ β + 22 / 10 * u * β := by
    have := (abs_le.mp hbt).2
    linarith
  calc |M.div γ s - β| ≤ |M.div γ s - β / t| + |β / t - β| := abs_sub_le _ _ _
    _ ≤ u * (β + 22 / 10 * u * β) + 22 / 10 * u * β :=
        add_le_add (hd.trans (mul_le_mul_of_nonneg_left hbt' hu0)) hbt
    _ ≤ 4 * u * β := by
        nlinarith [mul_nonneg (mul_nonneg hu0 hβ) (by linarith : (0 : ℝ) ≤ 1 / 100 - u)]

/-- One rounded component $\mathrm{fl}(a + \mathrm{fl}(\mathrm{fl}(w h) g))$ against
$a + \beta w/\sqrt2$, for $\lvert\sqrt2 h - 1\rvert \le 6\boldsymbol{u}$ and
$\lvert g - \beta\rvert \le 4\boldsymbol{u}\beta$. -/
private theorem abs_add_mul_mul_sub_le (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) {a w h g β : ℝ} (hβ : 0 ≤ β) (hh : |√2 * h - 1| ≤ 7 * u)
    (hg : |g - β| ≤ 4 * u * β) :
    |M.add a (M.mul (M.mul w h) g) - (a + β * (w / √2))| ≤
      u * |a| + 18 * u * |β * (w / √2)| := by
  have hsmall : (0 : ℝ) ≤ 1 / 100 - u := by linarith
  have hm1 := hM.mul w h
  have hm2 := hM.mul (M.mul w h) g
  have ha := hM.add a (M.mul (M.mul w h) g)
  simp only [id] at hm1 hm2 ha
  set m1 := M.mul w h
  set m2 := M.mul m1 g
  set W := |w / √2|
  have hW : 0 ≤ W := abs_nonneg _
  have ewh : w * h = w / √2 * (√2 * h) := by field_simp
  have hsh : |√2 * h| ≤ 1 + 7 * u := by
    have := abs_sub_abs_le_abs_sub (√2 * h) 1
    rw [abs_one] at this
    linarith
  have hwh : |w * h| ≤ W * (1 + 7 * u) := by
    rw [ewh, abs_mul]
    exact mul_le_mul_of_nonneg_left hsh hW
  have hm1' : |m1 - w / √2| ≤ 9 * u * W := by
    have e : w * h - w / √2 = w / √2 * (√2 * h - 1) := by rw [ewh]; ring
    calc |m1 - w / √2| ≤ |m1 - w * h| + |w * h - w / √2| := abs_sub_le _ _ _
      _ ≤ u * (W * (1 + 7 * u)) + W * (7 * u) := by
          refine add_le_add (hm1.trans (mul_le_mul_of_nonneg_left hwh hu0)) ?_
          rw [e, abs_mul]
          exact mul_le_mul_of_nonneg_left hh hW
      _ ≤ 9 * u * W := by nlinarith [mul_nonneg (mul_nonneg hu0 hsmall) hW, mul_nonneg hu0 hW]
  have hm1a : |m1| ≤ W * (1 + 9 * u) := by
    have := abs_sub_abs_le_abs_sub m1 (w / √2)
    nlinarith
  have hga : |g| ≤ β * (1 + 4 * u) := by
    have := abs_sub_abs_le_abs_sub g β
    rw [abs_of_nonneg hβ] at this
    nlinarith
  have hp : |m1 * g - β * (w / √2)| ≤ 14 * u * (W * β) := by
    have e : m1 * g - β * (w / √2) = m1 * (g - β) + β * (m1 - w / √2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hβ]
    have h1 := mul_le_mul hm1a hg (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hm1' hβ
    nlinarith [mul_nonneg (mul_nonneg hu0 hsmall) (mul_nonneg hW hβ),
      mul_nonneg hu0 (mul_nonneg hW hβ)]
  have hm1g : |m1 * g| ≤ W * β * (1 + 14 * u) := by
    have := abs_sub_abs_le_abs_sub (m1 * g) (β * (w / √2))
    rw [abs_mul β, abs_of_nonneg hβ] at this
    nlinarith
  have hp2 : |m2 - β * (w / √2)| ≤ 16 * u * (W * β) := by
    calc |m2 - β * (w / √2)| ≤ |m2 - m1 * g| + |m1 * g - β * (w / √2)| := abs_sub_le _ _ _
      _ ≤ u * (W * β * (1 + 14 * u)) + 14 * u * (W * β) :=
          add_le_add (hm2.trans (mul_le_mul_of_nonneg_left hm1g hu0)) hp
      _ ≤ 16 * u * (W * β) := by
          nlinarith [mul_nonneg (mul_nonneg hu0 hsmall) (mul_nonneg hW hβ),
            mul_nonneg hu0 (mul_nonneg hW hβ)]
  have hWβ : |β * (w / √2)| = W * β := by rw [abs_mul, abs_of_nonneg hβ, mul_comm]
  rw [hWβ]
  have hsum : |a + m2| ≤ |a| + W * β * (1 + 16 * u) := by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have := abs_sub_abs_le_abs_sub m2 (β * (w / √2))
    rw [hWβ] at this
    nlinarith
  calc |M.add a m2 - (a + β * (w / √2))|
      ≤ |M.add a m2 - (a + m2)| + |m2 - β * (w / √2)| := by
        have := abs_sub_le (M.add a m2) (a + m2) (a + β * (w / √2))
        rwa [show a + m2 - (a + β * (w / √2)) = m2 - β * (w / √2) by ring] at this
    _ ≤ u * (|a| + W * β * (1 + 16 * u)) + 16 * u * (W * β) :=
        add_le_add (ha.trans (mul_le_mul_of_nonneg_left hsum hu0)) hp2
    _ ≤ u * |a| + 18 * u * (W * β) := by
        nlinarith [mul_nonneg (mul_nonneg hu0 hsmall) (mul_nonneg hW hβ),
      mul_nonneg hu0 (mul_nonneg hW hβ)]

/-- A complex number whose components are bounded by sums of nonnegative pieces is bounded by the
sum of the norms of the pieces. -/
private theorem norm_le_of_abs_re_im_le {z a b : ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hre : |z.re| ≤ r * |a.re| + s * |b.re|) (him : |z.im| ≤ r * |a.im| + s * |b.im|) :
    ‖z‖ ≤ r * ‖a‖ + s * ‖b‖ := by
  let w : ℂ := ⟨r * |a.re| + s * |b.re|, r * |a.im| + s * |b.im|⟩
  have hzw : ‖z‖ ≤ ‖w‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp only [Complex.normSq_apply, w]
    have h1 := mul_self_le_mul_self (abs_nonneg _) hre
    have h2 := mul_self_le_mul_self (abs_nonneg _) him
    rw [abs_mul_abs_self] at h1 h2
    linarith
  have ew : w = (r : ℂ) * ⟨|a.re|, |a.im|⟩ + (s : ℂ) * ⟨|b.re|, |b.im|⟩ := by
    apply Complex.ext <;> simp [w]
  have hn : ∀ c : ℂ, ‖(⟨|c.re|, |c.im|⟩ : ℂ)‖ = ‖c‖ := fun c => by
    rw [Complex.norm_def, Complex.norm_def]
    simp only [Complex.normSq_apply, abs_mul_abs_self]
  refine hzw.trans ?_
  rw [ew]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hn, hn, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr,
    Real.norm_of_nonneg hs]

/-- The Frobenius norm is bounded by entrywise domination in norm. -/
private theorem frobNorm_le_mul_add_mul_of_norm_apply_le {N : ℕ} {E A B : Matrix (Fin N) (Fin N) ℂ}
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (h : ∀ i j, ‖E i j‖ ≤ r * ‖A i j‖ + s * ‖B i j‖) :
    frobNorm E ≤ r * frobNorm A + s * frobNorm B := by
  let F : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => (‖A i j‖ : ℂ)
  let G : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => (‖B i j‖ : ℂ)
  have hF : frobNorm F = frobNorm A := by
    have h1 := frobNorm_sq_eq_sum F
    have h2 := frobNorm_sq_eq_sum A
    simp only [F, Matrix.of_apply, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at h1
    rw [← h2] at h1
    exact (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp h1
  have hG : frobNorm G = frobNorm B := by
    have h1 := frobNorm_sq_eq_sum G
    have h2 := frobNorm_sq_eq_sum B
    simp only [G, Matrix.of_apply, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at h1
    rw [← h2] at h1
    exact (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp h1
  have hle : frobNorm E ≤ frobNorm ((r : ℂ) • F + (s : ℂ) • G) := by
    refine frobNorm_le_of_norm_apply_le fun i j => (h i j).trans (le_of_eq ?_)
    simp only [F, G, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  refine hle.trans ((frobNorm_add_le _ _).trans (le_of_eq ?_))
  rw [frobNorm_smul, frobNorm_smul, hF, hG, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hr, Real.norm_of_nonneg hs]

end PerturbRounding

/-- **The rounding of a scaled Gaussian perturbation** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], the perturbation step): on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1/100$, for $N \ge 1$, $\gamma \ge 0$, a complex $\mathbf{A}$ of order
$N$ and real words $x$, the computed $\widehat{\mathbf{A}}$ (`NLAlib.Ops.Machine.perturbWords`)
and the complex matrix $\mathbf{G}$ of the words (`NLAlib.Computation.tapeComplexMatrix`,
entries $(x_{2k} + i x_{2k+1})/\sqrt2$) satisfy
$$\Bigl\|\widehat{\mathbf{A}} - \Bigl(\mathbf{A} + \frac{\gamma}{\sqrt N}\mathbf{G}\Bigr)\Bigr\|_2
  \le 20N\boldsymbol{u}\Bigl(\|\mathbf{A}\|_2 + \frac{\gamma}{\sqrt N}\|\mathbf{G}\|_2\Bigr).$$ -/
theorem Ops.StdModel.specNorm_perturbWords_sub_le {M : Ops.Machine ℝ} {u : ℝ}
    (hM : Ops.StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N : ℕ} (hN : 1 ≤ N) {γ : ℝ}
    (hγ : 0 ≤ γ) (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) :
    specNorm (M.perturbWords γ A x -
        (A + ((γ / √(N : ℝ) : ℝ) : ℂ) • Computation.tapeComplexMatrix x N)) ≤
      20 * N * u * (specNorm A + γ / √(N : ℝ) * specNorm (Computation.tapeComplexMatrix x N)) := by
  set β := γ / √(N : ℝ)
  set G := Computation.tapeComplexMatrix x N
  have hβ : 0 ≤ β := div_nonneg hγ (Real.sqrt_nonneg _)
  have hh := abs_sqrt_two_mul_sqrtHalf_sub_one_le hM hu0 hu
  have hg := abs_div_sqrt_lit_sub_le hM hu0 hu hN hγ
  have hent : ∀ i j, ‖(M.perturbWords γ A x - (A + (β : ℂ) • G)) i j‖ ≤
      u * ‖A i j‖ + 18 * u * ‖((β : ℂ) • G) i j‖ := by
    intro i j
    have hidx : (j : ℕ) * N + i = i + N * j := by ring
    refine norm_le_of_abs_re_im_le hu0 (by positivity) ?_ ?_
    · simpa [Ops.Machine.perturbWords, G, Computation.tapeComplexMatrix, hidx] using
        abs_add_mul_mul_sub_le hM hu0 hu (a := (A i j).re) (w := x (2 * (i + N * j))) hβ hh hg
    · simpa [Ops.Machine.perturbWords, G, Computation.tapeComplexMatrix, hidx] using
        abs_add_mul_mul_sub_le hM hu0 hu (a := (A i j).im) (w := x (2 * (i + N * j) + 1)) hβ hh
          hg
  have hF := frobNorm_le_mul_add_mul_of_norm_apply_le hu0 (by positivity) hent
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : √(N : ℝ) ≤ N := by
    have h1 : 1 ≤ √(N : ℝ) := Real.one_le_sqrt.mpr hN1
    nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ N)]
  have hA := frobNorm_le_sqrt_card_mul_specNorm A
  have hP := frobNorm_le_sqrt_card_mul_specNorm ((β : ℂ) • G)
  rw [Fintype.card_fin] at hA hP
  rw [specNorm_smul, Complex.norm_real, Real.norm_of_nonneg hβ] at hP
  refine (specNorm_le_frobNorm _).trans (hF.trans ?_)
  have hAn := specNorm_nonneg A
  have hGn := mul_nonneg hβ (specNorm_nonneg G)
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  calc u * frobNorm A + 18 * u * frobNorm ((β : ℂ) • G)
      ≤ u * (√(N : ℝ) * specNorm A) + 18 * u * (√(N : ℝ) * (β * specNorm G)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hu0)
          (mul_le_mul_of_nonneg_left hP (by positivity))
    _ ≤ 20 * N * u * (specNorm A + β * specNorm G) := by
        nlinarith [mul_le_mul_of_nonneg_right hsq (mul_nonneg hu0 hAn),
          mul_le_mul_of_nonneg_right hsq (mul_nonneg hu0 hGn),
          mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (mul_nonneg hu0 hAn),
          mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (mul_nonneg hu0 hGn)]

end NLAlib
