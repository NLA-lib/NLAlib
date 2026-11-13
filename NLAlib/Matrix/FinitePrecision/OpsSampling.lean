/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsMachine

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

end NLAlib
