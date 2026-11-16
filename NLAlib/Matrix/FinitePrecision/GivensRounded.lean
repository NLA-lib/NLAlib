/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Blas.Pair

/-!
# Rounded Givens rotations

The complex Givens rotation of the pair $(u, v)$ has the coefficients $c = \bar u / r$,
$s = \bar v / r$ with $r = \sqrt{\lvert u\rvert^2 + \lvert v\rvert^2}$ (`NLAlib.givensCoeffs`).
On a machine with the standard model of rounded arithmetic at the unit roundoff $\boldsymbol{u}$
(`NLAlib.Ops.StdModel`, with a rounded square root) this file bounds

* the computed coefficients: each within $4\boldsymbol{u}$ of the exact ones, relatively
  (`NLAlib.Ops.StdModel.norm_roundedGivensCoeffs_sub_le`);
* the computed complex linear combination $c x + s y$ of word pairs, as the operation core
  computes it (`NLAlib.Ops.Pair.linearWords`): within $5\boldsymbol{u}(\lvert c\rvert\lvert x\rvert
  + \lvert s\rvert\lvert y\rvert)$ (`NLAlib.Ops.StdModel.norm_linearWords_sub_le`);
* both computed outputs of the rotation of a pair, jointly: within $12\boldsymbol{u}$ of the exact
  rotation (`NLAlib.Ops.StdModel.norm_linearWords_rotation_sub_le`);
* a rotation of two rows (columns) of a matrix whose every column (row) pair is computed within
  $\eta$ of the exact rotation of the pair, relatively: within $2\eta\|\mathbf{A}\|_2$ in the
  spectral norm (`NLAlib.IsRoundedRowRotation.specNorm_sub_le`).

The last statement is the reusable rounded-kernel lemma: it turns a per-pair error, which is what
a program proof over a generic machine returns, into the spectral-norm error that
`NLAlib.IsPerturbedUnitarySimilar.of_specNorm_sub_le` consumes. Per two rows the error is
$O(\boldsymbol{u})\|\mathbf{A}\|_2$, so a sweep of $n$ rotations has backward error
$O(n\boldsymbol{u})$ (the analysis of [BanksGarzaVargasSrivastava2022, Lemma 3.5] has
$32n^{3/2}\boldsymbol{u}$). [Higham2002, Lemmas 19.7–19.8].

## Main definitions

* `NLAlib.roundedGivensCoeffs`: the coefficients computed by a machine, in a fixed instruction
  order.
* `NLAlib.IsRoundedRowRotation`, `NLAlib.IsRoundedColRotation`: a rotation computed pairwise
  within a relative error.
## Main results

* `NLAlib.exists_hasOrthonormalCols_rotateTo`: rotations taking $\mathbf{e}_N$ to a computed
  vector, as used by the random Hessenberg form of [BanksGarzaVargasSrivastava2025].
* `NLAlib.norm_toLp_sub_mulVec_le_sum`, `NLAlib.specNorm_sub_mul_mul_conjTranspose_le_sum`: errors
  along a chain of unitary steps add up.
* `NLAlib.exists_norm_conjTranspose_col_sub_le`, `NLAlib.specNorm_sub_rotateTo_le`: its vector and
  matrix parts.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-- The Givens coefficients computed by the machine `M` from the pair $(u, v)$, in this
instruction order: the squared radius as
$(u_1^2 + u_2^2) + (v_1^2 + v_2^2)$, its rounded square root, and, unless it is zero, the
rounded quotients of the conjugated components (negation is exact). The zero radius gives the
literals $(1, 0)$. -/
noncomputable def roundedGivensCoeffs (M : Machine ℝ) (u v : ℂ) : ℂ × ℂ :=
  let r := M.sqrt (M.add (M.add (M.mul u.re u.re) (M.mul u.im u.im))
    (M.add (M.mul v.re v.re) (M.mul v.im v.im)))
  if r = 0 then (⟨M.lit 1, M.lit 0⟩, ⟨M.lit 0, M.lit 0⟩)
  else (⟨M.div u.re r, M.div (M.neg u.im) r⟩, ⟨M.div v.re r, M.div (M.neg v.im) r⟩)

/-- One rounded addition of two approximations: the form of `stdModel_sub_combine` for `M.add`. -/
private lemma stdModel_add_combine {u : ℝ} {M : Machine ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    {a b S₁ S₂ T₁ T₂ e : ℝ} (h1 : |a - S₁| ≤ e * T₁) (h2 : |b - S₂| ≤ e * T₂)
    (hS₁ : |S₁| ≤ T₁) (hS₂ : |S₂| ≤ T₂) :
    |M.add a b - (S₁ + S₂)| ≤ ((1 + u) * (1 + e) - 1) * (T₁ + T₂) := by
  have h := hM.add a b
  simp only [id] at h
  have ha : |a| ≤ (1 + e) * T₁ := by
    have := abs_add_le S₁ (a - S₁)
    rw [add_sub_cancel] at this
    linarith
  have hb : |b| ≤ (1 + e) * T₂ := by
    have := abs_add_le S₂ (b - S₂)
    rw [add_sub_cancel] at this
    linarith
  have hab : |a + b| ≤ (1 + e) * (T₁ + T₂) := (abs_add_le a b).trans (by linarith)
  have h3 : |M.add a b - (S₁ + S₂)| ≤ |M.add a b - (a + b)| + |a - S₁| + |b - S₂| := by
    have := abs_add_three (M.add a b - (a + b)) (a - S₁) (b - S₂)
    have e3 : M.add a b - (S₁ + S₂) = (M.add a b - (a + b)) + (a - S₁) + (b - S₂) := by ring
    rw [e3]
    exact this
  have h4 : u * |a + b| ≤ u * ((1 + e) * (T₁ + T₂)) := mul_le_mul_of_nonneg_left hab hu
  nlinarith

/-- The coefficient $(1 + u)^3 - 1$ of three rounded operations lies in $[0, 3.04u]$. -/
private lemma rounded_coeff_bounds {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) :
    0 ≤ (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 ∧
      (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 ≤ 76 / 25 * u := by
  have hE : (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 = 3 * u + 3 * u ^ 2 + u ^ 3 := by ring
  rw [hE]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg hu (sub_nonneg.2 hu'), mul_nonneg (mul_nonneg hu hu) (sub_nonneg.2 hu')]

/-- The squared computed radius sum: three rounded operations per term of the squared norm. -/
private lemma rounded_radius_sub_le {u : ℝ} {M : Machine ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (x y : ℂ) :
    |M.add (M.add (M.mul x.re x.re) (M.mul x.im x.im)) (M.add (M.mul y.re y.re) (M.mul y.im y.im)) -
        (x.re * x.re + x.im * x.im + (y.re * y.re + y.im * y.im))| ≤
      ((1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1) *
        (x.re * x.re + x.im * x.im + (y.re * y.re + y.im * y.im)) := by
  have pr : ∀ p : ℝ, |M.mul p p - p * p| ≤ u * (p * p) := fun p => by
    have h := hM.mul p p
    simp only [id] at h
    rwa [abs_mul_self] at h
  have d1 := stdModel_add_combine hM hu (pr x.re) (pr x.im) (abs_mul_self _).le
    (abs_mul_self _).le
  have d2 := stdModel_add_combine hM hu (pr y.re) (pr y.im) (abs_mul_self _).le
    (abs_mul_self _).le
  exact stdModel_add_combine hM hu d1 d2
    (le_of_eq (abs_of_nonneg (add_nonneg (mul_self_nonneg x.re) (mul_self_nonneg x.im))))
    (le_of_eq (abs_of_nonneg (add_nonneg (mul_self_nonneg y.re) (mul_self_nonneg y.im))))

/-- Square root step: from a computed squared radius $\hat S$ with
$\lvert \hat S - S\rvert \le E S$, a computed root $\hat q$ with relative error $u$ has error at
most $13u/5$ times $\sqrt S$. -/
private lemma rounded_radius_le {E u S Sh qh : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (hE0 : 0 ≤ E)
    (hE : E ≤ 76 / 25 * u) (hS : 0 < S) (hSt : |Sh - S| ≤ E * S)
    (hq : |qh - √Sh| ≤ u * √Sh) : |qh - √S| ≤ 13 / 5 * u * √S := by
  have hE1 : E ≤ 19 / 625 := by nlinarith
  have h1E : 0 ≤ 1 - E := by linarith
  have hlt := abs_le.1 hSt
  have hSh : 0 ≤ Sh := by nlinarith [mul_nonneg h1E hS.le]
  have hq2 : √Sh ^ 2 = Sh := Real.sq_sqrt hSh
  have hr2 : √S ^ 2 = S := Real.sq_sqrt hS.le
  have hr0 : 0 < √S := Real.sqrt_pos.2 hS
  have hq0 : 0 ≤ √Sh := Real.sqrt_nonneg _
  generalize √Sh = q at *
  generalize √S = r at *
  have hlow : (1 - E) * r ≤ q := by
    refine (sq_le_sq₀ (mul_nonneg h1E hr0.le) hq0).1 ?_
    rw [hq2, mul_pow, hr2]
    nlinarith [mul_nonneg (mul_nonneg h1E hE0) (mul_nonneg hS.le hS.le)]
  have e : |q - r| * (q + r) = |Sh - S| := by
    rw [← hq2, ← hr2, ← abs_of_nonneg (add_nonneg hq0 hr0.le), ← abs_mul]
    congr 1
    ring
  have hD2 : |q - r| * (q + r) ≤ E * r ^ 2 := by rw [e, hr2]; exact hSt
  have h5 : (2 - E) * r * |q - r| ≤ (q + r) * |q - r| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hD4 : (2 - E) * |q - r| * r ≤ E * r * r := by nlinarith
  have hD5' : |q - r| ≤ 311 / 200 * u * r := by
    have hD6 : 49 / 25 * |q - r| ≤ (2 - E) * |q - r| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have hD7 : (2 - E) * |q - r| ≤ E * r :=
      le_of_mul_le_mul_right hD4 hr0
    nlinarith [mul_le_mul_of_nonneg_right hE hr0.le]
  have htri := abs_sub_le qh q r
  have hqr : q - r ≤ |q - r| := le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_left hD5' hu, mul_nonneg (mul_nonneg hu hr0.le)
    (sub_nonneg.2 hu'), mul_le_mul_of_nonneg_left hqr hu]

/-- Division step: the quotient $c' \approx a / r'$ with relative error $u$, and
$\lvert r' - r\rvert \le 13ur/5$, has relative error at most $4u$ against $a / r$. -/
private lemma rounded_div_le {u a r r' c' : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (hr : 0 < r)
    (hq : |r' - r| ≤ 13 / 5 * u * r) (hc : |c' - a / r'| ≤ u * |a / r'|) :
    |c' - a / r| ≤ 4 * u * |a / r| := by
  have hlo : (1 - 13 / 5 * u) * r ≤ r' := by linarith [(abs_le.1 hq).1]
  have hpos : 0 < (1 - 13 / 5 * u) * r := mul_pos (by linarith) hr
  have hr'pos : 0 < r' := by linarith
  have e : a / r' - a / r = (a / r') * ((r - r') / r) := by
    field_simp
  have h2 : |(r - r') / r| ≤ 13 / 5 * u := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, abs_sub_comm]
    linarith [hq]
  have hwc : |a / r' - a / r| ≤ 13 / 5 * u * |a / r'| := by
    rw [e, abs_mul]
    nlinarith [abs_nonneg (a / r')]
  have hwa : (1 - 13 / 5 * u) * |a / r'| ≤ |a / r| := by
    rw [abs_div, abs_div, abs_of_pos hr'pos, abs_of_pos hr, ← mul_div_assoc,
      div_le_div_iff₀ hr'pos hr]
    nlinarith [mul_le_mul_of_nonneg_left hlo (abs_nonneg a)]
  have htri : |c' - a / r| ≤ |c' - a / r'| + |a / r' - a / r| := abs_sub_le _ _ _
  have hw := abs_nonneg (a / r')
  nlinarith [mul_le_mul_of_nonneg_left hwa hu, mul_nonneg (mul_nonneg hu hw)
    (show (0 : ℝ) ≤ 2 / 5 - 52 / 5 * u by linarith)]

/-- A complex number is within $k$ of another, componentwise, when each real and imaginary
part is: $\lvert \tilde z - z\rvert \le k\lvert z\rvert$. -/
private lemma norm_sub_le_of_re_im {zt z : ℂ} {k : ℝ} (hk : 0 ≤ k)
    (h1 : |zt.re - z.re| ≤ k * |z.re|) (h2 : |zt.im - z.im| ≤ k * |z.im|) :
    ‖zt - z‖ ≤ k * ‖z‖ := by
  have hw : ‖zt - z‖ ^ 2 = (zt.re - z.re) ^ 2 + (zt.im - z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have a1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  simp only [mul_pow, sq_abs] at a1 a2
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))).1 ?_
  rw [hw, mul_pow, hz]
  linarith [mul_add (k ^ 2) (z.re ^ 2) (z.im ^ 2)]

/-- One computed Givens coefficient, componentwise: the quotient of the conjugated pair by the
computed radius $r'$ is within $4u$ of the exact one, when $\lvert r' - r\rvert \le 13ur/5$. -/
private lemma rounded_comp_le {u : ℝ} {M : Machine ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) {p : ℂ} {r r' : ℝ} (hr : 0 < r) (hq : |r' - r| ≤ 13 / 5 * u * r) :
    ‖(⟨M.div p.re r', M.div (M.neg p.im) r'⟩ : ℂ) - star p / (r : ℂ)‖ ≤
      4 * u * ‖star p / (r : ℂ)‖ := by
  have hlo : (1 - 13 / 5 * u) * r ≤ r' := by linarith [(abs_le.1 hq).1]
  have hr'ne : r' ≠ 0 := by
    have : 0 < (1 - 13 / 5 * u) * r := mul_pos (by linarith) hr
    linarith
  have hneg : M.neg p.im = -p.im := hM.neg p.im
  have hc1 := hM.div p.re r' hr'ne
  have hc2 := hM.div (M.neg p.im) r' hr'ne
  simp only [id] at hc1 hc2
  rw [show M.neg p.im / r' = -p.im / r' by rw [hneg]] at hc2
  refine norm_sub_le_of_re_im (by positivity) ?_ ?_
  · simp only [Complex.div_ofReal_re, Complex.star_def, Complex.conj_re]
    exact rounded_div_le hu hu' hr hq hc1
  · simp only [Complex.div_ofReal_im, Complex.star_def, Complex.conj_im]
    exact rounded_div_le hu hu' hr hq hc2

/-- **Rounded Givens coefficients**: under the standard model with
$0 \le \boldsymbol{u} \le 1/100$, each computed coefficient is within $4\boldsymbol{u}$ of the
exact one, relatively: $\lvert\tilde c - c\rvert \le 4\boldsymbol{u}\lvert c\rvert$ and
$\lvert\tilde s - s\rvert \le 4\boldsymbol{u}\lvert s\rvert$. [Higham2002, Lemma 19.7]. -/
theorem Ops.StdModel.norm_roundedGivensCoeffs_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (x y : ℂ) :
    ‖(roundedGivensCoeffs M x y).1 - (givensCoeffs x y).1‖ ≤ 4 * u * ‖(givensCoeffs x y).1‖ ∧
      ‖(roundedGivensCoeffs M x y).2 - (givensCoeffs x y).2‖ ≤
        4 * u * ‖(givensCoeffs x y).2‖ := by
  have hSxy : ‖x‖ ^ 2 + ‖y‖ ^ 2 = x.re * x.re + x.im * x.im + (y.re * y.re + y.im * y.im) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [roundedGivensCoeffs, givensCoeffs, hSxy]
  set S := x.re * x.re + x.im * x.im + (y.re * y.re + y.im * y.im) with hS_def
  set Sh := M.add (M.add (M.mul x.re x.re) (M.mul x.im x.im))
    (M.add (M.mul y.re y.re) (M.mul y.im y.im)) with hSh_def
  have hrad : |Sh - S| ≤ ((1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1) * S :=
    rounded_radius_sub_le hM hu x y
  have hE0 := (rounded_coeff_bounds hu hu').1
  have hE := (rounded_coeff_bounds hu hu').2
  set E := (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 with hE_def
  have hSn : 0 ≤ S := by
    rw [hS_def]
    exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  have hShn : 0 ≤ Sh := by
    have hE1 : E ≤ 1 := by linarith
    nlinarith [(abs_le.1 hrad).1, mul_nonneg (sub_nonneg.2 hE1) hSn]
  have hq := hM.sqrt Sh hShn
  simp only [id] at hq
  rcases eq_or_lt_of_le hSn with h0 | hpos
  · -- zero radius: both the exact and the computed radius vanish
    have hSh0 : Sh = 0 := by
      have h := hrad
      rw [← h0, mul_zero, sub_zero, abs_nonpos_iff] at h
      exact h
    have hsq0 : Real.sqrt S = 0 := by rw [← h0, Real.sqrt_zero]
    have hr0 : M.sqrt Sh = 0 := by
      have h := hq
      rw [hSh0, Real.sqrt_zero, mul_zero, sub_zero, abs_nonpos_iff] at h
      rw [hSh0]
      exact h
    simp only [hsq0, hr0, if_true]
    have hl1 := hM.lit 1
    have hl0 := hM.lit 0
    simp only [id, Rat.cast_one, Rat.cast_zero, abs_one, abs_zero, mul_one, mul_zero,
      sub_zero] at hl1 hl0
    have hl0' : M.lit 0 = 0 := abs_nonpos_iff.1 hl0
    constructor
    · apply norm_sub_le_of_re_im (by positivity)
      · simp only [Complex.one_re, abs_one, mul_one]
        linarith
      · simp [hl0']
    · apply norm_sub_le_of_re_im (by positivity) <;> simp [hl0']
  · -- positive radius: the computed radius is within 13u/5 of the exact one
    have hr := Real.sqrt_pos.2 hpos
    have hq' := rounded_radius_le hu hu' hE0 hE hpos hrad hq
    have hne : M.sqrt Sh ≠ 0 := by
      intro h
      rw [h, zero_sub, abs_neg, abs_of_pos hr] at hq'
      nlinarith [mul_le_mul_of_nonneg_right hu' hr.le]
    simp only [hne, hr.ne', if_false]
    exact ⟨rounded_comp_le hM hu hu' hr hq', rounded_comp_le hM hu hu' hr hq'⟩

/-- One rounded subtraction of two approximations, in the form of
`NLAlib.Ops.StdModel.abs_add_sub_le`. -/
private lemma stdModel_sub_combine {u : ℝ} {M : Machine ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    {a b S₁ S₂ T₁ T₂ e : ℝ} (h1 : |a - S₁| ≤ e * T₁) (h2 : |b - S₂| ≤ e * T₂)
    (hS₁ : |S₁| ≤ T₁) (hS₂ : |S₂| ≤ T₂) :
    |M.sub a b - (S₁ - S₂)| ≤ ((1 + u) * (1 + e) - 1) * (T₁ + T₂) := by
  have h := hM.sub a b
  simp only [id] at h
  have ha : |a| ≤ (1 + e) * T₁ := by
    have := abs_add_le S₁ (a - S₁)
    rw [add_sub_cancel] at this
    linarith
  have hb : |b| ≤ (1 + e) * T₂ := by
    have := abs_add_le S₂ (b - S₂)
    rw [add_sub_cancel] at this
    linarith
  have hab : |a - b| ≤ (1 + e) * (T₁ + T₂) := (abs_sub a b).trans (by linarith)
  have h3 : |M.sub a b - (S₁ - S₂)| ≤ |M.sub a b - (a - b)| + |a - S₁| + |b - S₂| := by
    have := abs_add_three (M.sub a b - (a - b)) (a - S₁) (-(b - S₂))
    rw [abs_neg] at this
    have e3 : M.sub a b - (S₁ - S₂) = (M.sub a b - (a - b)) + (a - S₁) + -(b - S₂) := by ring
    rw [e3]
    exact this
  have h4 : u * |a - b| ≤ u * ((1 + e) * (T₁ + T₂)) := mul_le_mul_of_nonneg_left hab hu
  nlinarith

/-- The coefficient of the two rounded levels, $(1 + u)^3 - 1 = 3u + 3u^2 + u^3$, lies in
$[0, 7u/2]$ for $0 \le u \le 1/100$. -/
private lemma linearWords_coeff_bounds {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) :
    0 ≤ (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 ∧
      (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 ≤ 7 / 2 * u := by
  have hE : (1 + u) * (1 + ((1 + u) * (1 + u) - 1)) - 1 = 3 * u + 3 * u ^ 2 + u ^ 3 := by ring
  rw [hE]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg hu (sub_nonneg.2 hu'), mul_nonneg (mul_nonneg hu hu) (sub_nonneg.2 hu')]

/-- $2(ES)^2 \le (5uS)^2$ once $0 \le E \le 7u/2$. -/
private lemma two_sq_mul_le {E u : ℝ} (hE0 : 0 ≤ E) (hEu : E ≤ 7 / 2 * u)
    (S : ℝ) : 2 * (E * S) ^ 2 ≤ (5 * u * S) ^ 2 := by
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hEu 2) (sq_nonneg S)
  nlinarith [sq_nonneg (u * S)]

/-- A complex difference from a pair of real parts with errors at most $B$ has modulus at most
$C$ when $2B^2 \le C^2$. -/
private lemma norm_mk_sub_le {R I C B : ℝ} {z : ℂ} (hC : 0 ≤ C) (hR : |R - z.re| ≤ B)
    (hI : |I - z.im| ≤ B) (h2 : 2 * B ^ 2 ≤ C ^ 2) :
    ‖(⟨R, I⟩ : ℂ) - z‖ ≤ C := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hR
  rw [← sq_le_sq₀ (norm_nonneg _) hC, Complex.sq_norm, Complex.normSq_apply]
  change (R - z.re) * (R - z.re) + (I - z.im) * (I - z.im) ≤ C ^ 2
  have hr : (R - z.re) * (R - z.re) ≤ B ^ 2 := by
    nlinarith [abs_mul_abs_self (R - z.re), abs_nonneg (R - z.re)]
  have hi : (I - z.im) * (I - z.im) ≤ B ^ 2 := by
    nlinarith [abs_mul_abs_self (I - z.im), abs_nonneg (I - z.im)]
  linarith

/-- Cauchy–Schwarz for the sum of moduli $\lvert pr\rvert + \lvert qs\rvert$. -/
private lemma abs_mul_add_abs_mul_le (p q r s : ℝ) :
    |p * r| + |q * s| ≤ √(p ^ 2 + q ^ 2) * √(r ^ 2 + s ^ 2) := by
  have hAB : |p * r| * |q * s| = |p * s| * |q * r| := by
    rw [← abs_mul, ← abs_mul]
    congr 1
    ring
  have key : (|p * r| + |q * s|) ^ 2 ≤ (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (|p * s| - |q * r|), sq_abs (p * s), sq_abs (q * r),
      sq_abs (p * r), sq_abs (q * s)]
  rw [← Real.sqrt_mul (by positivity)]
  calc |p * r| + |q * s| = √((|p * r| + |q * s|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √((p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2)) := Real.sqrt_le_sqrt key

/-- **Rounded complex linear combination**: the pair computed by `NLAlib.Ops.Pair.linearWords`
from the pairs of $a, b, x, y$ is within $5\boldsymbol{u}(\lvert a\rvert\lvert x\rvert +
\lvert b\rvert\lvert y\rvert)$ of $a x + b y$, for $0 \le \boldsymbol{u} \le 1/100$
(each real component carries at most three roundings). [Higham2002, Lemma 3.5]. -/
theorem Ops.StdModel.norm_linearWords_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (a b x y : ℂ) :
    ‖(⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        (a * x + b * y)‖ ≤ 5 * u * (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) := by
  have pr : ∀ p q : ℝ, |M.mul p q - p * q| ≤ u * |p * q| := fun p q => by
    have h := hM.mul p q
    simp only [id] at h
    exact h
  -- real part: two levels of rounded operations on the four products
  have d1 := stdModel_sub_combine hM hu (pr a.re x.re) (pr a.im x.im) le_rfl le_rfl
  have d2 := stdModel_sub_combine hM hu (pr b.re y.re) (pr b.im y.im) le_rfl le_rfl
  have hre := stdModel_add_combine hM hu d1 d2 (abs_sub _ _) (abs_sub _ _)
  -- imaginary part: the same tree, with additions only
  have i1 := stdModel_add_combine hM hu (pr a.re x.im) (pr a.im x.re) le_rfl le_rfl
  have i2 := stdModel_add_combine hM hu (pr b.re y.im) (pr b.im y.re) le_rfl le_rfl
  have him := stdModel_add_combine hM hu i1 i2 (abs_add_le _ _) (abs_add_le _ _)
  -- Cauchy–Schwarz on the products
  have na : ‖a‖ = √(a.re ^ 2 + a.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have nb : ‖b‖ = √(b.re ^ 2 + b.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have nx : ‖x‖ = √(x.re ^ 2 + x.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have ny : ‖y‖ = √(y.re ^ 2 + y.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  have nx' : ‖x‖ = √(x.im ^ 2 + x.re ^ 2) := by rw [nx, add_comm]
  have ny' : ‖y‖ = √(y.im ^ 2 + y.re ^ 2) := by rw [ny, add_comm]
  have c1 := abs_mul_add_abs_mul_le a.re a.im x.re x.im
  have c2 := abs_mul_add_abs_mul_le b.re b.im y.re y.im
  have c3 := abs_mul_add_abs_mul_le a.re a.im x.im x.re
  have c4 := abs_mul_add_abs_mul_le b.re b.im y.im y.re
  rw [← na, ← nx] at c1
  rw [← nb, ← ny] at c2
  rw [← na, ← nx'] at c3
  rw [← nb, ← ny'] at c4
  have hS1 : |a.re * x.re| + |a.im * x.im| + (|b.re * y.re| + |b.im * y.im|) ≤
      ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by linarith
  have hS2 : |a.re * x.im| + |a.im * x.re| + (|b.re * y.im| + |b.im * y.re|) ≤
      ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by linarith
  obtain ⟨hE0, hEu⟩ := linearWords_coeff_bounds hu hu'
  have hSn : 0 ≤ ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by positivity
  have hre' := hre.trans (mul_le_mul_of_nonneg_left
    (le_trans (by linarith) hS1) hE0)
  have him' := him.trans (mul_le_mul_of_nonneg_left hS2 hE0)
  have hzre : (a * x + b * y).re = a.re * x.re - a.im * x.im + (b.re * y.re - b.im * y.im) := by
    simp [Complex.mul_re]
  have hzim : (a * x + b * y).im = (a.re * x.im + a.im * x.re) + (b.re * y.im + b.im * y.re) := by
    simp [Complex.mul_im]
  simp only [Pair.linearWords]
  exact norm_mk_sub_le (mul_nonneg (mul_nonneg (by norm_num) hu) hSn)
    (by rw [hzre]; exact hre') (by rw [hzim]; exact him') (two_sq_mul_le hE0 hEu _)

variable {n : ℕ}

/-- `A'` is the rotation of the rows $i, j$ of `A` by the exact Givens rotation of the
coefficients $(c, s)$, computed within the relative error $\eta$ per column: the rows other than
$i, j$ are kept, and for every column $k$ the computed pair $(\mathbf{A}'_{ik}, \mathbf{A}'_{jk})$
is within $\eta\,\|(\mathbf{A}_{ik}, \mathbf{A}_{jk})\|$ of the rotated pair. -/
def IsRoundedRowRotation (η : ℝ) (i j : Fin n) (c s : ℂ) (A A' : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  (∀ r k, r ≠ i → r ≠ j → A' r k = A r k) ∧
    ∀ k, Real.sqrt (‖A' i k - (givens i j c s * A) i k‖ ^ 2 +
      ‖A' j k - (givens i j c s * A) j k‖ ^ 2) ≤ η * Real.sqrt (‖A i k‖ ^ 2 + ‖A j k‖ ^ 2)

/-- `A'` is the rotation of the columns $i, j$ of `A` by the conjugate transpose of the exact
Givens rotation of $(c, s)$, computed within the relative error $\eta$ per row. -/
def IsRoundedColRotation (η : ℝ) (i j : Fin n) (c s : ℂ) (A A' : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  (∀ r k, k ≠ i → k ≠ j → A' r k = A r k) ∧
    ∀ r, Real.sqrt (‖A' r i - (A * (givens i j c s)ᴴ) r i‖ ^ 2 +
      ‖A' r j - (A * (givens i j c s)ᴴ) r j‖ ^ 2) ≤ η * Real.sqrt (‖A r i‖ ^ 2 + ‖A r j‖ ^ 2)

/-- **A rotation of two rows computed pairwise has Frobenius-norm error
$2\eta\|\mathbf{A}\|_2$**: the error is supported on two rows, its Frobenius norm is at most
$\eta$ times the Frobenius norm of those rows, which is at most $\sqrt 2\,\|\mathbf{A}\|_2$.
[Higham2002, Lemma 19.8]. -/
theorem IsRoundedRowRotation.frobNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedRowRotation η i j c s A A') (hη : 0 ≤ η) :
    frobNorm (A' - givens i j c s * A) ≤ 2 * η * specNorm A := by
  obtain ⟨hout, hcol⟩ := h
  have hrow : ∀ r : Fin n, ∑ k, ‖A r k‖ ^ 2 ≤ specNorm A ^ 2 := by
    intro r
    have h1 := norm_toLp_col_le_specNorm Aᴴ r
    rw [specNorm_conjTranspose] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [EuclideanSpace.norm_sq_eq] at h2
    simpa [Matrix.col_apply, Matrix.conjTranspose_apply] using h2
  have hD : ∀ r k, r ≠ i → r ≠ j → (A' - givens i j c s * A) r k = 0 := by
    intro r k hr hr'
    rw [Matrix.sub_apply, hout r k hr hr', givens_mul_apply_of_ne hr hr', sub_self]
  have hcolsq : ∀ k, ‖(A' - givens i j c s * A) i k‖ ^ 2 + ‖(A' - givens i j c s * A) j k‖ ^ 2 ≤
      η ^ 2 * (‖A i k‖ ^ 2 + ‖A j k‖ ^ 2) := by
    intro k
    have h3 := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hη (Real.sqrt_nonneg _))).2 (hcol k)
    rw [mul_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at h3
    simpa [Matrix.sub_apply] using h3
  have hsum : ∑ r, ∑ k, ‖(A' - givens i j c s * A) r k‖ ^ 2 ≤
      ∑ k, (‖(A' - givens i j c s * A) i k‖ ^ 2 + ‖(A' - givens i j c s * A) j k‖ ^ 2) := by
    by_cases hij : i = j
    · rw [Fintype.sum_eq_single i]
      · exact Finset.sum_le_sum fun k _ => le_add_of_nonneg_right (sq_nonneg _)
      · intro r hr
        exact Finset.sum_eq_zero fun k _ => by
          simp [hD r k hr (fun h => hr (h.trans hij.symm))]
    · rw [Fintype.sum_eq_add i j hij]
      · exact le_of_eq (Finset.sum_add_distrib).symm
      · intro r hr
        exact Finset.sum_eq_zero fun k _ => by simp [hD r k hr.1 hr.2]
  have hfro : frobNorm (A' - givens i j c s * A) ^ 2 ≤ (2 * η * specNorm A) ^ 2 := by
    rw [frobNorm_sq_eq_sum]
    calc ∑ r, ∑ k, ‖(A' - givens i j c s * A) r k‖ ^ 2
        ≤ ∑ k, (‖(A' - givens i j c s * A) i k‖ ^ 2 + ‖(A' - givens i j c s * A) j k‖ ^ 2) := hsum
      _ ≤ ∑ k, η ^ 2 * (‖A i k‖ ^ 2 + ‖A j k‖ ^ 2) := Finset.sum_le_sum fun k _ => hcolsq k
      _ = η ^ 2 * (∑ k, ‖A i k‖ ^ 2 + ∑ k, ‖A j k‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ η ^ 2 * (specNorm A ^ 2 + specNorm A ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add (hrow i) (hrow j)) (sq_nonneg η)
      _ ≤ (2 * η * specNorm A) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg (specNorm A))]
  exact (sq_le_sq₀ (frobNorm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hη) (specNorm_nonneg A))).1 hfro

/-- **A rotation of two rows computed pairwise has spectral-norm error $2\eta\|\mathbf{A}\|_2$**
(`NLAlib.IsRoundedRowRotation.frobNorm_sub_le`). [Higham2002, Lemma 19.8]. -/
theorem IsRoundedRowRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedRowRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - givens i j c s * A) ≤ 2 * η * specNorm A :=
  (specNorm_le_frobNorm _).trans (h.frobNorm_sub_le hη)

/-- **A rotation of two columns computed pairwise has spectral-norm error
$2\eta\|\mathbf{A}\|_2$.** [Higham2002, Lemma 19.8]. -/
theorem IsRoundedColRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedColRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - A * (givens i j c s)ᴴ) ≤ 2 * η * specNorm A := by
  have hG : ∀ r k, (givens i j c s * Aᴴ) r k = star ((A * (givens i j c s)ᴴ) k r) := by
    intro r k
    rw [← Matrix.conjTranspose_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h' : IsRoundedRowRotation η i j c s Aᴴ A'ᴴ := by
    refine ⟨fun r k hr hk => ?_, fun k => ?_⟩
    · simp only [Matrix.conjTranspose_apply, h.1 k r hr hk]
    · have e := h.2 k
      simp only [Matrix.conjTranspose_apply, hG, ← star_sub, norm_star]
      exact e
  have hT : A' - A * (givens i j c s)ᴴ = ((A'ᴴ - givens i j c s * Aᴴ))ᴴ := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  rw [hT, specNorm_conjTranspose]
  have := h'.specNorm_sub_le hη
  rw [specNorm_conjTranspose] at this
  exact this

/-- **Rounded coefficients and rounded application**: rotating a pair by the computed
coefficients $(\tilde c, \tilde s)$ of $(u, v)$ with the rounded linear combination is within
$12\boldsymbol{u}$, relatively, of rotating it by the exact Givens rotation of $(u, v)$ (the
coefficient error contributes $4\sqrt 2\,\boldsymbol{u}$, the application $5\boldsymbol{u}$ up
to second order). The exact rotation is unitary, so the computed rotation of two rows is an
`NLAlib.IsRoundedRowRotation` with $\eta = 12\boldsymbol{u}$ for a unitary rotation.
[Higham2002, Lemmas 19.7–19.8]. -/
theorem Ops.StdModel.norm_rotatePair_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (p q x y : ℂ) :
    ‖(⟨(Pair.linearWords M ((roundedGivensCoeffs M p q).1.re, (roundedGivensCoeffs M p q).1.im)
          ((roundedGivensCoeffs M p q).2.re, (roundedGivensCoeffs M p q).2.im)
          (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M ((roundedGivensCoeffs M p q).1.re, (roundedGivensCoeffs M p q).1.im)
          ((roundedGivensCoeffs M p q).2.re, (roundedGivensCoeffs M p q).2.im)
          (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        ((givensCoeffs p q).1 * x + (givensCoeffs p q).2 * y)‖ ≤
      12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hc1, hc2⟩ := norm_roundedGivensCoeffs_sub_le hM hu hu' p q
  have hL := norm_linearWords_sub_le hM hu hu' (roundedGivensCoeffs M p q).1
    (roundedGivensCoeffs M p q).2 x y
  have hU := norm_givensCoeffs_fst_sq_add p q
  set a := (roundedGivensCoeffs M p q).1
  set b := (roundedGivensCoeffs M p q).2
  set c := (givensCoeffs p q).1
  set s := (givensCoeffs p q).2
  have ha : ‖a‖ ≤ (1 + 4 * u) * ‖c‖ := by linarith [norm_sub_norm_le a c]
  have hb : ‖b‖ ≤ (1 + 4 * u) * ‖s‖ := by linarith [norm_sub_norm_le b s]
  have h2 : ‖(a * x + b * y) - (c * x + s * y)‖ ≤ 4 * u * ‖c‖ * ‖x‖ + 4 * u * ‖s‖ * ‖y‖ := by
    have e : (a * x + b * y) - (c * x + s * y) = (a - c) * x + (b - s) * y := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hc2 (norm_nonneg _))
  have hK2 : (‖c‖ * ‖x‖ + ‖s‖ * ‖y‖) ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have e : (‖c‖ ^ 2 + ‖s‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [hU, one_mul]
    nlinarith [sq_nonneg (‖c‖ * ‖y‖ - ‖s‖ * ‖x‖)]
  have hK0 : 0 ≤ ‖c‖ * ‖x‖ + ‖s‖ * ‖y‖ := by positivity
  have hK : ‖c‖ * ‖x‖ + ‖s‖ * ‖y‖ ≤ Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    calc ‖c‖ * ‖x‖ + ‖s‖ * ‖y‖ = Real.sqrt ((‖c‖ * ‖x‖ + ‖s‖ * ‖y‖) ^ 2) :=
          (Real.sqrt_sq hK0).symm
      _ ≤ Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt hK2
  have h1 : ‖(⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        (a * x + b * y)‖ ≤ 5 * u * ((1 + 4 * u) * ‖c‖ * ‖x‖ + (1 + 4 * u) * ‖s‖ * ‖y‖) :=
    hL.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) (by linarith))
  have h3 : 5 * u * ((1 + 4 * u) * ‖c‖ * ‖x‖ + (1 + 4 * u) * ‖s‖ * ‖y‖) +
      (4 * u * ‖c‖ * ‖x‖ + 4 * u * ‖s‖ * ‖y‖) =
      (9 * u + 20 * u ^ 2) * (‖c‖ * ‖x‖ + ‖s‖ * ‖y‖) := by ring
  have h4 : (9 * u + 20 * u ^ 2) * (‖c‖ * ‖x‖ + ‖s‖ * ‖y‖) ≤
      12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hK hu,
      mul_nonneg (sub_nonneg.2 hu') (mul_nonneg hu hK0)]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (a * x + b * y) _).trans ?_
  linarith [h1, h2, h3, h4]

/-- The rotation $(x, y) \mapsto (p x + q y, -\bar q x + \bar p y)$ scales the Euclidean norm
by $\sqrt{\lvert p\rvert^2 + \lvert q\rvert^2}$. -/
private lemma rotation_norm_sq (p q x y : ℂ) :
    ‖p * x + q * y‖ ^ 2 + ‖-star q * x + star p * y‖ ^ 2 =
      (‖p‖ ^ 2 + ‖q‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Two errors, each at most the sum of two parts, have a joint size at most the sum of the joint
sizes of the parts (Minkowski's inequality in the plane). -/
private lemma sq_add_sq_le_of_parts {E₁ E₂ e₁ e₂ d₁ d₂ p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h₁ : E₁ ≤ e₁ + d₁) (h₂ : E₂ ≤ e₂ + d₂) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (he : e₁ ^ 2 + e₂ ^ 2 ≤ p ^ 2) (hd : d₁ ^ 2 + d₂ ^ 2 ≤ q ^ 2) :
    E₁ ^ 2 + E₂ ^ 2 ≤ (p + q) ^ 2 := by
  have hcs : e₁ * d₁ + e₂ * d₂ ≤ p * q := by
    have h1 : (e₁ * d₁ + e₂ * d₂) ^ 2 ≤ (p * q) ^ 2 := by
      nlinarith [sq_nonneg (e₁ * d₂ - e₂ * d₁), mul_le_mul he hd (by positivity) (sq_nonneg p)]
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have s1 : E₁ ^ 2 ≤ (e₁ + d₁) ^ 2 := pow_le_pow_left₀ hE₁ h₁ 2
  have s2 : E₂ ^ 2 ≤ (e₂ + d₂) ^ 2 := pow_le_pow_left₀ hE₂ h₂ 2
  have r1 : (e₁ + d₁) ^ 2 + (e₂ + d₂) ^ 2 =
      (e₁ ^ 2 + e₂ ^ 2) + (d₁ ^ 2 + d₂ ^ 2) + 2 * (e₁ * d₁ + e₂ * d₂) := by ring
  have r2 : (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * (p * q) := by ring
  linarith

/-- The application part of a computed rotation of a pair: two linear combinations with
coefficients within $4\boldsymbol{u}$ of a unit pair $(A, B)$, each computed within
$5\boldsymbol{u}$, have a joint error at most $7.5\boldsymbol{u}\,\|(X, Y)\|$. -/
private lemma rotation_app_sq_le {u A B X Y a b e₁ e₂ : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 100)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hAB : A ^ 2 + B ^ 2 = 1)
    (ha : a ≤ (1 + 4 * u) * A) (hb : b ≤ (1 + 4 * u) * B) (he₁0 : 0 ≤ e₁) (he₂0 : 0 ≤ e₂)
    (he₁ : e₁ ≤ 5 * u * (a * X + b * Y)) (he₂ : e₂ ≤ 5 * u * (b * X + a * Y)) :
    e₁ ^ 2 + e₂ ^ 2 ≤ (15 / 2 * u) ^ 2 * (X ^ 2 + Y ^ 2) := by
  have hk : 0 ≤ 5 * u * (1 + 4 * u) := by positivity
  have hf₁ : e₁ ≤ 5 * u * (1 + 4 * u) * (A * X + B * Y) := by
    refine he₁.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right ha hX, mul_le_mul_of_nonneg_right hb hY]
  have hf₂ : e₂ ≤ 5 * u * (1 + 4 * u) * (B * X + A * Y) := by
    refine he₂.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right ha hY, mul_le_mul_of_nonneg_right hb hX]
  have hsum : (A * X + B * Y) ^ 2 + (B * X + A * Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by
    have h2ab : 2 * (A * B) ≤ 1 := by nlinarith [sq_nonneg (A - B)]
    have h2xy : 2 * (X * Y) ≤ X ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
    have hm := mul_le_mul h2ab h2xy (by positivity) zero_le_one
    nlinarith [hm]
  have h1 := pow_le_pow_left₀ he₁0 hf₁ 2
  have h2 := pow_le_pow_left₀ he₂0 hf₂ 2
  have hk2 : (5 * u * (1 + 4 * u)) ^ 2 * 2 ≤ (15 / 2 * u) ^ 2 := by
    have h4 : (1 + 4 * u) ^ 2 ≤ 9 / 8 := by nlinarith
    have e1 : (5 * u * (1 + 4 * u)) ^ 2 * 2 = 50 * u ^ 2 * (1 + 4 * u) ^ 2 := by ring
    have e2 : (15 / 2 * u) ^ 2 = 50 * u ^ 2 * (9 / 8) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have r : (5 * u * (1 + 4 * u) * (A * X + B * Y)) ^ 2 +
      (5 * u * (1 + 4 * u) * (B * X + A * Y)) ^ 2 =
      (5 * u * (1 + 4 * u)) ^ 2 * ((A * X + B * Y) ^ 2 + (B * X + A * Y) ^ 2) := by ring
  have h3 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (5 * u * (1 + 4 * u)))
  have h5 := mul_le_mul_of_nonneg_right hk2 (add_nonneg (sq_nonneg X) (sq_nonneg Y))
  nlinarith

/-- **A computed rotation of a pair is within $12\boldsymbol{u}$, jointly**: on a machine with the
standard model at $0 \le \boldsymbol{u} \le 1/100$, coefficient words $a, b$ within
$4\boldsymbol{u}$ of a unit pair $(\alpha, \beta)$, relatively, rotate $(x, y)$ by
`NLAlib.Ops.Pair.linearWords` to the computed $(a x + b y, -\bar b x + \bar a y)$, which is within
$12\boldsymbol{u}\,\|(x, y)\|$ of $(\alpha x + \beta y, -\bar\beta x + \bar\alpha y)$ in the
Euclidean norm of the pair. The coefficient errors contribute $4\boldsymbol{u}$ jointly (the
error matrix is a multiple of a unitary one), the application $5\sqrt 2\,\boldsymbol{u}$ to first
order. This is the per-pair hypothesis of `NLAlib.IsRoundedRowRotation` and
`NLAlib.IsRoundedColRotation` with $\eta = 12\boldsymbol{u}$, for the row rotation by
$(\tilde c, \tilde s)$ and for the column rotation by $(\bar{\tilde c}, \bar{\tilde s})$.
[Higham2002, Lemma 19.8]. -/
theorem Ops.StdModel.norm_linearWords_rotation_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) {a b α β : ℂ}
    (hαβ : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1)
    (ha : ‖a - α‖ ≤ 4 * u * ‖α‖) (hb : ‖b - β‖ ≤ 4 * u * ‖β‖) (x y : ℂ) :
    Real.sqrt (‖(⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
          (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
          (α * x + β * y)‖ ^ 2 +
        ‖(⟨(Pair.linearWords M ((-star b).re, (-star b).im) ((star a).re, (star a).im)
            (x.re, x.im) (y.re, y.im)).1,
          (Pair.linearWords M ((-star b).re, (-star b).im) ((star a).re, (star a).im)
            (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) - (-star β * x + star α * y)‖ ^ 2) ≤
      12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have he₁ := hM.norm_linearWords_sub_le hu hu' a b x y
  have he₂ := hM.norm_linearWords_sub_le hu hu' (-star b) (star a) x y
  rw [norm_neg, norm_star, norm_star] at he₂
  generalize (⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
    (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) = L₁ at he₁ ⊢
  generalize (⟨(Pair.linearWords M ((-star b).re, (-star b).im) ((star a).re, (star a).im)
      (x.re, x.im) (y.re, y.im)).1,
    (Pair.linearWords M ((-star b).re, (-star b).im) ((star a).re, (star a).im)
      (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) = L₂ at he₂ ⊢
  have happ := rotation_app_sq_le hu hu' (norm_nonneg x) (norm_nonneg y)
    hαβ (by linarith [norm_sub_norm_le a α]) (by linarith [norm_sub_norm_le b β])
    (norm_nonneg _) (norm_nonneg _) he₁ he₂
  have hcoef : ‖(a - α) * x + (b - β) * y‖ ^ 2 +
      ‖-star (b - β) * x + star (a - α) * y‖ ^ 2 ≤ (4 * u) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    rw [rotation_norm_sq]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc _ ≤ (4 * u * ‖α‖) ^ 2 + (4 * u * ‖β‖) ^ 2 := add_le_add h1 h2
      _ = (4 * u) ^ 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) := by ring
      _ = (4 * u) ^ 2 := by rw [hαβ, mul_one]
  have hd₁ : ‖L₁ - (α * x + β * y)‖ ≤ ‖L₁ - (a * x + b * y)‖ + ‖(a - α) * x + (b - β) * y‖ := by
    refine (norm_add_le _ _).trans_eq' ?_
    congr 1; ring
  have hd₂ : ‖L₂ - (-star β * x + star α * y)‖ ≤ ‖L₂ - (-star b * x + star a * y)‖ +
      ‖-star (b - β) * x + star (a - α) * y‖ := by
    refine (norm_add_le _ _).trans_eq' ?_
    congr 1; simp only [star_sub]; ring
  have hR : 0 ≤ Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) := Real.sqrt_nonneg _
  have hR2 : Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have key := sq_add_sq_le_of_parts (p := 15 / 2 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (q := 4 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)) (by positivity) (by positivity) hd₁ hd₂
    (norm_nonneg _) (norm_nonneg _) (by rw [mul_pow, hR2]; exact happ)
    (by rw [mul_pow, hR2]; exact hcoef)
  have h12 : (15 / 2 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2) +
      4 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2 ≤
      (12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hu hR]) 2
  calc _ ≤ Real.sqrt ((12 * u * Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt (key.trans h12)
    _ = _ := Real.sqrt_sq (by positivity)

/-! ### Rotating $\mathbf{e}_N$ to a computed vector -/

/-- $(1 + x)^n - 1 \le nx + (nx)^2$ for $x \ge 0$ and $nx \le 1$. -/
theorem one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hnx : n * x ≤ 1) :
    (1 + x) ^ n - 1 ≤ n * x + (n * x) ^ 2 := by
  have h1 : (1 + x) ^ n ≤ Real.exp (n * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := n * x)
    (by rw [abs_of_nonneg (by positivity)]; exact hnx))).2
  linarith

/-- The geometric accumulation: $\sum_{j < n} x(1 + x)^j = (1 + x)^n - 1$. -/
theorem sum_mul_one_add_pow (x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, x * (1 + x) ^ j = (1 + x) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Errors along a chain of isometries add up: if $x_{j+1}$ is within $\varepsilon_j$ of
$\mathbf{U}_j x_j$ for unitary $\mathbf{U}_j$ and $\mathbf{P}_{j+1} = \mathbf{U}_j\mathbf{P}_j$,
$\mathbf{P}_0 = \mathbf{I}$, then $x_k$ is within $\sum_{j<k}\varepsilon_j$ of
$\mathbf{P}_k x_0$. -/
theorem norm_toLp_sub_mulVec_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = U j * P j) (x : ℕ → m → ℂ) (k : ℕ) :
    ‖WithLp.toLp 2 (x k - P k *ᵥ x 0)‖ ≤
      ∑ j ∈ Finset.range k, ‖WithLp.toLp 2 (x (j + 1) - U j *ᵥ x j)‖ := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : x (k + 1) - P (k + 1) *ᵥ x 0 =
        (x (k + 1) - U k *ᵥ x k) + U k *ᵥ (x k - P k *ᵥ x 0) := by
      rw [hP, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]; abel
    rw [he, WithLp.toLp_add, Finset.sum_range_succ]
    refine (norm_add_le _ _).trans ?_
    rw [(hU k).norm_toLp_mulVec]
    linarith

/-- Errors along a chain of unitary similarities add up: if $\mathbf{A}_{j+1}$ is within
$\varepsilon_j$ of $\mathbf{U}_j\mathbf{A}_j\mathbf{U}_j^{\mathsf H}$ for unitary
$\mathbf{U}_j$, then $\mathbf{A}_k$ is within $\sum_{j<k}\varepsilon_j$ of
$\mathbf{P}_k\mathbf{A}_0\mathbf{P}_k^{\mathsf H}$. -/
theorem specNorm_sub_mul_mul_conjTranspose_le_sum {m : Type*} [Fintype m] [DecidableEq m]
    {U P : ℕ → Matrix m m ℂ} (hU : ∀ j, HasOrthonormalCols (U j)) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j + 1) = U j * P j) (A : ℕ → Matrix m m ℂ) (k : ℕ) :
    specNorm (A k - P k * A 0 * (P k)ᴴ) ≤
      ∑ j ∈ Finset.range k, specNorm (A (j + 1) - U j * A j * (U j)ᴴ) := by
  induction k with
  | zero => simp [hP0]
  | succ k ih =>
    have he : A (k + 1) - P (k + 1) * A 0 * (P (k + 1))ᴴ =
        (A (k + 1) - U k * A k * (U k)ᴴ) + U k * (A k - P k * A 0 * (P k)ᴴ) * (U k)ᴴ := by
      rw [hP, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [he, Finset.sum_range_succ]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU k).conjTranspose.specNorm_mul_right, (hU k).specNorm_mul_left]
    linarith

/-- Truncating a vector to its first $k$ coordinates does not increase its norm. -/
theorem norm_toLp_truncate_le {m : ℕ} (x : Fin m → ℂ) (k : ℕ) :
    ‖WithLp.toLp 2 (fun i : Fin m => if (i : ℕ) < k then x i else 0)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  dsimp only
  split_ifs <;> simp

/-- A rotation that zeros coordinate $j$ of $x$ moves the truncation point by one: the first
$j + 1$ coordinates of $\mathbf{G}_j x$ are the first $j$ coordinates of $x$ and a zero. -/
theorem truncate_givens_mulVec {n : ℕ} (j : Fin n) (x : Fin (n + 1) → ℂ) :
    (fun i : Fin (n + 1) => if (i : ℕ) < (j : ℕ) + 1 then
        (givens j.castSucc j.succ (givensCoeffs (star (x j.succ)) (-star (x j.castSucc))).1
          (givensCoeffs (star (x j.succ)) (-star (x j.castSucc))).2 *ᵥ x) i else 0) =
      fun i : Fin (n + 1) => if (i : ℕ) < (j : ℕ) then x i else 0 := by
  have hne : j.castSucc ≠ j.succ := Fin.ne_of_val_ne (by simp)
  funext i
  by_cases hij : (i : ℕ) < j
  · rw [if_pos (by omega), if_pos hij, givens_mulVec_apply_of_ne (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))]
  · rw [if_neg hij]
    by_cases hi : (i : ℕ) = j
    · rw [if_pos (by omega), show i = j.castSucc from Fin.ext (by simp [hi]),
        givens_mulVec_apply_left hne]
      have h := neg_star_givensCoeffs_snd_mul_add (star (x j.succ)) (-star (x j.castSucc))
      have h' := congrArg star h
      simp only [star_add, star_mul, star_neg, star_star, star_zero] at h'
      linear_combination -h'
    · rw [if_neg (by omega)]

/-- The scalar step of `NLAlib.exists_hasOrthonormalCols_rotateTo`: a vector $v$ of norm
$\gamma > 0$ whose first $n$ coordinates have norm $t$ is, after a phase, within
$\sqrt2\,t/\gamma$ of $\gamma\mathbf{e}_{n+1}$, relatively. -/
theorem exists_norm_single_sub_smul_le {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 -
      (c * ((‖WithLp.toLp 2 v‖⁻¹ : ℝ) : ℂ)) • v)‖ ≤ √2 * (‖WithLp.toLp 2 (fun i : Fin (n + 1) =>
        if (i : ℕ) < n then v i else 0)‖ / ‖WithLp.toLp 2 v‖) := by
  set γ := ‖WithLp.toLp 2 v‖ with hγ
  have hγ0 : 0 < γ := norm_pos_iff.mpr (by simpa using hv)
  set w := ‖v (Fin.last n)‖
  set t := ‖WithLp.toLp 2 (fun i : Fin (n + 1) => if (i : ℕ) < n then v i else 0)‖
  have hsq : γ ^ 2 = t ^ 2 + w ^ 2 := by
    simp only [γ, t, w, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last, lt_irrefl, if_false, Fin.is_lt, if_true, norm_zero]
    simp
  refine ⟨if v (Fin.last n) = 0 then 1 else star (v (Fin.last n)) / (w : ℂ), ?_, ?_⟩
  · split_ifs with h
    · simp
    · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h)]
  set c : ℂ := if v (Fin.last n) = 0 then 1 else star (v (Fin.last n)) / (w : ℂ) with hc
  have hc' : ‖c * ((γ⁻¹ : ℝ) : ℂ)‖ = γ⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hc]
    split_ifs with h
    · simp
    · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h), one_mul]
  have hlast : c * ((γ⁻¹ : ℝ) : ℂ) * v (Fin.last n) = ((w / γ : ℝ) : ℂ) := by
    simp only [hc]
    split_ifs with h
    · simp [w, h]
    · have hw : (w : ℂ) ≠ 0 := by simpa [w] using h
      calc star (v (Fin.last n)) / (w : ℂ) * ((γ⁻¹ : ℝ) : ℂ) * v (Fin.last n)
          = v (Fin.last n) * star (v (Fin.last n)) * ((γ⁻¹ : ℝ) : ℂ) / w := by ring
        _ = ((w / γ : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj']
          push_cast
          field_simp
          rfl
  have hw : w ≤ γ := by nlinarith [norm_nonneg (WithLp.toLp 2 (fun i : Fin (n + 1) =>
    if (i : ℕ) < n then v i else 0)), norm_nonneg (v (Fin.last n))]
  have ht2 : t ^ 2 = ∑ i : Fin n, ‖v i.castSucc‖ ^ 2 := by
    simp [t, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  have h2 : ‖WithLp.toLp 2 (Pi.single (Fin.last n) 1 - (c * ((γ⁻¹ : ℝ) : ℂ)) • v)‖ ^ 2 =
      γ⁻¹ ^ 2 * t ^ 2 + (1 - w / γ) ^ 2 := by
    rw [ht2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Finset.mul_sum]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    rw [hlast]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, zero_sub, norm_neg, norm_mul, hc',
        mul_pow]
    · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
  have h3 : (1 - w / γ) ^ 2 ≤ γ⁻¹ ^ 2 * t ^ 2 := by
    rw [show 1 - w / γ = γ⁻¹ * (γ - w) by field_simp, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [norm_nonneg (v (Fin.last n))]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [h2, mul_pow, Real.sq_sqrt zero_le_two, div_pow]
  have e : γ⁻¹ ^ 2 * t ^ 2 = t ^ 2 / γ ^ 2 := by rw [inv_pow, mul_comm, div_eq_mul_inv]
  linarith

/-- The vector part of `NLAlib.exists_hasOrthonormalCols_rotateTo`: along the rotations
$\mathbf{U}_j$ that zero the computed vectors one coordinate at a time, the last column of
$\mathbf{P}_n^{\mathsf H}$, $\mathbf{P}_n = \mathbf{U}_{n-1}\cdots\mathbf{U}_0$, is within $5n\eta$
of the direction of $\mathbf{g}^{(0)}$, up to a phase. -/
theorem exists_norm_conjTranspose_col_sub_le {n : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hnη : n * η ≤ 1 / 8) {cs : ℕ → ℂ × ℂ} {g : ℕ → Fin (n + 1) → ℂ}
    {U P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : ∀ j, HasOrthonormalCols (U j))
    (hP0 : P 0 = 1) (hP : ∀ j, P (j + 1) = U j * P j)
    (hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2)
    (hcs : ∀ j : Fin n, cs j = givensCoeffs (star (g j j.succ)) (-star (g j j.castSucc)))
    (hg : ∀ j : Fin n, ‖WithLp.toLp 2 (g ((j : ℕ) + 1) - U j *ᵥ g j)‖ ≤
      η * ‖WithLp.toLp 2 (g j)‖) (hg0 : g 0 ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖WithLp.toLp 2 ((fun k => (P n)ᴴ k (Fin.last n)) -
      (c * ((‖WithLp.toLp 2 (g 0)‖⁻¹ : ℝ) : ℂ)) • g 0)‖ ≤ 5 * n * η := by
  set γ := ‖WithLp.toLp 2 (g 0)‖
  have hγ : 0 < γ := norm_pos_iff.mpr (by simpa using hg0)
  set tr : ℕ → (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ := fun k x i => if (i : ℕ) < k then x i else 0
  have htr_sub : ∀ k x y, tr k (x - y) = tr k x - tr k y := fun k x y => by
    funext i; simp only [tr, Pi.sub_apply]; split_ifs <;> simp
  set E := ∑ j ∈ Finset.range n, ‖WithLp.toLp 2 (g (j + 1) - U j *ᵥ g j)‖
  have hPu : ∀ k, HasOrthonormalCols (P k) := fun k => by
    induction k with
    | zero => rw [hP0]; exact hasOrthonormalCols_one
    | succ k ih => rw [hP]; exact (hU k).mul ih
  have hgrow : ∀ j ≤ n, ‖WithLp.toLp 2 (g j)‖ ≤ (1 + η) ^ j * γ := fun j => by
    induction j with
    | zero => simp [γ]
    | succ j ih =>
      intro hj
      have h := hg ⟨j, by omega⟩
      have h1 := norm_sub_norm_le (WithLp.toLp 2 (g (j + 1))) (WithLp.toLp 2 (U j *ᵥ g j))
      rw [← WithLp.toLp_sub, (hU j).norm_toLp_mulVec] at h1
      rw [pow_succ]
      nlinarith [ih (by omega)]
  have hE : E ≤ 9 / 8 * (n * η) * γ := by
    calc E ≤ ∑ j ∈ Finset.range n, η * (1 + η) ^ j * γ := Finset.sum_le_sum fun j hj => by
          have hj' := Finset.mem_range.mp hj
          have := hg ⟨j, hj'⟩
          nlinarith [hgrow j hj'.le]
      _ = ((1 + η) ^ n - 1) * γ := by rw [← Finset.sum_mul, sum_mul_one_add_pow]
      _ ≤ (n * η + (n * η) ^ 2) * γ := by
          gcongr; exact one_add_pow_sub_one_le hη (by linarith)
      _ ≤ 9 / 8 * (n * η) * γ := by gcongr; nlinarith [mul_nonneg n.cast_nonneg hη]
  have htail : ∀ k ≤ n, ‖WithLp.toLp 2 (tr k (g k))‖ ≤
      ∑ j ∈ Finset.range k, ‖WithLp.toLp 2 (g (j + 1) - U j *ᵥ g j)‖ := fun k => by
    induction k with
    | zero => simp [tr]; rfl
    | succ k ih =>
      intro hk
      have he : tr (k + 1) (g (k + 1)) = tr (k + 1) (g (k + 1) - U k *ᵥ g k) + tr k (g k) := by
        have h := truncate_givens_mulVec (⟨k, by omega⟩ : Fin n) (g k)
        rw [← hcs ⟨k, by omega⟩, ← hUj ⟨k, by omega⟩] at h
        rw [htr_sub, show tr (k + 1) (U k *ᵥ g k) = tr k (g k) from h]
        abel
      rw [he, WithLp.toLp_add, Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := norm_toLp_truncate_le (g (k + 1) - U k *ᵥ g k) (k + 1)
      exact (norm_add_le _ _).trans (by linarith)
  set v := P n *ᵥ g 0
  have hv : ‖WithLp.toLp 2 v‖ = γ := (hPu n).norm_toLp_mulVec _
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv; linarith
  have hprop := norm_toLp_sub_mulVec_le_sum hU hP0 hP g n
  have htv : ‖WithLp.toLp 2 (tr n v)‖ ≤ 2 * E := by
    have h : tr n v = tr n (g n) - tr n (g n - v) := by rw [htr_sub]; abel
    rw [h, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans ?_
    linarith [htail n le_rfl, norm_toLp_truncate_le (g n - v) n]
  obtain ⟨c, hc1, hc⟩ := exists_norm_single_sub_smul_le v hv0
  refine ⟨c, hc1, ?_⟩
  rw [hv] at hc
  have hcol : (fun k => (P n)ᴴ k (Fin.last n)) - (c * ((γ⁻¹ : ℝ) : ℂ)) • g 0 =
      (P n)ᴴ *ᵥ (Pi.single (Fin.last n) 1 - (c * ((γ⁻¹ : ℝ) : ℂ)) • v) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      (hPu n).conjTranspose_mul_self, Matrix.one_mulVec]
    congr 1
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol, (hPu n).conjTranspose.norm_toLp_mulVec]
  refine hc.trans ?_
  have hs : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc √2 * (‖WithLp.toLp 2 (tr n v)‖ / γ) ≤ 3 / 2 * (2 * E / γ) := by gcongr
    _ ≤ 3 / 2 * (2 * (9 / 8 * (n * η) * γ) / γ) := by gcongr
    _ ≤ 5 * n * η := by
        field_simp
        nlinarith [mul_nonneg n.cast_nonneg hη]

/-- The matrix part of `NLAlib.exists_hasOrthonormalCols_rotateTo`: rounded rotations of the
rows and then the columns $j, j + 1$ by $\mathbf{U}_j$, each with relative error $\eta$ per pair,
keep $\mathbf{A}_n$ within $8n\eta\|\mathbf{A}_0\|_2$ of
$\mathbf{P}_n\mathbf{A}_0\mathbf{P}_n^{\mathsf H}$ for $n\eta \le 1/8$. -/
theorem specNorm_sub_rotateTo_le {n : ℕ} {η : ℝ} (hη : 0 ≤ η) (hnη : n * η ≤ 1 / 8)
    {cs : ℕ → ℂ × ℂ} {A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {U P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : ∀ j, HasOrthonormalCols (U j))
    (hP0 : P 0 = 1) (hP : ∀ j, P (j + 1) = U j * P j)
    (hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2)
    (hA : ∀ j : Fin n, ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsRoundedRowRotation η j.castSucc j.succ (cs j).1 (cs j).2 (A j) A' ∧
        IsRoundedColRotation η j.castSucc j.succ (cs j).1 (cs j).2 A' (A ((j : ℕ) + 1))) :
    specNorm (A n - P n * A 0 * (P n)ᴴ) ≤ 8 * n * η * specNorm (A 0) := by
  set β := 4 * η + 4 * η ^ 2
  have hβ : 0 ≤ β := by positivity
  have hD : ∀ j < n, specNorm (A (j + 1) - U j * A j * (U j)ᴴ) ≤ β * specNorm (A j) := by
    intro j hj
    obtain ⟨A', hr, hc⟩ := hA ⟨j, hj⟩
    have h1 := hr.specNorm_sub_le hη
    have h2 := hc.specNorm_sub_le hη
    rw [← hUj ⟨j, hj⟩] at h1 h2
    have h3 : specNorm A' ≤ (1 + 2 * η) * specNorm (A j) := by
      have := (abs_le.mp (abs_specNorm_sub_specNorm_le A' (U j * A j))).2
      rw [(hU j).specNorm_mul_left] at this
      linarith
    have he : A (j + 1) - U j * A j * (U j)ᴴ =
        (A (j + 1) - A' * (U j)ᴴ) + (A' - U j * A j) * (U j)ᴴ := by
      simp only [Matrix.sub_mul]; abel
    rw [he]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU j).conjTranspose.specNorm_mul_right]
    nlinarith [specNorm_nonneg (A j)]
  have hgrow : ∀ j ≤ n, specNorm (A j) ≤ (1 + β) ^ j * specNorm (A 0) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h := (abs_le.mp (abs_specNorm_sub_specNorm_le (A (j + 1)) (U j * A j * (U j)ᴴ))).2
      rw [(hU j).conjTranspose.specNorm_mul_right, (hU j).specNorm_mul_left] at h
      rw [pow_succ]
      nlinarith [hD j (by omega), ih (by omega), specNorm_nonneg (A j)]
  refine (specNorm_sub_mul_mul_conjTranspose_le_sum hU hP0 hP A n).trans ?_
  calc ∑ j ∈ Finset.range n, specNorm (A (j + 1) - U j * A j * (U j)ᴴ)
      ≤ ∑ j ∈ Finset.range n, β * (1 + β) ^ j * specNorm (A 0) :=
        Finset.sum_le_sum fun j hj => by
          have hj' := Finset.mem_range.mp hj
          nlinarith [hD j hj', hgrow j hj'.le]
    _ = ((1 + β) ^ n - 1) * specNorm (A 0) := by rw [← Finset.sum_mul, sum_mul_one_add_pow]
    _ ≤ 8 * n * η * specNorm (A 0) := by
        refine mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _)
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        have hη8 : η ≤ 1 / 8 := le_trans (le_mul_of_one_le_left hη
          (by exact_mod_cast hn)) hnη
        have hnβ : n * β ≤ 9 / 2 * (n * η) := by
          simp only [β]; nlinarith [mul_nonneg n.cast_nonneg hη]
        refine (one_add_pow_sub_one_le hβ (by linarith)).trans ?_
        nlinarith [mul_nonneg n.cast_nonneg hβ]

/-- Rotating $\mathbf{e}_N$ to a computed vector: let $n$ adjacent rotations, step $j$ by the
exact Givens rotation $\mathbf{G}_j$ of the coefficients $(c_j, s_j)$ that
`NLAlib.givensCoeffs` computes from $(\bar g^{(j)}_{j+1}, -\bar g^{(j)}_j)$ (so that
$\mathbf{G}_j$ zeros entry $j$ of $\mathbf{g}^{(j)}$), take the vectors
$\mathbf{g}^{(j+1)}$ within $\eta\|\mathbf{g}^{(j)}\|$ of $\mathbf{G}_j\mathbf{g}^{(j)}$, and the
matrices $\mathbf{A}_{j+1}$ by a rounded rotation of the rows $j, j + 1$ and then of the columns
$j, j + 1$ of $\mathbf{A}_j$ (`NLAlib.IsRoundedRowRotation`, `NLAlib.IsRoundedColRotation`, relative
error $\eta \ge 0$), with $n\eta \le 1/8$ and $\mathbf{g}^{(0)} \ne 0$. Then there are a unitary
$\mathbf{Q}$ and $\lvert c\rvert = 1$ with
$$\|\mathbf{Q}\mathbf{e}_N - c\,\mathbf{g}^{(0)}/\|\mathbf{g}^{(0)}\|\| \le 5n\eta, \qquad
  \|\mathbf{A}_n - \mathbf{Q}^{\mathsf{H}}\mathbf{A}_0\mathbf{Q}\|_2 \le
  8n\eta\|\mathbf{A}_0\|_2\,.$$
The rounded coefficients and their application meet the hypotheses with $\eta = 12\boldsymbol{u}$
(`NLAlib.Ops.StdModel.norm_rotatePair_sub_le`). The last column is close to the direction of
$\mathbf{g}^{(0)}$, not equal to it: the computed rotations do not zero their entries exactly.
No printed source. -/
theorem exists_hasOrthonormalCols_rotateTo {η : ℝ} (hη : 0 ≤ η) (hnη : n * η ≤ 1 / 8)
    {cs : ℕ → ℂ × ℂ} {g : ℕ → Fin (n + 1) → ℂ} {A : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hcs : ∀ j : Fin n, cs j = givensCoeffs (star (g j j.succ)) (-star (g j j.castSucc)))
    (hg : ∀ j : Fin n, ‖WithLp.toLp 2 (g ((j : ℕ) + 1) -
      givens j.castSucc j.succ (cs j).1 (cs j).2 *ᵥ g j)‖ ≤ η * ‖WithLp.toLp 2 (g j)‖)
    (hA : ∀ j : Fin n, ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsRoundedRowRotation η j.castSucc j.succ (cs j).1 (cs j).2 (A j) A' ∧
        IsRoundedColRotation η j.castSucc j.succ (cs j).1 (cs j).2 A' (A ((j : ℕ) + 1)))
    (hg0 : g 0 ≠ 0) :
    ∃ (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ), HasOrthonormalCols Q ∧ ‖c‖ = 1 ∧
      ‖WithLp.toLp 2 ((fun k => Q k (Fin.last n)) -
          (c * ((‖WithLp.toLp 2 (g 0)‖⁻¹ : ℝ) : ℂ)) • g 0)‖ ≤ 5 * n * η ∧
      specNorm (A n - Qᴴ * A 0 * Q) ≤ 8 * n * η * specNorm (A 0) := by
  set U : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun j => if h : j < n then
    givens (⟨j, by omega⟩ : Fin (n + 1)) ⟨j + 1, by omega⟩ (cs j).1 (cs j).2 else 1 with hUdef
  have hUj : ∀ j : Fin n, U j = givens j.castSucc j.succ (cs j).1 (cs j).2 := fun j => by
    simp only [hUdef, dif_pos j.isLt]; rfl
  have hU : ∀ j, HasOrthonormalCols (U j) := fun j => by
    by_cases h : j < n
    · rw [show U j = U (⟨j, h⟩ : Fin n) from rfl, hUj]
      exact hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
        (by rw [hcs]; exact norm_givensCoeffs_fst_sq_add _ _)
    · simp only [hUdef, dif_neg h]; exact hasOrthonormalCols_one
  set P : ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun k => Nat.rec 1 (fun j Pj => U j * Pj) k
  have hPu : ∀ k, HasOrthonormalCols (P k) := fun k => by
    induction k with
    | zero => exact hasOrthonormalCols_one
    | succ k ih => exact (hU k).mul ih
  obtain ⟨c, hc1, hcol⟩ := exists_norm_conjTranspose_col_sub_le hη hnη hU (P := P) rfl
    (fun _ => rfl) hUj hcs (fun j => by rw [hUj]; exact hg j) hg0
  refine ⟨(P n)ᴴ, c, (hPu n).conjTranspose, hc1, hcol, ?_⟩
  rw [Matrix.conjTranspose_conjTranspose]
  exact specNorm_sub_rotateTo_le hη hnη hU rfl (fun _ => rfl) hUj hA

end NLAlib
