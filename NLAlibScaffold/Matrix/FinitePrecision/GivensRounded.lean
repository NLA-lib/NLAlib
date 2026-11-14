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
* a rotation of two rows (columns) of a matrix whose every column (row) pair is computed within
  $\eta$ of the exact rotation of the pair, relatively: within $2\eta\|\mathbf{A}\|_2$ in the
  spectral norm (`NLAlib.IsRoundedRowRotation.specNorm_sub_le`).

The last statement is the reusable rounded-kernel lemma: it turns a per-pair error, which is what
a program proof over a generic machine returns, into the spectral-norm error that
`NLAlib.IsPerturbedUnitarySimilar.of_specNorm_sub_le` consumes. Per two rows the error is
$O(\boldsymbol{u})\|\mathbf{A}\|_2$, so a sweep of $n$ rotations has backward error
$O(n\boldsymbol{u})$, better than the $32n^{3/2}\boldsymbol{u}$ of
[BanksGarzaVargasSrivastava2022, Lemma 3.5]. [Higham2002, Lemmas 19.7–19.8].

## Main definitions

* `NLAlib.roundedGivensCoeffs`: the coefficients computed by a machine, in the instruction order
  of the shifted QR program.
* `NLAlib.IsRoundedRowRotation`, `NLAlib.IsRoundedColRotation`: a rotation computed pairwise
  within a relative error.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-- The Givens coefficients computed by the machine `M` from the pair $(u, v)$, in the order of
the instructions of the shifted QR program: the squared radius as
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

/-- The coefficient `(1 + u)³ - 1` of three rounded operations lies in `[0, 3.04 u]`. -/
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

/-- Square root step: from a computed squared radius `Sh` with `|Sh - S| ≤ E S`, a computed
root `qh` with relative error `u` has error at most `13u/5` times `√S`. -/
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

/-- Division step: the quotient `c' ≈ a / r'` with relative error `u`, and `|r' - r| ≤ 13u r/5`,
has relative error at most `4u` against `a / r`. -/
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

/-- A complex number is within `k` of another, componentwise, when each real and imaginary
part is: `‖zt - z‖ ≤ k ‖z‖`. -/
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
computed radius `r'` is within `4u` of the exact one, when `|r' - r| ≤ 13u r/5`. -/
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

/-- **Rounded complex linear combination**: the pair computed by `NLAlib.Ops.Pair.linearWords`
from the pairs of $a, b, x, y$ is within $5\boldsymbol{u}(\lvert a\rvert\lvert x\rvert +
\lvert b\rvert\lvert y\rvert)$ of $a x + b y$, for $0 \le \boldsymbol{u} \le 1/100$
(each real component carries at most three roundings). [Higham2002, Lemma 3.5]. -/
theorem Ops.StdModel.norm_linearWords_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) (a b x y : ℂ) :
    ‖(⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
        (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) -
        (a * x + b * y)‖ ≤ 5 * u * (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) := by
  sorry

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

/-- **A rotation of two rows computed pairwise has spectral-norm error $2\eta\|\mathbf{A}\|_2$**:
the error is supported on two rows, its Frobenius norm is at most $\eta$ times the Frobenius
norm of those rows, which is at most $\sqrt 2\,\|\mathbf{A}\|_2$. [Higham2002, Lemma 19.8]. -/
theorem IsRoundedRowRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedRowRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - givens i j c s * A) ≤ 2 * η * specNorm A := by
  sorry

/-- **A rotation of two columns computed pairwise has spectral-norm error
$2\eta\|\mathbf{A}\|_2$.** [Higham2002, Lemma 19.8]. -/
theorem IsRoundedColRotation.specNorm_sub_le {η : ℝ} {i j : Fin n} {c s : ℂ}
    {A A' : Matrix (Fin n) (Fin n) ℂ} (h : IsRoundedColRotation η i j c s A A') (hη : 0 ≤ η) :
    specNorm (A' - A * (givens i j c s)ᴴ) ≤ 2 * η * specNorm A := by
  sorry

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
  sorry

end NLAlib
