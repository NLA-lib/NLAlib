/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.VectorErrors

/-!
# Mixed errors in vector norms and normalization

A self-dot cache and its following square root are separate rounded operations. Their
error estimate keeps the absolute contribution, and assumes nonnegative cache explicitly.
Componentwise division bounds retain the positive computed divisor rather than hiding a
smallness condition in a relative error parameter. No execution or range success is asserted.

## Main results

* `NLAlib.Computation.AbsRelErr.abs_sub_le_of_sq_of_sqrt`: the decoded norm estimate.
* `NLAlib.Computation.abs_norm_sub_one_le_of_div_of_absRelErr`: linear normalization error.
* `NLAlib.Computation.abs_norm_sq_sub_one_le_of_div_of_absRelErr`: squared norm defect.
* `NLAlib.Computation.norm_sub_smul_inv_norm_le_of_div_of_absRelErr`: input-direction error.
-/

@[expose] public section

namespace NLAlib.Computation

/-- A nonnegative squared cache with mixed error gives a norm error bounded by
$\alpha r+\sqrt E$, for $r\ge0$, $\alpha\ge0$ and $E\ge0$. The absolute term is
retained even when the true norm is zero. -/
theorem AbsRelErr.abs_sub_sqrt_le_of_sq {α E r s : ℝ} (h : AbsRelErr α E (r ^ 2) s)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hE : 0 ≤ E) :
    |r - Real.sqrt s| ≤ α * r + Real.sqrt E := by
  have hs0 := Real.sqrt_nonneg s
  have hE0 := Real.sqrt_nonneg E
  have hss := Real.sq_sqrt hs
  have hEE := Real.sq_sqrt hE
  have he : -(α * r ^ 2 + E) ≤ r ^ 2 - s ∧ r ^ 2 - s ≤ α * r ^ 2 + E := by
    simpa only [abs_of_nonneg (sq_nonneg r)] using _root_.abs_le.mp h
  have hup : Real.sqrt s ≤ (1 + α) * r + Real.sqrt E := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hprod := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + α) hr) hE0
      nlinarith [mul_nonneg hα (sq_nonneg r), sq_nonneg (α * r)]
  have hlo : (1 - α) * r ≤ Real.sqrt s + Real.sqrt E := by
    by_cases hα1 : α ≤ 1
    · have hprod := mul_nonneg hs0 hE0
      have halpha := mul_nonneg (mul_nonneg hα (by linarith : 0 ≤ 1 - α)) (sq_nonneg r)
      nlinarith [sq_nonneg ((1 - α) * r - (Real.sqrt s + Real.sqrt E))]
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr).trans (add_nonneg hs0 hE0)
  exact _root_.abs_le.mpr ⟨by linarith, by linarith⟩
/-- Composing a nonnegative squared cache with a mixed-error square root gives
$$\lvert r-q\rvert\le(\alpha+u(1+\alpha))r+(1+u)\sqrt E+\eta\,.$$
The exact norm $r$, coefficients $\alpha,u$ and squared-cache allowance $E$ are nonnegative.
Cache nonnegativity is an explicit input, not inferred from an error bound. -/
theorem AbsRelErr.abs_sub_le_of_sq_of_sqrt {α E u η r s q : ℝ}
    (h : AbsRelErr α E (r ^ 2) s) (hsqrt : AbsRelErr u η (Real.sqrt s) q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hE : 0 ≤ E)
    (hu : 0 ≤ u) :
    |r - q| ≤ (α + u * (1 + α)) * r + (1 + u) * Real.sqrt E + η := by
  have hn := h.abs_sub_sqrt_le_of_sq hr hs hα hE
  have hup : Real.sqrt s ≤ (1 + α) * r + Real.sqrt E := by
    linarith [(_root_.abs_le.mp hn).1]
  have hroot := hsqrt.abs_sub_le
  rw [abs_of_nonneg (Real.sqrt_nonneg s)] at hroot
  calc
    |r - q| ≤ |r - Real.sqrt s| + |Real.sqrt s - q| := _root_.abs_sub_le _ _ _
    _ ≤ (α * r + Real.sqrt E) + (u * ((1 + α) * r + Real.sqrt E) + η) :=
      add_le_add hn (hroot.trans (by gcongr))
    _ = _ := by ring

/-- Rounded component divisions give a linear near-unit estimate
$\lvert\|\mathbf{y}\|-1\rvert\le(D+A)/b$, where
$D=u\|\mathbf{x}\|+b\sqrt d\eta$. The actual divisor $b$ is positive, $A$ bounds its norm
error, and the arithmetic allowances are nonnegative. An explicit margin $(D+A)/b<1$
therefore suffices for a nonzero output vector. No execution success is asserted. -/
theorem abs_norm_sub_one_le_of_div_of_absRelErr {n : Type*} [Fintype n]
    {u η b A : ℝ} {x y : n → ℝ}
    (h : ∀ i, AbsRelErr u η (x i / b) (y i))
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hb : 0 < b)
    (hscale : |‖WithLp.toLp 2 x‖ - b| ≤ A) :
    let D := u * ‖WithLp.toLp 2 x‖ + b * Real.sqrt (Fintype.card n) * η
    let t := (D + A) / b
    |‖WithLp.toLp 2 y‖ - 1| ≤ t := by
  intro D t
  have hd : ‖WithLp.toLp 2 (x - b • y)‖ ≤ D := by
    simpa only [D, abs_of_pos hb] using norm_sub_smul_div_le_of_absRelErr h hu hη hb.ne'
  have he : |‖WithLp.toLp 2 x‖ - b * ‖WithLp.toLp 2 y‖| ≤ D := by
    have hh := abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 (b • y))
    rw [← WithLp.toLp_sub, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hb] at hh
    exact hh.trans hd
  apply (le_div_iff₀ hb).2
  have ht := _root_.abs_sub_le (b * ‖WithLp.toLp 2 y‖) ‖WithLp.toLp 2 x‖ b
  rw [show b * ‖WithLp.toLp 2 y‖ - b = b * (‖WithLp.toLp 2 y‖ - 1) by ring,
    abs_mul, abs_of_pos hb] at ht
  rw [abs_sub_comm (b * ‖WithLp.toLp 2 y‖) ‖WithLp.toLp 2 x‖] at ht
  nlinarith

/-- The squared norm defect after rounded component divisions is at most $t(2+t)$,
where $D=u\|\mathbf{x}\|+b\sqrt d\eta$ and
$t=(D+A)/b$. Here $b>0$ is the actual divisor, $A$ bounds its norm error, and the two
arithmetic allowances are nonnegative. The bound remains explicit when normalization is
poor; no nonzero output or successful execution is assumed. -/
theorem abs_norm_sq_sub_one_le_of_div_of_absRelErr {n : Type*} [Fintype n]
    {u η b A : ℝ} {x y : n → ℝ}
    (h : ∀ i, AbsRelErr u η (x i / b) (y i))
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hb : 0 < b)
    (hscale : |‖WithLp.toLp 2 x‖ - b| ≤ A) :
    let D := u * ‖WithLp.toLp 2 x‖ + b * Real.sqrt (Fintype.card n) * η
    let t := (D + A) / b
    |‖WithLp.toLp 2 y‖ ^ 2 - 1| ≤ t * (2 + t) := by
  intro D t
  have hn : |‖WithLp.toLp 2 y‖ - 1| ≤ t :=
    abs_norm_sub_one_le_of_div_of_absRelErr h hu hη hb hscale
  have ht : 0 ≤ t := (abs_nonneg _).trans hn
  have hy : |‖WithLp.toLp 2 y‖ + 1| ≤ 2 + t := by
    rw [abs_of_nonneg (by positivity)]
    linarith [(_root_.abs_le.mp hn).2]
  rw [show ‖WithLp.toLp 2 y‖ ^ 2 - 1 =
    (‖WithLp.toLp 2 y‖ - 1) * (‖WithLp.toLp 2 y‖ + 1) by ring, abs_mul]
  exact mul_le_mul hn hy (abs_nonneg _) ht

/-- Rounding the component divisions and then normalizing their decoded direction gives
$$\|\mathbf{x}-b\|\mathbf{y}\|^{-1}\mathbf{y}\|\le2D+A\,,$$
where $D=u\|\mathbf{x}\|+b\sqrt d\eta$. The actual divisor is positive, the allowances
are nonnegative, and $A$ bounds its norm error. Total inversion includes a zero decoded
output; this result alone does not assert nonzero continuation or successful execution. -/
theorem norm_sub_smul_inv_norm_le_of_div_of_absRelErr {n : Type*} [Fintype n]
    {u η b A : ℝ} {x y : n → ℝ}
    (h : ∀ i, AbsRelErr u η (x i / b) (y i))
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hb : 0 < b)
    (hscale : |‖WithLp.toLp 2 x‖ - b| ≤ A) :
    ‖WithLp.toLp 2 (x - b • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      2 * (u * ‖WithLp.toLp 2 x‖ + b * Real.sqrt (Fintype.card n) * η) + A := by
  let D := u * ‖WithLp.toLp 2 x‖ + b * Real.sqrt (Fintype.card n) * η
  have hd : ‖WithLp.toLp 2 (x - b • y)‖ ≤ D := by
    simpa only [D, abs_of_pos hb] using norm_sub_smul_div_le_of_absRelErr h hu hη hb.ne'
  have hn := abs_norm_sub_one_le_of_div_of_absRelErr h hu hη hb hscale
  have hqa : b * |‖WithLp.toLp 2 y‖ - 1| ≤ D + A := by
    have ht : |‖WithLp.toLp 2 y‖ - 1| * b ≤ D + A := (le_div_iff₀ hb).1 hn
    nlinarith only [ht]
  have hnear : ‖WithLp.toLp 2 (b • y - b • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      b * |‖WithLp.toLp 2 y‖ - 1| := by
    rw [smul_smul, ← sub_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    by_cases hy : ‖WithLp.toLp 2 y‖ = 0
    · simp [hy, hb.le]
    · calc
        _ = |(b - b * ‖WithLp.toLp 2 y‖⁻¹) * ‖WithLp.toLp 2 y‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
        _ = |b * (‖WithLp.toLp 2 y‖ - 1)| := by congr 1; field_simp
        _ ≤ _ := by rw [abs_mul, abs_of_pos hb]
  have heq : x - b • (‖WithLp.toLp 2 y‖⁻¹ • y) =
      (x - b • y) + (b • y - b • (‖WithLp.toLp 2 y‖⁻¹ • y)) := by abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (by linarith [hnear.trans hqa])

end NLAlib.Computation
