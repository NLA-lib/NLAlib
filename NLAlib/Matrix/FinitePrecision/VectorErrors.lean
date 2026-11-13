/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ArithmeticError
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector bounds for relative and absolute arithmetic errors

Coordinatewise arithmetic defects give Euclidean bounds with an absolute contribution
proportional to the square root of the dimension. These statements retain separate
multiplication and addition allowances and require no precision/dimension smallness window.
They do not assert successful execution or absence of overflow; the kernel consumers supply
those obligations from the existing arithmetic contract. [Higham2002, §2.2 and §3.1].

## Main results

* `NLAlib.Computation.AbsRelErr.norm_sub_le`: componentwise mixed errors lifted to vectors.
* `NLAlib.Computation.norm_sub_add_smul_le_of_absRelErr`: multiplication-addition defects.
* `NLAlib.Computation.norm_sub_smul_div_le_of_absRelErr`: rescaling a rounded division.
-/

@[expose] public section

namespace NLAlib.Computation

variable {n : Type*} [Fintype n]

/-- Componentwise mixed errors give a Euclidean error at most
$u\|\mathbf{x}\|+\sqrt{d}\eta$ in dimension $d$. Both allowances are nonnegative;
the statement includes dimension zero. -/
theorem AbsRelErr.norm_sub_le {u η : ℝ} {x z : n → ℝ}
    (h : ∀ i, AbsRelErr u η (x i) (z i)) (hu : 0 ≤ u) (hη : 0 ≤ η) :
    ‖WithLp.toLp 2 (x - z)‖ ≤
      u * ‖WithLp.toLp 2 x‖ + Real.sqrt (Fintype.card n) * η :=
  EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le hu hη h

/-- A coordinatewise rounded multiplication followed by addition has Euclidean error at most
$$u_a\|\mathbf{y}\|+(u_m+u_a+u_m u_a)\lvert a\rvert\|\mathbf{x}\|
\quad+\sqrt{d}\bigl((1+u_a)\eta_m+\eta_a\bigr)\,.$$
All four allowances are nonnegative. Multiplication and addition may use different precision
or underflow allowances; no division by a vector norm is needed. -/
theorem norm_sub_add_smul_le_of_absRelErr {um ua ηm ηa a : ℝ} {x y q z : n → ℝ}
    (hq : ∀ i, AbsRelErr um ηm (a * x i) (q i))
    (hz : ∀ i, AbsRelErr ua ηa (y i + q i) (z i))
    (hum : 0 ≤ um) (hua : 0 ≤ ua) (hηm : 0 ≤ ηm) (hηa : 0 ≤ ηa) :
    ‖WithLp.toLp 2 (y + a • x - z)‖ ≤
      ua * ‖WithLp.toLp 2 y‖ +
      (um + ua + um * ua) * |a| * ‖WithLp.toLp 2 x‖ +
      Real.sqrt (Fintype.card n) * ((1 + ua) * ηm + ηa) := by
  have hm := AbsRelErr.norm_sub_le hq hum hηm
  change ‖WithLp.toLp 2 (a • x - q)‖ ≤
    um * ‖WithLp.toLp 2 (a • x)‖ + Real.sqrt (Fintype.card n) * ηm at hm
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at hm
  have ha := AbsRelErr.norm_sub_le hz hua hηa
  change ‖WithLp.toLp 2 (y + q - z)‖ ≤
    ua * ‖WithLp.toLp 2 (y + q)‖ + Real.sqrt (Fintype.card n) * ηa at ha
  have hqnorm : ‖WithLp.toLp 2 q‖ ≤ |a| * ‖WithLp.toLp 2 x‖ +
      (um * (|a| * ‖WithLp.toLp 2 x‖) + Real.sqrt (Fintype.card n) * ηm) := by
    have ht := norm_sub_le (WithLp.toLp 2 (a • x)) (WithLp.toLp 2 (a • x - q))
    rw [← WithLp.toLp_sub, sub_sub_cancel, WithLp.toLp_smul, norm_smul,
      Real.norm_eq_abs] at ht
    exact ht.trans (add_le_add le_rfl hm)
  have hyq : ‖WithLp.toLp 2 (y + q)‖ ≤ ‖WithLp.toLp 2 y‖ + ‖WithLp.toLp 2 q‖ := by
    rw [WithLp.toLp_add]
    exact norm_add_le _ _
  have heq : y + a • x - z = (a • x - q) + (y + q - z) := by abel
  rw [heq, WithLp.toLp_add]
  have ht := (norm_add_le (WithLp.toLp 2 (a • x - q))
    (WithLp.toLp 2 (y + q - z))).trans (add_le_add hm ha)
  have hbound := mul_le_mul_of_nonneg_left (hyq.trans (add_le_add le_rfl hqnorm)) hua
  nlinarith only [ht, hbound]

/-- Rescaling componentwise division errors by a nonzero stored divisor gives
$$\|\mathbf{x}-b\mathbf{y}\|\le u\|\mathbf{x}\|+\lvert b\rvert\sqrt{d}\eta\,.$$
The allowances are nonnegative. The divisor may have either sign; no lower bound on its
magnitude or on the input norm is assumed. -/
theorem norm_sub_smul_div_le_of_absRelErr {u η b : ℝ} {x y : n → ℝ}
    (h : ∀ i, AbsRelErr u η (x i / b) (y i))
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hb : b ≠ 0) :
    ‖WithLp.toLp 2 (x - b • y)‖ ≤
      u * ‖WithLp.toLp 2 x‖ + |b| * Real.sqrt (Fintype.card n) * η := by
  have hs (i : n) : AbsRelErr u (|b| * η) (x i) (b * y i) := by
    exact (h i).abs_sub_mul_le_of_div hb
  have hv := AbsRelErr.norm_sub_le hs hu (mul_nonneg (abs_nonneg b) hη)
  change ‖WithLp.toLp 2 (x - b • y)‖ ≤
    u * ‖WithLp.toLp 2 x‖ + Real.sqrt (Fintype.card n) * (|b| * η) at hv
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hv

end NLAlib.Computation
