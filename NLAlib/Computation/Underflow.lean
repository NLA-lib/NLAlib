/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract

/-!
# Arithmetic errors with an absolute allowance

`NLAlib.Computation.AbsRelErr` permits an absolute error in addition to relative error.
The absolute allowance can describe gradual underflow in a finite-exponent format or the
quantization error of fixed-point arithmetic. It is independent of the word representation,
rounding rule, operation charge and storage width. The interpretation and range conditions
remain those of `NLAlib.Computation.IsArithErrSem`.

The allowances can vary with the operation: IEEE addition and subtraction need no absolute
underflow allowance, whereas multiplication and division do. A relative-only contract transfers
to this relation, but its all-range success assumptions do not certify a finite-exponent backend.
[Higham2002, §2.2].

## Main results

* `NLAlib.Computation.RelErr.absRelErr`: relative errors admit a nonnegative absolute allowance.
* `NLAlib.Computation.AbsRelErr.relErr`: a zero absolute allowance recovers relative error.
* `NLAlib.Computation.AbsRelErr.abs_add_sub_le`: multiplication-addition error composition.
* `NLAlib.Computation.AbsRelErr.abs_le_of_eq_zero`: magnitude compatible with a computed zero.
* `NLAlib.Computation.IsRelErrSem.isArithErrSem_absRelErr`: existing contract compatibility.
-/

@[expose] public section

namespace NLAlib.Computation

/-- An exact value $a$ and a computed value $z$ have mixed error allowances $u$ and $\eta$ when
$\lvert a-z\rvert \le u\lvert a\rvert+\eta$. Nonnegativity of the allowances is a separate
hypothesis where needed. [Higham2002, §2.2], the standard model with gradual underflow. -/
def AbsRelErr (u η a z : ℝ) : Prop := |a - z| ≤ u * |a| + η

/-- The mixed-error predicate is exactly its defining absolute-error inequality. -/
theorem absRelErr_iff {u η a z : ℝ} : AbsRelErr u η a z ↔ |a - z| ≤ u * |a| + η :=
  Iff.rfl

namespace AbsRelErr

variable {u v η ζ a b q z um ua ηm ηa : ℝ}

/-- Read the absolute-error inequality from the mixed-error interface. -/
theorem abs_sub_le (h : AbsRelErr u η a z) : |a - z| ≤ u * |a| + η := h

/-- Increasing either allowance preserves the mixed-error certificate. -/
theorem mono (h : AbsRelErr u η a z) (hu : u ≤ v) (hη : η ≤ ζ) :
    AbsRelErr v ζ a z := by
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg a)) hη)

/-- A computed value is bounded by the exact magnitude and both error allowances. -/
theorem abs_le (h : AbsRelErr u η a z) : |z| ≤ (1 + u) * |a| + η := by
  calc
    |z| = |a - (a - z)| := by congr 1; ring
    _ ≤ |a| + |a - z| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-(a - z))
    _ ≤ |a| + (u * |a| + η) := add_le_add le_rfl h
    _ = (1 + u) * |a| + η := by ring

/-- A zero absolute allowance recovers relative error when the relative allowance is
nonnegative, including an exact value of zero. -/
theorem relErr (h : AbsRelErr u 0 a z) (hu : 0 ≤ u) : RelErr u a z := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hz : z = 0 := by
      have hzero : |z| ≤ 0 := by simpa only [AbsRelErr, zero_sub, abs_neg, abs_zero,
        mul_zero, add_zero] using h
      exact abs_nonpos_iff.mp hzero
    exact ⟨0, by simpa only [abs_zero] using hu, by simp only [hz, zero_mul]⟩
  · refine ⟨(z - a) / a, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr ha)]
      simpa only [AbsRelErr, add_zero, abs_sub_comm] using h
    · field_simp
      ring

/-- A mixed defect can be absorbed into a larger relative budget $v\ge0$ whenever
$\eta\le(v-u)\lvert a\rvert$. The scale condition is explicit, and permits an exact value of zero
only when the absolute allowance can also be absorbed there. -/
theorem relErr_of_le (h : AbsRelErr u η a z) (hv : 0 ≤ v)
    (hη : η ≤ (v - u) * |a|) : RelErr v a z := by
  have hbound : AbsRelErr v 0 a z := by
    change |a - z| ≤ v * |a| + 0
    have he := h.abs_sub_le
    nlinarith only [he, hη]
  exact hbound.relErr hv

/-- Above a positive exact-value scale $\tau$, mixed error gives relative error
$u+\eta/\tau$. Both original allowances are nonnegative. This is a conditional scale
transfer, not an assertion that an algorithm remains above the scale. -/
theorem relErr_of_abs_ge (h : AbsRelErr u η a z) (hu : 0 ≤ u) (hη : 0 ≤ η)
    {τ : ℝ} (hτ : 0 < τ) (ha : τ ≤ |a|) : RelErr (u + η / τ) a z := by
  apply h.relErr_of_le (add_nonneg hu (div_nonneg hη hτ.le))
  have he : η / τ * τ = η := div_mul_cancel₀ η hτ.ne'
  have hb := mul_le_mul_of_nonneg_left ha (div_nonneg hη hτ.le)
  nlinarith only [he, hb]

/-- Multiplying back a rounded quotient gives
$\lvert a-bz\rvert\le u\lvert a\rvert+\lvert b\rvert\eta$ for a nonzero divisor $b$.
This remains valid when the computed
quotient is zero and requires no sign or smallness assumption. -/
theorem abs_sub_mul_le_of_div {b : ℝ} (h : AbsRelErr u η (a / b) z) (hb : b ≠ 0) :
    |a - b * z| ≤ u * |a| + |b| * η := by
  have heq : b * (a / b) = a := mul_div_cancel₀ a hb
  have habs : |b| * |a / b| = |a| := by rw [← abs_mul, heq]
  calc
    |a - b * z| = |b| * |a / b - z| := by rw [← abs_mul, mul_sub, heq]
    _ ≤ |b| * (u * |a / b| + η) :=
      mul_le_mul_of_nonneg_left h.abs_sub_le (abs_nonneg b)
    _ = u * (|b| * |a / b|) + |b| * η := by ring
    _ = u * |a| + |b| * η := by rw [habs]

/-- Mixed multiplication and addition errors compose with independent precision and absolute
allowances. If $q$ approximates $a$ and $z$ approximates $b+q$, the returned value differs from
$b+a$ by at most $u_a\lvert b\rvert+(u_m+u_a+u_m u_a)\lvert a\rvert+
(1+u_a)\eta_m+\eta_a$. Only the addition allowance must be nonnegative. -/
theorem abs_add_sub_le (hm : AbsRelErr um ηm a q) (ha : AbsRelErr ua ηa (b + q) z)
    (hua : 0 ≤ ua) :
    |b + a - z| ≤ ua * |b| + (um + ua + um * ua) * |a| +
      (1 + ua) * ηm + ηa := by
  have hsum : |b + q| ≤ |b| + ((1 + um) * |a| + ηm) :=
    (abs_add_le b q).trans (add_le_add le_rfl hm.abs_le)
  calc
    |b + a - z| = |(a - q) + (b + q - z)| := by congr 1; ring
    _ ≤ |a - q| + |b + q - z| := abs_add_le _ _
    _ ≤ (um * |a| + ηm) + (ua * |b + q| + ηa) := add_le_add hm ha
    _ ≤ (um * |a| + ηm) + (ua * (|b| + ((1 + um) * |a| + ηm)) + ηa) := by
      exact add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left hsum hua) le_rfl)
    _ = ua * |b| + (um + ua + um * ua) * |a| + (1 + ua) * ηm + ηa := by ring

/-- A computed zero permits a nonzero exact value only within the absolute-error allowance. -/
theorem mul_abs_le_of_eq_zero (h : AbsRelErr u η a 0) : (1 - u) * |a| ≤ η := by
  have hzero : |a| ≤ u * |a| + η := by simpa only [AbsRelErr, sub_zero] using h
  nlinarith

/-- If the relative allowance is less than one, a computed zero certifies
$\lvert a\rvert \le \eta/(1-u)$. This does not assert that the exact value is zero. -/
theorem abs_le_of_eq_zero (h : AbsRelErr u η a 0) (hu : u < 1) :
    |a| ≤ η / (1 - u) := by
  apply (le_div_iff₀ (sub_pos.mpr hu)).2
  simpa only [mul_comm] using h.mul_abs_le_of_eq_zero

/-- A positive margin between the exact magnitude and its mixed error envelope prevents
the computed value from vanishing. No sign assumption on the exact value is required. -/
theorem ne_zero (h : AbsRelErr u η a z) (hmargin : η < (1 - u) * |a|) : z ≠ 0 := by
  intro hz
  subst z
  exact (not_le_of_gt hmargin) h.mul_abs_le_of_eq_zero

/-- A nonnegative exact value whose lower error margin is positive has a positive computed
value. This is a sufficient guard certificate even when underflow is permitted. -/
theorem pos (h : AbsRelErr u η a z) (ha : 0 ≤ a) (hmargin : η < (1 - u) * a) :
    0 < z := by
  have hsub : a - z ≤ u * a + η := by
    exact (le_abs_self (a - z)).trans (by simpa only [AbsRelErr, abs_of_nonneg ha] using h)
  nlinarith

end AbsRelErr

/-- Relative error is a mixed-error certificate for every nonnegative absolute allowance. -/
theorem RelErr.absRelErr {u η a z : ℝ} (h : RelErr u a z) (hη : 0 ≤ η) :
    AbsRelErr u η a z := by
  obtain ⟨δ, hδ, rfl⟩ := h
  calc
    |a - a * (1 + δ)| = |a| * |δ| := by
      rw [show a - a * (1 + δ) = -a * δ by ring, abs_mul, abs_neg]
    _ ≤ |a| * u := mul_le_mul_of_nonneg_left hδ (abs_nonneg a)
    _ ≤ u * |a| + η := by linarith

/-- A relative-error semantics also satisfies the existing arithmetic interface with any
nonnegative operation-dependent absolute allowances. The original range and success conditions
are retained, so this bridge makes no new claim about overflow or finite machine formats. -/
theorem IsRelErrSem.isArithErrSem_absRelErr {P K : Type} {u : P → ℝ}
    {η : P → BinOp → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem)
    (hη : ∀ p op, 0 ≤ η p op) (hsafe : ∀ p, safe p 0) :
    IsArithErrSem (fun p op => AbsRelErr (u p) (η p op)) dec safe sem := by
  have harith := h.isArithErrSem hsafe
  exact { harith with bin_err := fun p op x y z hop hrun =>
    (harith.bin_err p op x y z hop hrun).absRelErr (hη p op) }

/-- A floor-relative semantics supplies mixed arithmetic error with absolute allowance
$u\tau$, for nonnegative unit roundoff and floor and an exact zero literal. The floor contract
alone permits a nonzero rounded zero, so exactness is required separately. All range conditions
are retained; in particular this does not replace range obligations by global success.
[Higham2002, §2.2]. -/
theorem IsFloorRelErrSem.isArithErrSem_absRelErr {P K : Type} {u τ : P → ℝ}
    {dec : P → K → ℝ} {safe : P → ℝ → Prop} {sem : ScalarSem P K}
    (h : IsFloorRelErrSem u τ dec safe sem) (hu : ∀ p, 0 ≤ u p)
    (hτ : ∀ p, 0 ≤ τ p) (hlit : IsExactIntLit dec sem 0) :
    IsArithErrSem (fun p _ => AbsRelErr (u p) (u p * τ p)) dec safe sem := by
  refine ⟨?_, h.bin_ok, ?_, h.neg, h.conj⟩
  · intro p op x y z hop hrun
    exact (h.bin_err p op x y z hop hrun).trans (by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [hτ p])
        (by linarith [abs_nonneg (op.realOp (dec p x) (dec p y))])) (hu p))
  · intro p
    simpa only [Nat.cast_zero] using hlit p 0 le_rfl

end NLAlib.Computation
