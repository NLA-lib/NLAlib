/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.OneEigMath
public import NLAlib.Ops.Catalog.Scalar

/-!
# The rounding of `OneEig`

The computed words of `OneEig` ([BanksGarzaVargasSrivastava2025, §3.2]) in the standard model of
rounded arithmetic: the six directions $e^{i\pi j/3}$ computed from the literals $1$, $0$, $1/2$
and a rounded $\sqrt3$, the candidate points $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(\tau D) + s) +
w)$ of a round, and the bar $\mathrm{fl}(\tau\,\mathrm{fl}(0.66))$. A computed candidate is a net
point perturbed by the disk sample and a rounding error of order $\boldsymbol{u}\Sigma$, which the
margin of the six-point net absorbs (the paper's erratum P5); the precision condition of
`DistSpec` makes that rounding error small against the inner radius $\eta_1$.

## Main definitions

* `NLAlib.SmallEig.oneEigDirWords`, `NLAlib.SmallEig.oneEigDir`: the computed directions.
* `NLAlib.SmallEig.oneEigPointWord`: a computed candidate point.

## Main results

* `NLAlib.SmallEig.norm_oneEigDir_sub_hexDir_le`: the directions are within $5\boldsymbol{u}$.
* `NLAlib.SmallEig.norm_oneEigPointWord_sub_hexNet_le`: a candidate is a perturbed net point.
* `NLAlib.SmallEig.oneEigCandidates_spec`: the candidates of a good round.
* `NLAlib.SmallEig.mul_sq_le_of_distSpec_precision`: the precision against the inner radius.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Metric Ops

/-- The twelve direction words of `NLAlib.SmallEig.oneEigDirections` on the machine `M`: the
pairs $(1, 0)$, $(1/2, \sqrt3/2)$, $(-1/2, \sqrt3/2)$, $(-1, 0)$, $(-1/2, -\sqrt3/2)$,
$(1/2, -\sqrt3/2)$ as computed. -/
def oneEigDirWords (M : Machine ℝ) (i : ℕ) : ℝ :=
  [M.lit 1, M.lit 0, M.lit (1 / 2), M.mul (M.sqrt (M.lit 3)) (M.lit (1 / 2)),
    M.neg (M.lit (1 / 2)), M.mul (M.sqrt (M.lit 3)) (M.lit (1 / 2)), M.neg (M.lit 1), M.lit 0,
    M.neg (M.lit (1 / 2)), M.neg (M.mul (M.sqrt (M.lit 3)) (M.lit (1 / 2))), M.lit (1 / 2),
    M.neg (M.mul (M.sqrt (M.lit 3)) (M.lit (1 / 2)))].getD i 0

/-- The computed $\sqrt3/2$ of `NLAlib.SmallEig.oneEigDirections` is within $3.6\boldsymbol{u}$:
$\lvert\mathrm{fl}(\mathrm{fl}(\sqrt{\mathrm{fl}(3)})\,\mathrm{fl}(1/2)) - \sqrt3/2\rvert \le
3.6\boldsymbol{u}$ in the standard model at $0 \le \boldsymbol{u} \le 1/100$. -/
theorem abs_sqrtThreeWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) :
    |M.mul (M.sqrt (M.lit 3)) (M.lit (1 / 2)) - √3 / 2| ≤ 3.6 * u := by
  have hl : |M.lit 3 - 3| ≤ 3 * u := by have := hM.lit 3; simp at this; linarith
  have hh : |M.lit (1 / 2) - 1 / 2| ≤ u / 2 := by
    have := hM.lit (1 / 2); simp only [id] at this; push_cast at this
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this; linarith
  set ℓ := M.lit 3
  set h := M.lit (1 / 2)
  have hℓ0 : 0 ≤ ℓ := by have := (abs_le.mp hl).1; linarith
  have hq := hM.sqrt ℓ hℓ0
  have hr := hM.mul (M.sqrt ℓ) h
  simp only [id] at hq hr
  set q := M.sqrt ℓ
  set a := √ℓ with ha
  have ha2 : a ^ 2 = ℓ := Real.sq_sqrt hℓ0
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb1 : (1.73 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hb3 : √3 ≤ 1.7321 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hab : |a - √3| ≤ 1.74 * u := by
    have e : |a - √3| * (a + √3) = |ℓ - 3| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ a + √3), ← abs_mul]; congr 1; nlinarith
    have hpos : 1.73 ≤ a + √3 := by linarith
    nlinarith [abs_nonneg (a - √3)]
  have hqb : |q - √3| ≤ 3.49 * u := by
    have := abs_sub_le q a (√3)
    have : a ≤ 1.75 := by linarith [(abs_le.mp hab).2]
    nlinarith
  have hqh : |q * h - √3 / 2| ≤ 2.63 * u := by
    have e : q * h - √3 / 2 = (q - √3) * h + √3 * (h - 1 / 2) := by ring
    rw [e]
    have h1 : |h| ≤ 0.505 := by rw [abs_le] at hh ⊢; constructor <;> linarith
    calc |(q - √3) * h + √3 * (h - 1 / 2)| ≤ |q - √3| * |h| + √3 * |h - 1 / 2| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ √3)]
      _ ≤ 3.49 * u * 0.505 + 1.7321 * (u / 2) := by gcongr
      _ ≤ 2.63 * u := by nlinarith
  have hqh' : |q * h| ≤ 0.9 := by
    have := abs_sub_abs_le_abs_sub (q * h) (√3 / 2)
    rw [abs_of_pos (by positivity : (0:ℝ) < √3 / 2)] at this
    linarith
  calc |M.mul q h - √3 / 2| ≤ |M.mul q h - q * h| + |q * h - √3 / 2| := abs_sub_le _ _ _
    _ ≤ u * 0.9 + 2.63 * u := by gcongr; exact hr.trans (by gcongr)
    _ ≤ 3.6 * u := by linarith

/-- The direction `j` of `NLAlib.SmallEig.oneEigDirections` as computed on the machine `M`. -/
def oneEigDir (M : Machine ℝ) (j : ℕ) : ℂ :=
  ⟨oneEigDirWords M (2 * j), oneEigDirWords M (2 * j + 1)⟩

/-- The computed directions are accurate: in the standard model at
$0 \le \boldsymbol{u} \le 1/100$ with the literals $0$ and $1$ exact, each computed direction of
`NLAlib.SmallEig.oneEigDirections` is within $5\boldsymbol{u}$ of $e^{i\pi j/3}$. -/
theorem norm_oneEigDir_sub_hexDir_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (j : Fin 6) :
    ‖oneEigDir M j - hexDir j‖ ≤ 5 * u := by
  have hh : |M.lit (1 / 2) - 1 / 2| ≤ u / 2 := by
    have := hM.lit (1 / 2); simp only [id] at this; push_cast at this
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this; linarith
  have hr := abs_sqrtThreeWord_sub_le hM hu0 hu
  have hneg : ∀ a, M.neg a = -a := fun a => by simpa using hM.neg a
  have hre : ∀ k : Fin 6, (hexDir k).re = Real.cos (Real.pi * k / 3) := fun k =>
    Complex.exp_ofReal_mul_I_re _
  have him : ∀ k : Fin 6, (hexDir k).im = Real.sin (Real.pi * k / 3) := fun k =>
    Complex.exp_ofReal_mul_I_im _
  have hcos2 : Real.cos (Real.pi * 2 / 3) = -(1 / 2) := by
    rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hsin2 : Real.sin (Real.pi * 2 / 3) = √3 / 2 := by
    rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have hcos4 : Real.cos (Real.pi * 4 / 3) = -(1 / 2) := by
    rw [show Real.pi * 4 / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_three]
  have hsin4 : Real.sin (Real.pi * 4 / 3) = -(√3 / 2) := by
    rw [show Real.pi * 4 / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_pi_div_three]
  have hcos5 : Real.cos (Real.pi * 5 / 3) = 1 / 2 := by
    rw [show Real.pi * 5 / 3 = -(Real.pi / 3) + 2 * Real.pi by ring, Real.cos_add_two_pi,
      Real.cos_neg, Real.cos_pi_div_three]
  have hsin5 : Real.sin (Real.pi * 5 / 3) = -(√3 / 2) := by
    rw [show Real.pi * 5 / 3 = -(Real.pi / 3) + 2 * Real.pi by ring, Real.sin_add_two_pi,
      Real.sin_neg, Real.sin_pi_div_three]
  simp only [one_div] at hh hr
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, hre, him, oneEigDir]
  fin_cases j
  all_goals simp only [oneEigDirWords, h1, h0, one_div, mul_zero, List.getD_eq_getElem?_getD,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some, CharP.cast_eq_zero, zero_div, Real.cos_zero,
    sub_self, abs_zero,
    Nat.one_lt_ofNat, List.getElem_cons_succ, Real.sin_zero, add_zero, mul_nonneg_iff_of_pos_left,
    hneg, mul_one, Nat.reduceLT, Nat.cast_one, Real.cos_pi_div_three, Real.sin_pi_div_three,
    Nat.reduceMul, Nat.cast_ofNat, hcos2, sub_neg_eq_add, hsin2, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_div_cancel_right₀, Real.cos_pi, Real.sin_pi, hcos4, hsin4, hcos5,
    Nat.lt_add_one, hsin5]
  all_goals first
    | positivity
    | refine (add_le_add (abs_le.mpr ⟨?_, ?_⟩ : _ ≤ u / 2)
        (abs_le.mpr ⟨?_, ?_⟩ : _ ≤ 3.6 * u)).trans (by linarith) <;> linarith

/-- The candidate point $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(\tau D) + s) + w)$ of a round of
`NLAlib.SmallEig.oneEig`, componentwise on the machine `M`. -/
def oneEigPointWord (M : Machine ℝ) (τ : ℝ) (D s w : ℂ) : ℂ :=
  ⟨M.add (M.add (M.mul τ D.re) s.re) w.re, M.add (M.add (M.mul τ D.im) s.im) w.im⟩

/-- Three rounded operations $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(ax) + y) + z)$ in the standard
model at $0 \le \boldsymbol{u} \le 1/100$ are within
$4\boldsymbol{u}(\lvert ax\rvert + \lvert y\rvert + \lvert z\rvert)$ of $ax + y + z$. -/
theorem abs_add_add_mul_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 100) (a x y z : ℝ) :
    |M.add (M.add (M.mul a x) y) z - (a * x + y + z)| ≤ 4 * u * (|a * x| + |y| + |z|) := by
  have h1 := hM.mul a x
  have h2 := hM.add (M.mul a x) y
  have h3 := hM.add (M.add (M.mul a x) y) z
  simp only [id] at h1 h2 h3
  set p := M.mul a x
  set q := M.add p y
  set r := M.add q z
  have hp : |p| ≤ (1 + u) * |a * x| := by
    have := abs_sub_abs_le_abs_sub p (a * x); nlinarith
  have hq : |q - (p + y)| ≤ u * (|p| + |y|) := h2.trans (by gcongr; exact abs_add_le _ _)
  have hq' : |q| ≤ (1 + u) * (|p| + |y|) := by
    have := abs_sub_abs_le_abs_sub q (p + y)
    have := abs_add_le p y
    nlinarith
  have hr : |r - (q + z)| ≤ u * (|q| + |z|) := h3.trans (by gcongr; exact abs_add_le _ _)
  have e : r - (a * x + y + z) = (r - (q + z)) + (q - (p + y)) + (p - a * x) := by ring
  rw [e]
  have hA := abs_nonneg (a * x)
  have hY := abs_nonneg y
  have hZ := abs_nonneg z
  have hp' : |p| ≤ 1.01 * |a * x| := by nlinarith [mul_le_mul_of_nonneg_right hu hA]
  have hq'' : |q| ≤ 1.03 * |a * x| + 1.01 * |y| := by
    nlinarith [mul_le_mul_of_nonneg_right hu (add_nonneg (abs_nonneg p) hY)]
  calc |(r - (q + z)) + (q - (p + y)) + (p - a * x)|
      ≤ |r - (q + z)| + |q - (p + y)| + |p - a * x| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ u * (|q| + |z|) + u * (|p| + |y|) + u * |a * x| := by gcongr
    _ ≤ u * (1.03 * |a * x| + 1.01 * |y| + |z|) + u * (1.01 * |a * x| + |y|) + u * |a * x| := by
        gcongr
    _ ≤ 4 * u * (|a * x| + |y| + |z|) := by nlinarith

/-- The rounding of a candidate point of `OneEig`: in the standard model at
$0 \le \boldsymbol{u} \le 1/100$, the computed point `NLAlib.SmallEig.oneEigPointWord` is within
$8\boldsymbol{u}(\lvert\tau\rvert\lvert D\rvert + \lvert s\rvert + \lvert w\rvert)$ of
$\tau D + s + w$. -/
theorem norm_oneEigPointWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) (τ : ℝ) (D s w : ℂ) :
    ‖oneEigPointWord M τ D s w - (τ * D + s + w)‖ ≤ 8 * u * (|τ| * ‖D‖ + ‖s‖ + ‖w‖) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre := abs_add_add_mul_sub_le hM hu0 hu τ D.re s.re w.re
  have him := abs_add_add_mul_sub_le hM hu0 hu τ D.im s.im w.im
  simp only [oneEigPointWord, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    add_zero]
  rw [abs_mul] at hre him
  have h1 := Complex.abs_re_le_norm D
  have h2 := Complex.abs_im_le_norm D
  have h3 := Complex.abs_re_le_norm s
  have h4 := Complex.abs_im_le_norm s
  have h5 := Complex.abs_re_le_norm w
  have h6 := Complex.abs_im_le_norm w
  have hτ := abs_nonneg τ
  have : |τ| * |D.re| ≤ |τ| * ‖D‖ := by gcongr
  have : |τ| * |D.im| ≤ |τ| * ‖D‖ := by gcongr
  nlinarith

/-- A computed candidate of `OneEig` is a perturbed net point: in the standard model at
$0 \le \boldsymbol{u} \le 1/5000$, for a direction $D$ within $5\boldsymbol{u}$ of
$e^{i\pi j/3}$, $\tau \ge 0$, $\lvert s\rvert + \tau \le 4.06\,\Sigma$ and
$\lvert w\rvert \le 0.02\,\Sigma$, the computed point `NLAlib.SmallEig.oneEigPointWord` is within
$40\boldsymbol{u}\Sigma$ of $s + \tau D + w$ and within $60\boldsymbol{u}\Sigma$ of
$s + \tau e^{i\pi j/3} + w$. -/
theorem norm_oneEigPointWord_sub_hexNet_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 5000) {S τ : ℝ} {D s w : ℂ} {j : Fin 6}
    (hD : ‖D - hexDir j‖ ≤ 5 * u) (hτ : 0 ≤ τ) (hsτ : ‖s‖ + τ ≤ 4.06 * S)
    (hw : ‖w‖ ≤ 0.02 * S) :
    ‖oneEigPointWord M τ D s w - (τ * D + s + w)‖ ≤ 40 * u * S ∧
      ‖oneEigPointWord M τ D s w - (s + τ * hexDir j + w)‖ ≤ 60 * u * S := by
  have h8 := norm_oneEigPointWord_sub_le hM hu0 (by linarith) τ D s w
  have hS : 0 ≤ S := by nlinarith [norm_nonneg s]
  have hDn : ‖D‖ ≤ 1 + 5 * u := by
    have := norm_sub_norm_le D (hexDir j); rw [norm_hexDir] at this; linarith
  rw [abs_of_nonneg hτ] at h8
  have hτS : τ ≤ 4.06 * S := by linarith [norm_nonneg s]
  have hX : τ * ‖D‖ + ‖s‖ + ‖w‖ ≤ 4.1 * S := by
    have : τ * ‖D‖ ≤ τ + 5 * u * τ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hτS (by positivity : (0:ℝ) ≤ 5 * u)]
  have h1 : ‖oneEigPointWord M τ D s w - (τ * D + s + w)‖ ≤ 32.8 * u * S := by
    nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0:ℝ) ≤ 8 * u)]
  refine ⟨h1.trans (by nlinarith), ?_⟩
  have e : oneEigPointWord M τ D s w - (s + τ * hexDir j + w) =
      (oneEigPointWord M τ D s w - (τ * D + s + w)) + τ * (D - hexDir j) := by ring
  rw [e]
  have h2 : ‖(τ : ℂ) * (D - hexDir j)‖ ≤ 5 * u * (4.06 * S) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ]
    nlinarith [mul_le_mul_of_nonneg_left hτS (by positivity : (0:ℝ) ≤ 5 * u)]
  calc _ ≤ ‖oneEigPointWord M τ D s w - (τ * D + s + w)‖ + ‖(τ : ℂ) * (D - hexDir j)‖ :=
        norm_add_le _ _
    _ ≤ 32.8 * u * S + 5 * u * (4.06 * S) := add_le_add h1 h2
    _ ≤ 60 * u * S := by nlinarith

/-- The bar of a round of `OneEig` is above $0.6501\,\tau$: in the standard model at
$0 \le \boldsymbol{u} \le 1/5000$, for $\tau > 0$,
$0.6501\,\tau < \mathrm{fl}(\tau\,\mathrm{fl}(0.66))$. -/
theorem lt_mul_lit_sixtySix {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : u ≤ 1 / 5000) {τ : ℝ} (hτ : 0 < τ) :
    0.6501 * τ < M.mul τ (M.lit (66 / 100)) := by
  have hl := hM.lit (66 / 100)
  have hm := hM.mul τ (M.lit (66 / 100))
  simp only [id] at hl hm
  push_cast at hl
  rw [abs_of_pos (by norm_num : (0:ℝ) < 66 / 100)] at hl
  obtain ⟨hl1, -⟩ := abs_le.mp hl
  have hk : 0.6597 ≤ M.lit (66 / 100) := by nlinarith
  have hk' : M.lit (66 / 100) ≤ 0.6602 := by nlinarith [(abs_le.mp hl).2]
  rw [abs_of_pos (by positivity : 0 < τ * M.lit (66 / 100))] at hm
  obtain ⟨hm1, -⟩ := abs_le.mp hm
  nlinarith [mul_le_mul_of_nonneg_left hk hτ.le, mul_le_mul_of_nonneg_left hk' hτ.le,
    mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ τ * M.lit (66 / 100))]

/-- The candidates of a good round of `OneEig`: in the standard model at
$0 \le \boldsymbol{u} \le 1/5000$ with the literals $0$ and $1$ exact, let $\beta > 0$,
$\eta_2 \le 0.02\,\Sigma$, $\eta_2 + 60\boldsymbol{u}\Sigma \le 0.027\,\beta$, an estimate
$\tau > 0.9\beta$ of the distance from $s$ to the $d_i$ within $10\%$,
$\lvert s\rvert + \tau \le 4.06\,\Sigma$, $\lvert w\rvert \le \eta_2$, and every
$s + \tau D_j + w$ ($D_j$ the computed directions) at distance at least
$\eta_1 + 40\boldsymbol{u}\Sigma$ from every $d_i$. Then every computed candidate
`NLAlib.SmallEig.oneEigPointWord` has modulus at most $10\Sigma$, distance at least $\eta_1$ from
every $d_i$ and lies within $\eta_2 + 60\boldsymbol{u}\Sigma$ of the net point
$s + \tau e^{i\pi j/3}$, and $1.1$ times the distance of some candidate is at most
$0.6501\,\tau$. -/
theorem oneEigCandidates_spec {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 5000) (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) {n : ℕ} {d : Fin (n + 1) → ℂ}
    {S β η₁ η₂ τ : ℝ} {s w : ℂ} (hβ : 0 < β) (hηr : η₂ + 60 * u * S ≤ 0.027 * β)
    (hη₂S : η₂ ≤ 0.02 * S) (hτβ : 0.9 * β < τ)
    (hacc : 0.9 * infDist s (Set.range d) ≤ τ ∧ τ ≤ 1.1 * infDist s (Set.range d))
    (hsτ : ‖s‖ + τ ≤ 4.06 * S) (hw : ‖w‖ ≤ η₂)
    (hfar : ∀ (j : Fin 6) (i : Fin (n + 1)),
      η₁ + 40 * u * S ≤ ‖s + τ * oneEigDir M j + w - d i‖) :
    (∀ j : Fin 6, (‖oneEigPointWord M τ (oneEigDir M j) s w‖ ≤ 10 * S ∧
        ∀ i, η₁ ≤ ‖d i - oneEigPointWord M τ (oneEigDir M j) s w‖) ∧
      ‖oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j)‖ ≤ η₂ + 60 * u * S) ∧
    ∃ j : Fin 6, 1.1 * (⨅ i, ‖oneEigPointWord M τ (oneEigDir M j) s w - d i‖) ≤ 0.6501 * τ := by
  have hτ0 : 0 < τ := by linarith
  have hS : 0 ≤ S := by nlinarith [norm_nonneg s]
  have hnear : ∀ j : Fin 6, ‖oneEigPointWord M τ (oneEigDir M j) s w -
      (τ * oneEigDir M j + s + w)‖ ≤ 40 * u * S ∧
      ‖oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j + w)‖ ≤ 60 * u * S :=
    fun j => norm_oneEigPointWord_sub_hexNet_le hM hu0 hu
      (norm_oneEigDir_sub_hexDir_le hM hu0 (by linarith) h0 h1 j) hτ0.le hsτ (hw.trans hη₂S)
  have hpt : ∀ j : Fin 6, ‖oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j)‖ ≤
      η₂ + 60 * u * S := fun j => by
    have e : oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j) =
        (oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j + w)) + w := by ring
    rw [e]
    linarith [norm_add_le (oneEigPointWord M τ (oneEigDir M j) s w - (s + τ * hexDir j + w)) w,
      (hnear j).2]
  have hnet : ∀ j : Fin 6, ‖s + τ * hexDir j‖ ≤ ‖s‖ + τ := fun j => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_hexDir, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
  refine ⟨fun j => ⟨⟨?_, fun i => ?_⟩, hpt j⟩, ?_⟩
  · have := norm_sub_norm_le (oneEigPointWord M τ (oneEigDir M j) s w) (s + τ * hexDir j)
    nlinarith [hpt j, hnet j, mul_le_mul_of_nonneg_right hu hS]
  · have h1 := hfar j i
    have h2 := (hnear j).1
    have e : d i - oneEigPointWord M τ (oneEigDir M j) s w =
        -((s + τ * oneEigDir M j + w - d i) +
          (oneEigPointWord M τ (oneEigDir M j) s w - (τ * oneEigDir M j + s + w))) := by ring
    rw [e, norm_neg]
    have := norm_sub_norm_le (s + τ * oneEigDir M j + w - d i)
      (-(oneEigPointWord M τ (oneEigDir M j) s w - (τ * oneEigDir M j + s + w)))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  · obtain ⟨j, hj⟩ := exists_infDist_hexNet_le (Set.range_nonempty d) (Set.finite_range d) hacc
      hτ0
    refine ⟨j, ?_⟩
    rw [← infDist_range_eq_iInf]
    have := infDist_le_infDist_add_dist (x := oneEigPointWord M τ (oneEigDir M j) s w)
      (y := s + τ * hexDir j) (s := Set.range d)
    rw [dist_eq_norm] at this
    linarith [hpt j]

/-- The precision of `OneEig` against its inner radius: if
$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(\eta_1/(2N + 20\Sigma))^m$ with $\kappa \ge 1$,
$m \ge 2$, $n \ge 1$, $N \ge 0$, $\Sigma > 0$, $0 < \eta_1 \le 20\Sigma$ and $\boldsymbol{u} \ge 0$,
then $480000\,\boldsymbol{u}\Sigma^2 \le \eta_1^2$. -/
theorem mul_sq_le_of_distSpec_precision {n m : ℕ} {u κ η₁ S N : ℝ}
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / (2 * N + 20 * S)) ^ m) (hκ : 1 ≤ κ)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (hN : 0 ≤ N) (hS : 0 < S) (hη₁ : 0 < η₁) (hη₁S : η₁ ≤ 20 * S)
    (hu0 : 0 ≤ u) : 480000 * u * S ^ 2 ≤ η₁ ^ 2 := by
  set x := η₁ / (2 * N + 20 * S) with hx
  have hx0 : 0 < x := by positivity
  have hxS : x ≤ η₁ / (20 * S) := div_le_div_of_nonneg_left hη₁.le (by positivity) (by linarith)
  have hx1 : x ≤ 1 := hxS.trans ((div_le_one (by positivity)).mpr hη₁S)
  have hxm : x ^ m ≤ x ^ 2 := pow_le_pow_of_le_one hx0.le hx1 hm
  have hk : (8004 * κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hn4 : (4 : ℝ) ≤ (n + 1) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hxm' : (8004 * κ)⁻¹ * x ^ m ≤ x ^ 2 :=
    (mul_le_of_le_one_left (by positivity) hk).trans hxm
  have hx2 : x ^ 2 ≤ (η₁ / (20 * S)) ^ 2 := pow_le_pow_left₀ hx0.le hxS 2
  have h1200 : 1200 * u ≤ (η₁ / (20 * S)) ^ 2 := by nlinarith
  rw [div_pow, le_div_iff₀ (by positivity)] at h1200
  nlinarith

end NLAlib.SmallEig
