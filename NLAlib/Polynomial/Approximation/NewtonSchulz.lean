/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Newton–Schulz iteration for the sign function

The cubic $g(x) = \tfrac12 x(3 - x^2)$ (`NLAlib.newtonSchulz`) fixes $-1$, $0$ and $1$, with
$g'(\pm 1) = 0$. For $0 < |x_0| < \sqrt{3}$ the exact iteration preserves the initial sign and
converges quadratically to it. At $x_0=2$, the first step is $-1$ and every later step equals $-1$.
Under the initial-value and roundoff bounds of the perturbed iteration theorem, it reaches
$\lvert 1 - x^2 \rvert \le \varepsilon$ after
`NLAlib.newtonSchulzSteps` $x_0$ $\varepsilon$ steps, about
$2\log_2(1/\lvert x_0 \rvert) + \log_2\log_2(1/\varepsilon)$ ([Shah2024, Section 2]). Applied to a
Hermitian matrix through the functional calculus it is the inverse-free iteration for the matrix
sign function.

## Main definitions

* `NLAlib.newtonSchulz`: the cubic $g$.
* `NLAlib.newtonSchulzSteps`: the step count of the perturbed scalar iteration.

## Main results

* `NLAlib.one_sub_newtonSchulz_sq`: $1 - g(x)^2 = (1 - x^2)^2(4 - x^2)/4$.
* `NLAlib.div_mul_abs_le_abs_newtonSchulz_of_abs_le`: $g$ grows the modulus by $11/8$ below $1/2$.
* `NLAlib.mul_newtonSchulz_add_pos`, `NLAlib.abs_le_abs_newtonSchulz_add`: Lemma 2.3.
* `NLAlib.abs_one_sub_newtonSchulz_add_sq_le`,
  `NLAlib.abs_one_sub_newtonSchulz_add_sq_le_add`: Lemma 2.4.
* `NLAlib.abs_one_sub_sq_le_of_newtonSchulzSteps_le`: Lemma 2.5.
-/

@[expose] public section

namespace NLAlib

/-- The **Newton–Schulz map** $g(x) = \tfrac12 x(3 - x^2)$, Newton's method for
$x^{-2} - 1 = 0$. [Shah2024, Section 2.1].
Algorithm: newton-schulz-sign -/
noncomputable def newtonSchulz (x : ℝ) : ℝ :=
  x * (3 - x ^ 2) / 2

/-- The **step count of the perturbed Newton–Schulz iteration** from $x_0$ to tolerance
$\varepsilon$:
$$N(x_0, \varepsilon) = \frac52 + 2\log_2\frac{1}{\min(\lvert x_0 \rvert, 1/2)} +
\log_2\log_2\frac{1}{\varepsilon} \,,$$
a real number; the iteration count is any natural number at least this value. Junk values: at
$x_0 = 0$ the middle term is $0$ (Mathlib's $0^{-1} = 0$), and the last term is $0$ unless
$\varepsilon < 1/2$. [Shah2024, Lemma 2.5], the quantity $N_{\mathrm{SCALAR}}$ there. -/
noncomputable def newtonSchulzSteps (x₀ ε : ℝ) : ℝ :=
  5 / 2 + 2 * Real.logb 2 (min |x₀| (1 / 2))⁻¹ + Real.logb 2 (Real.logb 2 ε⁻¹)

section Analysis

/-- The Newton–Schulz map is odd: $g(-x) = -g(x)$. -/
theorem newtonSchulz_neg (x : ℝ) : newtonSchulz (-x) = -newtonSchulz x := by
  unfold newtonSchulz
  ring

/-- The defect identity of the Newton–Schulz map: for every real $x$,
$$1 - g(x)^2 = \frac{(1 - x^2)^2(4 - x^2)}{4} \,.$$
No printed source; it gives both the range of $g$ and its quadratic convergence. -/
theorem one_sub_newtonSchulz_sq (x : ℝ) :
    1 - newtonSchulz x ^ 2 = (1 - x ^ 2) ^ 2 * (4 - x ^ 2) / 4 := by
  unfold newtonSchulz
  ring

/-- The Newton–Schulz map sends $[-2, 2]$ into $[-1, 1]$: $\lvert g(x) \rvert \le 1$ for
$\lvert x \rvert \le 2$. [Shah2024, proof of Lemma 2.5], there on $[-1.5, 1.5]$. -/
theorem abs_newtonSchulz_le_one {x : ℝ} (hx : |x| ≤ 2) : |newtonSchulz x| ≤ 1 := by
  have hx2 : x ^ 2 ≤ 4 := by nlinarith [sq_abs x, abs_nonneg x]
  have h1 := one_sub_newtonSchulz_sq x
  have h2 : 0 ≤ (1 - x ^ 2) ^ 2 * (4 - x ^ 2) / 4 :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
  nlinarith [sq_abs (newtonSchulz x), abs_nonneg (newtonSchulz x)]

/-- Every exact iterate after the first is bounded by one in magnitude when $\lvert x\rvert \le 2$.
[Higham2008, §8.3]. -/
theorem abs_iterate_newtonSchulz_le_one {x : ℝ} (hx : |x| ≤ 2) (k : ℕ) :
    |(newtonSchulz^[k + 1]) x| ≤ 1 := by
  induction k with
  | zero => exact abs_newtonSchulz_le_one hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact abs_newtonSchulz_le_one (ih.trans (by norm_num))

private theorem newtonSchulz_mem_Icc {x : ℝ} (hx : 0 ≤ x) (hx3 : x ^ 2 ≤ 3) :
    newtonSchulz x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (mul_nonneg hx (sub_nonneg.mpr hx3)) (by norm_num), ?_⟩
  apply (le_abs_self _).trans (abs_newtonSchulz_le_one _)
  rw [abs_of_nonneg hx]
  nlinarith

private theorem iterate_newtonSchulz_mem_Icc {x : ℝ} (hx : 0 ≤ x) (hx3 : x ^ 2 ≤ 3) (k : ℕ) :
    (newtonSchulz^[k + 1]) x ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => exact newtonSchulz_mem_Icc hx hx3
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply newtonSchulz_mem_Icc ih.1
    exact ((sq_le_sq₀ ih.1 zero_le_one).mpr ih.2).trans (by norm_num)

/-- From $x>0$ with $x^2<3$, all singular coefficients after the first cubic update belong
to $(0,1]$. [Higham2008, §8.3]. -/
theorem newtonSchulz_iterate_mem_Ioc {x : ℝ} (hx : 0 < x) (hx3 : x ^ 2 < 3) (k : ℕ) :
    (newtonSchulz^[k + 1]) x ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨?_, (iterate_newtonSchulz_mem_Icc hx.le hx3.le k).2⟩
  induction k with
  | zero => exact div_pos (mul_pos hx (sub_pos.mpr hx3)) (by norm_num)
  | succ k ih =>
    rw [Function.iterate_succ_apply', newtonSchulz]
    have h := (iterate_newtonSchulz_mem_Icc hx.le hx3.le k).2
    exact div_pos (mul_pos ih (by nlinarith [sq_nonneg ((newtonSchulz^[k + 1]) x - 1)]))
      (by norm_num)

/-- The scalar Gram defect after $k+1$ Newton–Schulz updates is bounded by the first defect
raised to $2^k$, for every $\lvert x\rvert\le 2$. [Higham2008, §8.3]. -/
theorem one_sub_iterate_newtonSchulz_sq_le_pow {x : ℝ} (hx : |x| ≤ 2) (k : ℕ) :
    1 - (newtonSchulz^[k + 1]) x ^ 2 ≤ (1 - newtonSchulz x ^ 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := abs_iterate_newtonSchulz_le_one hx k
    have he : 0 ≤ 1 - (newtonSchulz^[k + 1]) x ^ 2 := by
      nlinarith [sq_abs ((newtonSchulz^[k + 1]) x), abs_nonneg ((newtonSchulz^[k + 1]) x)]
    rw [Function.iterate_succ_apply', one_sub_newtonSchulz_sq]
    calc
      _ ≤ (1 - (newtonSchulz^[k + 1]) x ^ 2) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg (1 - (newtonSchulz^[k + 1]) x ^ 2))
          (sq_nonneg ((newtonSchulz^[k + 1]) x))]
      _ ≤ _ := by
        simpa only [← pow_mul, Nat.pow_succ] using pow_le_pow_left₀ he ih 2

/-- For $0\le x$ and $x^2\le 3$, the distance of every subsequent Newton–Schulz coefficient
to one is at most its Gram defect. [Higham2008, §8.3]. -/
theorem abs_iterate_newtonSchulz_sub_one_le {x : ℝ} (hx : 0 ≤ x) (hx3 : x ^ 2 ≤ 3) (k : ℕ) :
    |(newtonSchulz^[k + 1]) x - 1| ≤ 1 - (newtonSchulz^[k + 1]) x ^ 2 := by
  obtain ⟨hp, hle⟩ := iterate_newtonSchulz_mem_Icc hx hx3 k
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hle)]

open Filter in
open scoped Topology in
/-- Newton–Schulz iterates from $x>0$ with $x^2<3$ converge to one.
[Higham2008, §8.3]. -/
theorem tendsto_iterate_newtonSchulz {x : ℝ} (hx : 0 < x) (hx3 : x ^ 2 < 3) :
    Tendsto (fun k => (newtonSchulz^[k]) x) atTop (𝓝 1) := by
  have ⟨h0, h1⟩ := newtonSchulz_iterate_mem_Ioc hx hx3 0
  change 0 < newtonSchulz x at h0
  change newtonSchulz x ≤ 1 at h1
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by nlinarith [sq_nonneg (newtonSchulz x - 1)] : 0 ≤ 1 - newtonSchulz x ^ 2)
    (by nlinarith [sq_pos_of_pos h0] : 1 - newtonSchulz x ^ 2 < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hx2 : |x| ≤ 2 := by rw [abs_of_pos hx]; nlinarith
  have ht : Tendsto (fun k => (newtonSchulz^[k + 1]) x - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (abs_iterate_newtonSchulz_sub_one_le hx.le hx3.le k).trans
      (one_sub_iterate_newtonSchulz_sq_le_pow hx2 k)) hp
  have hh : Tendsto (fun k => (newtonSchulz^[k + 1]) x) atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using ht.add_const 1
  exact (tendsto_add_atTop_iff_nat 1).mp hh

/-- The Newton–Schulz map grows the modulus near zero: for $\lvert x \rvert \le 1/2$,
$\tfrac{11}{8}\lvert x \rvert \le \lvert g(x) \rvert$, since $g(x)/x = (3 - x^2)/2 \ge 11/8$.
No printed source; it makes the errors of the perturbed matrix iteration a geometric series. -/
theorem div_mul_abs_le_abs_newtonSchulz_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    11 / 8 * |x| ≤ |newtonSchulz x| := by
  have hsq : x ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs x, abs_nonneg x]
  unfold newtonSchulz
  rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 3 - x ^ 2), abs_two]
  nlinarith [mul_nonneg (abs_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 4 - x ^ 2)]

/-- **The perturbed Newton–Schulz step keeps the sign** (Lemma 2.3, first part): if
$\lvert \xi \rvert \le u$ and $u < \lvert x \rvert < \sqrt3 - (\sqrt3 - 1)u$, then $g(x) + \xi$
has the sign of $x$, that is $x(g(x) + \xi) > 0$. [Shah2024, Lemma 2.3], there with
$u \le 3/16$, not needed here.
Result: newton-schulz-sign-perturbed-step-keeps-sign -/
theorem mul_newtonSchulz_add_pos {u x ξ : ℝ} (hξ : |ξ| ≤ u) (hux : u < |x|)
    (hx : |x| < √3 - (√3 - 1) * u) : 0 < x * (newtonSchulz x + ξ) := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  have hu0 : 0 ≤ u := le_trans (abs_nonneg _) hξ
  have key : ∀ y η : ℝ, 0 < y → |η| ≤ u → u < y → y < √3 - (√3 - 1) * u →
      0 < y * (newtonSchulz y + η) := by
    intro y η hy hη huy hyu
    have hys : y < √3 := by nlinarith
    have hgu : u < newtonSchulz y := by
      unfold newtonSchulz
      rcases le_total y 1 with h1 | h1
      · nlinarith [mul_nonneg (mul_nonneg hy.le (sub_nonneg.2 h1)) (show (0:ℝ) ≤ 1 + y by linarith)]
      · have hG : 0 ≤ (√3 - y) * (√3 - 1) * (y - 1) * (y + √3 + 1) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
            (by linarith)
        have hc : ((√3 - y) / 2 - (√3 - 1) * y / 2) * (√3 ^ 2 - 3) = 0 := by rw [hs]; ring
        have hg : √3 - y ≤ (√3 - 1) * (y * (3 - y ^ 2) / 2) := by nlinarith [hG, hc]
        nlinarith [hg]
    exact mul_pos hy (by linarith [neg_abs_le η])
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · rw [abs_of_neg hneg] at hux hx
    have h := key (-x) (-ξ) (by linarith) (by rwa [abs_neg]) (by linarith) (by linarith)
    rw [newtonSchulz_neg] at h
    linarith [h, show -x * (-newtonSchulz x + -ξ) = x * (newtonSchulz x + ξ) by ring]
  · rw [abs_zero] at hux
    linarith
  · rw [abs_of_pos hpos] at hux hx
    exact key x ξ hpos hξ hux hx

/-- **The perturbed Newton–Schulz step does not decrease the modulus** (Lemma 2.3, second part):
if $\lvert \xi \rvert \le u$ and $\tfrac83 u \le \lvert x \rvert \le 1 - \tfrac83 u$, then
$\lvert x \rvert \le \lvert g(x) + \xi \rvert$. [Shah2024, Lemma 2.3].
Result: newton-schulz-sign-perturbed-step-modulus -/
theorem abs_le_abs_newtonSchulz_add {u x ξ : ℝ} (hξ : |ξ| ≤ u) (h₁ : 8 / 3 * u ≤ |x|)
    (h₂ : |x| ≤ 1 - 8 / 3 * u) : |x| ≤ |newtonSchulz x + ξ| := by
  have hξ' := abs_le.mp hξ
  have hK : ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ 1 - a → 3 / 4 * a ≤ t * (1 - t ^ 2) := by
    intro a t ha hat htb
    have ha2 : a ≤ 1 / 2 := by linarith
    have ht0 : 0 ≤ t := by linarith
    have hc : t ^ 2 + t * a + a ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ht0 (show 0 ≤ 1 - a - t by linarith),
        mul_nonneg ha (show 0 ≤ 1 - a by linarith)]
    have h1 := mul_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 hc)
    have h2 := mul_nonneg ha (show 0 ≤ 1 / 4 - a ^ 2 by nlinarith)
    nlinarith [h1, h2]
  have key : ∀ t : ℝ, 8 / 3 * u ≤ t → t ≤ 1 - 8 / 3 * u → t + u ≤ newtonSchulz t := by
    intro t ht1 ht2
    have hu : 0 ≤ u := le_trans (abs_nonneg _) hξ
    have := hK (8 / 3 * u) t (by positivity) ht1 ht2
    unfold newtonSchulz
    nlinarith
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at h₁ h₂ ⊢
    have := key x h₁ h₂
    exact le_trans (show x ≤ newtonSchulz x + ξ by linarith [hξ'.1]) (le_abs_self _)
  · rw [abs_of_neg hx0] at h₁ h₂ ⊢
    have h := key (-x) h₁ h₂
    rw [newtonSchulz_neg] at h
    exact le_trans (show -x ≤ -(newtonSchulz x + ξ) by linarith [hξ'.2]) (neg_le_abs _)

/-- **Quadratic decrease of the defect under perturbation** (Lemma 2.4, first part): if
$20\lvert \xi \rvert \le \lvert x \rvert \le 1 - \sqrt{10\lvert \xi \rvert}$, then
$$\lvert 1 - (g(x) + \xi)^2 \rvert \le \lvert 1 - x^2 \rvert^2 \,.$$
[Shah2024, Lemma 2.4].
Result: newton-schulz-sign-perturbed-defect -/
theorem abs_one_sub_newtonSchulz_add_sq_le {x ξ : ℝ} (h₁ : 20 * |ξ| ≤ |x|)
    (h₂ : |x| ≤ 1 - √(10 * |ξ|)) : |1 - (newtonSchulz x + ξ) ^ 2| ≤ |1 - x ^ 2| ^ 2 := by
  -- core: for `0 ≤ t ≤ 1` and the error bounds, with `y = g t`, `e = |η|`:
  -- `2 y e + e^2 ≤ (1 - t^2)^2 t^2 / 4`, then `|1 - (y + η)^2| ≤ (1 - t^2)^2`.
  have core : ∀ t η : ℝ, 0 ≤ t → t ≤ 1 → 20 * |η| ≤ t → t ≤ 1 - √(10 * |η|) →
      |1 - (newtonSchulz t + η) ^ 2| ≤ (1 - t ^ 2) ^ 2 := by
    intro t η ht0 ht1 hη1 hη2
    have he0 : 0 ≤ |η| := abs_nonneg η
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 10 * |η| by positivity)
    have hη2' : 10 * |η| ≤ (1 - t) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (10 * |η|)]
    have hy0 : 0 ≤ newtonSchulz t := by
      unfold newtonSchulz
      nlinarith [mul_nonneg ht0 (show (0:ℝ) ≤ 3 - t ^ 2 by nlinarith)]
    have hkey : 2 * newtonSchulz t * |η| + |η| ^ 2 ≤ (1 - t ^ 2) ^ 2 * t ^ 2 / 4 := by
      unfold newtonSchulz at *
      rcases le_total t (1 / 2) with h | h
      · have e1 : |η| ≤ t / 20 := by linarith
        have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
        have poly : 3 - t ^ 2 + 1 / 20 ≤ 5 * (1 - t ^ 2) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sq_nonneg t)]
        nlinarith [mul_le_mul_of_nonneg_right e1 (show (0:ℝ) ≤ 2 * (t * (3 - t ^ 2) / 2) + t / 20 by
            nlinarith [mul_nonneg ht0 (show (0:ℝ) ≤ 3 - t ^ 2 by nlinarith)]),
          mul_le_mul_of_nonneg_left e1 he0, mul_nonneg (sq_nonneg t) (sub_nonneg.2 poly)]
      · have e1 : |η| ≤ (1 - t) ^ 2 / 10 := by linarith
        have e2 : |η| ≤ 1 / 40 := by nlinarith
        have poly2 : 8 * (t * (3 - t ^ 2) / 2) + 1 / 10 ≤ 10 * t ^ 2 * (1 + t) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 ht1)]
        nlinarith [mul_le_mul_of_nonneg_right e1 (show (0:ℝ) ≤ 2 * (t * (3 - t ^ 2) / 2) + 1 / 40 by
            nlinarith [mul_nonneg ht0 (show (0:ℝ) ≤ 3 - t ^ 2 by nlinarith)]),
          mul_le_mul_of_nonneg_left e2 he0, mul_nonneg (sq_nonneg (1 - t)) (sub_nonneg.2 poly2)]
    have h1 := one_sub_newtonSchulz_sq t
    have ht4 : t ^ 2 ≤ 4 := by nlinarith
    have hd0 : 0 ≤ (1 - t ^ 2) ^ 2 * (4 - t ^ 2) / 4 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
    have hd1 : (1 - t ^ 2) ^ 2 * (4 - t ^ 2) / 4 ≤ (1 - t ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (1 - t ^ 2)) (sq_nonneg t)]
    rw [abs_le]
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_left (le_abs_self η) hy0,
        mul_le_mul_of_nonneg_left (neg_abs_le η) hy0, sq_abs η,
        mul_nonneg (sq_nonneg (1 - t ^ 2)) (sq_nonneg t)]
  rw [sq_abs]
  rcases le_total 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at h₁ h₂
    exact core x ξ hx0 (by linarith [Real.sqrt_nonneg (10 * |ξ|)]) h₁ h₂
  · rw [abs_of_nonpos hx0] at h₁ h₂
    have h := core (-x) (-ξ) (by linarith) (by linarith [Real.sqrt_nonneg (10 * |ξ|)])
      (by rw [abs_neg]; linarith) (by rw [abs_neg]; linarith)
    rwa [newtonSchulz_neg, show (-newtonSchulz x + -ξ) ^ 2 = (newtonSchulz x + ξ) ^ 2 by ring,
      neg_sq] at h

/-- **The defect bound with an additive error** (Lemma 2.4, second part): if
$\lvert x \rvert \le \sqrt2$ and $\lvert \xi \rvert \le 1$, then
$$\lvert 1 - (g(x) + \xi)^2 \rvert \le \lvert 1 - x^2 \rvert^2 + 4\lvert \xi \rvert \,.$$
[Shah2024, Lemma 2.4].
Result: newton-schulz-sign-perturbed-defect-additive -/
theorem abs_one_sub_newtonSchulz_add_sq_le_add {x ξ : ℝ} (hx : |x| ≤ √2) (hξ : |ξ| ≤ 1) :
    |1 - (newtonSchulz x + ξ) ^ 2| ≤ |1 - x ^ 2| ^ 2 + 4 * |ξ| := by
  have hx2 : x ^ 2 ≤ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs, Real.sq_sqrt (by norm_num)] at this
  have hs2 : √2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hx2' : |x| ≤ 2 := hx.trans hs2
  have hg1 := abs_newtonSchulz_le_one hx2'
  have h1 : 0 ≤ 1 - newtonSchulz x ^ 2 := by
    rw [one_sub_newtonSchulz_sq]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
  have h2 : 1 - newtonSchulz x ^ 2 ≤ (1 - x ^ 2) ^ 2 := by
    rw [one_sub_newtonSchulz_sq]
    nlinarith [mul_nonneg (sq_nonneg (1 - x ^ 2)) (sq_nonneg x)]
  have hgξ : |newtonSchulz x * ξ| ≤ |ξ| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg ξ) hg1
  have hξ2 : ξ ^ 2 ≤ |ξ| := by
    nlinarith [sq_abs ξ, abs_nonneg ξ]
  rw [sq_abs, abs_le]
  constructor <;>
    nlinarith [neg_abs_le (newtonSchulz x * ξ), le_abs_self (newtonSchulz x * ξ),
      sq_nonneg (1 - x ^ 2), abs_nonneg ξ]

/-- **The perturbed iteration stays in $[-1 - u, 1 + u]$**: if $\lvert x_0 \rvert \le 3/2$,
$u \le 1/2$ and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$, then
$\lvert x_{k+1} \rvert \le 1 + u$ for every $k$. [Shah2024, proof of Lemma 2.5]. -/
theorem abs_le_one_add_of_abs_sub_newtonSchulz_le {u : ℝ} {x : ℕ → ℝ} (hu : u ≤ 1 / 2)
    (hx₀ : |x 0| ≤ 3 / 2) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) (k : ℕ) :
    |x (k + 1)| ≤ 1 + u := by
  have hnext : ∀ k, |x k| ≤ 2 → |x (k + 1)| ≤ 1 + u := fun k hk => by
    have h1 := abs_sub_abs_le_abs_sub (x (k + 1)) (newtonSchulz (x k))
    have h2 := abs_newtonSchulz_le_one hk
    linarith [hstep k]
  have hall : ∀ k, |x k| ≤ 3 / 2 := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ n ih => linarith [hnext n (by linarith)]
  exact hnext k (by linarith [hall k])

/-- On $\tfrac56 \le \lvert x \rvert \le \tfrac32$ the Newton–Schulz map has modulus
at least $\tfrac9{16}$. -/
private lemma nine_sixteenths_le_abs_newtonSchulz {x : ℝ} (h₁ : 5 / 6 ≤ |x|) (h₂ : |x| ≤ 3 / 2) :
    9 / 16 ≤ |newtonSchulz x| := by
  unfold newtonSchulz
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h₁ h₂
    have h : 9 / 16 ≤ x * (3 - x ^ 2) / 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 - x)
        (by nlinarith : (0 : ℝ) ≤ x ^ 2 + 3 / 2 * x - 3 / 4)]
    exact le_abs.mpr (Or.inl h)
  · rw [abs_of_nonpos hx] at h₁ h₂
    have h : 9 / 16 ≤ -(x * (3 - x ^ 2) / 2) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 + x)
        (by nlinarith : (0 : ℝ) ≤ x ^ 2 - 3 / 2 * x - 3 / 4)]
    exact le_abs.mpr (Or.inr h)

/-- **The perturbed iteration stays away from zero**: if $20u \le \lvert x_0 \rvert \le 3/2$,
$u \le 1/16$ and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$, then
$\min(\lvert x_0 \rvert, 1/2) \le \lvert x_k \rvert$ for every $k$. No printed source; [Shah2024,
proof of Theorem 2.6] uses it implicitly when it bounds every step by $a/b$. -/
theorem min_abs_le_abs_of_abs_sub_newtonSchulz_le {u : ℝ} {x : ℕ → ℝ} (hu : u ≤ 1 / 16)
    (h₂₀ : 20 * u ≤ |x 0|) (hx₀ : |x 0| ≤ 3 / 2)
    (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) (k : ℕ) :
    min |x 0| (1 / 2) ≤ |x k| := by
  have hu0 : 0 ≤ u := le_trans (abs_nonneg _) (hstep 0)
  have hbd : ∀ k, |x k| ≤ 3 / 2 := by
    intro k
    cases k with
    | zero => exact hx₀
    | succ j =>
      exact (abs_le_one_add_of_abs_sub_newtonSchulz_le (by linarith) hx₀ hstep j).trans
        (by linarith)
  have hlow : 8 / 3 * u ≤ min |x 0| (1 / 2) := le_min (by linarith) (by linarith)
  induction k with
  | zero => exact min_le_left _ _
  | succ j ih =>
    rcases le_or_gt (|x j|) (1 - 8 / 3 * u) with h | h
    · have h1 : 8 / 3 * u ≤ |x j| := hlow.trans ih
      have key := abs_le_abs_newtonSchulz_add (ξ := x (j + 1) - newtonSchulz (x j))
        (hstep j) h1 h
      rw [add_sub_cancel] at key
      exact ih.trans key
    · have h5 : 9 / 16 ≤ |newtonSchulz (x j)| :=
        nine_sixteenths_le_abs_newtonSchulz (by linarith) (hbd j)
      linarith [min_le_right |x 0| (1 / 2), hstep j,
        abs_sub_abs_le_abs_sub (newtonSchulz (x j)) (x (j + 1)),
        abs_sub_comm (newtonSchulz (x j)) (x (j + 1))]

/-- One perturbed Newton–Schulz step keeps the defect $\lvert 1 - x^2 \rvert$ below
$\varepsilon \le 3/80$ when the perturbation is at most $\varepsilon / 10$. -/
private lemma abs_one_sub_sq_succ_le {u ε : ℝ} {x : ℕ → ℝ} (hε₁ : 10 * u ≤ ε)
    (hε₂ : ε ≤ 3 / 80) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) {k : ℕ}
    (hk : |1 - x k ^ 2| ≤ ε) : |1 - x (k + 1) ^ 2| ≤ ε := by
  have hξ := hstep k
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hk
  have h := abs_one_sub_newtonSchulz_add_sq_le_add
    (Real.abs_le_sqrt (x := x k) (by linarith [(abs_le.mp hk).1])) (hξ.trans (by linarith))
  rw [add_sub_cancel] at h
  nlinarith [abs_nonneg (1 - x k ^ 2), mul_le_mul hk hk (abs_nonneg _) hε0]

/-- Once the defect is below $\varepsilon$ it stays below $\varepsilon$. -/
private lemma abs_one_sub_sq_add_le {u ε : ℝ} {x : ℕ → ℝ} (hε₁ : 10 * u ≤ ε)
    (hε₂ : ε ≤ 3 / 80) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) {k : ℕ}
    (hk : |1 - x k ^ 2| ≤ ε) (j : ℕ) : |1 - x (k + j) ^ 2| ≤ ε := by
  induction j with
  | zero => exact hk
  | succ j ih => exact abs_one_sub_sq_succ_le hε₁ hε₂ hstep ih

/-- Two perturbed steps after the iterate leaves $[0, 1 - \sqrt\varepsilon]$ in modulus bring
the defect below $\varepsilon$. -/
private lemma abs_one_sub_sq_add_three_le {u ε : ℝ} {x : ℕ → ℝ} (hε₁ : 10 * u ≤ ε)
    (hε₂ : ε ≤ 3 / 80) (hx₀ : |x 0| ≤ 3 / 2)
    (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) {k : ℕ}
    (hk : 1 - √ε < |x (k + 1)|) : |1 - x (k + 3) ^ 2| ≤ ε := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (hstep 0)
  have hs0 : 0 ≤ √ε := Real.sqrt_nonneg ε
  have hss : √ε ^ 2 = ε := Real.sq_sqrt (by linarith)
  have hs1 : √ε ≤ 1 / 5 := by nlinarith
  have hup := abs_le_one_add_of_abs_sub_newtonSchulz_le (by linarith) hx₀ hstep k
  have hsq := sq_abs (x (k + 1))
  have h₀ : |1 - x (k + 1) ^ 2| ≤ 2 * √ε - √ε ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [pow_le_pow_left₀ (abs_nonneg _) hup 2]
    · nlinarith [pow_le_pow_left₀ (by linarith) hk.le 2]
  have h₁ := abs_one_sub_newtonSchulz_add_sq_le_add
    (Real.abs_le_sqrt (x := x (k + 1)) (by nlinarith [(abs_le.mp h₀).1]))
    ((hstep (k + 1)).trans (by linarith))
  rw [add_sub_cancel] at h₁
  have hm₁ : |1 - x (k + 1 + 1) ^ 2| ≤ √ε ^ 2 * ((2 - √ε) ^ 2 + 2 / 5) := by
    nlinarith [pow_le_pow_left₀ (abs_nonneg _) h₀ 2, hstep (k + 1)]
  have h₂ := abs_one_sub_newtonSchulz_add_sq_le_add
    (Real.abs_le_sqrt (x := x (k + 1 + 1)) (by nlinarith [(abs_le.mp hm₁).1]))
    ((hstep (k + 1 + 1)).trans (by linarith))
  rw [add_sub_cancel] at h₂
  have hq : √ε * ((2 - √ε) ^ 2 + 2 / 5) ≤ 3 / 4 := by nlinarith
  have hm₁sq : |1 - x (k + 1 + 1) ^ 2| ^ 2 ≤ 9 / 16 * √ε ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hm₁ 2
    have := pow_le_pow_left₀ (by positivity) hq 2
    nlinarith
  change |1 - x (k + 1 + 1 + 1) ^ 2| ≤ ε
  nlinarith [hstep (k + 1 + 1)]

/-- While the iterates stay in $[0, 1 - \sqrt\varepsilon]$ in modulus, the defect squares at
each step, starting below $1 - \min(\lvert x_0 \rvert, 1/2)^2$. -/
private lemma exists_lt_abs_or_abs_one_sub_sq_le {u ε : ℝ} {x : ℕ → ℝ} (hε₁ : 10 * u ≤ ε)
    (hε₂ : ε ≤ 3 / 80) (h₂₀ : 20 * u ≤ |x 0|) (hx₀ : |x 0| ≤ 3 / 2)
    (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) (j : ℕ) :
    (∃ k ≤ j, 1 - √ε < |x (k + 1)|) ∨
      |1 - x (j + 1) ^ 2| ≤ (1 - min |x 0| (1 / 2) ^ 2) ^ 2 ^ j := by
  have hu : 0 ≤ u := (abs_nonneg _).trans (hstep 0)
  have ha k := min_abs_le_abs_of_abs_sub_newtonSchulz_le (by linarith) h₂₀ hx₀ hstep k
  have ha20 : 20 * u ≤ min |x 0| (1 / 2) := le_min h₂₀ (by linarith)
  have ha0 : 0 ≤ min |x 0| (1 / 2) := le_min (abs_nonneg _) (by norm_num)
  have hs0 : 0 ≤ √ε := Real.sqrt_nonneg ε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  induction j with
  | zero =>
    by_cases h : 1 - √ε < |x 1|
    · exact Or.inl ⟨0, le_rfl, h⟩
    right
    replace h := not_lt.mp h
    simp only [zero_add, pow_zero, pow_one]
    have h1 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 := pow_le_pow_left₀ ha0 (ha 1) 2
    rw [sq_abs] at h1 h2
    rw [abs_of_nonneg (by nlinarith)]
    linarith
  | succ j ih =>
    rcases ih with ⟨k, hk, h⟩ | ih
    · exact Or.inl ⟨k, hk.trans j.le_succ, h⟩
    by_cases h : 1 - √ε < |x (j + 1)|
    · exact Or.inl ⟨j, j.le_succ, h⟩
    right
    replace h := not_lt.mp h
    have hξ := hstep (j + 1)
    have h' := abs_one_sub_newtonSchulz_add_sq_le
      ((mul_le_mul_of_nonneg_left hξ (by norm_num)).trans (ha20.trans (ha (j + 1))))
      (h.trans (sub_le_sub_left (Real.sqrt_le_sqrt (by linarith)) 1))
    rw [add_sub_cancel] at h'
    rw [pow_succ (2 : ℕ) j, pow_mul]
    exact h'.trans (pow_le_pow_left₀ (abs_nonneg _) ih 2)

/-- **Convergence of the perturbed Newton–Schulz iteration** (Lemma 2.5): if
$0 < \varepsilon \le 3/80$, $10u \le \varepsilon$, $x_0 \ne 0$ with
$20u \le \lvert x_0 \rvert \le 3/2$, and $\lvert x_{k+1} - g(x_k) \rvert \le u$ for every $k$,
then for every natural $N \ge N(x_0, \varepsilon)$ (`NLAlib.newtonSchulzSteps`),
$$\lvert 1 - x_N^2 \rvert \le \varepsilon \,.$$
[Shah2024, Lemma 2.5]; there $x_0 \ne 0$ is implicit in $u > 0$.
Result: newton-schulz-sign-perturbed-convergence -/
theorem abs_one_sub_sq_le_of_newtonSchulzSteps_le {u ε : ℝ} {x : ℕ → ℝ} (hε : 0 < ε)
    (hε₁ : 10 * u ≤ ε) (hε₂ : ε ≤ 3 / 80) (h₀ : 0 < |x 0|) (h₂₀ : 20 * u ≤ |x 0|)
    (hx₀ : |x 0| ≤ 3 / 2) (hstep : ∀ k, |x (k + 1) - newtonSchulz (x k)| ≤ u) {N : ℕ}
    (hN : newtonSchulzSteps (x 0) ε ≤ N) : |1 - x N ^ 2| ≤ ε := by
  set a := min |x 0| (1 / 2) with ha_def
  have ha0 : 0 < a := lt_min h₀ (by norm_num)
  have ha_inv : 2 ≤ a⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) ha0]; linarith [min_le_right |x 0| (1 / 2)]
  set L := Real.logb 2 ε⁻¹ with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one,
      le_inv_comm₀ (by norm_num) hε]
    linarith
  -- the step count gives `4 L / a ^ 2 < 2 ^ N`
  have hpow : 4 * L * a⁻¹ ^ 2 < (2 : ℝ) ^ N := by
    rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    unfold newtonSchulzSteps at hN
    push_cast
    linarith
  have hN3 : 3 ≤ N := by
    by_contra h
    have : (2 : ℝ) ^ N ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [pow_le_pow_left₀ (by norm_num) ha_inv 2]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  -- the iterates leave `[0, 1 - √ε]` in modulus by step `n + 1`
  have hexit : ∃ k ≤ n, 1 - √ε < |x (k + 1)| := by
    refine (exists_lt_abs_or_abs_one_sub_sq_le hε₁ hε₂ h₂₀ hx₀ hstep n).elim id fun h => ?_
    by_contra hne
    have hle : |x (n + 1)| ≤ 1 - √ε := not_lt.mp fun h' => hne ⟨n, le_rfl, h'⟩
    have hss : √ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    -- inside `[0, 1 - √ε]` the defect is at least `√ε`
    have hm : √ε ≤ |1 - x (n + 1) ^ 2| := by
      have := pow_le_pow_left₀ (abs_nonneg _) hle 2
      rw [sq_abs] at this
      exact le_abs.mpr (Or.inl (by nlinarith [Real.sqrt_nonneg ε]))
    have hεle : ε ≤ (1 - a ^ 2) ^ 2 ^ (n + 1) := by
      rw [← hss, pow_succ (2 : ℕ) n, pow_mul]
      exact (pow_le_pow_left₀ (Real.sqrt_nonneg ε) hm 2).trans
        (pow_le_pow_left₀ (abs_nonneg _) h 2)
    have hexp : (1 - a ^ 2) ^ 2 ^ (n + 1) ≤ Real.exp (((2 ^ (n + 1) : ℕ) : ℝ) * -a ^ 2) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by nlinarith [min_le_right |x 0| (1 / 2)])
        (by linarith [Real.add_one_le_exp (-a ^ 2)]) _
    have hlog : Real.log ε = -(L * Real.log 2) := by
      rw [hL, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne', Real.log_inv, neg_neg]
    have h4 : 4 * L < 2 ^ (n + 3) * a ^ 2 := by
      have := mul_lt_mul_of_pos_right hpow (pow_pos ha0 2)
      rwa [mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow, mul_one] at this
    have hlt : Real.exp (((2 ^ (n + 1) : ℕ) : ℝ) * -a ^ 2) < ε := by
      rw [← Real.exp_log hε, Real.exp_lt_exp, hlog]
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_lt_sub_one_of_pos two_pos (by norm_num)]
      have : (2 : ℝ) ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
      push_cast
      nlinarith [mul_lt_mul_of_pos_left hlog2 (by linarith : (0 : ℝ) < L)]
    linarith
  obtain ⟨k, hk, h⟩ := hexit
  have := abs_one_sub_sq_add_le hε₁ hε₂ hstep
    (abs_one_sub_sq_add_three_le hε₁ hε₂ hx₀ hstep h) (n - k)
  rwa [show k + 3 + (n - k) = n + 3 by omega] at this

/-- The step count decreases in the starting modulus: for $0 < a \le \lvert x_0 \rvert$,
$N(x_0, \varepsilon) \le N(a, \varepsilon)$. -/
theorem newtonSchulzSteps_le_of_le_abs {a x₀ ε : ℝ} (ha : 0 < a) (h : a ≤ |x₀|) :
    newtonSchulzSteps x₀ ε ≤ newtonSchulzSteps a ε := by
  unfold newtonSchulzSteps
  rw [abs_of_pos ha]
  have hm : 0 < min a (1 / 2) := lt_min ha (by norm_num)
  have hmono : min a (1 / 2) ≤ min |x₀| (1 / 2) :=
    le_min (le_trans (min_le_left _ _) h) (min_le_right _ _)
  have hinv : (min |x₀| (1 / 2))⁻¹ ≤ (min a (1 / 2))⁻¹ := inv_anti₀ hm hmono
  have hpos : 0 < (min |x₀| (1 / 2))⁻¹ := inv_pos.2 (lt_of_lt_of_le hm hmono)
  linarith [Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hpos hinv]

/-- The step count decreases in the tolerance: for $0 < \varepsilon' \le \varepsilon \le 1/2$,
$N(x_0, \varepsilon) \le N(x_0, \varepsilon')$. -/
theorem newtonSchulzSteps_le_of_le {x₀ ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (hε : ε ≤ 1 / 2) :
    newtonSchulzSteps x₀ ε ≤ newtonSchulzSteps x₀ ε' := by
  unfold newtonSchulzSteps
  have hεpos : 0 < ε := lt_of_lt_of_le hε' h
  have hinv : ε⁻¹ ≤ ε'⁻¹ := inv_anti₀ hε' h
  have hgt1 : 1 < ε⁻¹ := by rw [one_lt_inv₀ hεpos]; linarith
  have hpos : 0 < Real.logb 2 ε⁻¹ := Real.logb_pos (by norm_num) hgt1
  have hin : Real.logb 2 ε⁻¹ ≤ Real.logb 2 ε'⁻¹ :=
    Real.logb_le_logb_of_le (by norm_num) (inv_pos.2 hεpos) hinv
  linarith [Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hpos hin]

end Analysis


/-- The Newton–Schulz step count `NLAlib.newtonSchulzSteps` $s$ $\varepsilon$ is nonnegative for
$0 < s \le 1/2$ and $0 < \varepsilon \le 1/2$. -/
theorem newtonSchulzSteps_nonneg {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2) (hε : 0 < ε)
    (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

end NLAlib
