/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import NLAlib.ForMathlib.Analysis.Convex.SupportingLine
public import NLAlib.ForMathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.ComputeDegree
import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Chebyshev growth outside the unit interval

Radical formulas and lower bounds for Mathlib's first-kind Chebyshev polynomials, the
monotonicity of their derivatives on $[1, \infty)$, and the supporting lines of the squared
Chebyshev filter that this monotonicity gives.
These are upstream candidates in `Polynomial.Chebyshev`.

## Main results

* `Polynomial.Chebyshev.eval_T_real_eq_of_one_le`: the radical closed form.
* `Polynomial.Chebyshev.pow_div_two_le_eval_T_real`: exponential lower growth.
* `Polynomial.Chebyshev.sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real`:
  the square-root condition-ratio lower bound.
* `Polynomial.Chebyshev.eval_T_two_mul`: $T_{2j}(x) = T_j(2x^2 - 1)$.
* `Polynomial.Chebyshev.monotoneOn_eval_T_real`: $T_q$ is monotone on $[1, \infty)$.
* `Polynomial.Chebyshev.abs_eval_T_comp_C_mul_X_sub_one_le`: the shifted filter $T_n(2x/s - 1)$
  is bounded by one on $[0, s]$.
* `Polynomial.Chebyshev.exp_mul_sqrt_div_two_le_eval_T_real`: the gap form of Chebyshev growth,
  $\tfrac12 e^{2q\sqrt{r}} \le T_q((1 + r)/(1 - r))$.
* `Polynomial.Chebyshev.exp_mul_sqrt_div_two_le_abs_eval_T_comp`: the shifted filter
  $T_d(2x/\tau^2 - 1)$ is at least $\tfrac12 e^{4d\sqrt{(s - \tau)/(s + \tau)}}$ on $[s^2, \infty)$.
* `Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_of_le`: a filter of degree at most $d$ that
  is large on $[s^2, \infty)$ and small on $[0, \tau^2]$, with ratio
  $4e^{-8d\sqrt{(s - \tau)/(s + \tau)}}$.
* `Polynomial.Chebyshev.le_exp_of_eval_T_real_le`: an inverse of Chebyshev growth,
  $T_q(x) \le y \Rightarrow x \le \exp((\log(2y)/q)^2/2)$.
* `Polynomial.Chebyshev.eval_iterate_derivative_T_real_nonneg`,
  `Polynomial.Chebyshev.monotoneOn_eval_iterate_derivative_T_real`: every derivative of $T_n$ is
  nonnegative and non-decreasing on $[1, \infty)$.
* `Polynomial.Chebyshev.hasSupportingLineOn_mul_eval_T_sq`: the squared Chebyshev filter
  $y\,T_j(2y - 1)^2$, not convex on $[0, \infty)$, has a supporting line there at every $x \ge 1$,
  which lets Jensen's inequality pass through it (`HasSupportingLineOn.le_integral_comp`).
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Real

/-- **Radical closed form of Chebyshev polynomials.** For $x\ge1$,
$$T_q(x)=\frac{(x+\sqrt{x^2-1})^q+(x-\sqrt{x^2-1})^q}{2}.$$
[Saad2003, §6.11.1, Eq. (6.111)], with the reciprocal term rewritten algebraically.

Result: chebyshev-growth
-/
theorem eval_T_real_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ (q : ℤ)).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ q + (x - Real.sqrt (x ^ 2 - 1)) ^ q) / 2 := by
  have hs : 0 < x + √(x ^ 2 - 1) := by positivity
  have h := T_real_cosh (arcosh x) (q : ℤ)
  rw [cosh_arcosh hx] at h
  rw [h, arcosh, ← add_sqrt_self_sq_sub_one_inv hx, Int.cast_natCast, ← Real.log_pow,
    cosh_log (pow_pos hs q), inv_pow]

/-- For $x\ge1$, the Chebyshev polynomial satisfies
$$(x+\sqrt{x^2-1})^q/2\le T_q(x).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem pow_div_two_le_eval_T_real {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ q / 2 ≤ (T ℝ (q : ℤ)).eval x := by
  rw [eval_T_real_eq_of_one_le hx]
  have hs : 0 ≤ x - √(x ^ 2 - 1) := by
    rw [← add_sqrt_self_sq_sub_one_inv hx]
    positivity
  have := pow_nonneg hs q
  linarith

/-- For $0<a<b$, the condition-ratio form of Chebyshev growth is
$$\frac12\left(\frac{\sqrt b+\sqrt a}{\sqrt b-\sqrt a}\right)^q
\le T_q\left(\frac{b+a}{b-a}\right).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (q : ℕ) :
    ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) ^ q / 2 ≤
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  have key : ∀ s t : ℝ, 0 < s → s < t →
      (t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2) +
        √(((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1) = (t + s) / (t - s) := by
    intro s t hs hst
    have hd : 0 < t ^ 2 - s ^ 2 := by nlinarith
    have hts : 0 < t - s := by linarith
    have hsq : ((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1 =
        (2 * t * s / (t ^ 2 - s ^ 2)) ^ 2 := by
      field_simp
      ring
    have ht : 0 < t := by linarith
    rw [hsq, Real.sqrt_sq (div_nonneg (by positivity) hd.le)]
    field_simp
    ring
  have h := key (√a) (√b) (Real.sqrt_pos.2 ha) (Real.sqrt_lt_sqrt ha.le hab)
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt (by linarith)] at h
  rw [← h]
  exact pow_div_two_le_eval_T_real (by rw [le_div_iff₀ (by linarith)]; linarith) q

/-- **Chebyshev composition with $T_2$**: $T_{2j}(x) = T_j(2x^2 - 1)$, for every integer $j$ and
every commutative ring. [TroppWebber2023, Lemma 9.3], part 1 in the form used there. -/
theorem eval_T_two_mul {R : Type*} [CommRing R] (j : ℤ) (x : R) :
    (T R (2 * j)).eval x = (T R j).eval (2 * x ^ 2 - 1) := by
  rw [mul_comm, T_mul, eval_comp, T_two]
  simp

/-- **Monotonicity outside the unit interval**: $T_q$ is non-decreasing on $[1, \infty)$.
[TroppWebber2023, Lemma 9.3], part 3. -/
theorem monotoneOn_eval_T_real (q : ℕ) :
    MonotoneOn (fun x : ℝ => (T ℝ (q : ℤ)).eval x) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx' : (1 : ℝ) ≤ x := hx
  have hy' : (1 : ℝ) ≤ y := hy
  simp only
  rw [← cosh_arcosh hx', ← cosh_arcosh hy', T_real_cosh, T_real_cosh, cosh_le_cosh,
    abs_of_nonneg (by have := arcosh_nonneg hx'; positivity),
    abs_of_nonneg (by have := arcosh_nonneg hy'; positivity)]
  exact mul_le_mul_of_nonneg_left
    ((arcosh_le_arcosh (by linarith) (by linarith)).2 hxy) (Nat.cast_nonneg q)

/-- The shifted Chebyshev filter is bounded by one on $[0, s]$: for $s > 0$ and
$0 \le x \le s$, $\lvert T_n(2x/s - 1) \rvert \le 1$. The constant is `Polynomial.C`, written
out because `Polynomial.Chebyshev.C` shadows it here. Upstream candidate. -/
theorem abs_eval_T_comp_C_mul_X_sub_one_le (n : ℤ) {s x : ℝ} (hs : 0 < s)
    (hx : x ∈ Set.Icc 0 s) : |((T ℝ n).comp (Polynomial.C (2 / s) * X - 1)).eval x| ≤ 1 := by
  simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]
  refine abs_eval_T_real_le_one n (abs_le.mpr ⟨?_, ?_⟩)
  · have : 0 ≤ 2 / s * x := mul_nonneg (by positivity) hx.1
    linarith
  · have : 2 / s * x ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs]
      linarith [hx.2]
    linarith

/-- **Chebyshev growth in terms of a relative gap**: for $0 \le r < 1$,
$$\frac12 e^{2q\sqrt{r}} \le T_q\Bigl(\frac{1 + r}{1 - r}\Bigr)\,.$$
With $r$ a relative gap $\gamma$, $(1 + \gamma)/(1 - \gamma)$ is the ratio of the two singular
values. [TroppWebber2023, Lemma 9.3], part 3. -/
theorem exp_mul_sqrt_div_two_le_eval_T_real (q : ℕ) {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    exp (2 * q * √r) / 2 ≤ (T ℝ (q : ℤ)).eval ((1 + r) / (1 - r)) := by
  rcases h₀.eq_or_lt with rfl | hr
  · norm_num [T_eval_one]
  have hs₁ : √r < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
  have h := sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real hr h₁ q
  rw [Real.sqrt_one] at h
  refine le_trans ?_ h
  gcongr
  rw [show 2 * (q : ℝ) * √r = q * (2 * √r) by ring, Real.exp_nat_mul]
  gcongr
  exact exp_two_mul_le_one_add_div_one_sub (Real.sqrt_nonneg r) hs₁

/-- The shifted Chebyshev filter above a level: for $0 < \tau \le s$, a degree $d$ and
$x \ge s^2$,
$$\tfrac12 e^{4d\sqrt{(s - \tau)/(s + \tau)}} \le \lvert T_d(2x/\tau^2 - 1) \rvert\,,$$
since $T_d(2y^2 - 1) = T_{2d}(y)$ at $y = \sqrt{x}/\tau \ge s/\tau$. The constant is
`Polynomial.C`, written out because `Polynomial.Chebyshev.C` shadows it here. Upstream
candidate. -/
theorem exp_mul_sqrt_div_two_le_abs_eval_T_comp (d : ℕ) {s τ x : ℝ} (hτ : 0 < τ) (hτs : τ ≤ s)
    (hx : s ^ 2 ≤ x) :
    exp (4 * d * √((s - τ) / (s + τ))) / 2 ≤
      |((T ℝ d).comp (Polynomial.C (2 / τ ^ 2) * X - 1)).eval x| := by
  set γ := (s - τ) / (s + τ) with hγ
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have hγ1 : γ < 1 := by rw [hγ, div_lt_one (by linarith)]; linarith
  have hratio : (1 + γ) / (1 - γ) = s / τ := by
    rw [hγ, one_add_div (by linarith), one_sub_div (by linarith), div_div_div_cancel_right₀
      (by linarith)]
    rw [div_eq_div_iff (by linarith) hτ.ne']
    ring
  have hx0 : 0 ≤ x := (sq_nonneg s).trans hx
  have hy : s ≤ √x := Real.le_sqrt_of_sq_le hx
  have h1 : 1 ≤ s / τ := by rw [le_div_iff₀ hτ]; linarith
  have hsy : s / τ ≤ √x / τ := div_le_div_of_nonneg_right hy hτ.le
  have hmono := monotoneOn_eval_T_real (2 * d) h1 (h1.trans hsy) hsy
  have hgrowth := exp_mul_sqrt_div_two_le_eval_T_real (2 * d) hγ0 hγ1
  rw [hratio] at hgrowth
  have hT : (T ℝ ((2 * d : ℕ) : ℤ)).eval (√x / τ) = (T ℝ (d : ℤ)).eval (2 * (√x / τ) ^ 2 - 1) := by
    rw [← eval_T_two_mul]
    push_cast
    rfl
  have hxy : 2 / τ ^ 2 * x - 1 = 2 * (√x / τ) ^ 2 - 1 := by
    rw [div_pow, Real.sq_sqrt hx0]
    ring
  have hexp : exp (2 * ((2 * d : ℕ) : ℝ) * √γ) = exp (4 * d * √γ) := by
    push_cast
    ring_nf
  rw [hexp] at hgrowth
  simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]
  rw [hxy, ← hT]
  exact (hgrowth.trans hmono).trans (le_abs_self _)

/-- **A Chebyshev filter between two levels**: for real $0 \le \tau \le s$ with $s > 0$ and a
degree $d$, there are a real polynomial $f$ of degree at most $d$ and constants $c > 0$ and $a$
with $\lvert f(x) \rvert \ge c$ for every $x \ge s^2$, $\lvert f(x) \rvert \le a$ for every
$x \in [0, \tau^2]$, and
$$\Bigl(\frac{a}{c}\Bigr)^2 \le 4\exp\Bigl(-8d\sqrt{\frac{s - \tau}{s + \tau}}\Bigr)\,.$$
For $\tau > 0$ the filter is $f(x) = T_d(2x/\tau^2 - 1)$ with $a = 1$ and
$c = \tfrac12 e^{4d\sqrt{(s - \tau)/(s + \tau)}}$; for $\tau = 0$ it is $x^d$.
[MuscoMusco2015, Lemma 5]; there a polynomial normalized at the level $(1 + \gamma)\alpha$ and
bounded by $\alpha/2^{q\sqrt{\gamma} - 1}$ on $[0, \alpha]$, here the ratio $(a/c)^2$ for any two
levels, at the rate of `Polynomial.Chebyshev.exp_mul_sqrt_div_two_le_eval_T_real`. Upstream
candidate. -/
theorem exists_degree_lt_div_sq_le_exp_of_le {s τ : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) (hs : 0 < s)
    (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ x, s ^ 2 ≤ x → c ≤ |f.eval x|) ∧
      (∀ x ∈ Set.Icc 0 (τ ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt ((s - τ) / (s + τ))) := by
  rcases hτ.eq_or_lt with rfl | hτ'
  · -- $\tau = 0$: the power $x^d$ vanishes at $0$ for $d \ge 1$.
    refine ⟨X ^ d, by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_self d, (s ^ 2) ^ d,
      (0 : ℝ) ^ d, by positivity, fun x hx => ?_, fun x hx => ?_, ?_⟩
    · rw [eval_pow, eval_X, abs_of_nonneg (pow_nonneg ((sq_nonneg s).trans hx) d)]
      exact pow_le_pow_left₀ (sq_nonneg s) hx d
    · have hx0 : x = 0 := le_antisymm (by simpa using hx.2) hx.1
      simp [hx0]
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · norm_num
      · rw [zero_pow hd.ne', zero_div, zero_pow two_ne_zero]
        positivity
  set γ := (s - τ) / (s + τ)
  refine ⟨(T ℝ (d : ℤ)).comp (Polynomial.C (2 / τ ^ 2) * X - 1), ?_, exp (4 * d * √γ) / 2, 1,
    by positivity, fun x hx => exp_mul_sqrt_div_two_le_abs_eval_T_comp d hτ' hτs hx,
    fun x hx => abs_eval_T_comp_C_mul_X_sub_one_le _ (by positivity) hx, ?_⟩
  · refine degree_le_natDegree.trans_lt ?_
    have h := natDegree_T_comp_le (d : ℤ) (p := Polynomial.C (2 / τ ^ 2) * X - 1)
      (by compute_degree)
    rw [Int.natAbs_natCast] at h
    exact_mod_cast h.trans_lt (by omega)
  · refine le_of_eq ?_
    rw [div_div_eq_mul_div, one_mul, div_pow, show -8 * (d : ℝ) * √γ =
      -(4 * (d : ℝ) * √γ) + -(4 * (d : ℝ) * √γ) by ring, exp_add, exp_neg]
    field_simp
    ring

/-- **Inverting Chebyshev growth**: for $q > 0$ and $x \ge 1$, if $T_q(x) \le y$ then
$$x \le \exp\Bigl(\frac{1}{2}\Bigl(\frac{\log(2y)}{q}\Bigr)^2\Bigr)\,.$$
Stated as an implication, with no inverse function: $T_q(x) = \cosh(q\operatorname{arcosh}x)$,
$\operatorname{arcosh} y \le \log(2y)$ and $\cosh t \le e^{t^2/2}$. The hypothesis $1 \le y$ follows
from the others. [TroppWebber2023, Lemma 9.3], part 4. -/
theorem le_exp_of_eval_T_real_le {q : ℕ} (hq : 0 < q) {x y : ℝ} (hx : 1 ≤ x)
    (h : (T ℝ (q : ℤ)).eval x ≤ y) : x ≤ exp ((log (2 * y) / q) ^ 2 / 2) := by
  have ha : 0 ≤ arcosh x := arcosh_nonneg hx
  have hT := T_real_cosh (arcosh x) (q : ℤ)
  rw [cosh_arcosh hx, Int.cast_natCast] at hT
  have hqa : 0 ≤ q * arcosh x := by positivity
  -- $e^{q a} \le 2\cosh(q a) = 2 T_q(x) \le 2y$, so $q a \le \log(2y)$.
  have h2y : exp (q * arcosh x) ≤ 2 * y := by
    have := cosh_eq (q * arcosh x)
    have := exp_pos (-(q * arcosh x))
    linarith
  have hlog : q * arcosh x ≤ log (2 * y) :=
    (le_log_iff_exp_le (lt_of_lt_of_le (exp_pos _) h2y)).2 h2y
  have hle : arcosh x ≤ log (2 * y) / q := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    linarith
  calc x = cosh (arcosh x) := (cosh_arcosh hx).symm
    _ ≤ exp (arcosh x ^ 2 / 2) := cosh_le_exp_half_sq _
    _ ≤ exp ((log (2 * y) / q) ^ 2 / 2) := by gcongr

/-- Every derivative of $T_n$ is a combination of $T_0, \dots, T_n$ with natural coefficients, so it
is nonnegative and non-decreasing on $[1, \infty)$. -/
private theorem iterate_derivative_T_real_aux (n k : ℕ) :
    (∀ x : ℝ, 1 ≤ x → 0 ≤ (derivative^[k] (T ℝ (n : ℤ))).eval x) ∧
      MonotoneOn (fun x : ℝ => (derivative^[k] (T ℝ (n : ℤ))).eval x) (Set.Ici 1) := by
  refine Submodule.span_induction (p := fun p _ => (∀ x : ℝ, 1 ≤ x → 0 ≤ p.eval x) ∧
      MonotoneOn (fun x : ℝ => p.eval x) (Set.Ici 1)) ?_ ?_ ?_ ?_
    (T_iterate_derivative_mem_span_T n k)
  · rintro _ ⟨m, -, rfl⟩
    refine ⟨fun x hx => ?_, monotoneOn_eval_T_real m⟩
    have := monotoneOn_eval_T_real m (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
    simp only [T_eval_one] at this
    linarith
  · exact ⟨fun _ _ => by simp, fun _ _ _ _ _ => by simp⟩
  · rintro p r - - ⟨hp₀, hp⟩ ⟨hr₀, hr⟩
    refine ⟨fun x hx => by simpa using add_nonneg (hp₀ x hx) (hr₀ x hx), fun x hx y hy hxy => ?_⟩
    simpa using add_le_add (hp hx hy hxy) (hr hx hy hxy)
  · rintro a p - ⟨hp₀, hp⟩
    refine ⟨fun x hx => by simpa using mul_nonneg a.cast_nonneg (hp₀ x hx),
      fun x hx y hy hxy => ?_⟩
    simpa using mul_le_mul_of_nonneg_left (hp hx hy hxy) a.cast_nonneg

/-- The derivatives of $T_n$ are nonnegative on $[1, \infty)$. -/
theorem eval_iterate_derivative_T_real_nonneg (n k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (derivative^[k] (T ℝ (n : ℤ))).eval x :=
  (iterate_derivative_T_real_aux n k).1 x hx

/-- The derivatives of $T_n$ are non-decreasing on $[1, \infty)$. -/
theorem monotoneOn_eval_iterate_derivative_T_real (n k : ℕ) :
    MonotoneOn (fun x : ℝ => (derivative^[k] (T ℝ (n : ℤ))).eval x) (Set.Ici 1) :=
  (iterate_derivative_T_real_aux n k).2

/-- **Supporting lines of the squared Chebyshev filter**: for every $j$ and every $x \ge 1$, the
function $\varphi(y) = y\,T_j(2y - 1)^2$ has a supporting line on $[0, \infty)$ at $x$. Since
$T_j(2y - 1) = T_{2j}(\sqrt{y})$, this is the filter $y\,T_{2j}(\sqrt{y})^2$ of the source.
[TroppWebber2023, Lemma 9.3], part 5; there for $x\,T_{2j}(x^{1/2})^2$ (the $x^{1/4}$ variant of the
source is not needed). -/
theorem hasSupportingLineOn_mul_eval_T_sq (j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    HasSupportingLineOn (fun y => y * ((T ℝ (j : ℤ)).eval (2 * y - 1)) ^ 2) (Set.Ici 0) x := by
  -- Write $g(t) = T_j(2t - 1)$ and $d(t) = T_j'(2t - 1)$, so $\varphi' = g^2 + 4tgd$.
  set g : ℝ → ℝ := fun t => (T ℝ (j : ℤ)).eval (2 * t - 1) with hg
  set d : ℝ → ℝ := fun t => (derivative (T ℝ (j : ℤ))).eval (2 * t - 1) with hd
  set φ : ℝ → ℝ := fun y => y * ((T ℝ (j : ℤ)).eval (2 * y - 1)) ^ 2
  set φ' : ℝ → ℝ := fun t => g t ^ 2 + 4 * (t * g t * d t) with hφ'
  have hderiv (t : ℝ) : HasDerivAt φ (φ' t) t := by
    have h₁ : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
    have h₂ := (Polynomial.hasDerivAt (T ℝ (j : ℤ)) (2 * t - 1)).comp t h₁
    refine ((hasDerivAt_id' t).mul (h₂.pow 2)).congr_deriv ?_
    simp only [hφ', hg, hd, Function.comp_apply, Pi.pow_apply]
    push_cast
    ring
  -- On $[1, \infty)$, $g \ge 1$ and $d \ge 0$ are non-decreasing, hence so is $\varphi'$.
  have hmono : MonotoneOn φ' (Set.Ici 1) := by
    intro s hs t ht hst
    have hs' : (1 : ℝ) ≤ 2 * s - 1 := by simp only [Set.mem_Ici] at hs; linarith
    have ht' : (1 : ℝ) ≤ 2 * t - 1 := by simp only [Set.mem_Ici] at ht; linarith
    have hst' : 2 * s - 1 ≤ 2 * t - 1 := by linarith
    have hg₁ : 1 ≤ g s := one_le_eval_T_real _ hs'
    have hgst : g s ≤ g t := monotoneOn_eval_T_real j hs' ht' hst'
    have hd₀ : 0 ≤ d s := by
      simpa using eval_iterate_derivative_T_real_nonneg (x := 2 * s - 1) j 1 hs'
    have hdst : d s ≤ d t := by
      simpa using monotoneOn_eval_iterate_derivative_T_real j 1 hs' ht' hst'
    have hs₀ : (0 : ℝ) ≤ s := by simp only [Set.mem_Ici] at hs; linarith
    have ht₀ : (0 : ℝ) ≤ t := by linarith
    have hgt₀ : 0 ≤ g t := by linarith
    simp only [hφ']
    gcongr
  -- On $[0, 1]$, $|g| \le 1$ and $|d| \le T_j'(1) = j^2$, so $\varphi' \le 1 + 4j^2 = \varphi'(1)$.
  have hle₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ' t ≤ φ' 1 := by
    rintro t ⟨ht₀, ht₁⟩
    have habs : |2 * t - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have hgt : |g t| ≤ 1 := abs_eval_T_real_le_one _ habs
    have hdt : |d t| ≤ (j : ℝ) ^ 2 := by
      have := abs_iterate_derivative_T_real_le (j : ℤ) 1 habs
      simpa [derivative_T_eval_one] using this
    have hg1 : g 1 = 1 := by norm_num [hg, T_eval_one]
    have hd1 : d 1 = (j : ℝ) ^ 2 := by norm_num [hd, derivative_T_eval_one]
    have hsq : g t ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hgt
    have hprod : t * g t * d t ≤ (j : ℝ) ^ 2 := by
      calc t * g t * d t ≤ |t * g t * d t| := le_abs_self _
        _ = t * (|g t| * |d t|) := by rw [abs_mul, abs_mul, abs_of_nonneg ht₀, mul_assoc]
        _ ≤ 1 * (1 * (j : ℝ) ^ 2) := by gcongr
        _ = (j : ℝ) ^ 2 := by ring
    simp only [hφ', hg1, hd1]
    linarith
  -- Hence $\varphi' \le \varphi'(x)$ on $[0, x]$ and $\varphi' \ge \varphi'(x)$ on
  -- $[x, \infty)$, so $\varphi(y) - \varphi'(x)\,y$ is minimised at $y = x$.
  have hx₁ : x ∈ Set.Ici (1 : ℝ) := hx
  refine ⟨φ' x, fun y hy => ?_⟩
  have hd' (t : ℝ) : HasDerivAt (fun t => φ t - φ' x * t) (φ' t - φ' x) t := by
    have := (hderiv t).sub ((hasDerivAt_id' t).const_mul (φ' x))
    rwa [mul_one] at this
  have hcont : Continuous fun t => φ t - φ' x * t :=
    continuous_iff_continuousAt.2 fun t => (hd' t).continuousAt
  suffices φ x - φ' x * x ≤ φ y - φ' x * y by linarith
  rcases le_total y x with hyx | hxy
  · have hanti : AntitoneOn (fun t => φ t - φ' x * t) (Set.Icc 0 x) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 x) hcont.continuousOn
        (fun t _ => (hd' t).hasDerivWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      rcases le_total t 1 with ht₁ | ht₁
      · have := hle₁ t ⟨ht.1.le, ht₁⟩
        have := hmono (Set.mem_Ici.2 le_rfl) hx₁ hx
        linarith
      · have := hmono (Set.mem_Ici.2 ht₁) hx₁ ht.2.le
        linarith
    exact hanti ⟨hy, hyx⟩ ⟨by linarith, le_rfl⟩ hyx
  · have hmon : MonotoneOn (fun t => φ t - φ' x * t) (Set.Ici x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x) hcont.continuousOn
        (fun t _ => (hd' t).hasDerivWithinAt) fun t ht => ?_
      rw [interior_Ici] at ht
      have := hmono hx₁ (Set.mem_Ici.2 (hx.trans ht.le)) (Set.mem_Ioi.1 ht).le
      linarith
    exact hmon (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxy) hxy

end Polynomial.Chebyshev
