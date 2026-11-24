/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A ratio inequality for real powers, and the Chernoff base

For $0 < a$, $x, y \in [a, a']$, $t \ge 0$ and real $\alpha$, the ratio of
$z^\alpha / (z + t)$ at $x$ and $y$ is at most $(a'/a)^{\max(\alpha, 1 - \alpha)}$: the kernel
inequality behind the near-optimality of Krylov methods for $\mathbf{A}^\alpha$. The base
$e^s / (1 + s)^{1+s}$ of the Chernoff tails, raised to a real power, in exponential form. The
power threshold $R^{1/(2p+1)} \le 1 + \varepsilon$ of subspace iteration. A difference of real
powers against the difference of the bases. Upstream candidates for
`Mathlib.Analysis.SpecialFunctions.Pow.Real`.

## Main results

* `Real.rpow_mul_add_le`:
  $x^\alpha (y + t) \le (a'/a)^{\max(\alpha, 1 - \alpha)}\, y^\alpha (x + t)$.
* `Real.exp_div_rpow_rpow_eq_exp`:
  $\bigl(e^s / (1 + s)^{1+s}\bigr)^a = e^{(s - (1 + s) \log(1 + s)) a}$.
* `Real.rpow_one_div_two_mul_add_one_le_one_add`: $R^{1/(2p+1)} \le 1 + \varepsilon$ for
  $p \ge 2\log(N + 1)/\varepsilon$ and $1 \le R \le 1 + N^2$.
* `Real.rpow_sub_rpow_le_max_mul`: $a^r - b^r \le \max(1, r)\,a^{r-1}(a - b)$ for
  $0 \le b \le a$ and $r > 0$; `Real.rpow_sub_rpow_le_max_mul_sq`, the same on the squares.
* `Real.one_add_one_div_rpow_le_exp_one`: $(1 + 1/p)^p \le e$ for real $p > 0$.
-/

@[expose] public section

namespace Real

/-- For $1 \le s \le K$ and $\beta \le E$ with $E \ge 0$, $s^\beta \le K^E$. -/
private theorem rpow_le_rpow_of_one_le {s K β E : ℝ} (hs : 1 ≤ s) (hsK : s ≤ K) (hβ : β ≤ E)
    (hE : 0 ≤ E) : s ^ β ≤ K ^ E :=
  calc s ^ β ≤ s ^ max β 0 := Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    _ ≤ K ^ max β 0 := Real.rpow_le_rpow (by linarith) hsK (le_max_right _ _)
    _ ≤ K ^ E := Real.rpow_le_rpow_of_exponent_le (hs.trans hsK) (max_le hβ hE)

/-- **The kernel ratio for the power weights**: for $0 < a$, $x, y \in [a, a']$, $t \ge 0$ and
real $\alpha$,
$$\frac{x^\alpha}{x + t} \le \Bigl(\frac{a'}{a}\Bigr)^{\max(\alpha, 1 - \alpha)}
\frac{y^\alpha}{y + t} \,,$$
written without division: the kernel $z^\alpha / (z + t)$ of a weighted Stieltjes function varies
by at most that factor on $[a, a']$. [ChenPersson2026, Lemma 6], there for the extreme
eigenvalues and integrated against a measure. -/
theorem rpow_mul_add_le {a a' x y t : ℝ} (ha : 0 < a) (hx : x ∈ Set.Icc a a')
    (hy : y ∈ Set.Icc a a') (ht : 0 ≤ t) (α : ℝ) :
    x ^ α * (y + t) ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by
  obtain ⟨hax, hxa⟩ := hx
  obtain ⟨hay, hya⟩ := hy
  have hx0 : 0 < x := ha.trans_le hax
  have hy0 : 0 < y := ha.trans_le hay
  have hE : 0 ≤ max α (1 - α) := by
    rcases le_total α (1 - α) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hxt : 0 < x + t := by linarith
  rcases le_total x y with hxy | hyx
  · -- $y = r x$ with $1 \le r \le a'/a$
    set r := y / x
    have hr1 : 1 ≤ r := (one_le_div hx0).mpr hxy
    have hrK : r ≤ a' / a := div_le_div₀ (by linarith) hya ha hax
    have hyr : y = r * x := by simp only [r]; field_simp
    have hyα : y ^ α = r ^ α * x ^ α := by rw [hyr, Real.mul_rpow (by linarith) hx0.le]
    have hr : r ^ (1 - α) * r ^ α = r := by
      rw [← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]
    have hyt : y + t ≤ r * (x + t) := by rw [hyr]; nlinarith
    have hK := rpow_le_rpow_of_one_le hr1 hrK (le_max_right α (1 - α)) hE
    have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    calc x ^ α * (y + t) ≤ x ^ α * (r * (x + t)) := by gcongr
      _ = r ^ (1 - α) * (y ^ α * (x + t)) := by
          rw [hyα]
          conv_lhs => rw [← hr]
          ring
      _ ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by gcongr
  · -- $x = s y$ with $1 \le s \le a'/a$
    set s := x / y
    have hs1 : 1 ≤ s := (one_le_div hy0).mpr hyx
    have hsK : s ≤ a' / a := div_le_div₀ (by linarith) hxa ha hay
    have hxs : x = s * y := by simp only [s]; field_simp
    have hxα : x ^ α = s ^ α * y ^ α := by rw [hxs, Real.mul_rpow (by linarith) hy0.le]
    have hK := rpow_le_rpow_of_one_le hs1 hsK (le_max_left α (1 - α)) hE
    have hyα : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
    calc x ^ α * (y + t) ≤ x ^ α * (x + t) := by gcongr
      _ = s ^ α * (y ^ α * (x + t)) := by rw [hxα]; ring
      _ ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by gcongr

/-- The Chernoff tail base in exponential form: for $s > -1$ and real $a$,
$\bigl(e^s / (1 + s)^{1+s}\bigr)^a = e^{(s - (1 + s) \log(1 + s)) a}$. It turns the source form
of the Chernoff tails into an exponent to optimise. -/
theorem exp_div_rpow_rpow_eq_exp {s : ℝ} (hs : 0 < 1 + s) (a : ℝ) :
    (exp s / (1 + s) ^ (1 + s)) ^ a = exp ((s - (1 + s) * log (1 + s)) * a) := by
  rw [rpow_def_of_pos (div_pos (exp_pos _) (rpow_pos_of_pos hs _)),
    log_div (exp_pos _).ne' (rpow_pos_of_pos hs _).ne', log_exp, log_rpow hs]

/-- The power threshold of the Tropp–Webber form of the gapless bound for subspace iteration: for
$N \ge 0$, $1 \le R \le 1 + N^2$, $0 < \varepsilon \le 1$ and
$p \ge 2\log(N + 1)/\varepsilon$, $$R^{1/(2p+1)} \le 1 + \varepsilon\,,$$ since
$\log R \le 2\log(N + 1) \le p\varepsilon$. -/
theorem rpow_one_div_two_mul_add_one_le_one_add {N R ε : ℝ} {p : ℕ} (hN : 0 ≤ N) (hR1 : 1 ≤ R)
    (hR : R ≤ 1 + N ^ 2) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hp : 2 * Real.log (N + 1) / ε ≤ p) :
    R ^ (1 / (2 * (p : ℝ) + 1)) ≤ 1 + ε := by
  have hpε : 2 * Real.log (N + 1) ≤ p * ε := by rwa [div_le_iff₀ hε] at hp
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hlogR : Real.log R ≤ 2 * Real.log (N + 1) := by
    calc Real.log R ≤ Real.log ((N + 1) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log (N + 1) := by rw [Real.log_pow]; norm_num
  have hden : 0 < 2 * (p : ℝ) + 1 := by positivity
  have hratio : Real.log R * (1 / (2 * (p : ℝ) + 1)) ≤ Real.log (1 + ε) := by
    rw [mul_one_div, div_le_iff₀ hden]
    have := div_two_le_log_one_add hε hε₁
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  rw [Real.rpow_def_of_pos (by linarith)]
  calc Real.exp (Real.log R * (1 / (2 * (p : ℝ) + 1))) ≤ Real.exp (Real.log (1 + ε)) :=
        Real.exp_le_exp.2 hratio
    _ = 1 + ε := Real.exp_log (by linarith)

/-- A difference of real powers against the difference of the bases: for $0 \le b \le a$ and
$r > 0$, $$a^r - b^r \le \max(1, r)\,a^{r-1}(a - b)\,.$$ For $r \ge 1$ this is Bernoulli's
inequality $(1 + s)^r \ge 1 + rs$ at $s = b/a - 1$; for $r < 1$ it is $b^r \ge b\,a^{r-1}$. The
constant $\max(1, r)$ cannot be replaced by $r$ when $r < 1$. Upstream candidate. -/
theorem rpow_sub_rpow_le_max_mul {a b r : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hr : 0 < r) :
    a ^ r - b ^ r ≤ max 1 r * a ^ (r - 1) * (a - b) := by
  rcases (hb.trans hab).eq_or_lt with rfl | ha
  · obtain rfl : b = 0 := le_antisymm hab hb
    simp
  have hsub : a ^ (r - 1) * a = a ^ r := by rw [rpow_sub_one ha.ne', div_mul_cancel₀ _ ha.ne']
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [max_eq_right hr1]
    have h := one_add_mul_self_le_rpow_one_add (s := b / a - 1)
      (by linarith [div_nonneg hb ha.le]) hr1
    rw [add_sub_cancel, div_rpow hb ha.le, le_div_iff₀ (rpow_pos_of_pos ha r)] at h
    have hba : b / a * a ^ r = b * a ^ (r - 1) := by
      rw [← hsub]; field_simp
    linear_combination h - r * hba - r * hsub
  · rw [max_eq_left hr1.le, one_mul]
    rcases hb.eq_or_lt with rfl | hb'
    · rw [zero_rpow hr.ne', sub_zero, sub_zero, hsub]
    · have h1 : a ^ (r - 1) ≤ b ^ (r - 1) := rpow_le_rpow_of_nonpos hb' hab (by linarith)
      have h2 : b ^ (r - 1) * b = b ^ r := by
        rw [rpow_sub_one hb'.ne', div_mul_cancel₀ _ hb'.ne']
      nlinarith

/-- `Real.rpow_sub_rpow_le_max_mul` on the squares: for $0 \le b \le a$ and $p > 0$,
$$a^p - b^p \le \max\Bigl(1, \frac{p}{2}\Bigr)\,a^{p-2}\,(a^2 - b^2)\,.$$ -/
theorem rpow_sub_rpow_le_max_mul_sq {a b p : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hp : 0 < p) :
    a ^ p - b ^ p ≤ max 1 (p / 2) * a ^ (p - 2) * (a ^ 2 - b ^ 2) := by
  have hsq (x r : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ r = x ^ (2 * r) := by
    rw [← rpow_two, ← rpow_mul hx]
  have h := rpow_sub_rpow_le_max_mul (sq_nonneg b) (pow_le_pow_left₀ hb hab 2)
    (show 0 < p / 2 by linarith)
  rwa [hsq _ _ (hb.trans hab), hsq _ _ hb, hsq _ _ (hb.trans hab),
    show 2 * (p / 2) = p by ring, show 2 * (p / 2 - 1) = p - 2 by ring] at h

/-- The real power $(1 + 1/p)^p$ is at most $e$ for $p > 0$; for natural $p$ this is
`Real.one_add_inv_pow_le_exp`. -/
theorem one_add_one_div_rpow_le_exp_one {p : ℝ} (hp : 0 < p) : (1 + 1 / p) ^ p ≤ exp 1 := by
  calc (1 + 1 / p) ^ p ≤ exp (1 / p) ^ p := by
        refine rpow_le_rpow (by positivity) ?_ hp.le
        linarith [add_one_le_exp (1 / p)]
    _ = exp 1 := by rw [← exp_mul, one_div_mul_cancel hp.ne']

end Real
