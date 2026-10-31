/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Polynomial

/-!
# The even Chebyshev filter

The even second-kind Chebyshev filter $b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$ is a polynomial of
degree $k$ in $x$ (only even powers occur in $U_{2k}$), equal to $1$ at $x = 1$ and bounded by
$1$ in absolute value on $[0, 1]$. On $[0, 1]$ it satisfies
$(1 - x)\,b_k(x)^2 \le (2k + 1)^{-2}$: it suppresses every point away from $1$ at the rate
$1/k$, with no gap.

A power of the filter, with the number of factors chosen from the weight of $\{1\}$, gives the
gap-free polynomial filter step of Kuczyński and Woźniakowski: for a finite measure $\nu$ on
$[0, 1]$ with an atom at $1$ and every $q \ge 1$ there is a polynomial $p$ of degree at most $q$
with $p(1) = 1$ and
$$1 - \frac{\int x\,p(x)^2\,d\nu}{\int p(x)^2\,d\nu} \le
\frac{4}{q^2}\Bigl(1 + \frac{\log(\nu(\mathbb{R})/\nu(\{1\}))}{\log 2}\Bigr)^2\,.$$
Applied to the spectral measure of a positive semidefinite matrix, rescaled to $[0, 1]$, it is
the deterministic step of the random-start Lanczos bound.

## Main definitions

* `NLAlib.evenChebyshevFilter`: $b_k$.

## Main results

* `NLAlib.one_sub_mul_eval_evenChebyshevFilter_sq_le`: the gap-free suppression.
* `NLAlib.exists_natDegree_le_one_sub_integral_mul_div_le`: the filter step for a measure.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- The coefficients of $U_n$ at the indices $j$ with $n + j$ odd vanish. -/
private theorem coeff_U_natCast_eq_zero_of_odd :
    ∀ (n j : ℕ), Odd (n + j) → (Chebyshev.U ℝ (n : ℤ)).coeff j = 0
  | 0, j, h => by
    have hj : j ≠ 0 := by rintro rfl; simp at h
    simp [Chebyshev.U_zero, coeff_one, hj]
  | 1, j, h => by
    have hj : j ≠ 1 := by rintro rfl; obtain ⟨m, hm⟩ := h; omega
    simp [Chebyshev.U_one, coeff_X, hj.symm]
  | n + 2, j, h => by
    have hU : Chebyshev.U ℝ ((n + 2 : ℕ) : ℤ) =
        2 * X * Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) - Chebyshev.U ℝ (n : ℤ) := by
      push_cast
      exact Chebyshev.U_add_two ℝ n
    obtain ⟨m, hm⟩ := h
    rw [hU, coeff_sub, coeff_U_natCast_eq_zero_of_odd n j ⟨m - 1, by omega⟩, sub_zero]
    rcases j with _ | i
    · rw [mul_assoc, coeff_ofNat_mul, coeff_X_mul_zero, mul_zero]
    · rw [mul_assoc, coeff_ofNat_mul, coeff_X_mul,
        coeff_U_natCast_eq_zero_of_odd (n + 1) i ⟨m - 1, by omega⟩, mul_zero]

/-- $U_{2k}$ is the expansion of its contraction: it has only even powers. -/
private theorem expand_contract_U_two_mul (k : ℕ) :
    expand ℝ 2 (contract 2 (Chebyshev.U ℝ ((2 * k : ℕ) : ℤ))) =
      Chebyshev.U ℝ ((2 * k : ℕ) : ℤ) := by
  ext n
  rw [coeff_expand two_pos, coeff_contract two_ne_zero]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · refine (coeff_U_natCast_eq_zero_of_odd _ _ ?_).symm
    obtain ⟨m, hm⟩ : Odd n := Nat.odd_iff.mpr (by omega)
    exact ⟨k + m, by omega⟩

/-- **Second-kind Chebyshev polynomials are bounded on $[-1, 1]$**: for $\lvert y \rvert \le 1$,
$\lvert U_n(y)\rvert \le n + 1$. [Trefethen2019, Ch. 3] (locator to check). -/
theorem abs_eval_U_le (n : ℕ) {y : ℝ} (hy : |y| ≤ 1) :
    |(Chebyshev.U ℝ (n : ℤ)).eval y| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hU : Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) =
        X * Chebyshev.U ℝ (n : ℤ) + Chebyshev.T ℝ ((n : ℤ) + 1) := by
      push_cast
      exact Chebyshev.U_eq_X_mul_U_add_T ℝ n
    rw [hU, eval_add, eval_mul, eval_X]
    have hT := Chebyshev.abs_eval_T_real_le_one ((n : ℤ) + 1) hy
    calc |y * (Chebyshev.U ℝ (n : ℤ)).eval y + (Chebyshev.T ℝ ((n : ℤ) + 1)).eval y|
        ≤ |y| * |(Chebyshev.U ℝ (n : ℤ)).eval y| + 1 := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (by gcongr)
      _ ≤ 1 * (n + 1) + 1 := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

/-- $(1 - y^2)\,U_n(y)^2 \le 1$ on $[-1, 1]$, from $\sin\theta\,U_n(\cos\theta) =
\sin((n + 1)\theta)$. -/
private theorem one_sub_sq_mul_eval_U_sq_le_one (n : ℤ) {y : ℝ} (hy : |y| ≤ 1) :
    (1 - y ^ 2) * (Chebyshev.U ℝ n).eval y ^ 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  have key := Chebyshev.U_real_cos (Real.arccos y) n
  rw [Real.cos_arccos h1 h2, Real.sin_arccos] at key
  have hy2 : 0 ≤ 1 - y ^ 2 := by nlinarith
  calc (1 - y ^ 2) * (Chebyshev.U ℝ n).eval y ^ 2
      = ((Chebyshev.U ℝ n).eval y * √(1 - y ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hy2]; ring
    _ ≤ 1 := by rw [key]; exact Real.sin_sq_le_one _

/-- The **even Chebyshev filter** $b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$, a polynomial of degree
$k$ in $x$: the contraction of the even polynomial $U_{2k}$ (Mathlib's
`Polynomial.Chebyshev.U`), scaled so that $b_k(1) = 1$. -/
noncomputable def evenChebyshevFilter (k : ℕ) : ℝ[X] :=
  C ((2 * k + 1 : ℝ)⁻¹) * contract 2 (Chebyshev.U ℝ ((2 * k : ℕ) : ℤ))

/-- The even Chebyshev filter has degree at most $k$. -/
theorem natDegree_evenChebyshevFilter_le (k : ℕ) : (evenChebyshevFilter k).natDegree ≤ k := by
  refine (natDegree_C_mul_le _ _).trans (natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_)
  rw [coeff_contract two_ne_zero]
  apply coeff_eq_zero_of_natDegree_lt
  rw [Chebyshev.natDegree_U_natCast]
  omega

/-- The characterising evaluation: for $x \ge 0$,
$b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$. -/
theorem eval_evenChebyshevFilter (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (evenChebyshevFilter k).eval x =
      (Chebyshev.U ℝ ((2 * k : ℕ) : ℤ)).eval (√x) / (2 * k + 1) := by
  rw [← expand_contract_U_two_mul k, expand_eval, Real.sq_sqrt hx, evenChebyshevFilter, eval_mul,
    eval_C, inv_mul_eq_div]

/-- The even Chebyshev filter is normalised at $1$: $b_k(1) = 1$. -/
theorem eval_evenChebyshevFilter_one (k : ℕ) : (evenChebyshevFilter k).eval 1 = 1 := by
  rw [eval_evenChebyshevFilter k zero_le_one, Real.sqrt_one, Chebyshev.U_eval_one]
  push_cast
  exact div_self (by positivity)

/-- The even Chebyshev filter is bounded by $1$ on $[0, 1]$: $\lvert b_k(x)\rvert \le 1$. -/
theorem abs_eval_evenChebyshevFilter_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(evenChebyshevFilter k).eval x| ≤ 1 := by
  have hy : |√x| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    exact Real.sqrt_le_one.mpr hx.2
  rw [eval_evenChebyshevFilter k hx.1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * k + 1),
    div_le_one (by positivity)]
  simpa using abs_eval_U_le (2 * k) hy

/-- Gap-free suppression by the even Chebyshev filter: for $x \in [0, 1]$,
$$(1 - x)\,b_k(x)^2 \le \frac{1}{(2k + 1)^2}\,,$$
from $(1 - y^2)\,U_{2k}(y)^2 \le 1$ on $[-1, 1]$. -/
theorem one_sub_mul_eval_evenChebyshevFilter_sq_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (1 - x) * (evenChebyshevFilter k).eval x ^ 2 ≤ 1 / (2 * k + 1) ^ 2 := by
  have hy : |√x| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    exact Real.sqrt_le_one.mpr hx.2
  have h := one_sub_sq_mul_eval_U_sq_le_one ((2 * k : ℕ) : ℤ) hy
  rw [Real.sq_sqrt hx.1] at h
  rw [eval_evenChebyshevFilter k hx.1, div_pow, mul_div_assoc']
  exact div_le_div_of_nonneg_right h (by positivity)

/-- A power $b_k^\ell$, $\ell \ge 1$, suppresses $1 - x$ on $[0, 1]$ up to $2^{-\ell}$:
$(1 - x)\,b_k(x)^{2\ell} \le c\,b_k(x)^{2\ell} + c\,2^{-\ell}$ with $c = 2/(2k + 1)^2$. -/
private theorem one_sub_mul_eval_evenChebyshevFilter_pow_sq_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (1 - x) * ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 ≤
      2 / (2 * k + 1) ^ 2 * ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 +
        2 / (2 * k + 1) ^ 2 * (1 / 2) ^ ℓ := by
  set t := (evenChebyshevFilter k).eval x
  set c : ℝ := 2 / (2 * k + 1) ^ 2
  have hc : 0 ≤ c := by positivity
  have h := one_sub_mul_eval_evenChebyshevFilter_sq_le k hx
  have hc2 : 1 / (2 * (k : ℝ) + 1) ^ 2 = c / 2 := by simp only [c]; ring
  rw [hc2] at h
  rcases le_or_gt (1 - x) c with hxc | hxc
  · have := mul_le_mul_of_nonneg_right hxc (sq_nonneg (t ^ ℓ))
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ℓ]
  · have hpos : 0 < 1 - x := hc.trans_lt hxc
    have ht2 : t ^ 2 ≤ 1 / 2 := by
      by_contra hne
      nlinarith [not_le.mp hne]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hℓ
    have hpow : (t ^ 2) ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ (sq_nonneg t) ht2 m
    have hmain : (1 - x) * (t ^ (1 + m)) ^ 2 ≤ c * (1 / 2) ^ (1 + m) := by
      calc (1 - x) * (t ^ (1 + m)) ^ 2 = ((1 - x) * t ^ 2) * (t ^ 2) ^ m := by ring
        _ ≤ (c / 2) * (1 / 2) ^ m :=
          mul_le_mul h hpow (pow_nonneg (sq_nonneg t) m) (by positivity)
        _ = c * (1 / 2) ^ (1 + m) := by ring
    nlinarith [mul_nonneg hc (sq_nonneg (t ^ (1 + m)))]

/-- The filter mean of a power of $b_k$: if $\nu$ is a finite measure on $[0, 1]$ with
$\nu(\{1\}) > 0$ and $\log(\nu(\mathbb{R})/\nu(\{1\})) \le \ell\log 2$, $\ell \ge 1$, then
$1 - \int x\,b_k^{2\ell}\,d\nu / \int b_k^{2\ell}\,d\nu \le 4/(2k + 1)^2$. -/
private theorem one_sub_integral_mul_div_le_four_div_sq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (h1 : 0 < ν.real {1}) (k : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hlog : Real.log (ν.real Set.univ / ν.real {1}) ≤ ℓ * Real.log 2) :
    1 - (∫ x, x * ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 ∂ν) /
        (∫ x, ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 ∂ν) ≤ 4 / (2 * k + 1) ^ 2 := by
  set g : ℝ → ℝ := fun x => ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 with hg
  set c : ℝ := 2 / (2 * k + 1) ^ 2
  have hc : 0 ≤ c := by positivity
  have hgc : Continuous g := ((evenChebyshevFilter k).continuous.pow ℓ).pow 2
  have hg01 : ∀ᵐ x ∂ν, 0 ≤ g x ∧ g x ≤ 1 := by
    filter_upwards [hν] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have ht : (evenChebyshevFilter k).eval x ^ 2 ≤ 1 := by
      have := abs_eval_evenChebyshevFilter_le_one k hx
      rw [sq_le_one_iff_abs_le_one]
      exact this
    simp only [hg]
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_one₀ (sq_nonneg _) ht
  have hgi : Integrable g ν := Integrable.of_bound hgc.aestronglyMeasurable 1 (by
    filter_upwards [hg01] with x hx
    rw [Real.norm_of_nonneg hx.1]
    exact hx.2)
  have hxgi : Integrable (fun x => x * g x) ν :=
    Integrable.of_bound (continuous_id.mul hgc).aestronglyMeasurable 1 (by
      filter_upwards [hν, hg01] with x hx hgx
      rw [norm_mul, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg hgx.1]
      nlinarith [hx.1, hx.2, hgx.1, hgx.2])
  have hH : ν.real {1} ≤ ∫ x, g x ∂ν := by
    have := setIntegral_le_integral (s := {1}) hgi (by
      filter_upwards [hg01] with x hx using hx.1)
    rw [integral_singleton] at this
    simpa [hg, eval_evenChebyshevFilter_one] using this
  have hI0 : 0 < ∫ x, g x ∂ν := h1.trans_le hH
  have hmass : (1 / 2) ^ ℓ * ν.real Set.univ ≤ ν.real {1} := by
    have hM : 0 < ν.real Set.univ := h1.trans_le (measureReal_mono (Set.subset_univ _))
    rw [← Real.log_pow, Real.log_le_log_iff (by positivity) (by positivity),
      div_le_iff₀ h1] at hlog
    rw [one_div_pow, one_div, inv_mul_le_iff₀ (by positivity)]
    exact hlog
  have hnum : ∫ x, (1 - x) * g x ∂ν ≤ c * (∫ x, g x ∂ν) + c * ((1 / 2) ^ ℓ * ν.real Set.univ) := by
    calc ∫ x, (1 - x) * g x ∂ν ≤ ∫ x, (c * g x + c * (1 / 2) ^ ℓ) ∂ν := by
          refine integral_mono_ae ((hgi.sub hxgi).congr ?_)
            ((hgi.const_mul c).add (integrable_const _)) ?_
          · filter_upwards with x
            simp only [Pi.sub_apply]
            ring
          · filter_upwards [hν] with x hx
            exact one_sub_mul_eval_evenChebyshevFilter_pow_sq_le k hx hℓ
      _ = c * (∫ x, g x ∂ν) + c * ((1 / 2) ^ ℓ * ν.real Set.univ) := by
          rw [integral_add (hgi.const_mul c) (integrable_const _), integral_const_mul,
            integral_const, smul_eq_mul]
          ring
  change 1 - (∫ x, x * g x ∂ν) / (∫ x, g x ∂ν) ≤ _
  rw [one_sub_div hI0.ne', ← integral_sub hgi hxgi]
  have hcongr : ∫ x, (g x - x * g x) ∂ν = ∫ x, (1 - x) * g x ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; ring)
  rw [hcongr, div_le_iff₀ hI0]
  calc ∫ x, (1 - x) * g x ∂ν ≤ c * (∫ x, g x ∂ν) + c * (∫ x, g x ∂ν) := by
        have := mul_le_mul_of_nonneg_left (hmass.trans hH) hc
        linarith
    _ = 4 / (2 * k + 1) ^ 2 * ∫ x, g x ∂ν := by simp only [c]; ring

/-- **The gap-free polynomial filter step**: for a finite measure $\nu$ supported in
$[0, 1]$ with an atom at $1$, $\nu(\{1\}) > 0$, and every $q \ge 1$, there is a real polynomial
$p$ of degree at most $q$ with $p(1) = 1$ and
$$1 - \frac{\int x\,p(x)^2\,d\nu}{\int p(x)^2\,d\nu} \le
\frac{4}{q^2}\Bigl(1 + \frac{\log(\nu(\mathbb{R})/\nu(\{1\}))}{\log 2}\Bigr)^2\,;$$
$p$ is a power of the even Chebyshev filter, the number of factors chosen from the logarithmic
ratio. [KuczynskiWozniakowski1992, Theorem 4.2] (locator to check); there for
the Lanczos method with a random start, here for any such measure. -/
theorem exists_natDegree_le_one_sub_integral_mul_div_le {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (h1 : 0 < ν.real {1}) {q : ℕ} (hq : 1 ≤ q) :
    ∃ p : ℝ[X], p.natDegree ≤ q ∧ p.eval 1 = 1 ∧
      1 - (∫ x, x * p.eval x ^ 2 ∂ν) / (∫ x, p.eval x ^ 2 ∂ν) ≤
        4 * (1 + Real.log (ν.real Set.univ / ν.real {1}) / Real.log 2) ^ 2 / q ^ 2 := by
  set L := Real.log (ν.real Set.univ / ν.real {1}) / Real.log 2 with hL
  have hHM : ν.real {1} ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg ((one_le_div h1).mpr hHM)) hlog2.le
  set ℓ := max 1 ⌈L⌉₊ with hℓdef
  have hℓ : 1 ≤ ℓ := le_max_left _ _
  have hℓL : (ℓ : ℝ) ≤ 1 + L := by
    rw [hℓdef, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) ((Nat.ceil_lt_add_one hL0).le.trans (by linarith))
  have hLℓ : L ≤ ℓ := (Nat.le_ceil L).trans (by exact_mod_cast le_max_right _ _)
  set k := q / ℓ with hk
  refine ⟨evenChebyshevFilter k ^ ℓ, ?_, ?_, ?_⟩
  · refine natDegree_pow_le.trans
      ((Nat.mul_le_mul_left ℓ (natDegree_evenChebyshevFilter_le k)).trans ?_)
    rw [mul_comm]
    exact Nat.div_mul_le_self q ℓ
  · rw [eval_pow, eval_evenChebyshevFilter_one, one_pow]
  have hlog : Real.log (ν.real Set.univ / ν.real {1}) ≤ ℓ * Real.log 2 := by
    rwa [hL, div_le_iff₀ hlog2] at hLℓ
  simp only [eval_pow]
  refine (one_sub_integral_mul_div_le_four_div_sq hν h1 k hℓ hlog).trans ?_
  have hqk : q < (k + 1) * ℓ := by
    have h1 := Nat.div_add_mod q ℓ
    have h2 := Nat.mod_lt q (show 0 < ℓ by omega)
    rw [hk]
    nlinarith
  have hq' : (q : ℝ) ≤ (2 * k + 1) * (1 + L) := by
    have h' : (q : ℝ) ≤ (k + 1) * ℓ := by exact_mod_cast hqk.le
    exact h'.trans (mul_le_mul (by linarith) hℓL (by positivity) (by positivity))
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := pow_le_pow_left₀ hq0.le hq' 2
  nlinarith

end NLAlib
