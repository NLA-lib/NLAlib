/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Algebra.Polynomial.Expand
public import NLAlib.Polynomial.Chebyshev.Residual
public import NLAlib.Polynomial.Chebyshev.ResidualMinimax

/-!
# Residual polynomials on two symmetric intervals

On $S = [-a', -a] \cup [a, a']$, $0 < a < a'$, the best residual polynomial of degree at most $q$
($p(0) = 1$) is even, $r_k(x^2)$ with $k = \lfloor q/2 \rfloor$ and $r_k$ the normalized
Chebyshev residual of $[a^2, a'^2]$, so the residual minimax value of $S$ is
$T_k\bigl((a'^2 + a^2)/(a'^2 - a^2)\bigr)^{-1}$. Its dual certificate lives on the $2(k + 1)$
points $\pm\sqrt{\xi_j}$, with $\xi_j$ the Chebyshev extrema of $[a^2, a'^2]$ and half the dual
weights $\omega_j$ on each sign. For $a = 1$, $a' = \kappa \ge 2$ the value is at least
$e^{-2q/\kappa}$: Lemmas 1 and 2 of [Shamir2026], with an explicit certificate in place of the
Kroó–Pinkus characterization.

A **Chebyshev two-interval spectrum** (`IsChebyshevTwoIntervalSpectrum`) is a list of
$\lvert n \rvert$ values on those $2(k + 1)$ points, each taken often enough that the counting
measure dominates $\lvert n \rvert/4$ times the normalized dual weights plus a margin $M$; it is
the spectrum of the hard instance of the linear-system lower bound.

## Main definitions

* `NLAlib.IsChebyshevTwoIntervalSpectrum`: values on the two-interval Chebyshev points with
  multiplicities dominating the dual weights.

## Main results

* `NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq`: the dual certificate.
* `NLAlib.residualMinimax_Icc_union_Icc`: the value $T_{\lfloor q/2 \rfloor}(\cdot)^{-1}$.
* `NLAlib.exp_neg_le_inv_eval_T_real`, `NLAlib.exp_neg_le_residualMinimax_Icc_union_Icc`: at
  least $e^{-2q/\kappa}$ on $[-\kappa, -1] \cup [1, \kappa]$.
* `NLAlib.exists_residualMinimax_Icc_union_Icc_sq_le_sum_mul_norm_sq`: the weighted form.
* `NLAlib.IsChebyshevTwoIntervalSpectrum.mem_Icc_union_Icc`,
  `NLAlib.IsChebyshevTwoIntervalSpectrum.inv_sq_le_sum_card_sub_mul_eval_sq`,
  `NLAlib.exists_isChebyshevTwoIntervalSpectrum`.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- A **Chebyshev two-interval spectrum** for $\kappa$, depth $s$ and margin $M$: with
$k = \lfloor s/2 \rfloor$, $\xi_j$ the Chebyshev extrema of $[1, \kappa^2]$ (`chebyshevExtremum`),
$\omega_j$ their dual weights (`chebyshevWeight`) and
$\tau = T_k\bigl((\kappa^2 + 1)/(\kappa^2 - 1)\bigr) = \sum_j \omega_j$, every value $d_i$ is one of
the $2(k + 1)$ points $\pm\sqrt{\xi_j}$, and each point is taken at least
$$\frac{\lvert n \rvert}{4}\cdot\frac{\omega_j}{2\tau} + M$$
times. For $\kappa > 1$ the points lie in $[-\kappa, -1] \cup [1, \kappa]$, and such a spectrum
exists once $4(s + 2)(M + 1) \le 3\lvert n \rvert$
(`NLAlib.exists_isChebyshevTwoIntervalSpectrum`). Junk: for $\kappa \le 1$ the points are not in
the two intervals; theorems assume $2 \le \kappa$. -/
structure IsChebyshevTwoIntervalSpectrum {n : Type*} [Fintype n] (κ : ℝ) (s M : ℕ)
    (d : n → ℝ) : Prop where
  /-- Every value is one of the points $\pm\sqrt{\xi_j}$. -/
  exists_eq : ∀ i, ∃ j : Fin (s / 2 + 1),
    d i = Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ∨
      d i = -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)
  /-- The point $+\sqrt{\xi_j}$ is taken at least $\lvert n \rvert\omega_j/(8\tau) + M$ times. -/
  le_card_pos : ∀ j : Fin (s / 2 + 1),
    (Fintype.card n : ℝ) / 4 * (chebyshevWeight 1 (κ ^ 2) (s / 2) j /
        (2 * (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))) + M ≤
      ((Finset.univ.filter fun i =>
        d i = Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)).card : ℝ)
  /-- The point $-\sqrt{\xi_j}$ is taken at least $\lvert n \rvert\omega_j/(8\tau) + M$ times. -/
  le_card_neg : ∀ j : Fin (s / 2 + 1),
    (Fintype.card n : ℝ) / 4 * (chebyshevWeight 1 (κ ^ 2) (s / 2) j /
        (2 * (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))) + M ≤
      ((Finset.univ.filter fun i =>
        d i = -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)).card : ℝ)

end NLAlib

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- **Dual certificate on two symmetric intervals**: for $0 < a < a'$ and $k = \lfloor q/2
\rfloor$, every $p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ has
$$T_k\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1} \le \sum_{j=0}^{k} \frac{\omega_j}{2}
\Bigl(\lvert p(\sqrt{\xi_j}) \rvert^2 + \lvert p(-\sqrt{\xi_j}) \rvert^2\Bigr) \,,$$
with $\xi_j$ the Chebyshev extrema of $[a^2, a'^2]$ and $\omega_j$ their dual weights
(`chebyshevExtremum`, `chebyshevWeight`).
This weighted certificate is the library’s two-interval form of the residual-polynomial argument
of [Greenbaum1997, §3.1, pp. 49–54], the bound behind the two-interval MINRES worst case. -/
theorem inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq {𝕜 : Type*} [RCLike 𝕜]
    {a a' : ℝ} (ha : 0 < a) (haa : a < a') {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q)
    (hp₀ : p.eval 0 = 1) :
    ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ ≤
      ∑ j : Fin (q / 2 + 1), chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)‖ ^ 2 +
          ‖p.eval (-((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜))‖ ^ 2) :=
    by
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have haa2 : a ^ 2 < a' ^ 2 := pow_lt_pow_left₀ haa ha.le two_ne_zero
  have hPd := degree_contract_le_of_degree_le two_ne_zero hp
  have hP₀ : (contract 2 p).eval 0 = 1 := by rw [eval_zero_contract two_ne_zero, hp₀]
  have hterm : ∀ j : Fin (q / 2 + 1),
      chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j *
        ‖(contract 2 p).eval (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j : 𝕜)‖ ^ 2 ≤
      chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)‖ ^ 2 +
          ‖p.eval (-((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜))‖ ^ 2) :=
    fun j => by
      have hξ0 : 0 ≤ chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j :=
        ha2.le.trans (chebyshevExtremum_mem_Icc haa2.le (q / 2) j).1
      have hx2 : ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜) ^ 2 =
          (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j : 𝕜) := by
        rw [← RCLike.ofReal_pow, Real.sq_sqrt hξ0]
      have h := mul_norm_eval_contract_two_sq_le p
        ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)
        (chebyshevWeight_pos ha2 haa2 (q / 2) j).le
      rwa [hx2] at h
  exact (inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq ha2 haa2 hPd hP₀).trans
    (Finset.sum_le_sum fun j _ => hterm j)

/-- **Residual minimax value of two symmetric intervals**: for $0 < a < a'$,
$$\min_{\deg p \le q,\ p(0) = 1}\ \max_{x \in [-a', -a] \cup [a, a']} \lvert p(x) \rvert =
T_{\lfloor q/2 \rfloor}\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1} \,,$$
attained by the even Chebyshev residual $r_{\lfloor q/2 \rfloor}(x^2)$ of $[a^2, a'^2]$.
[Greenbaum1997, §3.1, pp. 49–54] treats the symmetric two-interval residual bound. [Shamir2026,
Lemma 1] uses the lower half. -/
theorem residualMinimax_Icc_union_Icc {a a' : ℝ} (q : ℕ) (ha : 0 < a) (haa : a < a') :
    residualMinimax (Set.Icc (-a') (-a) ∪ Set.Icc a a') q =
      ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ := by
  have ha2 : 0 < a ^ 2 := by positivity
  have haa2 : a ^ 2 < a' ^ 2 := pow_lt_pow_left₀ haa ha.le two_ne_zero
  have hT : 0 < (T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)) :=
    zero_lt_one.trans_le (one_le_eval_T_real _ (by
      rw [le_div_iff₀ (by linarith)]
      linarith))
  refine le_antisymm ?_ ?_
  · refine residualMinimax_le (p := (chebyshevResidual (a ^ 2) (a' ^ 2) (q / 2)).comp (X ^ 2))
      ?_ (eval_chebyshevResidual_comp_X_sq_zero (q / 2) (pow_pos ha 2) haa2)
      (inv_nonneg.mpr hT.le)
      (fun x hx => abs_eval_chebyshevResidual_comp_X_sq_le (q / 2) ha haa x hx)
    exact (degree_chebyshevResidual_comp_X_sq_le _ _ _).trans (by
      exact_mod_cast (by omega : 2 * (q / 2) ≤ q))
  · refine le_residualMinimax fun p η hp hp₀ hη0 hle => ?_
    -- the points ±√ξ_j lie in S
    have hsq : ∀ j : Fin (q / 2 + 1),
        Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) ∈ Set.Icc a a' := fun j => by
      have h := chebyshevExtremum_mem_Icc (pow_le_pow_left₀ ha.le haa.le 2) (q / 2) j
      constructor
      · simpa only [Real.sqrt_sq ha.le] using Real.sqrt_le_sqrt h.1
      · simpa only [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ a')] using Real.sqrt_le_sqrt h.2
    have hj : ∀ j : Fin (q / 2 + 1),
        ‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : ℝ)‖ ≤ η ∧
        ‖p.eval (-(Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ))‖ ≤ η :=
      fun j => ⟨by rw [Real.norm_eq_abs]; exact hle _ (Or.inr (hsq j)),
        by
          rw [Real.norm_eq_abs]
          exact hle _ (Or.inl ⟨by linarith [(hsq j).2], by linarith [(hsq j).1]⟩)⟩
    have hsum :=
      inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq (𝕜 := ℝ) ha haa hp hp₀
    have hsum2 : ∑ j : Fin (q / 2 + 1), chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : ℝ)‖ ^ 2 +
          ‖p.eval (-(Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ))‖ ^ 2) ≤
        η ^ 2 * ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2))) := by
      rw [← sum_chebyshevWeight ha2 haa2, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have h0 := chebyshevWeight_pos ha2 haa2 (q / 2) j
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hj j).1 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (hj j).2 2
      nlinarith
    have hx : 0 < ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ :=
      inv_pos.mpr hT
    nlinarith [hsum.trans hsum2, mul_inv_cancel₀ hT.ne']

/-- The Chebyshev value on $[1, \kappa^2]$ decays at most like $e^{-4k/\kappa}$: for
$\kappa \ge 2$ and every $k$,
$$e^{-4k/\kappa} \le T_k\Bigl(\frac{\kappa^2 + 1}{\kappa^2 - 1}\Bigr)^{-1} \,.$$
[Shamir2026, Lemma 1]; there through $T_k(\cosh\theta) = \cosh(k\theta) \le e^{k\theta}$ with
$\theta = \log((\kappa + 1)/(\kappa - 1)) \le 4/\kappa$. -/
theorem exp_neg_le_inv_eval_T_real {κ : ℝ} (hκ : 2 ≤ κ) (k : ℕ) :
    Real.exp (-(4 * k / κ)) ≤ ((T ℝ (k : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))⁻¹ := by
  have hk := inv_eval_T_real_eq_two_mul_pow_div (a := 1) (a' := κ ^ 2) k one_pos (by nlinarith)
  rw [hk, div_one, Real.sqrt_sq (by linarith)]
  have hκ1 : 0 < κ - 1 := by linarith
  have hκ2 : 0 < κ + 1 := by linarith
  have hρ0 : 0 ≤ (κ - 1) / (κ + 1) := (div_pos hκ1 hκ2).le
  have hρ1 : (κ - 1) / (κ + 1) ≤ 1 := (div_le_one hκ2).mpr (by linarith)
  have hexp : Real.exp (-(4 / κ)) ≤ (κ - 1) / (κ + 1) := by
    have h2 : (κ + 1) / (κ - 1) = 1 + 2 / (κ - 1) := by
      field_simp
      ring
    have h3 : 2 / (κ - 1) ≤ 4 / κ := by
      rw [div_le_div_iff₀ hκ1 (by linarith)]
      linarith
    have h4 : (κ + 1) / (κ - 1) ≤ Real.exp (4 / κ) := by
      have := Real.add_one_le_exp (2 / (κ - 1))
      have := Real.exp_le_exp.mpr h3
      rw [h2]
      linarith
    rw [Real.exp_neg, show (κ - 1) / (κ + 1) = ((κ + 1) / (κ - 1))⁻¹ by rw [inv_div]]
    exact inv_anti₀ (div_pos hκ2 hκ1) h4
  have hexpk : Real.exp (-(4 * k / κ)) = (Real.exp (-(4 / κ))) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexpk]
  refine (pow_le_pow_left₀ (Real.exp_nonneg _) hexp k).trans ?_
  have hpow : ((κ - 1) / (κ + 1)) ^ (2 * k) ≤ 1 := pow_le_one₀ hρ0 hρ1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_of_le_one_right (pow_nonneg hρ0 k) hpow, pow_nonneg hρ0 k]

/-- **Polynomial inapproximability on two intervals**: for $\kappa \ge 2$ and every $q$, every
real polynomial $p$ of degree at most $q$ with $p(0) = 0$ has
$\max_{\lambda \in [-\kappa, -1] \cup [1, \kappa]} \lvert 1 - p(\lambda) \rvert \ge e^{-2q/\kappa}$:
$$e^{-2q/\kappa} \le \mathsf{residualMinimax}\bigl([-\kappa, -1] \cup [1, \kappa], q\bigr) \,.$$
[Shamir2026, Lemma 1]; there $\rho_d(\kappa)$, the infimum over $p(0) = 0$ of the maximum of
$\lvert 1 - p \rvert$, which is `NLAlib.residualMinimax` of the residual $1 - p$.
Result: polynomial-two-interval-inapproximability -/
theorem exp_neg_le_residualMinimax_Icc_union_Icc {κ : ℝ} (hκ : 2 ≤ κ) (q : ℕ) :
    Real.exp (-(2 * q / κ)) ≤ residualMinimax (Set.Icc (-κ) (-1) ∪ Set.Icc 1 κ) q := by
  have hκ1 : (1 : ℝ) < κ := by linarith
  have h := residualMinimax_Icc_union_Icc (a := 1) (a' := κ) q one_pos hκ1
  rw [one_pow] at h
  rw [h]
  refine (Real.exp_le_exp.2 ?_).trans (exp_neg_le_inv_eval_T_real (by linarith) (q / 2))
  have hq : ((4 * (q / 2 : ℕ) : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 4 * (q / 2) ≤ 2 * q)
  push_cast at hq
  have hκ0 : (0 : ℝ) < κ := by linarith
  have : 4 * ((q / 2 : ℕ) : ℝ) / κ ≤ 2 * (q : ℝ) / κ :=
    div_le_div_of_nonneg_right (by linarith) hκ0.le
  linarith

/-- Regrouping a sum over `ι` by the fibres of `g`: the weight of a point `x` is the sum of the
weights `c i` over the preimage of `x`. -/
private lemma sum_image_fiber_mul {ι : Type*} [Fintype ι] (g c : ι → ℝ) (F : ℝ → ℝ) :
    ∑ x ∈ Finset.univ.image g, (∑ i ∈ Finset.univ.filter (fun i => g i = x), c i) * F x =
      ∑ i, c i * F (g i) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := Finset.univ.image g)
    (fun i _ => Finset.mem_image_of_mem g (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- **Weighted inapproximability on two intervals**: for $0 < a < a'$ there are at most $q + 2$
points of $S = [-a', -a] \cup [a, a']$ and positive weights summing to $1$ on them such that every
$p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ has
$$\mathsf{residualMinimax}(S, q)^2 \le \sum_x w_x \lvert p(x) \rvert^2 \,.$$
The points are $\pm\sqrt{\xi_j}$ for the Chebyshev extrema $\xi_j$ of $[a^2, a'^2]$, with weights
$\omega_j/(2\tau)$, $\tau = \sum_j \omega_j$. The reverse inequality holds for every probability
vector, so the infimum over residuals of the weighted sum is the squared minimax value.
[Shamir2026, Lemma 2]; there with at most $q + 1$ points, from the Kroó–Pinkus
characterization (Kroó and Pinkus 2010, Theorem 2.3), here with the explicit Chebyshev points
($2\lfloor q/2 \rfloor + 2$ of them) and no characterization theorem. -/
theorem exists_residualMinimax_Icc_union_Icc_sq_le_sum_mul_norm_sq (𝕜 : Type*) [RCLike 𝕜]
    {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a' ∧ s.card ≤ q + 2 ∧
      ∃ w : ℝ → ℝ, (∀ x ∈ s, 0 < w x) ∧ ∑ x ∈ s, w x = 1 ∧
        ∀ p : 𝕜[X], p.degree ≤ q → p.eval 0 = 1 →
          residualMinimax (Set.Icc (-a') (-a) ∪ Set.Icc a a') q ^ 2 ≤
            ∑ x ∈ s, w x * ‖p.eval (x : 𝕜)‖ ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have haa2 : a ^ 2 < a' ^ 2 := by nlinarith
  have ha' : 0 < a' := by linarith
  -- the square roots of the Chebyshev extrema lie in [a, a']
  have hsq : ∀ j : Fin (q / 2 + 1),
      a ≤ Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) ∧
      Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) ≤ a' := by
    intro j
    obtain ⟨h1, h2⟩ := chebyshevExtremum_mem_Icc haa2.le (q / 2) j
    have h1' := Real.sqrt_le_sqrt h1
    have h2' := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq ha.le] at h1'
    rw [Real.sqrt_sq ha'.le] at h2'
    exact ⟨h1', h2'⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ,
      τ = (T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)) := ⟨_, rfl⟩
  have hτ : ∑ j : Fin (q / 2 + 1), chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j = τ := by
    rw [hτdef]; exact sum_chebyshevWeight ha2 haa2 (q / 2)
  have hτpos : 0 < τ := by
    rw [← hτ]
    exact Finset.sum_pos (fun j _ => chebyshevWeight_pos ha2 haa2 (q / 2) j) Finset.univ_nonempty
  -- the points `±√ξ_j` (indexed by `(j, b)`) and the weights `ω_j / (2τ)`
  let g : Fin (q / 2 + 1) × Bool → ℝ := fun i =>
    if i.2 then Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) i.1)
    else -Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) i.1)
  let c : Fin (q / 2 + 1) × Bool → ℝ := fun i =>
    chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) i.1 / (2 * τ)
  have hg : ∀ i, g i ∈ Set.Icc (-a') (-a) ∪ Set.Icc a a' := by
    rintro ⟨j, _ | _⟩
    · exact Or.inl ⟨by change -a' ≤ -Real.sqrt _; linarith [(hsq j).2],
        by change -Real.sqrt _ ≤ -a; linarith [(hsq j).1]⟩
    · exact Or.inr (hsq j)
  have hsub : (↑(Finset.univ.image g) : Set ℝ) ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a' := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hg i
  have hcard : (Finset.univ.image g).card ≤ q + 2 := by
    refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    omega
  have hw : ∀ x ∈ Finset.univ.image g, 0 < ∑ i ∈ Finset.univ.filter (fun i => g i = x), c i := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.sum_pos
      (fun j _ => div_pos (chebyshevWeight_pos ha2 haa2 (q / 2) j.1) (mul_pos two_pos hτpos))
      ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hsum : ∑ x ∈ Finset.univ.image g, ∑ i ∈ Finset.univ.filter (fun i => g i = x), c i = 1 := by
    have h := sum_image_fiber_mul g c (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    have hc : ∀ j : Fin (q / 2 + 1), ∑ b : Bool, c (j, b) =
        chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / τ := by
      intro j
      rw [Fintype.sum_bool]
      simp only [c]
      ring
    rw [h, Fintype.sum_prod_type, Finset.sum_congr rfl fun j _ => hc j]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, hτ, mul_inv_cancel₀ hτpos.ne']
  refine ⟨Finset.univ.image g, hsub, hcard, _, hw, hsum, ?_⟩
  intro p hp hp₀
  have hR := residualMinimax_Icc_union_Icc q ha haa
  have hD := inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq (𝕜 := 𝕜) ha haa hp hp₀
  rw [← hτdef] at hD
  have key : ∑ x ∈ Finset.univ.image g,
      (∑ i ∈ Finset.univ.filter (fun i => g i = x), c i) * ‖p.eval (x : 𝕜)‖ ^ 2 =
      (∑ j : Fin (q / 2 + 1), chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)‖ ^ 2 +
          ‖p.eval (-((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜))‖ ^ 2)
        / τ) := by
    refine (sum_image_fiber_mul g c (fun x => ‖p.eval (x : 𝕜)‖ ^ 2)).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    simp only [c, g, RCLike.ofReal_neg, if_true, Bool.false_eq_true, if_false]
    ring
  rw [hR, key, ← hτdef, sq]
  have h2 := mul_le_mul_of_nonneg_left hD (inv_nonneg.2 hτpos.le)
  refine h2.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {n : Type*} [Fintype n]

/-- The values of a Chebyshev two-interval spectrum lie in $[-\kappa, -1] \cup [1, \kappa]$ for
$\kappa > 1$. -/
theorem IsChebyshevTwoIntervalSpectrum.mem_Icc_union_Icc {κ : ℝ} {s M : ℕ} {d : n → ℝ}
    (hd : IsChebyshevTwoIntervalSpectrum κ s M d) (hκ : 1 < κ) (i : n) :
    d i ∈ Set.Icc (-κ) (-1) ∪ Set.Icc 1 κ := by
  obtain ⟨j, h | h⟩ := hd.exists_eq i
  · have hξ := chebyshevExtremum_mem_Icc (a := 1) (a' := κ ^ 2) (by nlinarith) (s / 2) j
    have h1 : 1 ≤ Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
      Real.one_le_sqrt.mpr hξ.1
    have h2 : Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ≤ κ :=
      (Real.sqrt_le_sqrt hξ.2).trans_eq (Real.sqrt_sq (by linarith))
    rw [h]
    exact Set.mem_union_right _ ⟨h1, h2⟩
  · have hξ := chebyshevExtremum_mem_Icc (a := 1) (a' := κ ^ 2) (by nlinarith) (s / 2) j
    have h1 : 1 ≤ Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
      Real.one_le_sqrt.mpr hξ.1
    have h2 : Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ≤ κ :=
      (Real.sqrt_le_sqrt hξ.2).trans_eq (Real.sqrt_sq (by linarith))
    rw [h]
    exact Set.mem_union_left _ ⟨by linarith, by linarith⟩

/-- A value taken at least once by `d` lies in the image of `d`. -/
private lemma mem_image_of_card_pos {d : n → ℝ} {t : ℝ}
    (h : 0 < (Finset.univ.filter fun i => d i = t).card) : t ∈ Finset.univ.image d := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter] at hi
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.2⟩

/-- Weighted residual bound on a Chebyshev two-interval spectrum: for $\kappa > 1$, a
Chebyshev two-interval spectrum $d$ with depth $s$ and margin $M$, and every real $p$ with
$\deg p \le s$ and $p(0) = 1$,
$$\frac{\lvert n \rvert}{4}\,T_k\Bigl(\frac{\kappa^2 + 1}{\kappa^2 - 1}\Bigr)^{-2} \le
\sum_{t} \bigl(m_t - M\bigr)\,p(t)^2 \,,$$
the sum over the distinct values $t$ of $d$, $m_t$ the number of $i$ with $d_i = t$, and
$k = \lfloor s/2 \rfloor$. -/
theorem IsChebyshevTwoIntervalSpectrum.inv_sq_le_sum_card_sub_mul_eval_sq {κ : ℝ} {s M : ℕ}
    {d : n → ℝ} (hd : IsChebyshevTwoIntervalSpectrum κ s M d) (hκ : 1 < κ) {p : ℝ[X]}
    (hp : p.degree ≤ s) (hp₀ : p.eval 0 = 1) :
    (Fintype.card n : ℝ) / 4 * ((T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))⁻¹ ^ 2 ≤
      ∑ t ∈ Finset.univ.image d,
        (((Finset.univ.filter fun i => d i = t).card : ℝ) - M) * p.eval t ^ 2 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hκ2 : (1 : ℝ) < κ ^ 2 := by nlinarith
  set τ := (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)) with hτdef
  set ω := chebyshevWeight 1 (κ ^ 2) (s / 2) with hωdef
  have hτ : ∑ j, ω j = τ := sum_chebyshevWeight one_pos hκ2 (s / 2)
  have hωpos : ∀ j, 0 < ω j := fun j => chebyshevWeight_pos one_pos hκ2 (s / 2) j
  have hτpos : 0 < τ := by
    rw [← hτ]; exact Finset.sum_pos (fun j _ => hωpos j) Finset.univ_nonempty
  have hξpos : ∀ j : Fin (s / 2 + 1), 0 < chebyshevExtremum 1 (κ ^ 2) (s / 2) j := fun j =>
    lt_of_lt_of_le one_pos (chebyshevExtremum_mem_Icc (a := 1) (a' := κ ^ 2) hκ2.le (s / 2) j).1
  have hsq : StrictMono fun j : Fin (s / 2 + 1) =>
      Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) := fun i j hij =>
    Real.sqrt_lt_sqrt (hξpos i).le (strictMono_chebyshevExtremum hκ2 (s / 2) hij)
  have hpos : ∀ j : Fin (s / 2 + 1), (0 : ℝ) < (Fintype.card n : ℝ) / 4 * (ω j / (2 * τ)) + M :=
    fun j => by have := hωpos j; positivity
  have hmemA : ∀ j : Fin (s / 2 + 1),
      Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ∈ Finset.univ.image d := fun j =>
    mem_image_of_card_pos (by exact_mod_cast (hpos j).trans_le (hd.le_card_pos j))
  have hmemB : ∀ j : Fin (s / 2 + 1),
      -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ∈ Finset.univ.image d := fun j =>
    mem_image_of_card_pos (by exact_mod_cast (hpos j).trans_le (hd.le_card_neg j))
  have himg : Finset.univ.image d =
      (Finset.univ.image fun j : Fin (s / 2 + 1) =>
        Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ∪
      (Finset.univ.image fun j : Fin (s / 2 + 1) =>
        -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) := by
    ext t
    constructor
    · intro ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨j, hj | hj⟩ := hd.exists_eq i
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩)
    · intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
        exact hmemA j
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
        exact hmemB j
  have hdisj : Disjoint (Finset.univ.image fun j : Fin (s / 2 + 1) =>
      Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j))
      (Finset.univ.image fun j : Fin (s / 2 + 1) =>
        -Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp ht'
    linarith [Real.sqrt_pos.mpr (hξpos j), Real.sqrt_nonneg (chebyshevExtremum 1 (κ ^ 2) (s / 2) l)]
  rw [himg, Finset.sum_union hdisj, Finset.sum_image (fun i _ j _ h => hsq.injective h),
    Finset.sum_image (fun i _ j _ h => hsq.injective (neg_injective h))]
  have hmain : τ⁻¹ ≤ ∑ j : Fin (s / 2 + 1), ω j / 2 *
      (p.eval (Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2 +
        p.eval (-Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2) := by
    have := inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq (𝕜 := ℝ)
      (a := 1) (a' := κ) one_pos hκ hp hp₀
    simpa only [one_pow, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs, sq_abs] using this
  have hK : 0 ≤ (Fintype.card n : ℝ) / (4 * τ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmain hK
  rw [Finset.mul_sum] at h1
  have h0 : (Fintype.card n : ℝ) / 4 * τ⁻¹ ^ 2 = (Fintype.card n : ℝ) / (4 * τ) * τ⁻¹ := by
    ring
  rw [h0]
  refine h1.trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : (Fintype.card n : ℝ) / (4 * τ) * (ω j / 2 *
      (p.eval (Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2 +
        p.eval (-Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2)) =
      (Fintype.card n : ℝ) / 4 * (ω j / (2 * τ)) *
        p.eval (Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2 +
      (Fintype.card n : ℝ) / 4 * (ω j / (2 * τ)) *
        p.eval (-Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j)) ^ 2 := by
    ring
  rw [e]
  gcongr <;> linarith [hd.le_card_pos j, hd.le_card_neg j]

/-- Realize prescribed multiplicities: an injective list of values `v` on `ι` and counts `c`
summing to `|n|` give `d : n → ℝ` with values in `range v` and fibre cardinalities `c`. -/
private lemma exists_fun_card_fiber {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : Function.Injective v) (c : ι → ℕ) (hc : ∑ t, c t = Fintype.card n) :
    ∃ d : n → ℝ, (∀ i, ∃ t, d i = v t) ∧
      ∀ t, (Finset.univ.filter fun i => d i = v t).card = c t := by
  classical
  have hcard : Fintype.card n = Fintype.card (Σ t, Fin (c t)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hc.symm
  let e : n ≃ Σ t, Fin (c t) := Fintype.equivOfCardEq hcard
  refine ⟨fun i => v (e i).1, fun i => ⟨(e i).1, rfl⟩, fun t => ?_⟩
  have hfilt : (Finset.univ.filter fun i => v (e i).1 = v t) =
      Finset.univ.filter fun i => (e i).1 = t :=
    Finset.filter_congr fun i _ => hv.eq_iff
  rw [hfilt, Finset.card_filter]
  refine (e.sum_comp (fun x => if x.1 = t then (1 : ℕ) else 0)).trans ?_
  rw [Fintype.sum_sigma,Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The signed Chebyshev points $(j, \mathrm{true}) \mapsto \sqrt{\xi_j}$,
$(j, \mathrm{false}) \mapsto -\sqrt{\xi_j}$ are injective. -/
private lemma chebyshevPoint_injective {κ : ℝ} (hκ : 1 < κ) (s : ℕ) :
    Function.Injective fun t : Fin (s / 2 + 1) × Bool =>
      if t.2 then √(chebyshevExtremum 1 (κ ^ 2) (s / 2) t.1)
      else -√(chebyshevExtremum 1 (κ ^ 2) (s / 2) t.1) := by
  have hlt : (1 : ℝ) < κ ^ 2 := by nlinarith
  have hpos : ∀ j : Fin (s / 2 + 1), 0 < √(chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
    fun j => Real.sqrt_pos.2 (by linarith [(chebyshevExtremum_mem_Icc hlt.le (s / 2) j).1])
  have hnn : ∀ j : Fin (s / 2 + 1), 0 ≤ chebyshevExtremum 1 (κ ^ 2) (s / 2) j :=
    fun j => by linarith [(chebyshevExtremum_mem_Icc hlt.le (s / 2) j).1]
  have hinj : ∀ j j' : Fin (s / 2 + 1), chebyshevExtremum 1 (κ ^ 2) (s / 2) j =
      chebyshevExtremum 1 (κ ^ 2) (s / 2) j' → j = j' := fun j j' h =>
    (strictMono_chebyshevExtremum hlt (s / 2)).injective h
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  cases b <;> cases b' <;> simp only [if_true, if_false, Bool.false_eq_true] at h
  all_goals first
    | (exfalso; linarith [hpos j, hpos j'])
    | rw [hinj j j' ((Real.sqrt_inj (hnn j) (hnn j')).1 h)]
    | rw [hinj j j' ((Real.sqrt_inj (hnn j) (hnn j')).1 (neg_inj.1 h))]

/-- Chebyshev two-interval spectra exist in every dimension
$\lvert n \rvert \ge \tfrac43 (s + 2)(M + 1)$: for $\kappa > 1$ and
$4(s + 2)(M + 1) \le 3\lvert n \rvert$ there is a Chebyshev two-interval spectrum on $n$ with
depth $s$ and margin $M$. -/
theorem exists_isChebyshevTwoIntervalSpectrum {κ : ℝ} (hκ : 1 < κ) {s M : ℕ}
    (hn : 4 * ((s + 2) * (M + 1)) ≤ 3 * Fintype.card n) :
    ∃ d : n → ℝ, IsChebyshevTwoIntervalSpectrum κ s M d := by
  classical
  -- points: `(j, true) ↦ √ξ_j`, `(j, false) ↦ -√ξ_j`
  set ξ : Fin (s / 2 + 1) → ℝ := fun j => chebyshevExtremum 1 (κ ^ 2) (s / 2) j with hξ
  set ω : Fin (s / 2 + 1) → ℝ := fun j => chebyshevWeight 1 (κ ^ 2) (s / 2) j with hω
  set τ : ℝ := (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)) with hτ
  have hτ1 : 1 ≤ τ := one_le_eval_T_real _ (by rw [le_div_iff₀ (by nlinarith)]; nlinarith)
  have hsum : ∑ j, ω j = τ := sum_chebyshevWeight zero_lt_one (by nlinarith) (s / 2)
  let v : Fin (s / 2 + 1) × Bool → ℝ := fun t => if t.2 then √(ξ t.1) else -√(ξ t.1)
  have hv : Function.Injective v := chebyshevPoint_injective hκ s
  -- real multiplicity bounds
  let B : Fin (s / 2 + 1) → ℝ := fun j => (Fintype.card n : ℝ) / 4 * (ω j / (2 * τ)) + M
  have hB0 : ∀ j, 0 ≤ B j := fun j => by
    have h1 : 0 ≤ ω j / (2 * τ) := div_nonneg (abs_nonneg _) (by linarith)
    have h2 : (0 : ℝ) ≤ (Fintype.card n : ℝ) / 4 := by positivity
    have h3 : (0 : ℝ) ≤ M := by positivity
    exact add_nonneg (mul_nonneg h2 h1) h3
  have hsumU : ∀ f : Fin (s / 2 + 1) → ℝ,
      ∑ u : Fin (s / 2 + 1) × Bool, f u.1 = 2 * ∑ j, f j := by
    intro f
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, two_mul, Finset.sum_add_distrib]
  have hsumB8 : ∑ j, B j = (Fintype.card n : ℝ) / 8 + ((s / 2 + 1 : ℕ) : ℝ) * M := by
    simp only [B, div_eq_mul_inv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hτne : τ ≠ 0 := by linarith
    field_simp
    ring
  have hPR : 2 * ((s / 2 + 1 : ℕ) : ℝ) ≤ (s : ℝ) + 2 := by
    have : 2 * (s / 2 + 1) ≤ s + 2 := by omega
    exact_mod_cast this
  have hnR : 4 * (((s : ℝ) + 2) * ((M : ℝ) + 1)) ≤ 3 * (Fintype.card n : ℝ) := by
    exact_mod_cast hn
  have hsumB : ∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊ ≤ Fintype.card n := by
    have h3 : ((∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊ : ℕ) : ℝ) ≤ (Fintype.card n : ℝ) := by
      push_cast
      calc ∑ u : Fin (s / 2 + 1) × Bool, (⌈B u.1⌉₊ : ℝ)
          ≤ ∑ u : Fin (s / 2 + 1) × Bool, (B u.1 + 1) :=
            Finset.sum_le_sum fun u _ => (Nat.ceil_lt_add_one (hB0 u.1)).le
        _ = (Fintype.card n : ℝ) / 4 + 2 * ((s / 2 + 1 : ℕ) : ℝ) * (M + 1) := by
            rw [Finset.sum_add_distrib, hsumU B]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              Fintype.card_bool, nsmul_eq_mul, hsumB8]
            push_cast
            ring
        _ ≤ Fintype.card n := by
            nlinarith [mul_le_mul_of_nonneg_right hPR (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
    exact_mod_cast h3
  let c : Fin (s / 2 + 1) × Bool → ℕ := fun t =>
    ⌈B t.1⌉₊ + if t = (0, true) then Fintype.card n - ∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊
      else 0
  have hc : ∑ t, c t = Fintype.card n := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  obtain ⟨d, hd1, hd2⟩ := exists_fun_card_fiber v hv c hc
  refine ⟨d, ⟨fun i => ?_, fun j => ?_, fun j => ?_⟩⟩
  · obtain ⟨⟨j, b⟩, hi⟩ := hd1 i
    cases b
    · exact ⟨j, Or.inr hi⟩
    · exact ⟨j, Or.inl hi⟩
  · have key : (Finset.univ.filter fun i => d i = √(ξ j)).card = c (j, true) := hd2 (j, true)
    have hc1 : ((⌈B j⌉₊ : ℕ) : ℝ) ≤ (c (j, true) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    change B j ≤ ((Finset.univ.filter fun i => d i =√(ξ j)).card : ℝ)
    rw [key]
    linarith [Nat.le_ceil (B j)]
  · have key : (Finset.univ.filter fun i => d i = -√(ξ j)).card = c (j, false) := hd2 (j, false)
    have hc1 : ((⌈B j⌉₊ : ℕ) : ℝ) ≤ (c (j, false) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    change B j ≤ ((Finset.univ.filter fun i => d i =-√(ξ j)).card : ℝ)
    rw [key]
    linarith [Nat.le_ceil (B j)]

end NLAlib
