/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.JacksonKernel
public import NLAlib.Polynomial.Approximation.ChebyshevTruncation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.MetricSpace.Lipschitz
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Constructive Jackson approximation

Jackson damping applied to the canonical full Chebyshev coefficients gives an inclusive
degree-$N$ approximant. The positive kernel has mass $2\pi$, including its full constant mode.
The construction follows [ChenTrogdonUbaru2022, Appendix C], specifically the first arXiv version,
and extends the norm estimate to real- or complex-valued functions.

Classical background is given in [Rivlin1981]. [ShahUrschelWest2026, §1 and Theorem 1.3]
identifies this construction as the Rivlin/KPM kernel and analyzes sharper asymptotic constants.

## Main results

* `jacksonApprox`: the explicit damped Chebyshev polynomial.
* `chebyshevCoeff_jacksonApprox`: its canonical coefficients.
* `norm_chebyshevCoeff_jacksonApprox_le`: damping contracts each coefficient.
* `isUniformApproxOn_jacksonApprox_of_lipschitz`: constructive uniform approximation.
* `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith`: the same on an interval $[a, b]$.
* `NLAlib.minimaxError_le_of_lipschitzOnWith`: Jackson's bound on $E_N(f; [a, b])$.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev Finset
open scoped NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Jackson approximant is $\sum_{k=0}^N g_{N,k}a_kT_k$, using the canonical full
coefficients and normalized sine-autocorrelation damping.
[ChenTrogdonUbaru2022, Appendix C, Theorem 38 and Lemma 45]. For arbitrary functions this is
a total finite polynomial; each coefficient retains its own Bochner-integral convention.
At $N=0$ it is the constant coefficient. It reproduces constants, but generally damps positive
polynomial modes rather than reproducing every polynomial within the degree budget. -/
noncomputable def jacksonApprox (f : ℝ → 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C ((jacksonDamping N k : 𝕜) * chebyshevCoeff f k) *
      Polynomial.Chebyshev.T 𝕜 (k : ℤ)

/-- Evaluate the finite Jackson approximant term by term. -/
theorem eval_jacksonApprox (f : ℝ → 𝕜) (N : ℕ) (x : 𝕜) :
    (jacksonApprox f N).eval x = ∑ k ∈ Finset.range (N + 1),
      (jacksonDamping N k : 𝕜) * chebyshevCoeff f k *
        (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval x := by
  simp only [jacksonApprox, eval_finsetSum, eval_mul, eval_C]

/-- The inclusive degree budget holds even when coefficients vanish. -/
theorem degree_jacksonApprox_le (f : ℝ → 𝕜) (N : ℕ) :
    (jacksonApprox f N).degree ≤ (N : WithBot ℕ) := by
  unfold jacksonApprox
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
  rw [C_mul']
  refine (degree_smul_le _ _).trans ?_
  rw [degree_T, Int.natAbs_natCast]
  exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)

/-- The canonical coefficients of the explicit approximant are precisely the damped input
coefficients, with zero padding beyond $N$. This finite orthogonality consequence of
[ChenTrogdonUbaru2022, Appendix C, Theorem 38] needs no regularity of the original function. -/
theorem chebyshevCoeff_jacksonApprox (f : ℝ → 𝕜) (N k : ℕ) :
    chebyshevCoeff (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) k =
      (jacksonDamping N k : 𝕜) * chebyshevCoeff f k := by
  unfold jacksonApprox
  simp_rw [C_mul']
  rw [chebyshevCoeff_sum_smul_T]
  by_cases hk : k < N + 1
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, hk,
      if_true]
  · have hNk : N < k := by omega
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, hk,
      if_false, jacksonDamping_of_lt hNk, RCLike.ofReal_zero, zero_mul]

/-- Each canonical coefficient contracts under Jackson damping, since the damping lies in
$[0,1]$. [ChenTrogdonUbaru2022, Appendix C, Lemma 45]. -/
theorem norm_chebyshevCoeff_jacksonApprox_le (f : ℝ → 𝕜) (N k : ℕ) :
    ‖chebyshevCoeff (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) k‖ ≤
      ‖chebyshevCoeff f k‖ := by
  rw [chebyshevCoeff_jacksonApprox, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (jacksonDamping_nonneg N k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (jacksonDamping_le_one N k)

private lemma integral_even (g : ℝ → 𝕜) (hg : Continuous g)
    (he : ∀ t, g (-t) = g t) :
    (∫ t in -Real.pi..Real.pi, g t) = 2 * ∫ t in 0..Real.pi, g t := by
  have hn := intervalIntegral.integral_comp_neg (f := g) (a := -Real.pi) (b := 0)
  simp_rw [he] at hn
  simp only [neg_zero, neg_neg] at hn
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-Real.pi) 0) (hg.intervalIntegrable 0 Real.pi), hn]
  ring

private lemma integral_odd (g : ℝ → 𝕜) (hg : Continuous g)
    (he : ∀ t, g (-t) = -g t) : (∫ t in -Real.pi..Real.pi, g t) = 0 := by
  have hn := intervalIntegral.integral_comp_neg (f := g) (a := -Real.pi) (b := 0)
  simp_rw [he] at hn
  rw [intervalIntegral.integral_neg] at hn
  simp only [neg_zero, neg_neg] at hn
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-Real.pi) 0) (hg.intervalIntegrable 0 Real.pi)]
  rw [← hn]
  exact add_neg_cancel _

private lemma integral_sine_pullback {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℕ) :
    (∫ t in -Real.pi..Real.pi,
      (Real.sin ((k : ℝ) * t) : 𝕜) * f (Real.cos t)) = 0 := by
  apply integral_odd (fun t => (Real.sin ((k : ℝ) * t) : 𝕜) * f (Real.cos t))
    ((by fun_prop : Continuous
    (fun t : ℝ => (Real.sin ((k : ℝ) * t) : 𝕜))).mul
      (hf.comp_continuous Real.continuous_cos Real.cos_mem_Icc))
  intro t
  simp only [mul_neg, Real.sin_neg, Real.cos_neg, RCLike.ofReal_neg, neg_mul]

private lemma integral_cosine_pullback {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℕ) :
    (∫ t in -Real.pi..Real.pi,
      (Real.cos ((k : ℝ) * t) : 𝕜) * f (Real.cos t)) =
      (2 * Real.pi / (if k = 0 then 1 else 2) : ℝ) * chebyshevCoeff f k := by
  rw [integral_even (fun t => (Real.cos ((k : ℝ) * t) : 𝕜) * f (Real.cos t))
    ((by fun_prop : Continuous
    (fun t : ℝ => (Real.cos ((k : ℝ) * t) : 𝕜))).mul
      (hf.comp_continuous Real.continuous_cos Real.cos_mem_Icc))
    (by intro t; simp only [mul_neg, Real.cos_neg])]
  simp only [chebyshevCoeff]
  simp_rw [mul_comm (f (Real.cos _))]
  split_ifs <;> push_cast <;> field_simp

private lemma integral_shifted_cosine {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℕ) (θ : ℝ) :
    (∫ t in -Real.pi..Real.pi,
      (Real.cos ((k : ℝ) * (θ - t)) : 𝕜) * f (Real.cos t)) =
      (Real.cos ((k : ℝ) * θ) : 𝕜) *
        ((2 * Real.pi / (if k = 0 then 1 else 2) : ℝ) * chebyshevCoeff f k) := by
  have hfc : Continuous (fun t : ℝ => f (Real.cos t)) :=
    hf.comp_continuous Real.continuous_cos Real.cos_mem_Icc
  have hc : Continuous (fun t : ℝ => (Real.cos ((k : ℝ) * t) : 𝕜) * f (Real.cos t)) :=
    (by fun_prop : Continuous (fun t : ℝ => (Real.cos ((k : ℝ) * t) : 𝕜))).mul hfc
  have hs : Continuous (fun t : ℝ => (Real.sin ((k : ℝ) * t) : 𝕜) * f (Real.cos t)) :=
    (by fun_prop : Continuous (fun t : ℝ => (Real.sin ((k : ℝ) * t) : 𝕜))).mul hfc
  simp_rw [mul_sub, Real.cos_sub, RCLike.ofReal_add, RCLike.ofReal_mul, add_mul, mul_assoc]
  rw [intervalIntegral.integral_add
    ((hc.const_mul _).intervalIntegrable _ _) ((hs.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sine_pullback hf, integral_cosine_pullback hf, mul_zero, add_zero]

private lemma continuous_kernel (N : ℕ) : Continuous (jacksonKernel N) := by
  unfold jacksonKernel
  fun_prop

private lemma integral_kernel_pullback {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (N : ℕ) (θ : ℝ) :
    (∫ t in -Real.pi..Real.pi, (jacksonKernel N (θ - t) : 𝕜) * f (Real.cos t)) =
      ((2 * Real.pi : ℝ) : 𝕜) * (jacksonApprox f N).eval (Real.cos θ : 𝕜) := by
  have hfc : Continuous (fun t : ℝ => f (Real.cos t)) :=
    hf.comp_continuous Real.continuous_cos Real.cos_mem_Icc
  have hterm (k : ℕ) : Continuous (fun t : ℝ => (jacksonDamping N (k + 1) : 𝕜) *
      ((Real.cos (((k + 1 : ℕ) : ℝ) * (θ - t)) : 𝕜) * f (Real.cos t))) :=
    (((by fun_prop : Continuous (fun t : ℝ =>
      (Real.cos (((k + 1 : ℕ) : ℝ) * (θ - t)) : 𝕜))).mul hfc).const_mul _)
  have hexp : ∀ t : ℝ, (jacksonKernel N (θ - t) : 𝕜) * f (Real.cos t) =
      f (Real.cos t) + 2 * ∑ k ∈ range N,
        (jacksonDamping N (k + 1) : 𝕜) *
          ((Real.cos (((k + 1 : ℕ) : ℝ) * (θ - t)) : 𝕜) * f (Real.cos t)) := by
    intro t
    simp only [jacksonKernel, RCLike.ofReal_add, RCLike.ofReal_mul,
      RCLike.ofReal_one, RCLike.ofReal_ofNat, map_sum, add_mul, one_mul, sum_mul, mul_assoc]
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (hfc.intervalIntegrable _ _)
    ((Continuous.const_mul (continuous_finsetSum _ (fun k _ => hterm k)) _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => (hterm k).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_shifted_cosine hf]
  have hzero := integral_cosine_pullback hf 0
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, RCLike.ofReal_one, one_mul,
    if_true, div_one] at hzero
  rw [hzero, eval_jacksonApprox, sum_range_succ']
  simp only [jacksonDamping_zero, RCLike.ofReal_one, one_mul, Nat.cast_zero,
    T_zero, eval_one, mul_one]
  have hT (k : ℕ) : (T 𝕜 (k : ℤ)).eval (Real.cos θ : 𝕜) =
      (Real.cos ((k : ℝ) * θ) : 𝕜) := by
    rw [← map_T (algebraMap ℝ 𝕜), eval_map_apply, T_real_cos]
    rfl
  simp_rw [hT, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
  simp only [RCLike.ofReal_div, RCLike.ofReal_mul, RCLike.ofReal_ofNat]
  rw [mul_add, mul_sum, mul_sum]
  conv_rhs => rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro k hk
  ring

private lemma integral_shift (g : ℝ → ℝ)
    (hg : Function.Periodic g (2 * Real.pi)) (θ : ℝ) :
    (∫ t in -Real.pi..Real.pi, g (θ - t)) = ∫ t in -Real.pi..Real.pi, g t := by
  rw [intervalIntegral.integral_comp_sub_left]
  convert hg.intervalIntegral_add_eq (θ - Real.pi) (-Real.pi) using 1 <;>
    congr 1 <;> ring

private lemma cosine_chord_young (θ t β : ℝ) (hβ : 0 < β) :
    |Real.cos t - Real.cos θ| ≤ (1 - Real.cos (θ - t)) / β + β / 2 := by
  have hθ := Real.sin_sq_add_cos_sq θ
  have ht := Real.sin_sq_add_cos_sq t
  have hc : (Real.cos t - Real.cos θ) ^ 2 ≤ 2 * (1 - Real.cos (θ - t)) := by
    rw [Real.cos_sub]
    nlinarith [sq_nonneg (Real.sin t - Real.sin θ)]
  have hy := sq_nonneg (|Real.cos t - Real.cos θ| - β)
  have habs : |Real.cos t - Real.cos θ| ^ 2 = (Real.cos t - Real.cos θ) ^ 2 := sq_abs _
  have he : ((1 - Real.cos (θ - t)) / β + β / 2) * β =
      (1 - Real.cos (θ - t)) + β ^ 2 / 2 := by field_simp
  apply (mul_le_mul_iff_right₀ hβ).mp
  nlinarith

private lemma integral_kernel_majorant (N : ℕ) (θ : ℝ) :
    (∫ t in -Real.pi..Real.pi, jacksonKernel N (θ - t) *
      ((1 - Real.cos (θ - t)) / (Real.pi / (N + 2)) + (Real.pi / (N + 2)) / 2)) ≤
      2 * Real.pi * (Real.pi / (N + 2)) := by
  let β : ℝ := Real.pi / (N + 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hK := integral_shift _ (jacksonKernel_periodic N) θ
  have hC := integral_shift (fun t => Real.cos t * jacksonKernel N t)
    (Real.cos_periodic.mul (jacksonKernel_periodic N)) θ
  rw [integral_jacksonKernel] at hK
  rw [integral_cos_mul_jacksonKernel] at hC
  have he : ∀ t : ℝ, jacksonKernel N (θ - t) *
      ((1 - Real.cos (θ - t)) / β + β / 2) =
      (jacksonKernel N (θ - t) - Real.cos (θ - t) * jacksonKernel N (θ - t)) / β +
        β / 2 * jacksonKernel N (θ - t) := by intro t; ring
  change (∫ t in -Real.pi..Real.pi, jacksonKernel N (θ - t) *
    ((1 - Real.cos (θ - t)) / β + β / 2)) ≤ _
  simp_rw [he]
  have hkc : Continuous (fun t => jacksonKernel N (θ - t)) :=
    (continuous_kernel N).comp (by fun_prop)
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_div,
    intervalIntegral.integral_sub (hkc.intervalIntegrable _ _)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, hK, hC]
  have hcos := (Real.one_sub_sq_div_two_le_cos (x := β))
  have hd : (2 * Real.pi - 2 * Real.pi * Real.cos β) / β ≤ Real.pi * β := by
    apply (div_le_iff₀ hβ).mpr
    nlinarith [Real.pi_pos]
  change (2 * Real.pi - 2 * Real.pi * Real.cos β) / β + β / 2 * (2 * Real.pi) ≤ _
  nlinarith

private lemma norm_error_cos {f : ℝ → 𝕜} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) (N : ℕ) (θ : ℝ) :
    ‖(jacksonApprox f N).eval (Real.cos θ : 𝕜) - f (Real.cos θ)‖ ≤
      (L : ℝ) * (Real.pi / (N + 2)) := by
  let β : ℝ := Real.pi / (N + 2)
  let w : ℝ → ℝ := fun t => jacksonKernel N (θ - t) *
    ((1 - Real.cos (θ - t)) / β + β / 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hc := hf.continuousOn
  have hfc : Continuous (fun t : ℝ => f (Real.cos t)) :=
    hc.comp_continuous Real.continuous_cos Real.cos_mem_Icc
  have hk : Continuous (fun t => jacksonKernel N (θ - t)) :=
    (continuous_kernel N).comp (by fun_prop)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hmass := integral_shift _ (jacksonKernel_periodic N) θ
  rw [integral_jacksonKernel] at hmass
  have hdiff : (∫ t in -Real.pi..Real.pi,
      (jacksonKernel N (θ - t) : 𝕜) * (f (Real.cos t) - f (Real.cos θ))) =
      ((2 * Real.pi : ℝ) : 𝕜) *
        ((jacksonApprox f N).eval (Real.cos θ : 𝕜) - f (Real.cos θ)) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; exact (RCLike.continuous_ofReal.comp hk).mul hfc)
      (by apply Continuous.intervalIntegrable; fun_prop),
      integral_kernel_pullback hc, intervalIntegral.integral_mul_const,
      RCLike.intervalIntegral_ofReal, hmass]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => (jacksonKernel N (θ - t) : 𝕜) * (f (Real.cos t) - f (Real.cos θ)))
    (g := fun t => (L : ℝ) * w t) (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)
    (Filter.Eventually.of_forall fun t _ => ?_) ((hw.const_mul _).intervalIntegrable _ _)
  · rw [hdiff, norm_mul, RCLike.norm_ofReal, abs_of_pos (by positivity),
      intervalIntegral.integral_const_mul] at hbound
    have hmean : (∫ t in -Real.pi..Real.pi, w t) ≤ 2 * Real.pi * β :=
      integral_kernel_majorant N θ
    have hscaled := mul_le_mul_of_nonneg_left hmean L.coe_nonneg
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.pi by positivity)).mp
    nlinarith
  · rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (jacksonKernel_nonneg _ _)]
    have hl := hf.dist_le_mul (Real.cos t) ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
      (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    rw [dist_eq_norm, Real.dist_eq] at hl
    have hy := cosine_chord_young θ t β hβ
    calc
      _ ≤ jacksonKernel N (θ - t) * ((L : ℝ) * |Real.cos t - Real.cos θ|) :=
        mul_le_mul_of_nonneg_left hl (jacksonKernel_nonneg _ _)
      _ ≤ jacksonKernel N (θ - t) * ((L : ℝ) *
          ((1 - Real.cos (θ - t)) / β + β / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy L.coe_nonneg)
          (jacksonKernel_nonneg _ _)
      _ = _ := by dsimp [w]; ring

/-- The proved Jackson approximation factor currently equals
the value <!-- value jacksonApproximationConstant --> $\pi$.
The source [ChenTrogdonUbaru2022, Appendix C, Theorem 38] gives factor $\pi^2/2$.
The chord/Young estimate below proves the smaller factor $\pi$ for the same construction
and hypotheses; no optimality is asserted. Consumers use positivity and the upper comparison. -/
noncomputable irreducible_def jacksonApproximationConstant : ℝ := Real.pi

/-- The Jackson approximation factor is positive:
we have <!-- value jacksonApproximationConstant --> $0 < \pi$. -/
theorem jacksonApproximationConstant_pos : 0 < jacksonApproximationConstant := by
  rw [jacksonApproximationConstant_def]
  exact Real.pi_pos

/-- The Jackson approximation factor is at most
its current value <!-- value jacksonApproximationConstant --> $\pi$. -/
theorem jacksonApproximationConstant_le : jacksonApproximationConstant ≤ Real.pi := by
  rw [jacksonApproximationConstant_def]

/-- **Jackson's theorem for Lipschitz functions.** Jackson damping gives a degree-$N$
approximation for any $L$-Lipschitz function on $[-1,1]$ with uniform error
at most <!-- value jacksonApproximationConstant -->
$$\frac{\pi L}{N+2}.$$
[ChenTrogdonUbaru2022, Appendix C, Theorem 38] proves the source bound
$\pi^2L/(2(N+2))$. The chord/Young estimate here proves the smaller displayed bound for the
same construction and extends it to RCLike values, keeping full-coefficient normalization.
The assertion includes $N=0$, $L=0$ and both endpoints; values outside the segment play no role.

Result: jackson-lipschitz
-/
theorem isUniformApproxOn_jacksonApprox_of_lipschitz
    {f : ℝ → 𝕜} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    Metric.IsUniformApproxOn
      (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) f (Set.Icc (-1 : ℝ) 1)
      (jacksonApproximationConstant * (L : ℝ) / (N + 2 : ℝ)) := by
  intro x hx
  have hcos := Real.cos_arccos hx.1 hx.2
  have h := norm_error_cos hf N (Real.arccos x)
  rw [hcos] at h
  rw [dist_eq_norm]
  rw [jacksonApproximationConstant_def]
  convert h using 1
  ring

/-- **Jackson's theorem on an interval**: an $L$-Lipschitz $f$ on $[a, b]$, $a < b$, is
within <!-- value jacksonApproximationConstant -->
$$\frac{\pi L(b - a)}{2(N + 2)}$$
of a polynomial of degree at most $N$ on $[a, b]$ (the constant is
`jacksonApproximationConstant`). The affine image of
`isUniformApproxOn_jacksonApprox_of_lipschitz`. [ChenTrogdonUbaru2022, Appendix C, Theorem 38];
there on $[-1, 1]$ with the factor $\pi^2/2$.
Result: jackson-lipschitz -/
theorem exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith
    {f : ℝ → 𝕜} {L : ℝ≥0} {a b : ℝ} (hab : a < b) (hf : LipschitzOnWith L f (Set.Icc a b))
    (N : ℕ) :
    ∃ p : 𝕜[X], p.degree ≤ (N : WithBot ℕ) ∧
      Metric.IsUniformApproxOn (fun x : ℝ => p.eval (x : 𝕜)) f (Set.Icc a b)
        (jacksonApproximationConstant * L * (b - a) / (2 * (N + 2))) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  let φ : ℝ → ℝ := fun t => ((b - a) * t + b + a) / 2
  let K : ℝ≥0 := ⟨(b - a) / 2, by positivity⟩
  have hφ : LipschitzOnWith K φ (Set.Icc (-1 : ℝ) 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    have h : φ x - φ y = (b - a) / 2 * (x - y) := by simp only [φ]; ring
    rw [Real.dist_eq, Real.dist_eq, h, abs_mul, abs_of_pos (by positivity : 0 < (b - a) / 2)]
    rfl
  have hmaps : Set.MapsTo φ (Set.Icc (-1 : ℝ) 1) (Set.Icc a b) := fun t ht => by
    simp only [φ, Set.mem_Icc] at ht ⊢
    constructor <;> nlinarith [ht.1, ht.2]
  let g : ℝ → 𝕜 := fun t => f (φ t)
  have hg : LipschitzOnWith (L * K) g (Set.Icc (-1 : ℝ) 1) := hf.comp hφ hmaps
  let q := jacksonApprox g N
  let s : 𝕜[X] := C ((2 / (b - a) : ℝ) : 𝕜) * X - C (((b + a) / (b - a) : ℝ) : 𝕜)
  refine ⟨q.comp s, ?_, ?_⟩
  · refine degree_le_natDegree.trans ?_
    have hq := natDegree_le_of_degree_le (degree_jacksonApprox_le g N)
    have hs : s.natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
          (by simp only [natDegree_C, zero_le]))
    have h : (q.comp s).natDegree ≤ N :=
      natDegree_comp_le.trans ((Nat.mul_le_mul hq hs).trans_eq (mul_one N))
    exact_mod_cast h
  · intro x hx
    let t := (2 * x - b - a) / (b - a)
    have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simp only [t, Set.mem_Icc, le_div_iff₀ hba, div_le_iff₀ hba]
      constructor <;> linarith [hx.1, hx.2]
    have hi : φ t = x := by
      simp only [φ, t]
      field_simp
      ring
    have he : s.eval (x : 𝕜) = (t : 𝕜) := by
      simp only [s, eval_sub, eval_mul, eval_C, eval_X, t]
      push_cast
      field_simp
      ring
    have h := (isUniformApproxOn_jacksonApprox_of_lipschitz hg N).apply ht
    change dist ((q.comp s).eval (x : 𝕜)) (f x) ≤ _
    rw [eval_comp, he]
    have hfx : g t = f x := by simp only [g, hi]
    rw [← hfx]
    refine h.trans_eq ?_
    have hK : (K : ℝ) = (b - a) / 2 := rfl
    rw [NNReal.coe_mul, hK]
    field_simp

/-- **Jackson's theorem for the minimax error**: an $L$-Lipschitz real $f$ on $[a, b]$, $a < b$,
satisfies <!-- value jacksonApproximationConstant -->
$$E_N(f; [a, b]) \le \frac{\pi L(b - a)}{2(N + 2)}$$
(the constant is `jacksonApproximationConstant`). [ChenTrogdonUbaru2022, Appendix C,
Theorem 38] gives the Jackson-damped bound on $[-1,1]$ with factor $\pi^2/2$. The local
first-moment estimate for the constructed polynomial yields the factor $\pi$ before rescaling the
interval.
Result: jackson-lipschitz -/
theorem minimaxError_le_of_lipschitzOnWith {f : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a < b)
    (hf : LipschitzOnWith L f (Set.Icc a b)) (N : ℕ) :
    minimaxError f (Set.Icc a b) N ≤
      jacksonApproximationConstant * L * (b - a) / (2 * (N + 2)) := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf N
  simp only [RCLike.ofReal_real_eq_id, id] at hε
  exact minimaxError_le_of_isUniformApproxOn hp (hε.nonneg (Set.nonempty_Icc.mpr hab.le)) hε

end NLAlib
