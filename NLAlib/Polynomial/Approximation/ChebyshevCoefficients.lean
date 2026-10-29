/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Topology.Algebra.Polynomial
public import NLAlib.ForMathlib.Analysis.RCLike.ToComplex
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-!
# Chebyshev coefficients

Canonical full Chebyshev coefficients for real-input, real- or complex-valued functions.
The constant coefficient uses $1/\pi$ and positive coefficients use $2/\pi$, so the expansion
has no half-constant term. Cosine Bochner integrals are primary; later contour representations
are equalities, not additional coefficient objects.

## Main results

* `NLAlib.chebyshevCoeff`: the canonical coefficient.
* `NLAlib.chebyshevCoeff_add`: additivity under interval integrability.
* `NLAlib.chebyshevCoeff_const_mul`: scalar linearity.
* `NLAlib.chebyshevCoeff_eval_T`: coefficient identification on the Chebyshev basis.
* `NLAlib.norm_chebyshevCoeff_le`: the coefficients of a function bounded by $M$ are at most $2M$.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The full coefficient is
$$a_k=\frac{2-\mathbf{1}_{k=0}}{\pi}\int_0^\pi f(\cos\theta)\cos(k\theta)\,d\theta.$$
[Trefethen2019, Theorem 3.1, Eqs. (3.11)–(3.12)], after cosine substitution, generalized to
RCLike values. Each weighted integrand has its own Bochner integrability condition; its integral
is zero when nonintegrable. Nonintegrability of the unweighted pullback does not force every
coefficient to vanish. No reconstruction is asserted for arbitrary functions. -/
noncomputable def chebyshevCoeff (f : ℝ → 𝕜) (k : ℕ) : 𝕜 :=
  (((if k = 0 then 1 else 2) / Real.pi : ℝ) : 𝕜) *
    ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)

/-- Every coefficient of the zero function vanishes. -/
theorem chebyshevCoeff_zero (k : ℕ) :
    chebyshevCoeff (fun _ : ℝ => (0 : 𝕜)) k = 0 := by
  simp only [chebyshevCoeff, zero_mul, intervalIntegral.integral_zero, mul_zero]

/-- Coefficients are additive when the cosine pullbacks are interval-integrable. -/
theorem chebyshevCoeff_add {f g : ℝ → 𝕜}
    (hf : IntervalIntegrable (fun θ => f (Real.cos θ)) volume 0 Real.pi)
    (hg : IntervalIntegrable (fun θ => g (Real.cos θ)) volume 0 Real.pi) (k : ℕ) :
    chebyshevCoeff (fun x => f x + g x) k = chebyshevCoeff f k + chebyshevCoeff g k := by
  have hc : ContinuousOn (fun θ : ℝ => (Real.cos ((k : ℝ) * θ) : 𝕜))
      (Set.uIcc 0 Real.pi) := by fun_prop
  simp only [chebyshevCoeff, add_mul]
  rw [intervalIntegral.integral_add (hf.mul_continuousOn hc) (hg.mul_continuousOn hc), mul_add]

/-- Coefficients commute with multiplication by a scalar, without integrability assumptions. -/
theorem chebyshevCoeff_const_mul (c : 𝕜) (f : ℝ → 𝕜) (k : ℕ) :
    chebyshevCoeff (fun x => c * f x) k = c * chebyshevCoeff f k := by
  simp only [chebyshevCoeff, mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, mul_comm _ c, mul_assoc]

private lemma eval_T_ofReal (j : ℕ) (x : ℝ) :
    (T 𝕜 (j : ℤ)).eval (x : 𝕜) = algebraMap ℝ 𝕜 ((T ℝ (j : ℤ)).eval x) := by
  rw [← map_T (algebraMap ℝ 𝕜), eval_map_apply]

private lemma integral_cos_mul_cos (j k : ℕ) :
    (∫ θ in 0..Real.pi, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
      if j = k then (if k = 0 then Real.pi else Real.pi / 2) else 0 := by
  have h := integral_measureT_eq_integral_cos
    (f := fun x => (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x)
  simp only [T_real_cos, Int.cast_natCast] at h
  rw [← h]
  split_ifs with hjk hk
  · subst j
    subst k
    exact integral_eval_T_real_mul_self_measureT_zero
  · subst j
    exact integral_T_real_mul_self_measureT_of_ne_zero hk
  · exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hjk

/-- The coefficient of $T_j$ at index $k$ is one for $j=k$ and zero otherwise.
[Trefethen2019, Exercise 3.7]; [GolubMeurant2010, §2.5.1]. The generic scalar form follows by
transporting Mathlib's real orthogonality through the real-to-RCLike integral map. -/
theorem chebyshevCoeff_eval_T (j k : ℕ) :
    chebyshevCoeff (fun x : ℝ => (Polynomial.Chebyshev.T 𝕜 (j : ℤ)).eval (x : 𝕜)) k =
      if j = k then 1 else 0 := by
  unfold chebyshevCoeff
  simp_rw [eval_T_ofReal, T_real_cos, Int.cast_natCast, ← RCLike.ofReal_mul]
  rw [RCLike.intervalIntegral_ofReal, integral_cos_mul_cos]
  split_ifs <;> simp [Real.pi_ne_zero]

/-- Canonical coefficients of a finite Chebyshev expansion are its basis coordinates.
This finite-linearity consequence of [Trefethen2019, Exercise 3.7] extends the basis
orthogonality to RCLike coefficients. Polynomial continuity supplies the integrability
hypotheses. -/
theorem chebyshevCoeff_sum_smul_T (c : ℕ → 𝕜) (s : Finset ℕ) (k : ℕ) :
    chebyshevCoeff (fun x : ℝ =>
      (∑ j ∈ s, c j • Polynomial.Chebyshev.T 𝕜 (j : ℤ)).eval (x : 𝕜)) k =
      ∑ j ∈ s, c j * (if j = k then 1 else 0) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, eval_zero, chebyshevCoeff_zero]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj, eval_add, eval_smul, smul_eq_mul]
    rw [chebyshevCoeff_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), chebyshevCoeff_const_mul,
      chebyshevCoeff_eval_T]
    simpa only [eval_finsetSum, eval_smul, smul_eq_mul] using congrArg
      (fun z => c j * (if j = k then 1 else 0) + z) ih

/-- A uniform bound $\|f(x)\|\le M$ on $[-1,1]$ bounds the zeroth full coefficient by $M$.
No continuity or integrability assumption is required for this total Bochner-integral bound.
This extends the zeroth-coefficient estimate of [Trefethen2019, Theorem 8.1] beyond analytic
functions, directly from its cosine integral. -/
theorem norm_chebyshevCoeff_zero_le {f : ℝ → 𝕜} {M : ℝ}
    (hM : Metric.IsUniformApproxOn f (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) :
    ‖chebyshevCoeff f 0‖ ≤ M := by
  have hi : ‖∫ θ in 0..Real.pi, f (Real.cos θ)‖ ≤ M * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := Real.pi) (f := fun θ => f (Real.cos θ)) (C := M)
      (fun θ _ => by
        simpa only [dist_zero_right] using
          hM.apply (show Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 from
            ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩))
    simpa only [sub_zero, abs_of_pos Real.pi_pos] using h
  simp only [chebyshevCoeff, ↓reduceIte, Nat.cast_zero, zero_mul, Real.cos_zero,
    RCLike.ofReal_one, mul_one, norm_mul, RCLike.norm_ofReal,
    abs_of_pos (div_pos zero_lt_one Real.pi_pos)]
  calc
    (1 / Real.pi) * ‖∫ θ in 0..Real.pi, f (Real.cos θ)‖ ≤
        (1 / Real.pi) * (M * Real.pi) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = M := by field_simp

/-- **Chebyshev coefficients of a bounded function**: a uniform bound $\|f(x)\| \le M$ on
$[-1, 1]$ bounds every full coefficient by $2M$ ($\lvert\cos(k\theta)\rvert \le 1$ in the cosine
integral); no continuity or integrability assumption is required. [Trefethen2019, Theorem 3.1],
the cosine integral it is read from. -/
theorem norm_chebyshevCoeff_le {f : ℝ → 𝕜} {M : ℝ}
    (hM : Metric.IsUniformApproxOn f (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) (k : ℕ) :
    ‖chebyshevCoeff f k‖ ≤ 2 * M := by
  have hM0 : 0 ≤ M := hM.nonneg ⟨0, by norm_num⟩
  have hi : ‖∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)‖ ≤
      M * Real.pi := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := Real.pi) (f := fun θ => f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜))
      (C := M) (fun θ _ => by
        have h1 : ‖f (Real.cos θ)‖ ≤ M := by
          simpa only [dist_zero_right] using
            hM.apply (show Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 from
              ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
        rw [norm_mul, RCLike.norm_ofReal]
        calc ‖f (Real.cos θ)‖ * |Real.cos ((k : ℝ) * θ)| ≤ M * 1 :=
              mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) hM0
          _ = M := mul_one M)
    simpa only [sub_zero, abs_of_pos Real.pi_pos] using h
  have hc : |(if k = 0 then 1 else 2 : ℝ) / Real.pi| ≤ 2 / Real.pi := by
    rw [abs_div, abs_of_pos Real.pi_pos]
    gcongr
    split_ifs <;> norm_num
  simp only [chebyshevCoeff, norm_mul, RCLike.norm_ofReal]
  calc |(if k = 0 then 1 else 2 : ℝ) / Real.pi| *
        ‖∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)‖ ≤
        2 / Real.pi * (M * Real.pi) := mul_le_mul hc hi (norm_nonneg _) (by positivity)
    _ = 2 * M := by field_simp

/-- The canonical Chebyshev coefficient commutes with the existing RCLike embedding into
$\mathbb C$. The identity is unconditional, including nonintegrable weighted integrands,
by Mathlib's interval-integral commutation for linear isometries. -/
theorem toComplex_chebyshevCoeff (f : ℝ → 𝕜) (k : ℕ) :
    RCLike.toComplex (chebyshevCoeff f k) =
      chebyshevCoeff (fun x => RCLike.toComplex (f x)) k := by
  let L : 𝕜 →ₗᵢ[ℝ] ℂ :=
    { RCLike.toComplex.toAlgHom.toLinearMap with
      norm_map' := RCLike.norm_toComplex }
  have hi := L.intervalIntegral_comp_comm
    (fun θ => f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜))
    (a := 0) (b := Real.pi) (μ := volume)
  change (∫ θ in 0..Real.pi,
      RCLike.toComplex (f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜))) =
    RCLike.toComplex (∫ θ in 0..Real.pi,
      f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)) at hi
  simp only [map_mul, RCLike.toComplex_ofReal] at hi
  simp only [chebyshevCoeff, map_mul, RCLike.toComplex_ofReal]
  exact congrArg (fun z : ℂ => (((if k = 0 then 1 else 2) / Real.pi : ℝ) : ℂ) * z) hi.symm

end NLAlib
