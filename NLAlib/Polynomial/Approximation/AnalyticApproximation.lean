/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.AnalyticCoefficients
public import NLAlib.Polynomial.Approximation.ChebyshevTruncation
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Geometric Chebyshev approximation on an open ellipse

The canonical degree-$N$ truncation has error $2M/(\rho^N(\rho-1))$ when a compatible complex
extension is holomorphic and bounded on the open Bernstein ellipse. Affine rescaling gives the
same error on any nondegenerate real interval. No boundary regularity is assumed.

## Main results

* `NLAlib.isUniformApproxOn_chebyshevTrunc_of_differentiableOn`: canonical uniform error.
* `NLAlib.exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn`: affine interval transport.
* `NLAlib.minimaxError_le_of_differentiableOn`: the Bernstein-ellipse bound on $E_N$.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev Real Set

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

private lemma continuous_restriction {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) :
    ContinuousOn f (Icc (-1 : ℝ) 1) := by
  have hF := hFd.continuousOn.comp Complex.continuous_ofReal.continuousOn
    (fun x hx => ofReal_mem_openBernsteinEllipse hρ hx)
  have hi : Isometry (RCLike.toComplex : 𝕜 → ℂ) :=
    AddMonoidHomClass.isometry_of_norm RCLike.toComplex RCLike.norm_toComplex
  exact hi.comp_continuousOn_iff.mp (hF.congr hExt)

private lemma summable_coefficients {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) :
    Summable (fun k : ℕ => ‖chebyshevCoeff f k‖) := by
  have hq : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans hρ))]
    exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ
  have hg : Summable (fun k : ℕ => 2 * M / ρ ^ k) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (summable_geometric_of_abs_lt_one hq).mul_left (2 * M)
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_nat_add_iff 1).mpr hg)
  intro k
  exact norm_chebyshevCoeff_le_of_differentiableOn hρ hFd hM hExt (Nat.succ_pos k)

private lemma norm_T_real_input_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖(T 𝕜 (k : ℤ)).eval (x : 𝕜)‖ ≤ 1 := by
  have h := eval_map_apply (p := T ℝ (k : ℤ)) (f := algebraMap ℝ 𝕜) x
  rw [map_T] at h
  have hn := congrArg norm h
  have hn' : ‖(T 𝕜 (k : ℤ)).eval (x : 𝕜)‖ = |(T ℝ (k : ℤ)).eval x| :=
    hn.trans (RCLike.norm_ofReal _)
  rw [hn']
  exact abs_eval_T_real_le_one _ (abs_le.mpr hx)

private lemma geometric_tail {ρ M : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    HasSum (fun i : ℕ => 2 * M / ρ ^ (i + (N + 1)))
      (2 * M / (ρ ^ N * (ρ - 1))) := by
  have hq : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans hρ))]
    exact (inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ
  have h := (hasSum_geometric_of_abs_lt_one hq).mul_left (2 * M * (ρ⁻¹) ^ (N + 1))
  convert h using 1 <;> try rfl
  · funext i
    rw [div_eq_mul_inv, ← inv_pow, pow_add]
    ring
  · rw [pow_succ]
    simp only [inv_pow]
    field_simp

/-- **Chebyshev truncation error for analytic functions.** With a compatible extension
holomorphic and bounded by $M$ on the OPEN Bernstein ellipse, the canonical degree-$N$
truncation satisfies
$$\|p_N(x)-f(x)\|\le\frac{2M}{\rho^N(\rho-1)}\quad(x\in[-1,1]).$$
[Trefethen2019, Theorem 8.2, Eq. (8.2)], generalized to RCLike values. Every $N\ge0$ and
$M=0$ are included. No continuous extension to the ellipse boundary is required.

Result: bernstein-ellipse-approx
-/
theorem isUniformApproxOn_chebyshevTrunc_of_differentiableOn
    {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    Metric.IsUniformApproxOn
      (fun x : ℝ => (chebyshevTrunc f N).eval (x : 𝕜)) f (Set.Icc (-1 : ℝ) 1)
      (2 * M / (ρ ^ N * (ρ - 1))) := by
  intro x hx
  let u : ℕ → 𝕜 := fun k => chebyshevCoeff f k * (T 𝕜 (k : ℤ)).eval (x : 𝕜)
  have hu : HasSum u (f x) := hasSum_chebyshevCoeff_mul_eval_T
    (continuous_restriction hρ hFd hExt) (summable_coefficients hρ hFd hM hExt) hx
  have hsplit := hu.summable.sum_add_tsum_nat_add (N + 1)
  rw [hu.tsum_eq] at hsplit
  have hp : (chebyshevTrunc f N).eval (x : 𝕜) = ∑ k ∈ Finset.range (N + 1), u k :=
    eval_chebyshevTrunc f N (x : 𝕜)
  have herr : f x - (chebyshevTrunc f N).eval (x : 𝕜) = ∑' i : ℕ, u (i + (N + 1)) := by
    rw [hp, ← hsplit]
    abel
  have ht : ∀ i : ℕ, ‖u (i + (N + 1))‖ ≤ 2 * M / ρ ^ (i + (N + 1)) := by
    intro i
    have hc := norm_chebyshevCoeff_le_of_differentiableOn hρ hFd hM hExt
      (k := i + (N + 1)) (by omega)
    exact (by
      dsimp [u]
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_T_real_input_le_one _ hx)).trans hc)
  rw [dist_eq_norm, norm_sub_rev, herr]
  exact tsum_of_norm_bounded (geometric_tail hρ N) ht

/-- **Polynomial approximation of analytic functions on an interval.** On $[a,b]$ with $a<b$,
a compatible extension of the affine pullback of $f$, holomorphic
and bounded by $M$ on the open Bernstein ellipse, gives a polynomial of degree at most $N$
with uniform error
$$\frac{2M}{\rho^N(\rho-1)}\,.$$
An affine-rescaling corollary of [Trefethen2019, Theorem 8.2], generalized to RCLike values.
The polynomial is obtained from the canonical truncation, including $N=0$.

Result: bernstein-ellipse-approx
-/
theorem exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn
    {f : ℝ → 𝕜} {F : ℂ → ℂ} {a b ρ M : ℝ} (hab : a < b) (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => RCLike.toComplex (f (((b - a) * t + b + a) / 2)))
      (fun t : ℝ => F (t : ℂ)) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    ∃ p : 𝕜[X], p.degree ≤ (N : WithBot ℕ) ∧
      Metric.IsUniformApproxOn (fun x : ℝ => p.eval (x : 𝕜)) f (Set.Icc a b)
        (2 * M / (ρ ^ N * (ρ - 1))) := by
  let g : ℝ → 𝕜 := fun t => f (((b - a) * t + b + a) / 2)
  let q := chebyshevTrunc g N
  let s : 𝕜[X] := C ((2 / (b - a) : ℝ) : 𝕜) * X - C (((b + a) / (b - a) : ℝ) : 𝕜)
  refine ⟨q.comp s, ?_, ?_⟩
  · refine degree_le_natDegree.trans ?_
    have hq := natDegree_le_of_degree_le (degree_chebyshevTrunc_le g N)
    have hs : s.natDegree ≤ 1 := by
      exact (natDegree_sub_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
          (by simp only [natDegree_C, zero_le]))
    have hn := natDegree_comp_le (p := q) (q := s)
    have h : (q.comp s).natDegree ≤ N := hn.trans ((Nat.mul_le_mul hq hs).trans_eq (mul_one N))
    exact_mod_cast h
  · intro x hx
    have hba : 0 < b - a := sub_pos.mpr hab
    let t := (2 * x - b - a) / (b - a)
    have ht : t ∈ Icc (-1 : ℝ) 1 := by
      dsimp [t]
      rw [Set.mem_Icc, le_div_iff₀ hba, div_le_iff₀ hba]
      constructor <;> linarith [hx.1, hx.2]
    have hi : ((b - a) * t + b + a) / 2 = x := by
      dsimp [t]
      field_simp
      ring
    have he : s.eval (x : 𝕜) = (t : 𝕜) := by
      simp only [s, eval_sub, eval_mul, eval_C, eval_X]
      dsimp [t]
      push_cast
      ring
    have h := (isUniformApproxOn_chebyshevTrunc_of_differentiableOn hρ hFd hM hExt N).apply ht
    change dist ((q.comp s).eval (x : 𝕜)) (f x) ≤ _
    rw [eval_comp, he]
    simpa only [g, hi] using h

/-- **Analytic functions and the minimax error.** On $[a, b]$, $a < b$, if the pullback
$t \mapsto f(((b - a)t + b + a)/2)$ of a real $f$ extends to a function holomorphic and bounded by
$M$ on the open Bernstein ellipse $E_\rho$, $\rho > 1$, then
$$E_N(f; [a, b]) \le \frac{2M}{\rho^N(\rho - 1)}\,.$$
[Trefethen2019, Theorem 8.2], there on $[-1, 1]$ for the Chebyshev
truncation.
Result: bernstein-ellipse-approx -/
theorem minimaxError_le_of_differentiableOn {f : ℝ → ℝ} {F : ℂ → ℂ} {a b ρ M : ℝ} (hab : a < b)
    (hρ : 1 < ρ) (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((b - a) * t + b + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    minimaxError f (Set.Icc a b) N ≤ 2 * M / (ρ ^ N * (ρ - 1)) := by
  obtain ⟨p, hdeg, hp⟩ := exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn (𝕜 := ℝ)
    (f := f) hab hρ hFd hM
    (fun t ht => by rw [← hExt ht]; exact RCLike.toComplex_ofReal (𝕜 := ℝ) _) N
  exact minimaxError_le_of_isUniformApproxOn hdeg (hp.nonneg (Set.nonempty_Icc.mpr hab.le)) hp

end NLAlib
