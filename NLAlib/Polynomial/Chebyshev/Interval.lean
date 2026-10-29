/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.ChebyshevTruncation
public import NLAlib.Polynomial.Chebyshev.EvenFilter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Chebyshev polynomials on an interval

The Chebyshev polynomials of the first kind pulled back to an interval $[\alpha, \beta]$,
$\hat T_i(x) = T_i\bigl((2x - \alpha - \beta)/(\beta - \alpha)\bigr)$: their degree, the bound
$\lvert\hat T_i\rvert \le 1$ and the Lipschitz constant $2i^2/(\beta - \alpha)$ on
$[\alpha, \beta]$, and the Chebyshev expansion of a polynomial bounded by $M$ on
$[\alpha, \beta]$ with coefficients at most $2M$, whence a Lipschitz constant for bounded
polynomials. These are the polynomial facts of the Druskin–Knizhnerman analysis of
finite-precision Lanczos (`NLAlibScaffold/Krylov/FinitePrecision/LanczosFunctions.lean`).

## Main results

* `NLAlib.chebyshevOn`: $\hat T_i$ on $[\alpha, \beta]$.
* `NLAlib.abs_eval_chebyshevOn_le_one`, `NLAlib.lipschitzOnWith_eval_chebyshevOn`: the bound
  and the Lipschitz constant on $[\alpha, \beta]$.
* `NLAlib.exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn`: the Chebyshev expansion of a
  bounded polynomial with bounded coefficients.
* `NLAlib.lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn`: the Lipschitz constant of a
  bounded polynomial.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-- The **Chebyshev polynomial of the first kind on $[\alpha, \beta]$**:
$\hat T_i(x) = T_i\bigl((2x - \alpha - \beta)/(\beta - \alpha)\bigr)$. -/
noncomputable def chebyshevOn (α β : ℝ) (i : ℕ) : ℝ[X] :=
  (Chebyshev.T ℝ (i : ℤ)).comp (C (2 / (β - α)) * X - C ((β + α) / (β - α)))

/-- The affine map onto $[-1, 1]$: for $\alpha < \beta$ and $x \in [\alpha, \beta]$,
$\lvert 2x/(\beta - \alpha) - (\beta + \alpha)/(\beta - \alpha)\rvert \le 1$. -/
theorem abs_div_mul_sub_div_le_one {α β : ℝ} (hαβ : α < β) {x : ℝ} (hx : x ∈ Set.Icc α β) :
    |2 / (β - α) * x - (β + α) / (β - α)| ≤ 1 := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  rw [show 2 / (β - α) * x - (β + α) / (β - α) = (2 * x - β - α) / (β - α) by
    field_simp; ring, abs_div, abs_of_pos hd, div_le_one hd, abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- $\hat T_i$ has degree at most $i$. -/
theorem degree_chebyshevOn_le (α β : ℝ) (i : ℕ) : (chebyshevOn α β i).degree ≤ i := by
  have hl : (C (2 / (β - α)) * X - C ((β + α) / (β - α))).natDegree ≤ 1 := by compute_degree
  have h := natDegree_comp_le (p := Chebyshev.T ℝ (i : ℤ))
    (q := C (2 / (β - α)) * X - C ((β + α) / (β - α)))
  rw [Chebyshev.natDegree_T, Int.natAbs_natCast] at h
  refine degree_le_natDegree.trans ?_
  exact_mod_cast h.trans (by nlinarith)

/-- $\lvert\hat T_i\rvert \le 1$ on $[\alpha, \beta]$. -/
theorem abs_eval_chebyshevOn_le_one {α β : ℝ} (hαβ : α < β) (i : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc α β) : |(chebyshevOn α β i).eval x| ≤ 1 := by
  simp only [chebyshevOn, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_div_mul_sub_div_le_one hαβ hx)

/-- $\hat T_i$ is $2i^2/(\beta - \alpha)$-Lipschitz on $[\alpha, \beta]$ (Markov's inequality for
Chebyshev polynomials: $\lvert T_i'\rvert \le T_i'(1) = i^2$ on $[-1, 1]$). -/
theorem lipschitzOnWith_eval_chebyshevOn {α β : ℝ} (hαβ : α < β) (i : ℕ) :
    LipschitzOnWith ‖2 * (i : ℝ) ^ 2 / (β - α)‖₊
      (fun x => (chebyshevOn α β i).eval x) (Set.Icc α β) := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  refine (convex_Icc α β).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (chebyshevOn α β i).differentiableAt) fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    Real.norm_of_nonneg (show 0 ≤ 2 * (i : ℝ) ^ 2 / (β - α) by positivity), Polynomial.deriv,
    chebyshevOn, derivative_comp, eval_mul, eval_comp]
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one,
    zero_add, sub_zero, eval_C, eval_sub, eval_mul, eval_X, Real.norm_eq_abs, abs_mul,
    abs_of_pos (div_pos two_pos hd)]
  have hT := Chebyshev.abs_iterate_derivative_T_real_le (i : ℤ) 1
    (abs_div_mul_sub_div_le_one hαβ hx)
  simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one, Int.cast_natCast] at hT
  rw [div_mul_eq_mul_div]
  gcongr

/-- **Chebyshev expansion of a polynomial on $[\alpha, \beta]$ with bounded coefficients**: a
real polynomial of degree at most $m$ bounded by $M$ on $[\alpha, \beta]$ is
$\sum_{i \le m} a_i\hat T_i$ with $\lvert a_0\rvert \le M$ and $\lvert a_i\rvert \le 2M$.
[Trefethen2019, Theorem 3.1]; the finite case of `NLAlib.chebyshevTrunc_eval`, scaled. -/
theorem exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn {α β : ℝ} (hαβ : α < β)
    {p : ℝ[X]} {m : ℕ} (hp : p.degree ≤ m) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    ∃ a : ℕ → ℝ, p = ∑ i ∈ Finset.range (m + 1), a i • chebyshevOn α β i ∧
      |a 0| ≤ M ∧ ∀ i, 1 ≤ i → |a i| ≤ 2 * M := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  set ℓ : ℝ[X] := C ((β - α) / 2) * X + C ((β + α) / 2) with hℓ
  set q := p.comp ℓ with hq
  have hqdeg : q.degree ≤ m := by
    have h := natDegree_comp_le (p := p) (q := ℓ)
    have hl : ℓ.natDegree ≤ 1 := by rw [hℓ]; compute_degree
    have hpm : p.natDegree ≤ m := natDegree_le_of_degree_le hp
    refine degree_le_natDegree.trans ?_
    exact_mod_cast h.trans (by nlinarith)
  have hqM : Metric.IsUniformApproxOn (fun t : ℝ => q.eval t) (fun _ => 0)
      (Set.Icc (-1 : ℝ) 1) M := fun t ht => by
    have hmem : (β - α) / 2 * t + (β + α) / 2 ∈ Set.Icc α β :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    simpa only [hq, eval_comp, hℓ, eval_add, eval_mul, eval_C, eval_X] using hM.apply hmem
  have h := chebyshevTrunc_eval (𝕜 := ℝ) hqdeg
  simp only [RCLike.ofReal_real_eq_id, id] at h
  refine ⟨fun i => chebyshevCoeff (fun t : ℝ => q.eval t) i, ?_, ?_, fun i _ => ?_⟩
  · refine Polynomial.funext fun x => ?_
    have hx := congrArg (eval (2 / (β - α) * x - (β + α) / (β - α))) h
    rw [eval_chebyshevTrunc] at hx
    have hinv : (β - α) / 2 * (2 / (β - α) * x - (β + α) / (β - α)) + (β + α) / 2 = x := by
      field_simp
      ring
    have hqx : q.eval (2 / (β - α) * x - (β + α) / (β - α)) = p.eval x := by
      rw [hq, eval_comp, hℓ]
      simp only [eval_add, eval_mul, eval_C, eval_X, hinv]
    rw [hqx] at hx
    rw [← hx, eval_finsetSum]
    simp only [eval_smul, smul_eq_mul, chebyshevOn, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
  · simpa only [Real.norm_eq_abs] using norm_chebyshevCoeff_zero_le hqM
  · simpa only [Real.norm_eq_abs] using norm_chebyshevCoeff_le hqM i

/-- $\sum_{i<n} i^2 \le n^3/3$. -/
private theorem sum_range_sq_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **Lipschitz constant of a bounded polynomial on an interval**, through its Chebyshev
expansion: a polynomial of degree at most $m$ bounded by $M$ on $[\alpha, \beta]$ is
$\tfrac43(m + 1)^3 M/(\beta - \alpha)$-Lipschitz there (unoptimised; Markov's inequality
gives $2m^2M/(\beta - \alpha)$). The expansion is [Trefethen2019, Theorem 3.1]; the
constant is composed here. -/
theorem lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn {α β : ℝ} (hαβ : α < β)
    {p : ℝ[X]} {m : ℕ} (hp : p.degree ≤ m) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    LipschitzOnWith ‖4 / 3 * (m + 1 : ℝ) ^ 3 * M / (β - α)‖₊
      (fun x => p.eval x) (Set.Icc α β) := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  have hM0 : 0 ≤ M := hM.nonneg ⟨α, le_rfl, hαβ.le⟩
  obtain ⟨a, hpa, ha0, ha⟩ := exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn hαβ hp hM
  have ha' : ∀ i, |a i| ≤ 2 * M := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · linarith
    · exact ha i hi
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [coe_nnnorm, Real.norm_of_nonneg (by positivity), hpa]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Real.dist_eq, ← Finset.sum_sub_distrib,
    ← mul_sub]
  calc |∑ i ∈ Finset.range (m + 1),
        a i * ((chebyshevOn α β i).eval x - (chebyshevOn α β i).eval y)|
      ≤ ∑ i ∈ Finset.range (m + 1), 2 * M * (2 * (i : ℝ) ^ 2 / (β - α) * |x - y|) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        have hL := (lipschitzOnWith_eval_chebyshevOn hαβ i).dist_le_mul x hx y hy
        rw [coe_nnnorm, Real.norm_of_nonneg (by positivity), Real.dist_eq, Real.dist_eq] at hL
        exact mul_le_mul (ha' i) hL (abs_nonneg _) (by positivity)
    _ = 4 * M * |x - y| / (β - α) * ∑ i ∈ Finset.range (m + 1), (i : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 4 * M * |x - y| / (β - α) * ((m + 1 : ℝ) ^ 3 / 3) := by
        gcongr
        exact_mod_cast sum_range_sq_le (m + 1)
    _ = 4 / 3 * (m + 1 : ℝ) ^ 3 * M / (β - α) * |x - y| := by ring

end NLAlib
