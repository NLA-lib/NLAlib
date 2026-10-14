/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TracePowers
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.GaussianIntegrationByParts
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.MatrixIntegral

/-!
# Trace moments of matrix series and the noncommutative Khintchine inequality

For a matrix series `Y = ∑ i, g i • A i` with real coefficients `g` and Hermitian `A i`, the even
trace moments satisfy `E tr Y^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p` when `g` is a standard Gaussian
vector or a vector of independent random signs: the noncommutative Khintchine inequality in trace
form. Both follow from one law-free step, which closes the moment recursion
`E tr Y^{2q+2} ≤ (2q + 1) E tr (V Y^{2q})` by trace Young; the two laws enter only through their
recursions, by Stein's identity coordinate by coordinate (Gaussian) or by flipping one sign at a
time (Rademacher). The second moment `E Y² = ∑ A i²` holds for any isotropic coefficient vector,
with no Hermitian hypothesis.

The spectral-norm moments `E ‖Y‖^{2p} ≤ (2p - 1)^p d ‖∑ A i²‖^p` compose the headline with
`specNorm_pow_le_re_trace_pow` and `re_trace_pow_le_card_mul_specNorm_pow` and are not stated.

## Main results

* `NLAlib.IsIsotropic.integral_sum_smul_sq`: `E (∑ ε i • A i)² = ∑ A i²`.
* `NLAlib.integral_re_trace_pow_le_of_recursion`: the law-free absorption step.
* `NLAlib.integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector`,
  `NLAlib.integral_re_trace_sum_smul_pow_le_of_hasLaw_rademacherVector`: noncommutative
  Khintchine.

## References

* [L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, *Matrix concentration
  inequalities via the method of exchangeable pairs*][MackeyEtAl2014], §7.
* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
  {A : ι → Matrix n n 𝕜}

/-! ### The second moment -/

private theorem sum_smul_sq_eq (ε : ι → ℝ) (A : ι → Matrix n n 𝕜) :
    (∑ i, ε i • A i) ^ 2 = ∑ i, ∑ j, (ε i * ε j) • (A i * A j) := by
  rw [sq, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm]

omit [Fintype ι] in
private theorem IsIsotropic.integrable_smul_mul [DecidableEq ι] {ε : Ω → ι → ℝ}
    (hε : IsIsotropic ε μ) (A : ι → Matrix n n 𝕜) (i j : ι) :
    Integrable (fun ω => (ε ω i * ε ω j) • (A i * A j)) μ := by
  simpa only [star_trivial] using (hε.integrable_mul_star i j).smul_const (A i * A j)

/-- A matrix series with isotropic real coefficients has second moment `E [Y²] = ∑ A i²`. No
Hermitian hypothesis, no independence and no probability measure: isotropy is all that is used.
[Tropp2015, chapter 4] (there for Gaussian and Rademacher coefficients). -/
theorem IsIsotropic.integral_sum_smul_sq [DecidableEq ι] {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : ∫ ω, (∑ i, ε ω i • A i) ^ 2 ∂μ = ∑ i, A i ^ 2 := by
  simp only [sum_smul_sq_eq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    hε.integrable_smul_mul A i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hε.integrable_smul_mul A i j]
  have h : ∀ j, ∫ ω, ε ω i * ε ω j ∂μ = if i = j then 1 else 0 := fun j => by
    simpa only [star_trivial] using hε.integral_mul_star i j
  simp only [integral_smul_const, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sq]

/-- The square of a matrix series with isotropic real coefficients is integrable, so
`IsIsotropic.integral_sum_smul_sq` is not between junk values. -/
theorem IsIsotropic.integrable_sum_smul_sq [DecidableEq ι] {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : Integrable (fun ω => (∑ i, ε ω i • A i) ^ 2) μ := by
  simp only [sum_smul_sq_eq]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    hε.integrable_smul_mul A i j

/-! ### The law-free step -/

/-- **The moment recursion closes.** If `E tr Y^{2q+2} ≤ (2q + 1) E tr (V Y^{2q})` for an almost
surely Hermitian `Y` and a positive semidefinite `V`, then
`E tr Y^{2q+2} ≤ (2q + 1)^{q+1} tr V^{q+1}`. Law-free: the Gaussian and Rademacher series satisfy
the recursion with `V = ∑ A i²`, and any other law with the recursion (exchangeable pairs) gets
the bound. [MackeyEtAl2014, Theorem 7.1] (the absorption step of its proof).
No integrability hypothesis is needed, by a case split: if `tr (V Y^{2q})` is not integrable its
integral is `0`, so `hrec` makes the left side at most `0`; if `tr Y^{2q+2}` is not integrable the
left side is `0`; in both cases the right side is nonnegative
(`Matrix.PosSemidef.re_trace_pow_nonneg`). Otherwise integrate trace Young
(`re_trace_mul_pow_le_add`),
`(q + 1)(2q + 1) tr (V Y^{2q}) ≤ (2q + 1)^{q+1} tr V^{q+1} + q tr Y^{2q+2}`, and combine with
`hrec`. -/
theorem integral_re_trace_pow_le_of_recursion [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {V : Matrix n n 𝕜} (hV : V.PosSemidef) (q : ℕ)
    (hrec : ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (V * Y ω ^ (2 * q)).trace ∂μ) :
    ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace := by
  have hR : 0 ≤ (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace :=
    mul_nonneg (by positivity) (hV.re_trace_pow_nonneg _)
  by_cases hM : Integrable (fun ω => RCLike.re (Y ω ^ (2 * q + 2)).trace) μ
  swap
  · rw [integral_undef hM]
    exact hR
  by_cases hW : Integrable (fun ω => RCLike.re (V * Y ω ^ (2 * q)).trace) μ
  swap
  · rw [integral_undef hW, mul_zero] at hrec
    linarith
  have hpoint : ∀ᵐ ω ∂μ, (q + 1 : ℝ) * (2 * q + 1) * RCLike.re (V * Y ω ^ (2 * q)).trace ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace +
        q * RCLike.re (Y ω ^ (2 * q + 2)).trace :=
    hY.mono fun ω hω => re_trace_mul_pow_le_add hV hω q
  have hi := integral_mono_ae (hW.const_mul ((q + 1 : ℝ) * (2 * q + 1)))
    ((integrable_const _).add (hM.const_mul (q : ℝ))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (integrable_const _) (hM.const_mul _), integral_const,
    integral_const_mul, probReal_univ, one_smul] at hi
  have hmul := mul_le_mul_of_nonneg_left hrec (by positivity : (0 : ℝ) ≤ q + 1)
  nlinarith

/-! ### Growth of trace polynomials of a series -/

/-- The real part of the trace, as a real continuous linear functional. -/
private noncomputable def reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (RCLike.reLm.comp (Matrix.traceLinearMap n ℝ 𝕜))

omit [DecidableEq n] in
private theorem reTraceCLM_apply (M : Matrix n n 𝕜) :
    reTraceCLM M = RCLike.re M.trace := rfl

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_sum_smul (hA : ∀ i, (A i).IsHermitian) (x : ι → ℝ) :
    (∑ i, x i • A i).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.2 <| isSelfAdjoint_sum _ fun i _ =>
    Matrix.isHermitian_iff_isSelfAdjoint.1 ((hA i).smul (IsSelfAdjoint.all (x i)))

private theorem posSemidef_sum_sq (hA : ∀ i, (A i).IsHermitian) :
    (∑ i, A i ^ 2).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => by
    simpa only [sq, (hA i).eq] using Matrix.posSemidef_conjTranspose_mul_self (A i)

private theorem norm_sum_smul_le (A : ι → Matrix n n 𝕜) (x : ι → ℝ) :
    ‖∑ i, x i • A i‖ ≤ (∑ i, ‖A i‖) * ‖x‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)

/-- `‖Y^a‖ ≤ D^{m+1} (1 + ‖x‖)^m` for `a ≤ m`, with `D = ‖1‖ + ∑ ‖A i‖ + 1`. -/
private theorem norm_sum_smul_pow_le (A : ι → Matrix n n 𝕜) (x : ι → ℝ) {a m : ℕ}
    (ham : a ≤ m) :
    ‖(∑ i, x i • A i) ^ a‖ ≤
      (‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1) * (1 + ‖x‖) ^ m := by
  set D := ‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1 with hD
  have hS : 0 ≤ ∑ i, ‖A i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hD1 : 1 ≤ D := by linarith [norm_nonneg (1 : Matrix n n 𝕜)]
  have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hY : ‖∑ i, x i • A i‖ ≤ D * (1 + ‖x‖) := (norm_sum_smul_le A x).trans (by
    nlinarith [norm_nonneg (1 : Matrix n n 𝕜), norm_nonneg x])
  have key : ∀ a : ℕ, ‖(∑ i, x i • A i) ^ a‖ ≤ D ^ (a + 1) * (1 + ‖x‖) ^ a := by
    intro a
    induction a with
    | zero => simp only [pow_zero, zero_add, pow_one, mul_one]; linarith
    | succ a ih =>
      rw [pow_succ]
      calc ‖(∑ i, x i • A i) ^ a * ∑ i, x i • A i‖
          ≤ ‖(∑ i, x i • A i) ^ a‖ * ‖∑ i, x i • A i‖ := norm_mul_le _ _
        _ ≤ (D ^ (a + 1) * (1 + ‖x‖) ^ a) * (D * (1 + ‖x‖)) :=
          mul_le_mul ih hY (norm_nonneg _) (by positivity)
        _ = D ^ (a + 1 + 1) * (1 + ‖x‖) ^ (a + 1) := by ring
  refine (key a).trans ?_
  gcongr

/-- The growth of a trace product: `|tr (B Y^a C Y^b)| ≤ c ‖B‖ ‖C‖ D^{2m+2} (1 + ‖x‖)^{2m}` for
`a, b ≤ m`. -/
private theorem abs_re_trace_mul_sum_smul_pow_mul_le (A : ι → Matrix n n 𝕜)
    (B C : Matrix n n 𝕜) {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m) (x : ι → ℝ) :
    |RCLike.re (B * (∑ i, x i • A i) ^ a * C * (∑ i, x i • A i) ^ b).trace| ≤
      ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * ‖B‖ * ‖C‖ *
        ((‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1)) ^ 2 * (1 + ‖x‖) ^ (2 * m) := by
  set Y := ∑ i, x i • A i
  have h1 := norm_sum_smul_pow_le A x ha
  have h2 := norm_sum_smul_pow_le A x hb
  have ht : |RCLike.re (B * Y ^ a * C * Y ^ b).trace| ≤
      ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * ‖B * Y ^ a * C * Y ^ b‖ := by
    rw [← reTraceCLM_apply, ← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ _
  have hn : ‖B * Y ^ a * C * Y ^ b‖ ≤ ‖B‖ * ‖Y ^ a‖ * ‖C‖ * ‖Y ^ b‖ := by
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
    exact norm_mul_le _ _
  refine ht.trans ?_
  calc ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * ‖B * Y ^ a * C * Y ^ b‖
      ≤ ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * (‖B‖ * ‖Y ^ a‖ * ‖C‖ * ‖Y ^ b‖) := by gcongr
    _ ≤ ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * (‖B‖ *
          ((‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1) * (1 + ‖x‖) ^ m) * ‖C‖ *
          ((‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1) * (1 + ‖x‖) ^ m)) := by gcongr
    _ = _ := by ring

/-- Trace polynomials of a series grow polynomially. -/
private theorem exists_abs_re_trace_mul_sum_smul_pow_mul_le (A : ι → Matrix n n 𝕜)
    (B C : Matrix n n 𝕜) (a b : ℕ) : ∃ K : ℝ, ∀ x : ι → ℝ,
      |RCLike.re (B * (∑ i, x i • A i) ^ a * C * (∑ i, x i • A i) ^ b).trace| ≤
        K * (1 + ‖x‖) ^ (2 * (a + b)) :=
  ⟨_, abs_re_trace_mul_sum_smul_pow_mul_le A B C (m := a + b) (by omega) (by omega)⟩

private theorem continuous_re_trace_mul_sum_smul_pow_mul (A : ι → Matrix n n 𝕜)
    (B C : Matrix n n 𝕜) (a b : ℕ) : Continuous fun x : ι → ℝ =>
      RCLike.re (B * (∑ i, x i • A i) ^ a * C * (∑ i, x i • A i) ^ b).trace := by
  simp only [← reTraceCLM_apply]
  exact reTraceCLM.continuous.comp (by fun_prop)

/-- The derivative of `x ↦ re tr (B Y(x)^m)`, by the noncommutative product rule. -/
private theorem hasFDerivAt_re_trace_mul_sum_smul_pow (A : ι → Matrix n n 𝕜)
    (B : Matrix n n 𝕜) (m : ℕ) (x : ι → ℝ) :
    ∃ f' : (ι → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun x : ι → ℝ => RCLike.re (B * (∑ i, x i • A i) ^ m).trace) f' x ∧
      ∀ v, f' v = ∑ l ∈ Finset.range m, RCLike.re (B * (∑ i, x i • A i) ^ (m.pred - l) *
        (∑ i, v i • A i) * (∑ i, x i • A i) ^ l).trace := by
  let _ : NormedAlgebra ℝ (Matrix n n 𝕜) := ⟨fun c A => by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])⟩
  let L : (ι → ℝ) →L[ℝ] Matrix n n 𝕜 := ∑ i, (ContinuousLinearMap.proj i).smulRight (A i)
  have hL : ∀ x, L x = ∑ i, x i • A i := fun x => by simp [L]
  have h := ((L.hasFDerivAt (x := x)).pow' m).const_mul B
  refine ⟨_, (reTraceCLM.hasFDerivAt.comp x h).congr_of_eventuallyEq ?_, fun v => ?_⟩
  · exact Filter.Eventually.of_forall fun y => by
      simp only [Function.comp, Pi.pow_apply, hL, reTraceCLM_apply]
  · simp [hL, reTraceCLM_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, Matrix.trace_smul,
      RCLike.smul_re]

private theorem contDiff_re_trace_mul_sum_smul_pow (A : ι → Matrix n n 𝕜)
    (B : Matrix n n 𝕜) (m : ℕ) :
    ContDiff ℝ 1 (fun x : ι → ℝ => RCLike.re (B * (∑ i, x i • A i) ^ m).trace) := by
  let _ : NormedAlgebra ℝ (Matrix n n 𝕜) := ⟨fun c A => by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])⟩
  let L : (ι → ℝ) →L[ℝ] Matrix n n 𝕜 := ∑ i, (ContinuousLinearMap.proj i).smulRight (A i)
  have hL : ∀ x, L x = ∑ i, x i • A i := fun x => by simp [L]
  have h : ContDiff ℝ 1 (fun x => reTraceCLM (B * L x ^ m)) :=
    reTraceCLM.contDiff.comp (contDiff_const.mul (L.contDiff.pow m))
  simpa only [hL, reTraceCLM_apply] using h

/-- The derivative of `x ↦ re tr (B Y(x)^m)` grows polynomially. -/
private theorem exists_norm_fderiv_re_trace_mul_sum_smul_pow_le (A : ι → Matrix n n 𝕜)
    (B : Matrix n n 𝕜) (m : ℕ) : ∃ K : ℝ, ∀ x : ι → ℝ,
      ‖fderiv ℝ (fun x : ι → ℝ => RCLike.re (B * (∑ i, x i • A i) ^ m).trace) x‖ ≤
        K * (1 + ‖x‖) ^ (2 * m) := by
  refine ⟨m * (‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * ‖B‖ * (∑ i, ‖A i‖) *
    ((‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1)) ^ 2), fun x => ?_⟩
  obtain ⟨f', hf', hv⟩ := hasFDerivAt_re_trace_mul_sum_smul_pow A B m x
  rw [hf'.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [hv, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l ∈ Finset.range m, |RCLike.re (B * (∑ i, x i • A i) ^ (m.pred - l) *
        (∑ i, v i • A i) * (∑ i, x i • A i) ^ l).trace|
      ≤ ∑ _l ∈ Finset.range m, ‖(reTraceCLM : Matrix n n 𝕜 →L[ℝ] ℝ)‖ * ‖B‖ *
          ((∑ i, ‖A i‖) * ‖v‖) * ((‖(1 : Matrix n n 𝕜)‖ + ∑ i, ‖A i‖ + 1) ^ (m + 1)) ^ 2 *
          (1 + ‖x‖) ^ (2 * m) := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        refine (abs_re_trace_mul_sum_smul_pow_mul_le A B _ (m := m)
          ((Nat.sub_le _ _).trans (Nat.pred_le _)) hl.le x).trans ?_
        gcongr
        exact norm_sum_smul_le A v
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- `tr Y^{2q+2} = ∑ i, x i tr (A i Y^{2q+1})`. -/
private theorem re_trace_sum_smul_pow_succ (A : ι → Matrix n n 𝕜) (x : ι → ℝ) (r : ℕ) :
    RCLike.re ((∑ i, x i • A i) ^ (r + 1)).trace =
      ∑ i, x i * RCLike.re (A i * (∑ i, x i • A i) ^ r).trace := by
  rw [pow_succ', Finset.sum_mul, Matrix.trace_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, RCLike.smul_re]

/-- The moment recursion, coordinate by coordinate. -/
private theorem integral_re_trace_sum_smul_pow_le_of_forall {X : Ω → ι → ℝ} (q : ℕ)
    (h1 : ∀ i, Integrable (fun ω =>
      X ω i * RCLike.re (A i * (∑ j, X ω j • A j) ^ (2 * q + 1)).trace) μ)
    (h2 : ∀ i, Integrable (fun ω => RCLike.re (A i ^ 2 * (∑ j, X ω j • A j) ^ (2 * q)).trace) μ)
    (h : ∀ i, ∫ ω, X ω i * RCLike.re (A i * (∑ j, X ω j • A j) ^ (2 * q + 1)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (A i ^ 2 * (∑ j, X ω j • A j) ^ (2 * q)).trace ∂μ) :
    ∫ ω, RCLike.re ((∑ i, X ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, X ω i • A i) ^ (2 * q)).trace ∂μ := by
  simp only [re_trace_sum_smul_pow_succ, Finset.sum_mul, Matrix.trace_sum, map_sum]
  rw [integral_finsetSum _ fun i _ => h1 i, integral_finsetSum _ fun i _ => h2 i,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h i

/-! ### Gaussian series -/

/-- A continuous function of polynomial growth of a Gaussian vector is integrable. -/
private theorem integrable_comp_of_hasGaussianLaw {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ)
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) {K : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ K * (1 + ‖x‖) ^ k) : Integrable (fun ω => F (X ω)) μ := by
  have hP := hX.isProbabilityMeasure
  exact Integrable.mono'
    ((integrable_one_add_norm_pow_of_memLp (fun p hp => hX.memLp hp) k).const_mul K)
    (hF.comp_aestronglyMeasurable hX.aemeasurable.aestronglyMeasurable)
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb (X ω))

/-- A coordinate times a function of polynomial growth has polynomial growth. -/
private theorem abs_apply_mul_le {F : (ι → ℝ) → ℝ} {K : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ K * (1 + ‖x‖) ^ k) (i : ι) (x : ι → ℝ) :
    |x i * F x| ≤ K * (1 + ‖x‖) ^ (k + 1) := by
  have hi : |x i| ≤ 1 + ‖x‖ := by
    have := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at this
    linarith [norm_nonneg x]
  rw [abs_mul, pow_succ]
  calc |x i| * |F x| ≤ (1 + ‖x‖) * (K * (1 + ‖x‖) ^ k) :=
        mul_le_mul hi (hb x) (abs_nonneg _) (by linarith [norm_nonneg x])
    _ = _ := by ring

/-- The polynomial trace moments of a Gaussian matrix series are integrable. Proof: Gaussian
moments of every order (`HasGaussianLaw.memLp`). -/
theorem integrable_re_trace_sum_smul_pow_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, g ω i • A i) ^ r).trace) μ := by
  obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A 1 1 r 0
  simp only [one_mul, mul_one, pow_zero] at hK
  have hc := continuous_re_trace_mul_sum_smul_pow_mul A 1 1 r 0
  simp only [one_mul, mul_one, pow_zero] at hc
  exact integrable_comp_of_hasGaussianLaw hg.hasGaussianLaw hc hK

/-- The Gaussian recursion in one coordinate, by Stein's identity. -/
private theorem integral_mul_re_trace_le_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) (i : ι) :
    ∫ ω, g ω i * RCLike.re (A i * (∑ j, g ω j • A j) ^ (2 * q + 1)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (A i ^ 2 * (∑ j, g ω j • A j) ^ (2 * q)).trace ∂μ := by
  classical
  have hG : HasGaussianLaw g μ := hg.hasGaussianLaw
  have hP := hG.isProbabilityMeasure
  set f : (ι → ℝ) → ℝ := fun x => RCLike.re (A i * (∑ j, x j • A j) ^ (2 * q + 1)).trace
    with hf_def
  have hf : ContDiff ℝ 1 f := contDiff_re_trace_mul_sum_smul_pow A (A i) _
  obtain ⟨C, hC⟩ := exists_norm_fderiv_re_trace_mul_sum_smul_pow_le A (A i) (2 * q + 1)
  have hstein :=
    integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow
      hG hf hC i
  have hmean : ∀ j, ∫ ω, g ω j ∂μ = 0 := fun j => integral_of_hasLaw_gaussianReal (hg.eval j)
  have hcov : ∀ j, covariance (fun ω => g ω i) (fun ω => g ω j) μ = if i = j then 1 else 0 := by
    intro j
    have h := (isIsotropic_of_hasLaw_gaussianVector hg).integral_mul_star i j
    simp only [star_trivial] at h
    rw [covariance, hmean i, hmean j]
    simpa only [sub_zero] using h
  simp only [hmean, sub_zero, hcov, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at hstein
  rw [hstein]
  have hfd : ∀ x, fderiv ℝ f x (Pi.single i 1) = ∑ l ∈ Finset.range (2 * q + 1),
      RCLike.re (A i * (∑ j, x j • A j) ^ (2 * q - l) * A i * (∑ j, x j • A j) ^ l).trace := by
    intro x
    obtain ⟨f', hf', hv⟩ := hasFDerivAt_re_trace_mul_sum_smul_pow A (A i) (2 * q + 1) x
    rw [hf'.fderiv, hv]
    simp [Pi.single_apply]
  have hpt : ∀ x, fderiv ℝ f x (Pi.single i 1) ≤
      (2 * q + 1 : ℝ) * RCLike.re (A i ^ 2 * (∑ j, x j • A j) ^ (2 * q)).trace := by
    intro x
    rw [hfd]
    calc ∑ l ∈ Finset.range (2 * q + 1),
          RCLike.re (A i * (∑ j, x j • A j) ^ (2 * q - l) * A i * (∑ j, x j • A j) ^ l).trace
        ≤ ∑ _l ∈ Finset.range (2 * q + 1),
          RCLike.re (A i ^ 2 * (∑ j, x j • A j) ^ (2 * q)).trace := by
          refine Finset.sum_le_sum fun l hl => ?_
          rw [Finset.mem_range] at hl
          have hl' : 2 * q - l + l = 2 * q := by omega
          have h := re_trace_mul_pow_mul_pow_le (hA i) (isHermitian_sum_smul hA x)
            (l := 2 * q - l) (k := l) (by rw [hl']; exact even_two_mul q)
          rwa [hl'] at h
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- integrability of both sides
  have hdc : Continuous fun x => fderiv ℝ f x (Pi.single i 1) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdi : Integrable (fun ω => fderiv ℝ f (g ω) (Pi.single i 1)) μ :=
    integrable_comp_of_hasGaussianLaw hG hdc (K := C * ‖(Pi.single i 1 : ι → ℝ)‖)
      (k := 2 * (2 * q + 1)) fun x => by
        rw [← Real.norm_eq_abs]
        refine ((fderiv ℝ f x).le_opNorm _).trans ?_
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i ^ 2) 1 (2 * q) 0
  simp only [mul_one, pow_zero] at hK
  have hc := continuous_re_trace_mul_sum_smul_pow_mul A (A i ^ 2) 1 (2 * q) 0
  simp only [mul_one, pow_zero] at hc
  have hgi := integrable_comp_of_hasGaussianLaw hG hc hK
  rw [← integral_const_mul]
  exact integral_mono hdi (hgi.const_mul _) fun ω => hpt (g ω)

/-- **The Gaussian moment recursion**: for a standard Gaussian vector `g` and Hermitian `A i`,
`E tr Y^{2q+2} ≤ (2q + 1) E tr ((∑ A i²) Y^{2q})` with `Y = ∑ g i • A i`.
[MackeyEtAl2014, Theorem 7.1] (there by exchangeable pairs). Proof:
`tr Y^{2q+2} = ∑ i, g i tr (A i Y^{2q+1})`; Stein's identity for derivatives of polynomial growth
(`integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow`)
in each coordinate gives `∑_{l ≤ 2q} E tr (A i Y^l A i Y^{2q-l})`, each term at most
`E tr (A i² Y^{2q})` (`re_trace_mul_pow_mul_pow_le`). -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, g ω i • A i) ^ (2 * q)).trace ∂μ := by
  have hG : HasGaussianLaw g μ := hg.hasGaussianLaw
  refine integral_re_trace_sum_smul_pow_le_of_forall q (fun i => ?_) (fun i => ?_)
    (integral_mul_re_trace_le_of_hasLaw_gaussianVector hg hA q)
  · obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i) 1 (2 * q + 1) 0
    simp only [mul_one, pow_zero] at hK
    have hc := continuous_re_trace_mul_sum_smul_pow_mul A (A i) 1 (2 * q + 1) 0
    simp only [mul_one, pow_zero] at hc
    exact integrable_comp_of_hasGaussianLaw hG ((continuous_apply i).mul hc)
      (abs_apply_mul_le hK i)
  · obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i ^ 2) 1 (2 * q) 0
    simp only [mul_one, pow_zero] at hK
    have hc := continuous_re_trace_mul_sum_smul_pow_mul A (A i ^ 2) 1 (2 * q) 0
    simp only [mul_one, pow_zero] at hc
    exact integrable_comp_of_hasGaussianLaw hG hc hK

/-- The headline from the recursion: `p = 0` directly, `p = q + 1` by the law-free step. -/
private theorem integral_re_trace_sum_smul_pow_le_of_recursion [IsProbabilityMeasure μ]
    {X : Ω → ι → ℝ} (hA : ∀ i, (A i).IsHermitian)
    (hrec : ∀ q : ℕ, ∫ ω, RCLike.re ((∑ i, X ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, X ω i • A i) ^ (2 * q)).trace ∂μ) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, X ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace := by
  rcases p with _ | q
  · simp
  · have h := integral_re_trace_pow_le_of_recursion
      (Y := fun ω => ∑ i, X ω i • A i) (ae_of_all _ fun ω => isHermitian_sum_smul hA (X ω))
      (posSemidef_sum_sq hA) q (hrec q)
    have e1 : 2 * (q + 1) = 2 * q + 2 := by ring
    have e2 : (2 * ((q + 1 : ℕ) : ℝ) - 1) = 2 * q + 1 := by push_cast; ring
    rw [e1, e2]
    exact h

/-- **Noncommutative Khintchine inequality**, Gaussian series: for a standard Gaussian vector `g`
and Hermitian `A i`, `E tr (∑ g i • A i)^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p`.
[MackeyEtAl2014, Theorem 7.1]; [Tropp2015, chapter 4]; here over any `RCLike` field and any
finite index types, every `p` (at `p = 0` both sides are `card n`). Buchholz's `(2p - 1)!!` is a
sharper constant of another shape, not stated.
Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace := by
  have hP := hg.isProbabilityMeasure
  exact integral_re_trace_sum_smul_pow_le_of_recursion hA
    (integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_gaussianVector hg hA) p

/-! ### Rademacher series -/

/-- A continuous function of polynomial growth of a vector of random signs is integrable. -/
private theorem integrable_comp_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) {F : (ι → ℝ) → ℝ} (hF : Continuous F) {K : ℝ}
    {k : ℕ} (hb : ∀ x, |F x| ≤ K * (1 + ‖x‖) ^ k) : Integrable (fun ω => F (ε ω)) μ := by
  have hP := hε.isProbabilityMeasure
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hb 0)
  refine Integrable.mono' (integrable_const (K * 2 ^ k))
    (hF.comp_aestronglyMeasurable hε.aemeasurable.aestronglyMeasurable) ?_
  filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hε] with ω hω
  have hn : ‖ε ω‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by nlinarith [hω i], by nlinarith [hω i]⟩
  rw [Real.norm_eq_abs]
  refine (hb _).trans ?_
  gcongr
  linarith

/-- The polynomial trace moments of a Rademacher matrix series are integrable. Proof: the
coordinates are almost surely bounded. -/
theorem integrable_re_trace_sum_smul_pow_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, ε ω i • A i) ^ r).trace) μ := by
  obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A 1 1 r 0
  simp only [one_mul, mul_one, pow_zero] at hK
  have hc := continuous_re_trace_mul_sum_smul_pow_mul A 1 1 r 0
  simp only [one_mul, mul_one, pow_zero] at hc
  exact integrable_comp_of_hasLaw_rademacherVector hε hc hK

/-- The deterministic sign-flip inequality: with `y` the vector `x` with its `i`-th sign flipped
and `x i² = 1`, `x i tr (A i Y(x)^{2q+1}) + y i tr (A i Y(y)^{2q+1})` is at most
`(2q + 1) (tr (A i² Y(x)^{2q}) + tr (A i² Y(y)^{2q}))`, by the mean value trace inequality. -/
private theorem sign_flip_le [DecidableEq ι] (hA : ∀ i, (A i).IsHermitian) (q : ℕ) (i : ι)
    (x : ι → ℝ) (hx : x i ^ 2 = 1) :
    x i * RCLike.re (A i * (∑ j, x j • A j) ^ (2 * q + 1)).trace +
      Function.update x i (-x i) i * RCLike.re (A i *
        (∑ j, Function.update x i (-x i) j • A j) ^ (2 * q + 1)).trace ≤
      (2 * q + 1 : ℝ) * (RCLike.re (A i ^ 2 * (∑ j, x j • A j) ^ (2 * q)).trace +
        RCLike.re (A i ^ 2 * (∑ j, Function.update x i (-x i) j • A j) ^ (2 * q)).trace) := by
  set y := Function.update x i (-x i) with hy
  have hyi : y i = -x i := Function.update_self _ _ _
  have hD : ∑ j, x j • A j - ∑ j, y j • A j = (2 * x i) • A i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hy, Function.update_of_ne hj])
      (by simp), hyi]
    congr 1
    ring
  have hmean := re_trace_sub_mul_pow_sub_pow_le (isHermitian_sum_smul hA x)
    (isHermitian_sum_smul hA y) (even_two_mul q)
  rw [hD] at hmean
  have hsq : ((2 * x i) • A i) ^ 2 = (4 : ℝ) • A i ^ 2 := by
    rw [smul_pow, mul_pow, hx]
    norm_num
  rw [hsq] at hmean
  simp only [Matrix.smul_mul, mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, map_sub, map_add, RCLike.smul_re] at hmean
  rw [hyi]
  push_cast at hmean
  linarith

/-- The Rademacher recursion in one coordinate, by flipping its sign. -/
private theorem integral_mul_re_trace_le_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) (i : ι) :
    ∫ ω, ε ω i * RCLike.re (A i * (∑ j, ε ω j • A j) ^ (2 * q + 1)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (A i ^ 2 * (∑ j, ε ω j • A j) ^ (2 * q)).trace ∂μ := by
  classical
  set T : (ι → ℝ) → (ι → ℝ) := fun x => Function.update x i (-x i) with hT
  have hTε : HasLaw (fun ω => T (ε ω)) (rademacherVector ι) μ :=
    (measurePreserving_update_neg_rademacherVector i).fun_comp_hasLaw hε
  set F : (ι → ℝ) → ℝ := fun x => x i * RCLike.re (A i * (∑ j, x j • A j) ^ (2 * q + 1)).trace
    with hF
  set G : (ι → ℝ) → ℝ := fun x => RCLike.re (A i ^ 2 * (∑ j, x j • A j) ^ (2 * q)).trace
    with hG
  obtain ⟨KF, hKF⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i) 1 (2 * q + 1) 0
  simp only [mul_one, pow_zero] at hKF
  have hcF := continuous_re_trace_mul_sum_smul_pow_mul A (A i) 1 (2 * q + 1) 0
  simp only [mul_one, pow_zero] at hcF
  obtain ⟨KG, hKG⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i ^ 2) 1 (2 * q) 0
  simp only [mul_one, pow_zero] at hKG
  have hGc := continuous_re_trace_mul_sum_smul_pow_mul A (A i ^ 2) 1 (2 * q) 0
  simp only [mul_one, pow_zero] at hGc
  have hFc : Continuous F := (continuous_apply i).mul hcF
  have hbF := abs_apply_mul_le hKF i
  have hFi := integrable_comp_of_hasLaw_rademacherVector hε hFc hbF
  have hFTi := integrable_comp_of_hasLaw_rademacherVector hTε hFc hbF
  have hGi := integrable_comp_of_hasLaw_rademacherVector hε hGc hKG
  have hGTi := integrable_comp_of_hasLaw_rademacherVector hTε hGc hKG
  have hFT : ∫ ω, F (T (ε ω)) ∂μ = ∫ ω, F (ε ω) ∂μ := by
    have h1 := hTε.integral_comp hFc.aestronglyMeasurable
    have h2 := hε.integral_comp hFc.aestronglyMeasurable
    simp only [Function.comp_def] at h1 h2
    rw [h1, h2]
  have hGT : ∫ ω, G (T (ε ω)) ∂μ = ∫ ω, G (ε ω) ∂μ := by
    have h1 := hTε.integral_comp hGc.aestronglyMeasurable
    have h2 := hε.integral_comp hGc.aestronglyMeasurable
    simp only [Function.comp_def] at h1 h2
    rw [h1, h2]
  have hpt : ∀ᵐ ω ∂μ, F (ε ω) + F (T (ε ω)) ≤ (2 * q + 1 : ℝ) * (G (ε ω) + G (T (ε ω))) := by
    filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hε] with ω hω
    exact sign_flip_le hA q i (ε ω) (hω i)
  have hi := integral_mono_ae (hFi.add hFTi) ((hGi.add hGTi).const_mul _) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add hFi hFTi, integral_const_mul, integral_add hGi hGTi, hFT, hGT] at hi
  change ∫ ω, F (ε ω) ∂μ ≤ (2 * q + 1 : ℝ) * ∫ ω, G (ε ω) ∂μ
  linarith

/-- **The Rademacher moment recursion**: for a vector `ε` of independent random signs and
Hermitian `A i`, `E tr Y^{2q+2} ≤ (2q + 1) E tr ((∑ A i²) Y^{2q})` with `Y = ∑ ε i • A i`.
[MackeyEtAl2014, Theorem 7.1] (there by exchangeable pairs). Proof: with `Y⁽ⁱ⁾` the series with
the `i`-th sign flipped (same law, `measurePreserving_update_neg_rademacherVector`),
`E [ε i tr (A i Y^{2q+1})] = ¼ E tr ((Y - Y⁽ⁱ⁾)(Y^{2q+1} - Y⁽ⁱ⁾^{2q+1}))`; the mean value trace
inequality (`re_trace_sub_mul_pow_sub_pow_le`) with `Y - Y⁽ⁱ⁾ = 2 ε i • A i` and `ε i² = 1`, and a
second flip. -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) *
        ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, ε ω i • A i) ^ (2 * q)).trace ∂μ := by
  refine integral_re_trace_sum_smul_pow_le_of_forall q (fun i => ?_) (fun i => ?_)
    (integral_mul_re_trace_le_of_hasLaw_rademacherVector hε hA q)
  · obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i) 1 (2 * q + 1) 0
    simp only [mul_one, pow_zero] at hK
    have hc := continuous_re_trace_mul_sum_smul_pow_mul A (A i) 1 (2 * q + 1) 0
    simp only [mul_one, pow_zero] at hc
    exact integrable_comp_of_hasLaw_rademacherVector hε ((continuous_apply i).mul hc)
      (abs_apply_mul_le hK i)
  · obtain ⟨K, hK⟩ := exists_abs_re_trace_mul_sum_smul_pow_mul_le A (A i ^ 2) 1 (2 * q) 0
    simp only [mul_one, pow_zero] at hK
    have hc := continuous_re_trace_mul_sum_smul_pow_mul A (A i ^ 2) 1 (2 * q) 0
    simp only [mul_one, pow_zero] at hc
    exact integrable_comp_of_hasLaw_rademacherVector hε hc hK

/-- **Noncommutative Khintchine inequality**, Rademacher series: for a vector `ε` of independent
random signs and Hermitian `A i`, `E tr (∑ ε i • A i)^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p`.
[MackeyEtAl2014, Theorem 7.1]; [Tropp2015, chapter 4]; here over any `RCLike` field and any
finite index types, every `p`.
Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace := by
  have hP := hε.isProbabilityMeasure
  exact integral_re_trace_sum_smul_pow_le_of_recursion hA
    (integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_rademacherVector hε hA) p

end NLAlib
