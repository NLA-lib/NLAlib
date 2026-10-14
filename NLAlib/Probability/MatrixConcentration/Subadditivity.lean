/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Convex.Integral
public import NLAlib.Matrix.Functions.Lieb
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.MatrixConcentration.Laplace

/-!
# Subadditivity of matrix cumulant generating functions

Lieb's concavity theorem in expectation: for a fixed Hermitian `H` and a random Hermitian `X`,
`E tr exp (H + X) ≤ tr exp (H + log E e^X)` (Tropp 2015, Corollary 3.4.2). For independent
random Hermitian matrices it gives the subadditivity of matrix cumulant generating functions,
`E tr exp (∑ X k) ≤ tr exp (∑ log E e^{X k})` (Tropp 2015, Lemma 3.5.1), the step from one summand
to a sum in every matrix concentration inequality.

## Main results

* `NLAlib.integral_re_trace_exp_add_le`: Lieb's theorem in expectation.
* `NLAlib.integral_re_trace_exp_sum_le`: subadditivity of matrix cumulant generating functions.
* `NLAlib.aemeasurable_of_integrable_exp`: an almost surely Hermitian random matrix with an
  integrable exponential is almost everywhere measurable.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.4, §3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Measurability -/

/-- An almost surely Hermitian random matrix with an integrable exponential is almost everywhere
measurable: `X = log (exp X)` almost surely, and the logarithm is continuous on the positive
definite matrices. -/
theorem aemeasurable_of_integrable_exp {X : Ω → Matrix n n 𝕜}
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ) :
    AEMeasurable X μ := by
  classical
  have hL : Measurable ({A : Matrix n n 𝕜 | A.PosDef}.piecewise (fun A => cfc Real.log A)
      fun _ => 0) :=
    continuousOn_cfc_log.measurable_piecewise continuousOn_const measurableSet_setOf_posDef
  refine (hL.comp_aemeasurable hint.aemeasurable).congr ?_
  filter_upwards [hX] with ω hω
  rw [Function.comp_apply, Set.piecewise_eq_of_mem _ _ _ (show exp (X ω) ∈ {A | A.PosDef} from
    hω.posDef_exp), hω.cfc_log_exp]

/-! ### Integrability -/

private theorem norm_re_trace_le_card_mul_specNorm_exp {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    ‖RCLike.re (exp M).trace‖ ≤ Fintype.card n * specNorm (exp M) := by
  rcases isEmpty_or_nonempty n with h | h
  · simp only [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty, map_zero, norm_zero,
      Fintype.card_eq_zero, Nat.cast_zero, zero_mul, le_refl]
  · rw [Real.norm_eq_abs, abs_of_pos hM.re_trace_exp_pos, hM.specNorm_exp]
    exact hM.re_trace_exp_le_card_mul_exp

private theorem specNorm_exp_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : specNorm (exp (A + B)) ≤ specNorm (exp A) * specNorm (exp B) := by
  have h := specNorm_exp_sum_le_prod (Finset.univ : Finset Bool)
    (A := fun b => cond b A B) fun b _ => by cases b <;> assumption
  simpa only [Fintype.sum_bool, Fintype.prod_bool, cond_true, cond_false] using h

/-- `tr exp (H + X)` is integrable when `‖exp X‖` is dominated by an integrable function. -/
private theorem integrable_re_trace_exp_add_of_le {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {X : Ω → Matrix n n 𝕜} (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {g : Ω → ℝ} (hg : Integrable g μ) (hle : ∀ᵐ ω ∂μ, specNorm (exp (X ω)) ≤ g ω) :
    Integrable (fun ω => RCLike.re (exp (H + X ω)).trace) μ := by
  refine (hg.const_mul (Fintype.card n * specNorm (exp H))).mono'
    (continuous_re_trace_exp.measurable.comp_aemeasurable
      (aemeasurable_const.add hXm)).aestronglyMeasurable ?_
  filter_upwards [hX, hle] with ω hω hωg
  calc ‖RCLike.re (exp (H + X ω)).trace‖ ≤ Fintype.card n * specNorm (exp (H + X ω)) :=
        norm_re_trace_le_card_mul_specNorm_exp (hH.add hω)
    _ ≤ Fintype.card n * (specNorm (exp H) * g ω) :=
        mul_le_mul_of_nonneg_left ((specNorm_exp_add_le hH hω).trans
          (mul_le_mul_of_nonneg_left hωg (specNorm_nonneg _))) (Nat.cast_nonneg _)
    _ = Fintype.card n * specNorm (exp H) * g ω := by ring

/-! ### Lieb's theorem in expectation -/

/-- **Lieb's theorem in expectation** ([Tropp2015], Corollary 3.4.2). -/
theorem integral_re_trace_exp_add_le [IsProbabilityMeasure μ] {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) {X : Ω → Matrix n n 𝕜} (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hint : Integrable (fun ω => exp (X ω)) μ) :
    ∫ ω, RCLike.re (exp (H + X ω)).trace ∂μ ≤
      RCLike.re (exp (H + cfc Real.log (∫ ω, exp (X ω) ∂μ))).trace := by
  have hpd : ∀ᵐ ω ∂μ, (exp (X ω)).PosDef := hX.mono fun ω hω => hω.posDef_exp
  have hm : (∫ ω, exp (X ω) ∂μ).PosDef := Matrix.posDef_integral hint hpd
  have heq : (fun ω => RCLike.re (exp (H + cfc Real.log (exp (X ω)))).trace) =ᵐ[μ]
      fun ω => RCLike.re (exp (H + X ω)).trace :=
    hX.mono fun ω hω => by simp only [hω.cfc_log_exp]
  have hi : Integrable (fun ω => RCLike.re (exp (H + X ω)).trace) μ :=
    integrable_re_trace_exp_add_of_le hH (aemeasurable_of_integrable_exp hX hint) hX hint.norm
      (ae_of_all _ fun ω => (specNorm_eq_norm _).le)
  rw [← integral_congr_ae heq]
  exact (concaveOn_re_trace_exp_add_cfc_log hH).le_map_integral_of_integral_mem
    (continuousOn_re_trace_exp_add_cfc_log H) hpd hint (hi.congr heq.symm) hm

/-- Replacing a random Hermitian `Z` independent of a random Hermitian `R` by `log E e^Z` does not
decrease `E tr exp (R + Z)`: condition on `R` and apply Lieb's theorem in expectation. -/
private theorem integral_re_trace_exp_add_le_of_indepFun [IsProbabilityMeasure μ]
    {R Z : Ω → Matrix n n 𝕜} (hind : IndepFun R Z μ) (hRm : AEMeasurable R μ)
    (hZm : AEMeasurable Z μ) (hR : ∀ᵐ ω ∂μ, (R ω).IsHermitian)
    (hZ : ∀ᵐ ω ∂μ, (Z ω).IsHermitian) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hRZ : Integrable (fun ω => RCLike.re (exp (R ω + Z ω)).trace) μ)
    (hRL : Integrable (fun ω => RCLike.re (exp (R ω + cfc Real.log (∫ u, exp (Z u) ∂μ))).trace)
      μ) :
    ∫ ω, RCLike.re (exp (R ω + Z ω)).trace ∂μ ≤
      ∫ ω, RCLike.re (exp (R ω + cfc Real.log (∫ u, exp (Z u) ∂μ))).trace ∂μ := by
  set L := cfc Real.log (∫ u, exp (Z u) ∂μ)
  have hexp : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  have hF : Continuous fun p : Matrix n n 𝕜 × Matrix n n 𝕜 => RCLike.re (exp (p.1 + p.2)).trace :=
    continuous_re_trace_exp.comp continuous_add
  have hG : Continuous fun A : Matrix n n 𝕜 => RCLike.re (exp (A + L)).trace :=
    continuous_re_trace_exp.comp (continuous_id.add continuous_const)
  have hherm : MeasurableSet {A : Matrix n n 𝕜 | A.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  have hmap := hind.map_prod_eq_prod_map_map hRm hZm
  have hp : Integrable (fun p : Matrix n n 𝕜 × Matrix n n 𝕜 => RCLike.re (exp (p.1 + p.2)).trace)
      ((μ.map R).prod (μ.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable (hRm.prodMk hZm)).2 hRZ
  have hr : Integrable (fun A => RCLike.re (exp (A + L)).trace) (μ.map R) :=
    (integrable_map_measure hG.aestronglyMeasurable hRm).2 hRL
  have he : Integrable (fun B : Matrix n n 𝕜 => exp B) (μ.map Z) :=
    (integrable_map_measure hexp.aestronglyMeasurable hZm).2 hint
  have hmz : ∀ᵐ B ∂μ.map Z, B.IsHermitian := (ae_map_iff hZm hherm).2 hZ
  have hmr : ∀ᵐ A ∂μ.map R, A.IsHermitian := (ae_map_iff hRm hherm).2 hR
  have : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZm
  calc ∫ ω, RCLike.re (exp (R ω + Z ω)).trace ∂μ
      = ∫ p, RCLike.re (exp (p.1 + p.2)).trace ∂((μ.map R).prod (μ.map Z)) := by
        rw [← hmap, integral_map (hRm.prodMk hZm) hF.aestronglyMeasurable]
    _ = ∫ A, ∫ B, RCLike.re (exp (A + B)).trace ∂μ.map Z ∂μ.map R := integral_prod _ hp
    _ ≤ ∫ A, RCLike.re (exp (A + L)).trace ∂μ.map R := by
        refine integral_mono_ae hp.integral_prod_left hr ?_
        filter_upwards [hmr] with A hA
        have h := integral_re_trace_exp_add_le hA hmz he
        rwa [integral_map hZm hexp.aestronglyMeasurable] at h
    _ = ∫ ω, RCLike.re (exp (R ω + L)).trace ∂μ := integral_map hRm hG.aestronglyMeasurable

variable {ι : Type*} {X : ι → Ω → Matrix n n 𝕜}

/-- The product of the spectral norms of the exponentials of independent summands over a finite
set is integrable. -/
private theorem integrable_prod_specNorm_exp (hind : iIndepFun X μ)
    (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) (s : Finset ι) :
    Integrable (fun ω => ∏ k ∈ s, specNorm (exp (X k ω))) μ := by
  classical
  have := hind.isProbabilityMeasure
  have hexp : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  set f : ι → Ω → ℝ := fun k ω => specNorm (exp (X k ω)) with hf
  have hfi : iIndepFun f μ :=
    hind.comp (fun _ A => specNorm (exp A)) fun _ => (continuous_specNorm.comp hexp).measurable
  have hfint : ∀ k, Integrable (f k) μ := fun k => (hint k).norm
  have hfm : ∀ k, AEMeasurable (f k) μ := fun k => (hfint k).aemeasurable
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, integrable_const]
  | insert a s ha ih =>
    have h1 : Integrable (∏ j ∈ s, f j) μ := by
      refine ih.congr (ae_of_all _ fun ω => ?_)
      simp only [Finset.prod_apply, hf]
    refine ((hfi.indepFun_finsetProd_of_notMem₀ hfm ha).integrable_mul h1 (hfint a)).congr
      (ae_of_all _ fun ω => ?_)
    simp only [Pi.mul_apply, Finset.prod_apply, Finset.prod_insert ha, hf]
    exact mul_comm _ _

private theorem integrable_re_trace_exp_add_sum (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (s : Finset ι) :
    Integrable (fun ω => RCLike.re (exp (H + ∑ k ∈ s, X k ω)).trace) μ := by
  have hXm : ∀ k, AEMeasurable (X k) μ := fun k => aemeasurable_of_integrable_exp (hX k) (hint k)
  refine integrable_re_trace_exp_add_of_le hH (Finset.aemeasurable_fun_sum s fun k _ => hXm k) ?_
    (integrable_prod_specNorm_exp hind hint s) ?_
  · filter_upwards [(Filter.eventually_all_finset s).2 fun k _ => hX k] with ω hω
    exact isSelfAdjoint_sum s hω
  · filter_upwards [(Filter.eventually_all_finset s).2 fun k _ => hX k] with ω hω
    exact specNorm_exp_sum_le_prod s hω

/-- Subadditivity over a finite set of indices, with a fixed Hermitian shift. -/
private theorem integral_re_trace_exp_add_sum_le (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ)
    (s : Finset ι) {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (exp (H + ∑ k ∈ s, X k ω)).trace ∂μ ≤
      RCLike.re (exp (H + ∑ k ∈ s, cfc Real.log (∫ ω, exp (X k ω) ∂μ))).trace := by
  classical
  have := hind.isProbabilityMeasure
  have hXm : ∀ k, AEMeasurable (X k) μ := fun k => aemeasurable_of_integrable_exp (hX k) (hint k)
  induction s using Finset.induction_on generalizing H with
  | empty =>
    simp only [Finset.sum_empty, add_zero, integral_const, probReal_univ, one_smul, le_refl]
  | insert a s ha ih =>
    obtain ⟨L, hLdef⟩ : ∃ L, cfc Real.log (∫ ω, exp (X a ω) ∂μ) = L := ⟨_, rfl⟩
    have hL : L.IsHermitian := hLdef ▸ cfc_predicate Real.log _
    have hRZ : IndepFun (fun ω => H + ∑ k ∈ s, X k ω) (X a) μ := by
      have h := (hind.indepFun_finsetSum_of_notMem₀ hXm ha).comp (measurable_const_add H)
        measurable_id
      convert h using 1
      · funext ω
        simp only [Function.comp_apply, Finset.sum_apply]
      · rfl
    have hR : ∀ᵐ ω ∂μ, (H + ∑ k ∈ s, X k ω).IsHermitian := by
      filter_upwards [(Filter.eventually_all_finset s).2 fun k _ => hX k] with ω hω
      exact hH.add (isSelfAdjoint_sum s hω)
    have e1 : ∀ ω, H + ∑ k ∈ insert a s, X k ω = (H + ∑ k ∈ s, X k ω) + X a ω := fun ω => by
      rw [Finset.sum_insert ha, add_left_comm, add_comm (X a ω)]
    have e2 : ∀ ω, (H + ∑ k ∈ s, X k ω) + L = (H + L) + ∑ k ∈ s, X k ω := fun ω => by
      rw [add_right_comm]
    have hint1 := integrable_re_trace_exp_add_sum hind hX hint hH (insert a s)
    have hint2 := integrable_re_trace_exp_add_sum hind hX hint (hH.add hL) s
    simp only [e1] at hint1 ⊢
    simp only [← e2] at hint2
    have step := integral_re_trace_exp_add_le_of_indepFun hRZ
      (aemeasurable_const.add (Finset.aemeasurable_fun_sum s fun k _ => hXm k)) (hXm a) hR
      (hX a) (hint a) hint1 (by rw [hLdef]; exact hint2)
    rw [hLdef] at step
    refine step.trans ?_
    simp only [e2]
    refine (ih (hH.add hL)).trans_eq ?_
    rw [Finset.sum_insert ha, hLdef, add_assoc]

variable [Fintype ι]

/-- The trace exponential of a sum of independent random Hermitian matrices with integrable
exponentials is integrable. -/
theorem integrable_re_trace_exp_sum (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) :
    Integrable (fun ω => RCLike.re (exp (∑ k, X k ω)).trace) μ := by
  simpa only [zero_add] using
    integrable_re_trace_exp_add_sum hind hX hint Matrix.isHermitian_zero Finset.univ

/-- **Subadditivity of matrix cumulant generating functions** ([Tropp2015], Lemma 3.5.1). -/
theorem integral_re_trace_exp_sum_le (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) :
    ∫ ω, RCLike.re (exp (∑ k, X k ω)).trace ∂μ ≤
      RCLike.re (exp (∑ k, cfc Real.log (∫ ω, exp (X k ω) ∂μ))).trace := by
  simpa only [zero_add] using
    integral_re_trace_exp_add_sum_le hind hX hint Finset.univ Matrix.isHermitian_zero

end NLAlib
