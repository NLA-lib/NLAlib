/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import NLAlib.ForMathlib.Analysis.Calculus.ContDiff.Hessian
public import NLAlib.Probability.Distributions.GaussianIntegrationByParts

/-!
# Gaussian interpolation and comparison

Kahane's Gaussian interpolation inequality and the two expectation comparisons proved from it:
the Sudakov–Fernique inequality `E max X ≤ E max Y` and Gordon's min-max inequality
`E min max X ≤ E min max Y`, each for centred finite Gaussian families whose increments compare.

A finite Gaussian family is `X : T → Ω → ℝ` with `HasGaussianLaw (fun ω t => X t ω) μ`, the
process form of Mathlib's `IsGaussianProcess` (for finite `T` the two are equivalent; the bridge
is added when a consumer holds an `IsGaussianProcess`). Gordon's two-index family is
`X : U → T → Ω → ℝ` with `HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ`. The two families
of a comparison live on different probability spaces: only their laws matter, and a comparison
process need not be built on the space of the process it bounds. Second moments of increments are
written as integrals, the form a consumer computes from isotropy. No equal-variance hypothesis is
needed in the expectation forms (unlike Slepian's tail comparison, which is not stated).

Over an empty index set the suprema and infima are `0` (`Real.iSup_of_isEmpty`), and both sides
of each comparison vanish.

## Main results

* `NLAlib.integral_comp_le_integral_comp_of_hasGaussianLaw`: Gaussian interpolation (Kahane).
* `NLAlib.integral_iSup_le_integral_iSup_of_hasGaussianLaw`: the Sudakov–Fernique inequality.
* `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw`: Gordon's min-max
  inequality.
* Integrability companions: `NLAlib.integrable_comp_of_hasGaussianLaw_of_contDiff_two`,
  `NLAlib.integrable_iSup_of_hasGaussianLaw`, `NLAlib.integrable_iInf_iSup_of_hasGaussianLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω}
  {ν : Measure Ω'}

section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem abs_le_of_contDiff_two {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) (x : ι → ℝ) :
    |F x| ≤ |F 0| + ‖fderiv ℝ F 0‖ * ‖x‖ + C * ‖x‖ ^ 2 := by
  have h := norm_sub_le_of_norm_iteratedFDeriv_two_le hF hF2 x
  rw [Real.norm_eq_abs] at h
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

omit [DecidableEq ι] in
/-- A function of class `C²` with Hessian bounded by `C` of a Gaussian vector is integrable: it
has quadratic growth and a Gaussian vector has every moment. -/
theorem integrable_comp_of_hasGaussianLaw_of_contDiff_two {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) : Integrable (fun ω => F (X ω)) μ := by
  have hP := hX.isProbabilityMeasure
  have h1 : Integrable (fun ω => ‖X ω‖) μ := hX.integrable.norm
  have h2 : Integrable (fun ω => ‖X ω‖ ^ 2) μ := hX.memLp_two.norm.integrable_sq
  refine Integrable.mono' (((integrable_const |F 0|).add (h1.const_mul ‖fderiv ℝ F 0‖)).add
      (h2.const_mul C))
    (hF.continuous.comp_aestronglyMeasurable hX.aemeasurable.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  simpa only [Pi.add_apply, Real.norm_eq_abs] using abs_le_of_contDiff_two hF hF2 (X ω)

omit [DecidableEq ι] in
private theorem norm_lincomb_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : ι → ℝ) :
    ‖fun j => a * x j + b * y j‖ ≤ ‖x‖ + ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, ← one_mul ‖x‖]
    exact mul_le_mul ha (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j) (abs_nonneg _)
      zero_le_one
  · rw [abs_mul, ← one_mul ‖y‖]
    exact mul_le_mul hb (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y j) (abs_nonneg _)
      zero_le_one

variable {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P : Measure Ω₀}

omit [Fintype ι] [DecidableEq ι] in
/-- Along the rotation `Z θ = cos θ A + sin θ B`, `Cov (Z' θ i, Z θ j)` is
`sin θ cos θ (E Bᵢ Bⱼ - E Aᵢ Aⱼ)` when the cross moments vanish. -/
private theorem covariance_rotation_eq [IsProbabilityMeasure P] {A B : Ω₀ → ι → ℝ}
    (hA : ∀ i, MemLp (fun ω => A ω i) 2 P) (hB : ∀ i, MemLp (fun ω => B ω i) 2 P)
    (hA0 : ∀ i, ∫ ω, A ω i ∂P = 0) (hB0 : ∀ i, ∫ ω, B ω i ∂P = 0)
    (hcross : ∀ i j, ∫ ω, A ω i * B ω j ∂P = 0) (θ : ℝ) (i j : ι) :
    cov[fun ω => -Real.sin θ * A ω i + Real.cos θ * B ω i,
      fun ω => Real.cos θ * A ω j + Real.sin θ * B ω j; P]
      = Real.sin θ * Real.cos θ * (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) := by
  set s := Real.sin θ
  set c := Real.cos θ
  have hD : MemLp (fun ω => -s * A ω i + c * B ω i) 2 P :=
    ((hA i).const_mul _).add ((hB i).const_mul _)
  have hZ : MemLp (fun ω => c * A ω j + s * B ω j) 2 P :=
    ((hA j).const_mul _).add ((hB j).const_mul _)
  rw [covariance_eq_sub hD hZ]
  have hD0 : ∫ ω, -s * A ω i + c * B ω i ∂P = 0 := by
    rw [integral_add (((hA i).integrable one_le_two).const_mul _)
      (((hB i).integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul, hA0,
      hB0]
    ring
  rw [hD0, zero_mul, sub_zero]
  have e : (fun ω => (-s * A ω i + c * B ω i) * (c * A ω j + s * B ω j))
      = fun ω => (-s * c) * (A ω i * A ω j) + (-s ^ 2) * (A ω i * B ω j)
        + c ^ 2 * (A ω j * B ω i) + (c * s) * (B ω i * B ω j) := by
    funext ω; ring
  have i1 : Integrable (fun ω => A ω i * A ω j) P := (hA i).integrable_mul (hA j)
  have i2 : Integrable (fun ω => A ω i * B ω j) P := (hA i).integrable_mul (hB j)
  have i3 : Integrable (fun ω => A ω j * B ω i) P := (hA j).integrable_mul (hB i)
  have i4 : Integrable (fun ω => B ω i * B ω j) P := (hB i).integrable_mul (hB j)
  simp only [Pi.mul_apply]
  rw [e, integral_add (((i1.const_mul _).fun_add (i2.const_mul _)).fun_add (i3.const_mul _))
    (i4.const_mul _), integral_add ((i1.const_mul _).fun_add (i2.const_mul _))
    (i3.const_mul _), integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul,
    integral_const_mul, integral_const_mul, hcross, hcross]
  ring

/-- `v ↦ ∂ᵢ F (R v)`, for `F` of class `C²` with bounded Hessian and `R` a contraction, is `C¹`
with derivative `w ↦ D² F (R v) (R w) eᵢ`, bounded by the Hessian bound. -/
private theorem contDiff_one_fderiv_comp_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) (R : E →L[ℝ] (ι → ℝ)) (hR : ∀ w, ‖R w‖ ≤ ‖w‖)
    (i : ι) :
    ContDiff ℝ 1 (fun v => fderiv ℝ F (R v) (Pi.single i 1)) ∧
      (∀ v w, fderiv ℝ (fun v => fderiv ℝ F (R v) (Pi.single i 1)) v w
        = fderiv ℝ (fderiv ℝ F) (R v) (R w) (Pi.single i 1)) ∧
      ∀ v, ‖fderiv ℝ (fun v => fderiv ℝ F (R v) (Pi.single i 1)) v‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF2 0)
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have hgd : ∀ v, HasFDerivAt (fun v => fderiv ℝ F (R v) (Pi.single i 1))
      (((fderiv ℝ (fderiv ℝ F) (R v)).comp R).flip (Pi.single i 1)) v := by
    intro v
    have h1 := ((hd (R v)).hasFDerivAt.comp v R.hasFDerivAt).clm_apply
      (hasFDerivAt_const (Pi.single i 1 : ι → ℝ) v)
    rw [ContinuousLinearMap.comp_zero, zero_add] at h1
    exact h1
  refine ⟨((hF.fderiv_right (m := 1) le_rfl).comp R.contDiff).clm_apply contDiff_const,
    fun v w => by rw [(hgd v).fderiv]; rfl, fun v => ?_⟩
  rw [(hgd v).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun w => ?_
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  calc ‖fderiv ℝ (fderiv ℝ F) (R v) (R w) (Pi.single i 1)‖
      ≤ ‖fderiv ℝ (fderiv ℝ F) (R v)‖ * ‖R w‖ * ‖(Pi.single i 1 : ι → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ C * ‖w‖ := by
      rw [Pi.norm_single, norm_one, mul_one]
      refine mul_le_mul ?_ (hR w) (norm_nonneg _) hC
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
      exact hF2 _

/-- The Stein step of the interpolation: Gaussian integration by parts for the pair
`(Z' θ i, Z θ)`, applied to `∂ᵢ F`. -/
private theorem integral_rotation_mul_fderiv_eq {A B : Ω₀ → ι → ℝ}
    (hAB : HasGaussianLaw (fun ω => (A ω, B ω)) P)
    (hA0 : ∀ i, ∫ ω, A ω i ∂P = 0) (hB0 : ∀ i, ∫ ω, B ω i ∂P = 0)
    (hcross : ∀ i j, ∫ ω, A ω i * B ω j ∂P = 0) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    {C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) (θ : ℝ) (i : ι) :
    ∫ ω, (-Real.sin θ * A ω i + Real.cos θ * B ω i) *
        fderiv ℝ F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j) (Pi.single i 1) ∂P
      = ∑ j, Real.sin θ * Real.cos θ * (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) *
        ∫ ω, fderiv ℝ (fderiv ℝ F) (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)
          (Pi.single j 1) (Pi.single i 1) ∂P := by
  have hP := hAB.isProbabilityMeasure
  set s := Real.sin θ
  set c := Real.cos θ
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF2 0)
  have hA : ∀ i, MemLp (fun ω => A ω i) 2 P := fun i =>
    (hAB.fst.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)).memLp_two
  have hB : ∀ i, MemLp (fun ω => B ω i) 2 P := fun i =>
    (hAB.snd.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)).memLp_two
  -- the Gaussian vector `V = (Z' θ, Z θ)` on `ι ⊕ ι`
  let pr : ι → (ι → ℝ) →L[ℝ] ℝ := fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j
  let M : (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι ⊕ ι → ℝ) := ContinuousLinearMap.pi fun k =>
    Sum.elim (fun j => (-s) • ((pr j).comp (ContinuousLinearMap.fst ℝ _ _)) +
        c • ((pr j).comp (ContinuousLinearMap.snd ℝ _ _)))
      (fun j => c • ((pr j).comp (ContinuousLinearMap.fst ℝ _ _)) +
        s • ((pr j).comp (ContinuousLinearMap.snd ℝ _ _))) k
  have hV : HasGaussianLaw (fun ω => M (A ω, B ω)) P := hAB.map_fun M
  have hVl : ∀ ω j, M (A ω, B ω) (Sum.inl j) = -s * A ω j + c * B ω j := fun ω j => by
    simp [M, pr]
  have hVr : ∀ ω j, M (A ω, B ω) (Sum.inr j) = c * A ω j + s * B ω j := fun ω j => by
    simp [M, pr]
  -- the test function `v ↦ ∂ᵢ F (v ∘ inr)`
  let R : (ι ⊕ ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ⊕ ι => ℝ) (Sum.inr j)
  have hRV : ∀ ω, R (M (A ω, B ω)) = fun j => c * A ω j + s * B ω j := fun ω => by
    funext j; exact hVr ω j
  obtain ⟨hgc, hgfd, hgb⟩ := contDiff_one_fderiv_comp_apply hF hF2 R (fun w =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun j => norm_le_pi_norm w (Sum.inr j)) i
  have hstein :=
    integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw hV hgc hgb
      (Sum.inl i)
  have hmean : ∫ ω, -s * A ω i + c * B ω i ∂P = 0 := by
    rw [integral_add (((hA i).integrable one_le_two).const_mul _)
      (((hB i).integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul, hA0,
      hB0]
    ring
  have hRl : ∀ j, R (Pi.single (Sum.inl j) 1) = 0 := fun j => by
    funext k; simp [R]
  have hRr : ∀ j, R (Pi.single (Sum.inr j) 1) = Pi.single j 1 := fun j => by
    funext k; simp [R, Pi.single_apply]
  rw [Fintype.sum_sum_type] at hstein
  simp only [hgfd, hRl, hRr, map_zero, zero_apply, integral_zero, mul_zero,
    Finset.sum_const_zero, zero_add] at hstein
  simp only [hmean, sub_zero, hRV, hVl] at hstein
  rw [hstein]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [hVr]
  exact covariance_rotation_eq hA hB hA0 hB0 hcross θ i j

omit [DecidableEq ι] in
/-- `θ ↦ E F (cos θ A + sin θ B)` is differentiable, with derivative
`E [D F (Z θ) (Z' θ)]`. -/
private theorem hasDerivAt_integral_rotation [IsProbabilityMeasure P] {A B : Ω₀ → ι → ℝ}
    (hA : MemLp A 2 P) (hB : MemLp B 2 P) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) (θ₀ : ℝ) :
    HasDerivAt (fun θ => ∫ ω, F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j) ∂P)
      (∫ ω, fderiv ℝ F (fun j => Real.cos θ₀ * A ω j + Real.sin θ₀ * B ω j)
        (fun j => -Real.sin θ₀ * A ω j + Real.cos θ₀ * B ω j) ∂P) θ₀ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF2 0)
  have hdiff : Differentiable ℝ F := hF.differentiable two_ne_zero
  have hdfc : Continuous (fderiv ℝ F) := hF.continuous_fderiv two_ne_zero
  set N : Ω₀ → ℝ := fun ω => ‖A ω‖ + ‖B ω‖ with hN
  have hNm : MemLp N 2 P := hA.norm.add hB.norm
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => by positivity
  have hAae := hA.aestronglyMeasurable.aemeasurable
  have hBae := hB.aestronglyMeasurable.aemeasurable
  have hZae : ∀ a b : ℝ, AEMeasurable (fun ω => fun j => a * A ω j + b * B ω j) P :=
    fun a b => (hAae.const_smul a).add (hBae.const_smul b)
  have hZb : ∀ θ ω, ‖fun j => Real.cos θ * A ω j + Real.sin θ * B ω j‖ ≤ N ω := fun θ ω =>
    norm_lincomb_le (Real.abs_cos_le_one θ) (Real.abs_sin_le_one θ) _ _
  have hDb : ∀ θ ω, ‖fun j => -Real.sin θ * A ω j + Real.cos θ * B ω j‖ ≤ N ω := fun θ ω =>
    norm_lincomb_le (by rw [abs_neg]; exact Real.abs_sin_le_one θ) (Real.abs_cos_le_one θ) _ _
  have hbound : ∀ θ ω, ‖fderiv ℝ F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)
      (fun j => -Real.sin θ * A ω j + Real.cos θ * B ω j)‖
      ≤ ‖fderiv ℝ F 0‖ * N ω + C * N ω ^ 2 := by
    intro θ ω
    refine ((fderiv ℝ F _).le_opNorm _).trans ?_
    have h1 : ‖fderiv ℝ F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)‖
        ≤ ‖fderiv ℝ F 0‖ + C * N ω := (norm_fderiv_le_of_norm_iteratedFDeriv_two_le hF hF2 _).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hZb θ ω) hC))
    calc _ ≤ (‖fderiv ℝ F 0‖ + C * N ω) * N ω :=
          mul_le_mul h1 (hDb θ ω) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hFi : Integrable (fun ω => F (fun j => Real.cos θ₀ * A ω j + Real.sin θ₀ * B ω j)) P := by
    refine Integrable.mono' (((integrable_const |F 0|).add
        ((hNm.integrable one_le_two).const_mul ‖fderiv ℝ F 0‖)).add
        (hNm.integrable_sq.const_mul C))
      (hF.continuous.comp_aestronglyMeasurable (hZae _ _).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    have h1 := abs_le_of_contDiff_two hF hF2 (fun j => Real.cos θ₀ * A ω j + Real.sin θ₀ * B ω j)
    have h2 := hZb θ₀ ω
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have h3 : ‖fun j => Real.cos θ₀ * A ω j + Real.sin θ₀ * B ω j‖ ^ 2 ≤ N ω ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [norm_nonneg (fderiv ℝ F 0)]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (s := Set.univ)
    (bound := fun ω => ‖fderiv ℝ F 0‖ * N ω + C * N ω ^ 2) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ =>
      (hF.continuous.comp_aestronglyMeasurable (hZae _ _).aestronglyMeasurable))
    hFi (((hdfc.comp continuous_fst).clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hZae _ _).prodMk (hZae _ _)).aestronglyMeasurable)
    (ae_of_all _ fun ω θ _ => hbound θ ω)
    (((hNm.integrable one_le_two).const_mul _).add (hNm.integrable_sq.const_mul C))
    (ae_of_all _ fun ω θ _ => ?_)).2
  · have hZd : HasDerivAt (fun θ => fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)
        (fun j => -Real.sin θ * A ω j + Real.cos θ * B ω j) θ := by
      rw [hasDerivAt_pi]
      intro j
      exact ((Real.hasDerivAt_cos θ).mul_const (A ω j)).add
        ((Real.hasDerivAt_sin θ).mul_const (B ω j))
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt θ hZd

/-- The derivative of the interpolation, after integration by parts:
`E [D F (Z θ) (Z' θ)] = sin θ cos θ E [∑ᵢⱼ Δᵢⱼ ∂ⱼ∂ᵢ F (Z θ)]`. -/
private theorem integral_fderiv_rotation_eq {A B : Ω₀ → ι → ℝ}
    (hAB : HasGaussianLaw (fun ω => (A ω, B ω)) P)
    (hA0 : ∀ i, ∫ ω, A ω i ∂P = 0) (hB0 : ∀ i, ∫ ω, B ω i ∂P = 0)
    (hcross : ∀ i j, ∫ ω, A ω i * B ω j ∂P = 0) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    {C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) (θ : ℝ) :
    ∫ ω, fderiv ℝ F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)
        (fun j => -Real.sin θ * A ω j + Real.cos θ * B ω j) ∂P
      = Real.sin θ * Real.cos θ * ∫ ω, ∑ i, ∑ j,
        (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) *
          fderiv ℝ (fderiv ℝ F) (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j)
            (Pi.single j 1) (Pi.single i 1) ∂P := by
  have hP := hAB.isProbabilityMeasure
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF2 0)
  set s := Real.sin θ
  set c := Real.cos θ
  have hAm : MemLp A 2 P := hAB.fst.memLp_two
  have hBm : MemLp B 2 P := hAB.snd.memLp_two
  have hAB' := (hAB.fst.aemeasurable.prodMk hAB.snd.aemeasurable).aestronglyMeasurable
  have hdfc : Continuous (fderiv ℝ F) := hF.continuous_fderiv two_ne_zero
  have hd2c : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (m := 1) le_rfl).continuous_fderiv one_ne_zero
  set N : Ω₀ → ℝ := fun ω => ‖A ω‖ + ‖B ω‖ with hN
  have hNm : MemLp N 2 P := hAm.norm.add hBm.norm
  have hterm : ∀ i, Integrable (fun ω => (-s * A ω i + c * B ω i) *
      fderiv ℝ F (fun j => c * A ω j + s * B ω j) (Pi.single i 1)) P := by
    intro i
    refine Integrable.mono' (((hNm.integrable one_le_two).const_mul ‖fderiv ℝ F 0‖).add
        (hNm.integrable_sq.const_mul C))
      ((by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) => (-s * p.1 i + c * p.2 i) *
        fderiv ℝ F (fun j => c * p.1 j + s * p.2 j) (Pi.single i 1)).comp_aestronglyMeasurable
        hAB') (ae_of_all _ fun ω => ?_)
    have hD : |-s * A ω i + c * B ω i| ≤ N ω := by
      have := norm_lincomb_le (by rw [abs_neg]; exact Real.abs_sin_le_one θ)
        (Real.abs_cos_le_one θ) (A ω) (B ω)
      exact (norm_le_pi_norm (fun j => -s * A ω j + c * B ω j) i).trans this
    have hZ : ‖fderiv ℝ F (fun j => c * A ω j + s * B ω j) (Pi.single i 1)‖
        ≤ ‖fderiv ℝ F 0‖ + C * N ω := by
      refine ((fderiv ℝ F _).le_opNorm _).trans ?_
      rw [Pi.norm_single, norm_one, mul_one]
      exact (norm_fderiv_le_of_norm_iteratedFDeriv_two_le hF hF2 _).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (norm_lincomb_le (Real.abs_cos_le_one θ)
          (Real.abs_sin_le_one θ) _ _) hC))
    rw [norm_mul, Real.norm_eq_abs]
    simp only [Pi.add_apply]
    calc _ ≤ N ω * (‖fderiv ℝ F 0‖ + C * N ω) :=
          mul_le_mul hD hZ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hH : ∀ i j, Integrable (fun ω => fderiv ℝ (fderiv ℝ F)
      (fun j => c * A ω j + s * B ω j) (Pi.single j 1) (Pi.single i 1)) P := by
    intro i j
    refine Integrable.mono' (integrable_const C)
      ((by fun_prop : Continuous fun p : (ι → ℝ) × (ι → ℝ) => fderiv ℝ (fderiv ℝ F)
        (fun j => c * p.1 j + s * p.2 j) (Pi.single j 1) (Pi.single i 1)).comp_aestronglyMeasurable
        hAB') (ae_of_all _ fun ω => ?_)
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    rw [Pi.norm_single, Pi.norm_single, norm_one, mul_one, mul_one,
      ← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
    exact hF2 _
  calc _ = ∫ ω, ∑ i, (-s * A ω i + c * B ω i) *
        fderiv ℝ F (fun j => c * A ω j + s * B ω j) (Pi.single i 1) ∂P := by
        congr 1; funext ω; exact apply_eq_sum_mul_apply_single _ _
    _ = ∑ i, ∑ j, s * c * (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) *
        ∫ ω, fderiv ℝ (fderiv ℝ F) (fun j => c * A ω j + s * B ω j)
          (Pi.single j 1) (Pi.single i 1) ∂P := by
        rw [integral_finsetSum _ fun i _ => hterm i]
        exact Finset.sum_congr rfl fun i _ =>
          integral_rotation_mul_fderiv_eq hAB hA0 hB0 hcross hF hF2 θ i
    _ = _ := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hH i j).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => (hH i j).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, mul_assoc]

omit [DecidableEq ι] in
private theorem iteratedFDeriv_two_apply_pair {F : (ι → ℝ) → ℝ} (x u v : ι → ℝ) :
    iteratedFDeriv ℝ 2 F x ![u, v] = fderiv ℝ (fderiv ℝ F) x u v := by
  rw [iteratedFDeriv_two_apply]
  rfl

/-- Kahane's inequality for a jointly Gaussian pair on one space with vanishing cross
moments. -/
private theorem integral_comp_le_integral_comp_of_hasGaussianLaw_pair {A B : Ω₀ → ι → ℝ}
    (hAB : HasGaussianLaw (fun ω => (A ω, B ω)) P)
    (hA0 : ∀ i, ∫ ω, A ω i ∂P = 0) (hB0 : ∀ i, ∫ ω, B ω i ∂P = 0)
    (hcross : ∀ i j, ∫ ω, A ω i * B ω j ∂P = 0) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    {C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C)
    (hcov : ∀ x, 0 ≤ ∑ i, ∑ j, (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) *
      iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]) :
    ∫ ω, F (A ω) ∂P ≤ ∫ ω, F (B ω) ∂P := by
  have hP := hAB.isProbabilityMeasure
  have hderiv := hasDerivAt_integral_rotation hAB.fst.memLp_two hAB.snd.memLp_two hF hF2
  set Φ : ℝ → ℝ := fun θ => ∫ ω, F (fun j => Real.cos θ * A ω j + Real.sin θ * B ω j) ∂P
    with hΦ
  have hpair : ∀ z : ι → ℝ, 0 ≤ ∑ i, ∑ j, (∫ ω, B ω i * B ω j ∂P - ∫ ω, A ω i * A ω j ∂P) *
      fderiv ℝ (fderiv ℝ F) z (Pi.single j 1) (Pi.single i 1) := by
    intro z
    have h := hcov z
    simp only [iteratedFDeriv_two_apply_pair] at h
    rw [Finset.sum_comm]
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    simp only [mul_comm (B _ i), mul_comm (A _ i)]
  have hmono : MonotoneOn Φ (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.pi / 2))
      (HasDerivAt.continuousOn fun θ _ => hderiv θ) (fun θ _ => (hderiv θ).hasDerivWithinAt)
      (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    rw [integral_fderiv_rotation_eq hAB hA0 hB0 hcross hF hF2 θ]
    refine mul_nonneg (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le
      (by linarith [hθ.2, Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩)) (integral_nonneg fun ω => hpair _)
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hmono ⟨le_refl 0, hpi⟩ ⟨hpi, le_refl _⟩ hpi
  simpa only [hΦ, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_mul, zero_mul, add_zero, zero_add] using h

/-- **Gaussian interpolation** (Kahane's inequality): for centred Gaussian vectors `X`, `Y` and
`F` of class `C²` with Hessian bounded by `C`, if
`∑ i j, (E Yᵢ Yⱼ - E Xᵢ Xⱼ) ∂ᵢⱼF(x) ≥ 0` for every `x`, then `E F(X) ≤ E F(Y)`.
[Vershynin2018, Lemma 7.2.7 and the proof of Theorem 7.2.1]; [Kahane1986]; there as an identity
along the interpolating path `√t X + √(1 - t) Y`, here the inequality it gives, with `X` and `Y`
on different probability spaces.
Result: gaussian-interpolation -/
theorem integral_comp_le_integral_comp_of_hasGaussianLaw {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hX0 : ∀ i, ∫ ω, X ω i ∂μ = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂ν = 0)
    {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C)
    (hcov : ∀ x, 0 ≤ ∑ i, ∑ j, (∫ ω, Y ω i * Y ω j ∂ν - ∫ ω, X ω i * X ω j ∂μ) *
      iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]) :
    ∫ ω, F (X ω) ∂μ ≤ ∫ ω, F (Y ω) ∂ν := by
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  have := hX.isGaussian_map
  have := hY.isGaussian_map
  set ρ := (μ.map X).prod (ν.map Y) with hρ
  have hlaw : HasGaussianLaw (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, p.2)) ρ :=
    IsGaussian.hasGaussianLaw_id
  have hfst : ∀ f : (ι → ℝ) → ℝ, Continuous f → ∫ p, f p.1 ∂ρ = ∫ ω, f (X ω) ∂μ := by
    intro f hf
    rw [← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable, hρ,
      Measure.map_fst_prod, measure_univ, one_smul,
      integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have hsnd : ∀ f : (ι → ℝ) → ℝ, Continuous f → ∫ p, f p.2 ∂ρ = ∫ ω, f (Y ω) ∂ν := by
    intro f hf
    rw [← integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable, hρ,
      Measure.map_snd_prod, measure_univ, one_smul,
      integral_map hY.aemeasurable hf.aestronglyMeasurable]
  have hmX : ∀ i j, ∫ p, p.1 i * p.1 j ∂ρ = ∫ ω, X ω i * X ω j ∂μ := fun i j =>
    hfst (fun x => x i * x j) (by fun_prop)
  have hmY : ∀ i j, ∫ p, p.2 i * p.2 j ∂ρ = ∫ ω, Y ω i * Y ω j ∂ν := fun i j =>
    hsnd (fun x => x i * x j) (by fun_prop)
  have hcross : ∀ i j, ∫ p, p.1 i * p.2 j ∂ρ = 0 := by
    intro i j
    rw [hρ, integral_prod_mul (fun x : ι → ℝ => x i) (fun y : ι → ℝ => y j),
      integral_map hX.aemeasurable (continuous_apply i).aestronglyMeasurable, hX0, zero_mul]
  have h := integral_comp_le_integral_comp_of_hasGaussianLaw_pair hlaw
    (fun i => (hfst _ (continuous_apply i)).trans (hX0 i))
    (fun i => (hsnd _ (continuous_apply i)).trans (hY0 i)) hcross hF hF2
    (fun x => by simpa only [hmX, hmY] using hcov x)
  rwa [hfst F hF.continuous, hsnd F hF.continuous] at h

end Interpolation

/-! ### The soft min-max and its Hessian -/

section SmoothMinMax

variable {U T : Type*} [Fintype U] [Fintype T]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : U × T => ℝ) j

/-- block partition function `S_u(x) = ∑_t exp(β x_{ut})` -/
private noncomputable def gmmS (β : ℝ) (u : U) (x : U × T → ℝ) : ℝ := ∑ t, Real.exp (β * x (u, t))
/-- `W(x) = ∑_u S_u(x)⁻¹` -/
private noncomputable def gmmW (β : ℝ) (x : U × T → ℝ) : ℝ := ∑ u, (gmmS β u x)⁻¹
/-- the smooth min-max `F_β(x) = -β⁻¹ log ∑_u (∑_t e^{β x_{ut}})⁻¹` -/
private noncomputable def gmmF (β : ℝ) (x : U × T → ℝ) : ℝ := -β⁻¹ * Real.log (gmmW β x)
/-- gradient `∂F/∂x_a = p_u q_{t|u}`, `a = (u,t)` -/
private noncomputable def gmmg (β : ℝ) (a : U × T) (x : U × T → ℝ) : ℝ :=
  Real.exp (β * x a) * ((gmmS β a.1 x) ^ 2)⁻¹ * (gmmW β x)⁻¹
/-- within-block weight `q_{s|u} = e^{β x_b}/S_u`, `u = a.1`, `b = (·, s)` -/
private noncomputable def gmmq (β : ℝ) (a b : U × T) (x : U × T → ℝ) : ℝ :=
  Real.exp (β * x b) / gmmS β a.1 x
/-- the Hessian of the smooth min-max -/
private noncomputable def gmmH [DecidableEq U] [DecidableEq T] (β : ℝ) (a b : U × T)
    (x : U × T → ℝ) : ℝ :=
  β * ((if a = b then gmmg β a x else 0)
    - 2 * (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0) + gmmg β a x * gmmg β b x)

omit [Fintype U] in
private theorem gmmS_pos [Nonempty T] (β : ℝ) (u : U) (x : U × T → ℝ) : 0 < gmmS β u x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem gmmW_pos [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) : 0 < gmmW β x :=
  Finset.sum_pos (fun u _ => inv_pos.2 (gmmS_pos β u x)) Finset.univ_nonempty

omit [Fintype U] in
private theorem gmm_exp_le_S (β : ℝ) (u : U) (t : T) (x : U × T → ℝ) :
    Real.exp (β * x (u, t)) ≤ gmmS β u x :=
  Finset.single_le_sum (f := fun t => Real.exp (β * x (u, t))) (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_univ t)

private theorem gmm_Sinv_le_W [Nonempty T] (β : ℝ) (u : U) (x : U × T → ℝ) :
    (gmmS β u x)⁻¹ ≤ gmmW β x :=
  Finset.single_le_sum (f := fun u => (gmmS β u x)⁻¹)
    (fun v _ => (inv_pos.2 (gmmS_pos β v x)).le) (Finset.mem_univ u)

private theorem gmmg_nonneg [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    0 ≤ gmmg β a x := by
  unfold gmmg
  have := gmmS_pos β a.1 x
  have := gmmW_pos β x
  positivity

private theorem gmmg_sum [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) :
    ∑ a, gmmg β a x = 1 := by
  rw [Fintype.sum_prod_type]
  have hW := (gmmW_pos β x).ne'
  have h : ∀ u, ∑ t, gmmg β (u, t) x = (gmmS β u x)⁻¹ * (gmmW β x)⁻¹ := by
    intro u
    have hS := (gmmS_pos β u x).ne'
    simp only [gmmg]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    change gmmS β u x * _ * _ = _
    field_simp
  simp_rw [h]
  rw [← Finset.sum_mul]
  change gmmW β x * _ = _
  field_simp

private theorem gmmg_le_one [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    gmmg β a x ≤ 1 := by
  rw [← gmmg_sum β x]
  exact Finset.single_le_sum (fun b _ => gmmg_nonneg β b x) (Finset.mem_univ a)

omit [Fintype U] in
private theorem gmmq_nonneg [Nonempty T] (β : ℝ) (a b : U × T) (x : U × T → ℝ) : 0 ≤ gmmq β a b x :=
  div_nonneg (Real.exp_pos _).le (gmmS_pos β a.1 x).le

omit [Fintype U] in
private theorem gmmq_le_one [Nonempty T] (β : ℝ) (a b : U × T) (h : a.1 = b.1) (x : U × T → ℝ) :
    gmmq β a b x ≤ 1 := by
  unfold gmmq
  rw [div_le_one (gmmS_pos β a.1 x), h]
  exact gmm_exp_le_S β b.1 b.2 x

private theorem gmmg_le_q [Nonempty U] [Nonempty T] (β : ℝ) (a b : U × T) (h : a.1 = b.1)
    (x : U × T → ℝ) : gmmg β b x ≤ gmmq β a b x := by
  unfold gmmg gmmq
  rw [h]
  have hS := gmmS_pos β b.1 x
  have hW := gmmW_pos β x
  have h1 := gmm_Sinv_le_W β b.1 x
  have he := Real.exp_pos (β * x b)
  rw [div_eq_mul_inv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ he.le
  rw [show ((gmmS β b.1 x) ^ 2)⁻¹ * (gmmW β x)⁻¹
      = (gmmS β b.1 x)⁻¹ * ((gmmS β b.1 x) * gmmW β x)⁻¹ by field_simp]
  refine mul_le_of_le_one_right (inv_pos.2 hS).le ?_
  rw [inv_le_one₀ (by positivity)]
  calc (1 : ℝ) = gmmS β b.1 x * (gmmS β b.1 x)⁻¹ := by field_simp
    _ ≤ gmmS β b.1 x * gmmW β x := mul_le_mul_of_nonneg_left h1 hS.le

section Hess
variable [DecidableEq U] [DecidableEq T]

private theorem gmmH_symm (β : ℝ) (a b : U × T) (x : U × T → ℝ) :
    gmmH β a b x = gmmH β b a x := by
  unfold gmmH
  by_cases hab : a = b
  · subst hab; rfl
  rw [if_neg hab, if_neg (Ne.symm hab)]
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    obtain ⟨u, t⟩ := a
    obtain ⟨v, s⟩ := b
    simp only at h1
    subst h1
    simp only [gmmg, gmmq]
    ring
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    ring

private theorem gmmH_rowsum [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) (x : U × T → ℝ) :
    ∑ b, gmmH β a b x = 0 := by
  unfold gmmH
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum, ← Finset.mul_sum, gmmg_sum, if_pos (Finset.mem_univ a)]
  have h : ∑ b : U × T, (if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0) = gmmg β a x := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a.1]
    · simp only [if_true]
      rw [← Finset.mul_sum]
      have hS := (gmmS_pos β a.1 x).ne'
      have : ∑ s, gmmq β a (a.1, s) x = 1 := by
        simp only [gmmq]
        rw [← Finset.sum_div]
        exact div_self hS
      rw [this, mul_one]
    · intro v _ hv
      exact Finset.sum_eq_zero fun s _ => if_neg (Ne.symm hv)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h]
  ring

private theorem gmmH_abs_le [Nonempty U] [Nonempty T] {β : ℝ} (hβ : 0 < β) (a b : U × T)
    (x : U × T → ℝ) : |gmmH β a b x| ≤ 4 * β := by
  have g0 := gmmg_nonneg β a x
  have g1 := gmmg_le_one β a x
  have hA : |(if a = b then gmmg β a x else 0)| ≤ 1 := by
    split_ifs <;> simp [abs_of_nonneg g0, g1]
  have hB : |(if a.1 = b.1 then gmmg β a x * gmmq β a b x else 0)| ≤ 1 := by
    split_ifs with h
    · rw [abs_of_nonneg (mul_nonneg g0 (gmmq_nonneg β a b x))]
      exact mul_le_one₀ g1 (gmmq_nonneg β a b x) (gmmq_le_one β a b h x)
    · simp
  have hC : |gmmg β a x * gmmg β b x| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg g0 (gmmg_nonneg β b x))]
    exact mul_le_one₀ g1 (gmmg_nonneg β b x) (gmmg_le_one β b x)
  unfold gmmH
  rw [abs_mul, abs_of_pos hβ, mul_comm 4]
  refine mul_le_mul_of_nonneg_left ?_ hβ.le
  rw [abs_le] at hA hB hC ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

end Hess

private theorem gmmS_hasFDerivAt [DecidableEq U] (β : ℝ) (u : U) (x : U × T → ℝ) :
    HasFDerivAt (gmmS β u)
      (∑ b, (if b.1 = u then β * Real.exp (β * x b) else 0) • PR b) x := by
  classical
  have h := HasFDerivAt.sum_sum_smul_proj (ι := U × T) (κ := T)
    (fun t => hasFDerivAt_exp_mul_apply_sum_smul_proj β (u, t) x)
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  obtain ⟨v, s⟩ := b
  by_cases hv : v = u
  · subst hv; simp [Prod.ext_iff]
  · simp [Prod.ext_iff, hv]

private theorem gmmW_hasFDerivAt [Nonempty U] [Nonempty T] (β : ℝ) (x : U × T → ℝ) :
    HasFDerivAt (gmmW β) (∑ b, (-(β * gmmW β x * gmmg β b x)) • PR b) x := by
  classical
  have h := HasFDerivAt.sum_sum_smul_proj (κ := U)
    (fun u => HasFDerivAt.inv_sum_smul_proj (gmmS_hasFDerivAt β u x) (gmmS_pos β u x).ne')
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hS := (gmmS_pos β b.1 x).ne'
  have hW := (gmmW_pos β x).ne'
  unfold gmmg
  generalize gmmW β x = W at hW ⊢
  field_simp

private theorem gmmF_hasFDerivAt [Nonempty U] [Nonempty T] {β : ℝ} (hβ : β ≠ 0)
    (x : U × T → ℝ) : HasFDerivAt (gmmF β) (∑ b, gmmg β b x • PR b) x := by
  have h := HasFDerivAt.const_mul_sum_smul_proj
    (HasFDerivAt.log_sum_smul_proj (gmmW_hasFDerivAt β x) (gmmW_pos β x).ne') (-β⁻¹)
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  have hW := (gmmW_pos β x).ne'
  field_simp

private theorem gmmg_hasFDerivAt [DecidableEq U] [DecidableEq T] [Nonempty U] [Nonempty T]
    (β : ℝ) (a : U × T) (x : U × T → ℝ) : HasFDerivAt (gmmg β a) (∑ b, gmmH β a b x • PR b) x := by
  have hS := (gmmS_pos β a.1 x).ne'
  have hW := (gmmW_pos β x).ne'
  have h := ((hasFDerivAt_exp_mul_apply_sum_smul_proj β a x).mul_sum_smul_proj
    ((gmmS_hasFDerivAt β a.1 x).pow_two_sum_smul_proj.inv_sum_smul_proj (pow_ne_zero 2 hS))
    ).mul_sum_smul_proj ((gmmW_hasFDerivAt β x).inv_sum_smul_proj hW)
  have e : gmmg β a = fun y : U × T → ℝ =>
      Real.exp (β * y a) * ((gmmS β a.1 y) ^ 2)⁻¹ * (gmmW β y)⁻¹ := by funext y; rfl
  rw [e]
  refine h.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  congr 1
  unfold gmmH
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    unfold gmmg gmmq
    field_simp
    ring
  · rw [if_neg hab, if_neg (Ne.symm hab)]
    by_cases h1 : a.1 = b.1
    · rw [if_pos h1, if_pos h1.symm]
      obtain ⟨u, t⟩ := a
      obtain ⟨v, s⟩ := b
      simp only at h1
      subst h1
      simp only [gmmg, gmmq]
      field_simp
      ring
    · rw [if_neg h1, if_neg (Ne.symm h1)]
      simp only [gmmg]
      field_simp
      ring

private theorem gmmg_continuous [Nonempty U] [Nonempty T] (β : ℝ) (a : U × T) :
    Continuous (gmmg (T := T) β a) := by
  classical
  exact continuous_iff_continuousAt.2 fun x => (gmmg_hasFDerivAt β a x).continuousAt

private theorem gmmH_continuous [DecidableEq U] [DecidableEq T] [Nonempty U] [Nonempty T]
    (β : ℝ) (a b : U × T) : Continuous (gmmH β a b) := by
  have hq : Continuous (gmmq (T := T) β a b) := by
    unfold gmmq gmmS
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => (gmmS_pos β a.1 x).ne')
  have hg := gmmg_continuous (T := T) β a
  have hg' := gmmg_continuous (T := T) β b
  unfold gmmH
  split_ifs <;> fun_prop

end SmoothMinMax

section Quad

private theorem gmm_quad_of_rowsum {ι : Type*} [Fintype ι] (H Δ : ι → ι → ℝ)
    (hsym : ∀ i j, H i j = H j i) (hrow : ∀ i, ∑ j, H i j = 0) :
    ∑ i, ∑ j, Δ i j * H i j
      = -(1 / 2) * ∑ i, ∑ j, H i j * (Δ i i + Δ j j - Δ i j - Δ j i) := by
  have e1 : ∑ i, ∑ j, H i j * (Δ i i + Δ j j - Δ i j - Δ j i)
      = ∑ i, ∑ j, H i j * Δ i i + ∑ i, ∑ j, H i j * Δ j j
        - ∑ i, ∑ j, H i j * Δ i j - ∑ i, ∑ j, H i j * Δ j i := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e2 : ∑ i, ∑ j, H i j * Δ i i = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_mul, hrow, zero_mul]
  have e3 : ∑ i, ∑ j, H i j * Δ j j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, show ∑ i, H i j = ∑ i, H j i from
      Finset.sum_congr rfl fun i _ => hsym i j, hrow, zero_mul]
  have e4 : ∑ i, ∑ j, H i j * Δ j i = ∑ i, ∑ j, Δ i j * H i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]; ring
  have e5 : ∑ i, ∑ j, H i j * Δ i j = ∑ i, ∑ j, Δ i j * H i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, e2, e3, e4, e5]
  ring

variable {U T : Type*} [Fintype U] [Fintype T] [DecidableEq U] [DecidableEq T]
  [Nonempty U] [Nonempty T]

/-- The key sign lemma: the Hessian of the smooth min-max pairs nonnegatively with any
covariance difference whose increments grow inside blocks and shrink across blocks. -/
private theorem gmm_hess_nonneg {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) (Δ : U × T → U × T → ℝ)
    (hs : ∀ a b : U × T, a.1 = b.1 → 0 ≤ Δ a a + Δ b b - Δ a b - Δ b a)
    (hd : ∀ a b : U × T, a.1 ≠ b.1 → Δ a a + Δ b b - Δ a b - Δ b a ≤ 0) :
    0 ≤ ∑ a, ∑ b, Δ a b * gmmH β a b x := by
  rw [gmm_quad_of_rowsum (fun a b => gmmH β a b x) Δ (fun a b => gmmH_symm β a b x)
    (fun a => gmmH_rowsum β a x)]
  have : ∑ a, ∑ b, gmmH β a b x * (Δ a a + Δ b b - Δ a b - Δ b a) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      have : Δ a a + Δ a a - Δ a a - Δ a a = 0 := by ring
      rw [this, mul_zero]
    by_cases h1 : a.1 = b.1
    · have hH : gmmH β a b x ≤ 0 := by
        unfold gmmH
        rw [if_neg hab, if_pos h1]
        have g0 := gmmg_nonneg β a x
        have hq := gmmg_le_q β a b h1 x
        have q0 := gmmq_nonneg β a b x
        have : gmmg β a x * gmmg β b x ≤ gmmg β a x * gmmq β a b x :=
          mul_le_mul_of_nonneg_left hq g0
        have : 0 ≤ gmmg β a x * gmmq β a b x := mul_nonneg g0 q0
        nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg hH (hs a b h1)
    · have hH : 0 ≤ gmmH β a b x := by
        unfold gmmH
        rw [if_neg hab, if_neg h1]
        have := mul_nonneg (gmmg_nonneg β a x) (gmmg_nonneg β b x)
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hH (hd a b h1)
  nlinarith

end Quad

section Bounds

variable {U T : Type*} [Fintype U] [Fintype T] [Nonempty U] [Nonempty T]

omit [Fintype U] [Nonempty U] [Nonempty T] in
private theorem gmmS_le_card {β : ℝ} (hβ : 0 < β) (u : U) (x : U × T → ℝ) :
    gmmS β u x ≤ (Fintype.card T : ℝ) * Real.exp (β * ⨆ t, x (u, t)) := by
  have hb : BddAbove (Set.range fun t => x (u, t)) := (Set.finite_range _).bddAbove
  have : gmmS β u x ≤ ∑ _t : T, Real.exp (β * ⨆ t, x (u, t)) :=
    Finset.sum_le_sum fun t _ => Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (le_ciSup hb t) hβ.le)
  simpa using this

omit [Fintype U] [Nonempty U] in
private theorem gmmS_ge_max (β : ℝ) (u : U) (x : U × T → ℝ) :
    Real.exp (β * ⨆ t, x (u, t)) ≤ gmmS β u x := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := fun t => x (u, t))
  rw [← ht0]
  exact gmm_exp_le_S β u t0 x

private theorem gmmF_ge {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) :
    (⨅ u, ⨆ t, x (u, t)) - Real.log (Fintype.card U) / β ≤ gmmF β x := by
  set m := ⨅ u, ⨆ t, x (u, t) with hm
  have hmu : ∀ u, m ≤ ⨆ t, x (u, t) := fun u => ciInf_le (Set.finite_range _).bddBelow u
  have hW : gmmW β x ≤ (Fintype.card U : ℝ) * Real.exp (-(β * m)) := by
    have : gmmW β x ≤ ∑ _u : U, Real.exp (-(β * m)) := by
      refine Finset.sum_le_sum fun u _ => ?_
      calc (gmmS β u x)⁻¹ ≤ (Real.exp (β * ⨆ t, x (u, t)))⁻¹ :=
            inv_anti₀ (Real.exp_pos _) (gmmS_ge_max β u x)
        _ = Real.exp (-(β * ⨆ t, x (u, t))) := (Real.exp_neg _).symm
        _ ≤ Real.exp (-(β * m)) := Real.exp_le_exp.2 (by nlinarith [hmu u])
    simpa using this
  have hc : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hl := Real.log_le_log (gmmW_pos β x) hW
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have h2 : β⁻¹ * Real.log (gmmW β x) ≤ β⁻¹ * (Real.log (Fintype.card U) + -(β * m)) :=
    mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hβ.le)
  have e : β⁻¹ * (Real.log (Fintype.card U) + -(β * m)) = Real.log (Fintype.card U) / β - m := by
    field_simp
    ring
  unfold gmmF
  linarith

private theorem gmmF_le {β : ℝ} (hβ : 0 < β) (x : U × T → ℝ) :
    gmmF β x ≤ (⨅ u, ⨆ t, x (u, t)) + Real.log (Fintype.card T) / β := by
  set m := ⨅ u, ⨆ t, x (u, t) with hm
  obtain ⟨u0, hu0⟩ := exists_eq_ciInf_of_finite (f := fun u => ⨆ t, x (u, t))
  have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hW : ((Fintype.card T : ℝ) * Real.exp (β * m))⁻¹ ≤ gmmW β x := by
    refine le_trans ?_ (gmm_Sinv_le_W β u0 x)
    refine inv_anti₀ (gmmS_pos β u0 x) ?_
    rw [hm, ← hu0]
    exact gmmS_le_card hβ u0 x
  have hl := Real.log_le_log (by positivity) hW
  rw [Real.log_inv, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have h2 : β⁻¹ * (-(Real.log (Fintype.card T) + β * m)) ≤ β⁻¹ * Real.log (gmmW β x) :=
    mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hβ.le)
  have e : β⁻¹ * (-(Real.log (Fintype.card T) + β * m)) = -(Real.log (Fintype.card T) / β + m) := by
    field_simp
  unfold gmmF
  linarith

end Bounds

section Comparison

variable {T U : Type*} [Finite T] [Finite U]

private theorem abs_iSup_le_norm [Fintype T] (x : T → ℝ) : |⨆ t, x t| ≤ ‖x‖ := by
  rcases isEmpty_or_nonempty T with hT | hT
  · rw [Real.iSup_of_isEmpty, abs_zero]; exact norm_nonneg _
  obtain ⟨t, ht⟩ := exists_eq_ciSup_of_finite (f := x)
  rw [← ht, ← Real.norm_eq_abs]
  exact norm_le_pi_norm x t

private theorem abs_iInf_iSup_le_norm [Fintype T] [Fintype U] (x : U × T → ℝ) :
    |⨅ u, ⨆ t, x (u, t)| ≤ ‖x‖ := by
  rcases isEmpty_or_nonempty U with hU | hU
  · rw [Real.iInf_of_isEmpty, abs_zero]; exact norm_nonneg _
  obtain ⟨u, hu⟩ := exists_eq_ciInf_of_finite (f := fun u => ⨆ t, x (u, t))
  rw [← hu]
  refine (abs_iSup_le_norm _).trans ((pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun t => ?_)
  exact norm_le_pi_norm x (u, t)

/-- The maximum of a finite Gaussian family is integrable. -/
theorem integrable_iSup_of_hasGaussianLaw {X : T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) : Integrable (fun ω => ⨆ t, X t ω) μ := by
  have := Fintype.ofFinite T
  have hP := hX.isProbabilityMeasure
  refine Integrable.mono' hX.integrable.norm
    ((Measurable.iSup fun t => measurable_pi_apply t).comp_aemeasurable
      hX.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_iSup_le_norm (fun t => X t ω)

/-- The min-max `min_u max_t X u t` of a finite Gaussian family on `U × T` is integrable. -/
theorem integrable_iInf_iSup_of_hasGaussianLaw {X : U → T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ) :
    Integrable (fun ω => ⨅ u, ⨆ t, X u t ω) μ := by
  have := Fintype.ofFinite T
  have := Fintype.ofFinite U
  have hP := hX.isProbabilityMeasure
  have hm : Measurable fun x : U × T → ℝ => ⨅ u, ⨆ t, x (u, t) :=
    Measurable.iInf fun u => Measurable.iSup fun t => measurable_pi_apply _
  refine Integrable.mono' hX.integrable.norm
    (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_iInf_iSup_le_norm (fun p : U × T => X p.1 p.2 ω)

omit [Finite T] in
private theorem integral_sub_sq_eq {X : T → Ω → ℝ} (hXm : ∀ t, MemLp (X t) 2 μ) (i j : T) :
    ∫ ω, (X i ω - X j ω) ^ 2 ∂μ = ∫ ω, X i ω * X i ω ∂μ + ∫ ω, X j ω * X j ω ∂μ
      - ∫ ω, X i ω * X j ω ∂μ - ∫ ω, X j ω * X i ω ∂μ := by
  have i1 : Integrable (fun ω => X i ω * X i ω) μ := (hXm i).integrable_mul (hXm i)
  have i2 : Integrable (fun ω => X j ω * X j ω) μ := (hXm j).integrable_mul (hXm j)
  have i3 : Integrable (fun ω => X i ω * X j ω) μ := (hXm i).integrable_mul (hXm j)
  have i4 : Integrable (fun ω => X j ω * X i ω) μ := (hXm j).integrable_mul (hXm i)
  have e : (fun ω => (X i ω - X j ω) ^ 2) = fun ω => X i ω * X i ω + X j ω * X j ω
      - X i ω * X j ω - X j ω * X i ω := by funext ω; ring
  rw [e, integral_sub ((i1.fun_add i2).sub' i3) i4, integral_sub (i1.fun_add i2) i3,
    integral_add i1 i2]

omit [Finite T] [Finite U] in
/-- The soft min-max is `C²` with Hessian bounded by `|U × T|² 4β`. -/
private theorem contDiff_two_gmmF [Fintype T] [Fintype U] [Nonempty T] [Nonempty U] {β : ℝ}
    (hβ : 0 < β) :
    ContDiff ℝ 2 (gmmF (U := U) (T := T) β) ∧ ∀ x,
      ‖iteratedFDeriv ℝ 2 (gmmF (U := U) (T := T) β) x‖
        ≤ Fintype.card (U × T) ^ 2 * (4 * β) := by
  classical
  exact ⟨contDiff_two_of_hasFDerivAt_sum_smul_proj (gmmF_hasFDerivAt hβ.ne') (gmmg_hasFDerivAt β)
    (gmmH_continuous β),
   norm_iteratedFDeriv_two_le_of_hasFDerivAt_sum_smul_proj (gmmF_hasFDerivAt hβ.ne')
    (gmmg_hasFDerivAt β) (by positivity) (gmmH_abs_le hβ)⟩

/-- The soft min-max comparison at inverse temperature `β`, from the interpolation
inequality. -/
private theorem integral_gmmF_le [Fintype T] [Fintype U] [Nonempty T] [Nonempty U]
    {X : Ω → U × T → ℝ} {Y : Ω' → U × T → ℝ}
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hX0 : ∀ a, ∫ ω, X ω a ∂μ = 0) (hY0 : ∀ a, ∫ ω, Y ω a ∂ν = 0)
    (hs : ∀ a b : U × T, a.1 = b.1 →
      ∫ ω, (X ω a - X ω b) ^ 2 ∂μ ≤ ∫ ω, (Y ω a - Y ω b) ^ 2 ∂ν)
    (hd : ∀ a b : U × T, a.1 ≠ b.1 →
      ∫ ω, (Y ω a - Y ω b) ^ 2 ∂ν ≤ ∫ ω, (X ω a - X ω b) ^ 2 ∂μ) {β : ℝ} (hβ : 0 < β) :
    ∫ ω, gmmF β (X ω) ∂μ ≤ ∫ ω, gmmF β (Y ω) ∂ν := by
  classical
  have hXm : ∀ a, MemLp (fun ω => X ω a) 2 μ := fun a =>
    (hX.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : U × T => ℝ) a)).memLp_two
  have hYm : ∀ a, MemLp (fun ω => Y ω a) 2 ν := fun a =>
    (hY.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : U × T => ℝ) a)).memLp_two
  set Δ : U × T → U × T → ℝ := fun a b =>
    ∫ ω, Y ω a * Y ω b ∂ν - ∫ ω, X ω a * X ω b ∂μ with hΔ
  have he : ∀ a b : U × T, Δ a a + Δ b b - Δ a b - Δ b a
      = ∫ ω, (Y ω a - Y ω b) ^ 2 ∂ν - ∫ ω, (X ω a - X ω b) ^ 2 ∂μ := by
    intro a b
    rw [integral_sub_sq_eq (X := fun a ω => X ω a) hXm a b,
      integral_sub_sq_eq (X := fun a ω => Y ω a) hYm a b, hΔ]
    ring
  obtain ⟨hF, hF2⟩ := contDiff_two_gmmF (U := U) (T := T) hβ
  refine integral_comp_le_integral_comp_of_hasGaussianLaw hX hY hX0 hY0 hF hF2 fun x => ?_
  have h := gmm_hess_nonneg hβ x Δ (fun a b hab => by rw [he]; linarith [hs a b hab])
    (fun a b hab => by rw [he]; linarith [hd a b hab])
  refine h.trans_eq (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  rw [iteratedFDeriv_two_apply_pair, fderiv_fderiv_apply_of_hasFDerivAt_sum_smul_proj
    (gmmF_hasFDerivAt hβ.ne') (gmmg_hasFDerivAt β), gmmH_symm]
  simp [Pi.single_apply, hΔ]

/-- Gordon's inequality, stated before the Sudakov–Fernique inequality, which is its case `U`
a point. -/
private theorem integral_iInf_iSup_le_aux {X : U → T → Ω → ℝ} {Y : U → T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) ν)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μ = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂ν = 0)
    (hsame : ∀ u t s, ∫ ω, (X u t ω - X u s ω) ^ 2 ∂μ ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂ν)
    (hdiff : ∀ u u' t s, u ≠ u' →
      ∫ ω, (Y u t ω - Y u' s ω) ^ 2 ∂ν ≤ ∫ ω, (X u t ω - X u' s ω) ^ 2 ∂μ) :
    ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ ≤ ∫ ω, ⨅ u, ⨆ t, Y u t ω ∂ν := by
  have := Fintype.ofFinite T
  have := Fintype.ofFinite U
  rcases isEmpty_or_nonempty U with hU | hU
  · simp
  rcases isEmpty_or_nonempty T with hT | hT
  · simp
  classical
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  have hIX := integrable_iInf_iSup_of_hasGaussianLaw hX
  have hIY := integrable_iInf_iSup_of_hasGaussianLaw hY
  set Lg := Real.log (Fintype.card U) + Real.log (Fintype.card T) with hLg
  have key : ∀ β : ℝ, 0 < β → ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ
      ≤ ∫ ω, ⨅ u, ⨆ t, Y u t ω ∂ν + Lg / β := by
    intro β hβ
    have hc := integral_gmmF_le hX hY (fun a => hX0 a.1 a.2) (fun a => hY0 a.1 a.2)
      (fun a b hab => by obtain ⟨u, t⟩ := a; obtain ⟨v, s⟩ := b; subst hab; exact hsame u t s)
      (fun a b hab => hdiff a.1 b.1 a.2 b.2 hab) hβ
    obtain ⟨hF, hF2⟩ := contDiff_two_gmmF (U := U) (T := T) hβ
    have hFX := integrable_comp_of_hasGaussianLaw_of_contDiff_two hX hF hF2
    have hFY := integrable_comp_of_hasGaussianLaw_of_contDiff_two hY hF hF2
    have h1 : ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ
        ≤ ∫ ω, (gmmF β (fun p : U × T => X p.1 p.2 ω) + Real.log (Fintype.card U) / β) ∂μ :=
      integral_mono hIX (hFX.add (integrable_const _)) fun ω => by
        have := gmmF_ge hβ (fun p : U × T => X p.1 p.2 ω)
        simp only at this ⊢
        linarith
    have h2 : ∫ ω, gmmF β (fun p : U × T => Y p.1 p.2 ω) ∂ν
        ≤ ∫ ω, ((⨅ u, ⨆ t, Y u t ω) + Real.log (Fintype.card T) / β) ∂ν :=
      integral_mono hFY (hIY.add (integrable_const _)) fun ω => by
        have := gmmF_le hβ (fun p : U × T => Y p.1 p.2 ω)
        simp only at this ⊢
        linarith
    rw [integral_add hIY (integrable_const _), integral_const, probReal_univ, one_smul] at h2
    rw [integral_add hFX (integrable_const _), integral_const, probReal_univ, one_smul] at h1
    rw [hLg, add_div]
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hL0 : 0 ≤ Lg := add_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos))
  have hβ : 0 < (Lg + 1) / ε := div_pos (by linarith) hε
  refine (key _ hβ).trans ?_
  gcongr
  rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- **The Sudakov–Fernique inequality**: for centred finite Gaussian families `X`, `Y` with
`E (X s - X t)² ≤ E (Y s - Y t)²` for all `s`, `t`, `E max X ≤ E max Y`.
[Vershynin2018, Theorem 7.2.11]; no equal-variance hypothesis (unlike Slepian's inequality), and
the two families on different probability spaces.
Result: sudakov-fernique -/
theorem integral_iSup_le_integral_iSup_of_hasGaussianLaw {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) (hY : HasGaussianLaw (fun ω t => Y t ω) ν)
    (hX0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂μ ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂ν) :
    ∫ ω, ⨆ t, X t ω ∂μ ≤ ∫ ω, ⨆ t, Y t ω ∂ν := by
  have := Fintype.ofFinite T
  let L : (T → ℝ) →L[ℝ] (Unit × T → ℝ) := ContinuousLinearMap.pi fun p =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) p.2
  have h := integral_iInf_iSup_le_aux (X := fun (_ : Unit) t ω => X t ω)
    (Y := fun (_ : Unit) t ω => Y t ω) (hX.map_fun L) (hY.map_fun L) (fun _ t => hX0 t)
    (fun _ t => hY0 t) (fun _ t s => hinc t s)
    (fun u u' _ _ h => absurd (Subsingleton.elim u u') h)
  simpa only [ciInf_const] using h

/-- **Gordon's min-max inequality**: for centred finite Gaussian families on `U × T` whose
increments are smaller for `X` within a block (`u` fixed) and larger for `X` across blocks,
`E min_u max_t X ≤ E min_u max_t Y`.
[Gordon1985]; [Vershynin2018, Exercise 7.2.14]; stated there with equal variances and as a tail
comparison, here the expectation form from increments alone, with the two families on different
probability spaces.
Result: gordon-inequality -/
theorem integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw
    {X : U → T → Ω → ℝ} {Y : U → T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) ν)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μ = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂ν = 0)
    (hsame : ∀ u t s, ∫ ω, (X u t ω - X u s ω) ^ 2 ∂μ ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂ν)
    (hdiff : ∀ u u' t s, u ≠ u' →
      ∫ ω, (Y u t ω - Y u' s ω) ^ 2 ∂ν ≤ ∫ ω, (X u t ω - X u' s ω) ^ 2 ∂μ) :
    ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ ≤ ∫ ω, ⨅ u, ⨆ t, Y u t ω ∂ν :=
  integral_iInf_iSup_le_aux hX hY hX0 hY0 hsame hdiff

end Comparison

end NLAlib
