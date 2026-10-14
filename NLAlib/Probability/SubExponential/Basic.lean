/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-exponential random variables

`NLAlib.HasSubexponentialMGF X v b μ` says that the moment generating function of `X` is at most
`exp (v l² / 2)` on the window `b |l| < 1`, with `exp (l X)` integrable there. With `b = 0` the
window is all of `ℝ` and this is Mathlib's `HasSubgaussianMGF X v μ`. Centred squares of
sub-Gaussian variables are sub-exponential (`NLAlib/Probability/SubGaussian/Square.lean`), and
the tail of a sum of independent sub-exponential variables is Bernstein's inequality
(`NLAlib/Probability/SubExponential/Tail.lean`).

## Main definitions

* `NLAlib.HasSubexponentialMGF X v b μ`: variance proxy `v`, scale `b`.

## Main results

* `NLAlib.HasSubexponentialMGF.add`: the sum of two sub-exponential variables, without
  independence.
* `NLAlib.HasSubexponentialMGF.sum_of_iIndepFun`, `.sum_const_mul_of_iIndepFun`: sums and
  weighted sums of independent sub-exponential variables.
* `NLAlib.hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`: scale `0` is the sub-Gaussian case.

## References

* [M. J. Wainwright, *High-Dimensional Statistics*][Wainwright2019], §2.1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

/-- `X` has a sub-exponential moment generating function with variance proxy `v` and scale `b`
under `μ`: for every `l` with `b * |l| < 1`, `exp (l * X)` is integrable and
`mgf X μ l ≤ exp (v * l ^ 2 / 2)` ([Wainwright2019], Definition 2.7, with `ν² = v`, `α = b`).
With `b = 0` the window is all of `ℝ` and this is `HasSubgaussianMGF X v μ`
(`hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`). -/
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- `exp (l * X)` is integrable on the window. -/
  integrable_exp_mul : ∀ l : ℝ, b * |l| < 1 → Integrable (fun ω => rexp (l * X ω)) μ
  /-- The moment generating function is at most `exp (v * l ^ 2 / 2)` on the window. -/
  mgf_le : ∀ l : ℝ, b * |l| < 1 → mgf X μ l ≤ rexp (v * l ^ 2 / 2)

namespace HasSubexponentialMGF

/-- The window `b * |l| < 1` is an open neighbourhood of `0`. -/
private lemma isOpen_window (b : ℝ≥0) : IsOpen {l : ℝ | (b : ℝ) * |l| < 1} :=
  isOpen_lt (by fun_prop) continuous_const

private lemma zero_mem_interior_integrableExpSet (h : HasSubexponentialMGF X v b μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  have hsub : {l : ℝ | (b : ℝ) * |l| < 1} ⊆ integrableExpSet X μ :=
    fun l hl => h.integrable_exp_mul l hl
  refine interior_mono hsub ?_
  rw [(isOpen_window b).interior_eq]
  simp

/-- A sub-exponential variable is almost everywhere measurable. -/
theorem aemeasurable (h : HasSubexponentialMGF X v b μ) : AEMeasurable X μ := by
  exact aemeasurable_of_mem_interior_integrableExpSet (zero_mem_interior_integrableExpSet h)

/-- A sub-exponential variable lives on a measure of total mass at most `1`. -/
theorem measure_univ_le_one (h : HasSubexponentialMGF X v b μ) : μ Set.univ ≤ 1 := by
  have : IsFiniteMeasure μ := by
    simpa [integrable_const_iff] using h.integrable_exp_mul 0 (by simp)
  suffices μ.real Set.univ ≤ 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h.mgf_le 0 (by simp)

/-- A sub-exponential variable lives on a finite measure. -/
theorem isFiniteMeasure (h : HasSubexponentialMGF X v b μ) : IsFiniteMeasure μ := by
  simpa [integrable_const_iff] using h.integrable_exp_mul 0 (by simp)

/-- A sub-exponential variable has moments of every order. -/
theorem memLp (h : HasSubexponentialMGF X v b μ) (p : ℝ≥0) : MemLp X p μ := by
  exact memLp_of_mem_interior_integrableExpSet (zero_mem_interior_integrableExpSet h) p

/-- A sub-exponential variable is integrable. -/
theorem integrable (h : HasSubexponentialMGF X v b μ) : Integrable X μ := by
  exact integrable_of_mem_interior_integrableExpSet (zero_mem_interior_integrableExpSet h)

/-- The cumulant generating function on the window. -/
theorem cgf_le (h : HasSubexponentialMGF X v b μ) {l : ℝ} (hl : b * |l| < 1) :
    cgf X μ l ≤ v * l ^ 2 / 2 := by
  calc cgf X μ l
  _ = log (mgf X μ l) := rfl
  _ ≤ log (rexp (v * l ^ 2 / 2)) := by
    by_cases h0 : μ = 0
    · rw [h0, mgf_zero_measure, Pi.zero_apply, log_zero, log_exp]
      positivity
    gcongr
    · exact mgf_pos' h0 (h.integrable_exp_mul l hl)
    · exact h.mgf_le l hl
  _ = v * l ^ 2 / 2 := log_exp _

/-- The property depends only on the almost-everywhere class of the variable. -/
theorem congr {Y : Ω → ℝ} (h : HasSubexponentialMGF X v b μ) (hXY : X =ᵐ[μ] Y) :
    HasSubexponentialMGF Y v b μ := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · refine (h.integrable_exp_mul l hl).congr ?_
    filter_upwards [hXY] with ω hω
    rw [hω]
  · rw [← mgf_congr hXY]
    exact h.mgf_le l hl

/-- A larger variance proxy and a larger scale. -/
theorem mono (h : HasSubexponentialMGF X v b μ) {v' b' : ℝ≥0} (hv : v ≤ v') (hb : b ≤ b') :
    HasSubexponentialMGF X v' b' μ := by
  have hb' : (b : ℝ) ≤ b' := by exact_mod_cast hb
  have hv' : (v : ℝ) ≤ v' := by exact_mod_cast hv
  have hw : ∀ l : ℝ, (b' : ℝ) * |l| < 1 → (b : ℝ) * |l| < 1 := fun l hl =>
    (mul_le_mul_of_nonneg_right hb' (abs_nonneg l)).trans_lt hl
  refine ⟨fun l hl => h.integrable_exp_mul l (hw l hl), fun l hl => ?_⟩
  refine (h.mgf_le l (hw l hl)).trans ?_
  gcongr

/-- The negative of a sub-exponential variable. -/
theorem neg (h : HasSubexponentialMGF X v b μ) : HasSubexponentialMGF (fun ω => -X ω) v b μ := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · have := h.integrable_exp_mul (-l) (by rwa [abs_neg])
    simpa only [neg_mul, mul_neg] using this
  · rw [show (fun ω => -X ω) = -X from rfl, mgf_neg]
    have := h.mgf_le (-l) (by rwa [abs_neg])
    rwa [neg_sq] at this

/-- A scalar multiple of a sub-exponential variable. -/
theorem const_mul (h : HasSubexponentialMGF X v b μ) (r : ℝ) :
    HasSubexponentialMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * v) (‖r‖₊ * b) μ := by
  have hw : ∀ l : ℝ, ((‖r‖₊ * b : ℝ≥0) : ℝ) * |l| < 1 → (b : ℝ) * |l * r| < 1 := by
    intro l hl
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs] at hl
    rw [abs_mul]
    calc (b : ℝ) * (|l| * |r|) = |r| * b * |l| := by ring
    _ < 1 := hl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (l * r) (hw l hl)
  · rw [mgf_const_mul, mul_comm r l]
    refine (h.mgf_le (l * r) (hw l hl)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
    ring

/-- The sum of two independent sub-exponential variables. -/
theorem add_of_indepFun {Y : Ω → ℝ} {v' b' : ℝ≥0} (hX : HasSubexponentialMGF X v b μ)
    (hY : HasSubexponentialMGF Y v' b' μ) (hXY : IndepFun X Y μ) :
    HasSubexponentialMGF (fun ω => X ω + Y ω) (v + v') (max b b') μ := by
  have hw : ∀ l : ℝ, ((max b b' : ℝ≥0) : ℝ) * |l| < 1 →
      (b : ℝ) * |l| < 1 ∧ (b' : ℝ) * |l| < 1 := by
    intro l hl
    rw [NNReal.coe_max] at hl
    exact ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg l)).trans_lt hl,
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg l)).trans_lt hl⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · exact hXY.integrable_exp_mul_add (hX.integrable_exp_mul l (hw l hl).1)
      (hY.integrable_exp_mul l (hw l hl).2)
  · calc mgf (fun ω => X ω + Y ω) μ l
    _ = mgf X μ l * mgf Y μ l :=
      hXY.mgf_add (hX.integrable_exp_mul l (hw l hl).1).1 (hY.integrable_exp_mul l (hw l hl).2).1
    _ ≤ rexp (v * l ^ 2 / 2) * rexp (v' * l ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX.mgf_le l (hw l hl).1
      · exact hY.mgf_le l (hw l hl).2
    _ = rexp (((v + v' : ℝ≥0) : ℝ) * l ^ 2 / 2) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring

/-- The sum of two sub-exponential variables, with **no independence assumption**: for Hölder
conjugate `p` and `q` (`1 / p + 1 / q = 1`), `X + Y` has variance proxy `max (p² v) (q² v')` and
scale `max (p b) (q b')`. The proof is convexity of `exp` with weights `1 / p` and `1 / q`,
`exp (l (X + Y)) ≤ exp (p l X) / p + exp (q l Y) / q`. For independent variables
`add_of_indepFun` gives the better proxy `v + v'`. -/
theorem add {Y : Ω → ℝ} {v' b' : ℝ≥0} (hX : HasSubexponentialMGF X v b μ)
    (hY : HasSubexponentialMGF Y v' b' μ) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    HasSubexponentialMGF (fun ω => X ω + Y ω) (max (p ^ 2 * v) (q ^ 2 * v'))
      (max (p * b) (q * b')) μ := by
  have hp : (0 : ℝ) < p := hpq.pos
  have hq : (0 : ℝ) < q := hpq.symm.pos
  have hpq' : 1 / (p : ℝ) + 1 / q = 1 := by
    have := congrArg ((↑) : ℝ≥0 → ℝ) hpq.inv_add_inv_eq_inv
    push_cast at this
    simpa only [one_div, inv_one] using this
  set V : ℝ≥0 := max (p ^ 2 * v) (q ^ 2 * v')
  set B : ℝ≥0 := max (p * b) (q * b')
  have hv₁ : (p : ℝ) ^ 2 * v ≤ V := by exact_mod_cast le_max_left _ _
  have hv₂ : (q : ℝ) ^ 2 * v' ≤ V := by exact_mod_cast le_max_right _ _
  have hb₁ : (p : ℝ) * b ≤ B := by exact_mod_cast le_max_left _ _
  have hb₂ : (q : ℝ) * b' ≤ B := by exact_mod_cast le_max_right _ _
  have hw₁ : ∀ l : ℝ, (B : ℝ) * |l| < 1 → (b : ℝ) * |p * l| < 1 := fun l hl => by
    rw [abs_mul, abs_of_pos hp]
    nlinarith [mul_le_mul_of_nonneg_right hb₁ (abs_nonneg l)]
  have hw₂ : ∀ l : ℝ, (B : ℝ) * |l| < 1 → (b' : ℝ) * |q * l| < 1 := fun l hl => by
    rw [abs_mul, abs_of_pos hq]
    nlinarith [mul_le_mul_of_nonneg_right hb₂ (abs_nonneg l)]
  have hpt : ∀ (l : ℝ) ω, rexp (l * (X ω + Y ω)) ≤
      1 / p * rexp (p * l * X ω) + 1 / q * rexp (q * l * Y ω) := by
    intro l ω
    have := convexOn_exp.2 (Set.mem_univ ((p : ℝ) * l * X ω)) (Set.mem_univ ((q : ℝ) * l * Y ω))
      (by positivity : (0 : ℝ) ≤ 1 / p) (by positivity : (0 : ℝ) ≤ 1 / q) hpq'
    have e₁ : 1 / (p : ℝ) * (p * l * X ω) = l * X ω := by field_simp
    have e₂ : 1 / (q : ℝ) * (q * l * Y ω) = l * Y ω := by field_simp
    simp only [smul_eq_mul, e₁, e₂] at this
    rwa [mul_add]
  have hm : ∀ l : ℝ, AEStronglyMeasurable (fun ω => rexp (l * (X ω + Y ω))) μ := fun l =>
    (measurable_exp.comp_aemeasurable
      ((hX.aemeasurable.add hY.aemeasurable).const_mul l)).aestronglyMeasurable
  have hint : ∀ l : ℝ, (B : ℝ) * |l| < 1 →
      Integrable (fun ω => 1 / p * rexp (p * l * X ω) + 1 / q * rexp (q * l * Y ω)) μ :=
    fun l hl => ((hX.integrable_exp_mul (p * l) (hw₁ l hl)).const_mul _).add
      ((hY.integrable_exp_mul (q * l) (hw₂ l hl)).const_mul _)
  have hint' : ∀ l : ℝ, (B : ℝ) * |l| < 1 → Integrable (fun ω => rexp (l * (X ω + Y ω))) μ :=
    fun l hl => (hint l hl).mono' (hm l) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact hpt l ω)
  refine ⟨hint', fun l hl => ?_⟩
  calc mgf (fun ω => X ω + Y ω) μ l
      ≤ ∫ ω, (1 / p * rexp (p * l * X ω) + 1 / q * rexp (q * l * Y ω)) ∂μ :=
        integral_mono (hint' l hl) (hint l hl) (hpt l)
    _ = 1 / p * mgf X μ (p * l) + 1 / q * mgf Y μ (q * l) := by
        rw [integral_add ((hX.integrable_exp_mul (p * l) (hw₁ l hl)).const_mul _)
          ((hY.integrable_exp_mul (q * l) (hw₂ l hl)).const_mul _), integral_const_mul,
          integral_const_mul]
        rfl
    _ ≤ 1 / p * rexp (v * (p * l) ^ 2 / 2) + 1 / q * rexp (v' * (q * l) ^ 2 / 2) := by
        gcongr
        · exact hX.mgf_le _ (hw₁ l hl)
        · exact hY.mgf_le _ (hw₂ l hl)
    _ ≤ 1 / p * rexp (V * l ^ 2 / 2) + 1 / q * rexp (V * l ^ 2 / 2) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
          (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
        · nlinarith [mul_le_mul_of_nonneg_right hv₁ (sq_nonneg l)]
        · nlinarith [mul_le_mul_of_nonneg_right hv₂ (sq_nonneg l)]
    _ = rexp (V * l ^ 2 / 2) := by rw [← add_mul, hpq', one_mul]

private lemma sum_of_iIndepFun_of_forall_aemeasurable {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ) {v b : ι → ℝ≥0}
    {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) (s.sup b) μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun l _ => ?_, fun l _ => ?_⟩
    · simp
    · simp [mgf]
  | insert i s his ih =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetSum_of_notMem₀ h_meas his).symm
    rw [Finset.sup_insert]
    refine add_of_indepFun (h _ (Finset.mem_insert_self _ _))
      (ih fun j hj => h _ (Finset.mem_insert_of_mem hj)) ?_
    convert h_indep'
    rw [Finset.sum_apply]

/-- The sum of independent sub-exponential variables: the variance proxies add and the scale is
the largest scale. -/
theorem sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {v b : ι → ℝ≥0}
    {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) (s.sup b) μ := by
  have hs : HasSubexponentialMGF (fun ω => ∑ i : s, X i ω) (∑ i : s, v i)
      (Finset.univ.sup fun i : s => b i) μ :=
    sum_of_iIndepFun_of_forall_aemeasurable (h_indep.precomp Subtype.val_injective)
      (fun i => (h i i.2).aemeasurable) (fun i _ => h i i.2)
  rw [Finset.sum_coe_sort, Finset.univ_eq_attach, Finset.sup_attach] at hs
  exact hs.congr (ae_of_all _ fun ω => Finset.sum_attach s (fun i => X i ω))

/-- A weighted sum of independent sub-exponential variables. -/
theorem sum_const_mul_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    (a : ι → ℝ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * v i)
      (s.sup fun i => ‖a i‖₊ * b i) μ := by
  have hY : iIndepFun (fun i ω => a i * X i ω) μ :=
    h_indep.comp (fun i x => a i * x) (fun i => by fun_prop)
  exact sum_of_iIndepFun hY fun i hi => (h i hi).const_mul (a i)

/-- A sub-exponential variable has mean zero under a probability measure. -/
theorem integral_eq_zero [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X v b μ) :
    ∫ ω, X ω ∂μ = 0 := by
  have hm : HasDerivAt (mgf X μ) (∫ ω, X ω ∂μ) 0 := by
    simpa using hasDerivAt_mgf (zero_mem_interior_integrableExpSet h)
  have hg : HasDerivAt (fun l : ℝ => rexp (v * l ^ 2 / 2)) 0 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (v : ℝ)).div_const 2).exp
  have hmax : IsLocalMax (fun l => mgf X μ l - rexp (v * l ^ 2 / 2)) 0 := by
    refine Filter.mem_of_superset ((isOpen_window b).mem_nhds (by simp)) fun l hl => ?_
    have := h.mgf_le l hl
    simp only [Set.mem_ofPred_eq, mgf_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_div, exp_zero, sub_self]
    linarith
  simpa using hmax.hasDerivAt_eq_zero (hm.sub hg)

end HasSubexponentialMGF

/-- A sub-Gaussian variable is sub-exponential with scale `0`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) : HasSubexponentialMGF X c 0 μ := by
  exact ⟨fun l _ => h.integrable_exp_mul l, fun l _ => h.mgf_le l⟩

/-- Scale `0` is the sub-Gaussian case. -/
theorem hasSubexponentialMGF_zero_iff_hasSubgaussianMGF :
    HasSubexponentialMGF X v 0 μ ↔ HasSubgaussianMGF X v μ := by
  refine ⟨fun h => ⟨fun l => h.integrable_exp_mul l (by simp), fun l => h.mgf_le l (by simp)⟩,
    fun h => h.hasSubexponentialMGF⟩

end NLAlib
