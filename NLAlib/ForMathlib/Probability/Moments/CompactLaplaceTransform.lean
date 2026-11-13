/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Laplace transforms of compactly supported finite measures

Weak compactness, atomic measures and compact-support differentiation supply a common interface
for scalar Laplace transforms. Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `MeasureTheory.IsCompactExpRepresentation.iteratedDeriv_eq_integral`.
-/
@[expose] public section

section

open MeasureTheory Filter Set Topology

open scoped NNReal

namespace MeasureTheory

/-- Pointwise limits of integrals against a family of continuous functions on a compact
space retain a single positive finite representing measure, provided the approximating
measures have a common mass bound. The index filter is arbitrary and nontrivial. -/
theorem exists_finiteMeasure_integral_eq_of_tendsto
    {X T I : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [BorelSpace X] [CompactSpace X] {l : Filter I} [l.NeBot]
    (K : T → C(X, ℝ)) (C : ℝ≥0) (F : I → T → ℝ) (f : T → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure X,
      μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure X, μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = f t := by
  let L : FiniteMeasure X → T → ℝ := fun μ t => ∫ x, K t x ∂μ
  have hL : Continuous L := continuous_pi fun t =>
    FiniteMeasure.continuous_integral_continuousMap (K t)
  have hc : IsCompact (L '' {μ : FiniteMeasure X | μ.mass ≤ C}) :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X C).image hL
  have hf : f ∈ L '' {μ : FiniteMeasure X | μ.mass ≤ C} := by
    apply hc.isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hlim)
    filter_upwards [hrep] with i hi
    obtain ⟨μ, hμ, heq⟩ := hi
    exact ⟨μ, hμ, funext heq⟩
  obtain ⟨μ, hμ, heq⟩ := hf
  exact ⟨μ, hμ, fun t => congrFun heq t⟩

/-- A pointwise limit of exponential transforms of positive finite measures on a common
compact interval is again an exponential transform on that interval, under a common mass
bound. This is the measure-compactness part of the repeated-eigenvalue reduction in Stahl's
BMV theorem; the full contour representation is a separate theorem. Empty intervals and
zero measures are included. -/
private theorem exists_finiteMeasure_exp_mul_eq_of_tendsto_of_mass_le
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ) (C : ℝ≥0)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = f t := by
  let K : ℝ → C(Icc a b, ℝ) := fun t =>
    ⟨fun x => Real.exp (t * (x : ℝ)), by fun_prop⟩
  have hrep' : ∀ᶠ i in l, ∃ μ : FiniteMeasure (Icc a b),
      μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = F i t := by
    filter_upwards [hrep] with i hi
    obtain ⟨μ, hmass, hsupp, hμ⟩ := hi
    refine ⟨μ.comap Subtype.val, (FiniteMeasure.mass_comap_le _ _).trans hmass, ?_⟩
    intro t
    change ∫ x : Icc a b, Real.exp (t * (x : ℝ))
      ∂(Measure.comap Subtype.val (μ : Measure ℝ)) = F i t
    rw [integral_subtype_comap (μ := (μ : Measure ℝ)) (s := Icc a b)
      measurableSet_Icc (fun x : ℝ => Real.exp (t * x)),
      Measure.restrict_eq_self_of_ae_mem hsupp, hμ]
  obtain ⟨μ, hmass, hμ⟩ :=
    exists_finiteMeasure_integral_eq_of_tendsto K C F f hrep' hlim
  refine ⟨μ.map Subtype.val, (FiniteMeasure.mass_map_le _ _).trans hmass, ?_, ?_⟩
  · change ∀ᵐ x ∂Measure.map (Subtype.val : Icc a b → ℝ) (μ : Measure (Icc a b)),
      x ∈ Icc a b
    exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
      (Eventually.of_forall fun x => x.property)
  · intro t
    change ∫ x, Real.exp (t * x)
      ∂Measure.map (Subtype.val : Icc a b → ℝ) (μ : Measure (Icc a b)) = f t
    have hval : IsClosedEmbedding (Subtype.val : Icc a b → ℝ) :=
      IsClosedEmbedding.subtypeVal isClosed_Icc
    rw [hval.integral_map
      (μ := (μ : Measure (Icc a b))) (fun x : ℝ => Real.exp (t * x))]
    exact hμ t

/-- A pointwise limit of exponential transforms of positive finite measures supported in a
common compact interval is represented by one positive finite measure on the same interval.
No separate mass bound is required: convergence at parameter zero bounds the masses. This
is the compactness reduction used to remove the simple-spectrum hypothesis from Stahl's
BMV representation (Stahl 2013, Theorem 1). The spectral-surface positivity theorem is not
an assumption or a conclusion here. -/
private theorem exists_finiteMeasure_exp_mul_eq_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ,
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure ℝ,
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = f t := by
  let C : ℝ≥0 := ⟨|f 0| + 1, by positivity⟩
  have hbound : ∀ᶠ i in l, F i 0 < (C : ℝ) :=
    (hlim 0).eventually (Iio_mem_nhds
      (lt_of_le_of_lt (le_abs_self (f 0)) (lt_add_one _)))
  have hrep' : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t := by
    filter_upwards [hrep, hbound] with i hi hbi
    obtain ⟨μ, hsupp, hμ⟩ := hi
    refine ⟨μ, ?_, hsupp, hμ⟩
    have hmass : (μ.mass : ℝ) = F i 0 := by
      calc
        (μ.mass : ℝ) = ∫ x : ℝ, (1 : ℝ) ∂(μ : Measure ℝ) := by
          simp only [integral_const, smul_eq_mul, mul_one]
          rfl
        _ = F i 0 := by simpa only [zero_mul, Real.exp_zero] using hμ 0
    change (μ.mass : ℝ) ≤ (C : ℝ)
    exact hmass.trans_le hbi.le
  obtain ⟨μ, -, hsupp, hμ⟩ :=
    exists_finiteMeasure_exp_mul_eq_of_tendsto_of_mass_le a b C F f hrep' hlim
  exact ⟨μ, hsupp, hμ⟩

end MeasureTheory

end

section

open MeasureTheory Set ProbabilityTheory

open scoped Topology

namespace MeasureTheory

/-- An finite positive measure represents `F` by exponentials and is
concentrated on `[a,b]`. This records a representation, not its existence. -/
structure IsCompactExpRepresentation (ν : FiniteMeasure ℝ) (F : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- The representing measure is concentrated on the specified interval. -/
  ae_mem_Icc : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b
  /-- The exponential transform is the represented function at every real parameter. -/
  integral_exp : ∀ t : ℝ, (∫ x, Real.exp (t * x) ∂(ν : Measure ℝ)) = F t

namespace IsCompactExpRepresentation

variable {ν : FiniteMeasure ℝ} {F : ℝ → ℝ} {a b : ℝ}

variable (h : IsCompactExpRepresentation ν F a b)

include h

/-- Compact support gives exponential integrability at every real parameter. -/
theorem integrable_exp (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (ν : Measure ℝ) :=
  integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable h.ae_mem_Icc

/-- The full real line lies in the interior of the exponential-integrability set. -/
theorem mem_interior_integrableExpSet (t : ℝ) :
    t ∈ interior (integrableExpSet (id : ℝ → ℝ) (ν : Measure ℝ)) := by
  have heq : integrableExpSet (id : ℝ → ℝ) (ν : Measure ℝ) = univ := by
    ext s
    simp only [mem_univ, iff_true]
    exact h.integrable_exp s
  simp [heq]

/-- Evaluation at zero identifies the total mass, including the zero measure. -/
theorem coe_mass_eq : (ν.mass : ℝ) = F 0 := by
  simpa using h.integral_exp 0

/-- Every derivative is the corresponding exponentially tilted moment. No
probability normalization is required. -/
theorem iteratedDeriv_eq_integral (k : ℕ) (t : ℝ) :
    iteratedDeriv k F t = ∫ x, x ^ k * Real.exp (t * x) ∂(ν : Measure ℝ) := by
  have heq : F = mgf (id : ℝ → ℝ) (ν : Measure ℝ) := by
    funext s
    exact (h.integral_exp s).symm
  rw [heq]
  exact iteratedDeriv_mgf (h.mem_interior_integrableExpSet t) k

/-- The moment integrands are integrable for every derivative order and real
parameter. -/
theorem integrable_pow_mul_exp (k : ℕ) (t : ℝ) :
    Integrable (fun x => x ^ k * Real.exp (t * x)) (ν : Measure ℝ) :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (h.mem_interior_integrableExpSet t) k

/-- All even derivatives of a positive exponential representation are nonnegative. -/
theorem iteratedDeriv_even_nonneg (r : ℕ) (t : ℝ) :
    0 ≤ iteratedDeriv (2 * r) F t := by
  rw [h.iteratedDeriv_eq_integral]
  apply integral_nonneg
  intro x
  exact mul_nonneg ((even_two_mul r).pow_nonneg x) (Real.exp_pos _).le

/-- For nonnegative time the lower support endpoint bounds every even derivative
from below. -/
theorem exp_mul_iteratedDeriv_even_zero_le (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (t * a) * iteratedDeriv (2 * r) F 0 ≤ iteratedDeriv (2 * r) F t := by
  rw [h.iteratedDeriv_eq_integral, h.iteratedDeriv_eq_integral]
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← integral_const_mul]
  apply integral_mono_ae
    (((h.integrable_pow_mul_exp (2 * r) 0).congr (by simp)).const_mul _)
    (h.integrable_pow_mul_exp (2 * r) t)
  filter_upwards [h.ae_mem_Icc] with x hx
  have hp : 0 ≤ x ^ (2 * r) := (even_two_mul r).pow_nonneg x
  have he : Real.exp (t * a) ≤ Real.exp (t * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1 ht)
  nlinarith

/-- For nonnegative time the upper support endpoint bounds every even derivative
from above. -/
theorem iteratedDeriv_even_le_exp_mul_zero (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv (2 * r) F t ≤ Real.exp (t * b) * iteratedDeriv (2 * r) F 0 := by
  rw [h.iteratedDeriv_eq_integral, h.iteratedDeriv_eq_integral]
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← integral_const_mul]
  apply integral_mono_ae (h.integrable_pow_mul_exp (2 * r) t)
    (((h.integrable_pow_mul_exp (2 * r) 0).congr (by simp)).const_mul _)
  filter_upwards [h.ae_mem_Icc] with x hx
  have hp : 0 ≤ x ^ (2 * r) := (even_two_mul r).pow_nonneg x
  have he : Real.exp (t * x) ≤ Real.exp (t * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 ht)
  nlinarith

end IsCompactExpRepresentation

/-- Limits of functions with positive exponential representations on a common
compact interval have a positive representation on that interval. Mass bounds
follow from convergence at zero, rather than being added as hypotheses. -/
theorem exists_isCompactExpRepresentation_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν (F i) a b)
    (hlim : ∀ t, Filter.Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν f a b := by
  have hrep' : ∀ᶠ i in l, ∃ ν : FiniteMeasure ℝ,
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b) ∧
        ∀ t, (∫ x, Real.exp (t * x) ∂(ν : Measure ℝ)) = F i t := by
    filter_upwards [hrep] with i hi
    obtain ⟨ν, hν⟩ := hi
    exact ⟨ν, hν.ae_mem_Icc, hν.integral_exp⟩
  obtain ⟨ν, hsupp, heq⟩ := exists_finiteMeasure_exp_mul_eq_of_tendsto a b F f hrep' hlim
  exact ⟨ν, hsupp, heq⟩

end MeasureTheory

end

section

open MeasureTheory Set

open scoped NNReal ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The positive finite atomic measure with weight `exp (a i)` at `b i`. -/
noncomputable def exponentialAtomicMeasure (a b : ι → ℝ) : FiniteMeasure ℝ :=
  ⟨∑ i, Real.toNNReal (Real.exp (a i)) • Measure.dirac (b i),
    by infer_instance⟩

/-- Unfolding the atomic measure gives a finite sum of scaled Dirac measures. -/
theorem exponentialAtomicMeasure_toMeasure (a b : ι → ℝ) :
    (exponentialAtomicMeasure a b : Measure ℝ) =
      ∑ i, ENNReal.ofReal (Real.exp (a i)) • Measure.dirac (b i) := by
  simp [exponentialAtomicMeasure, ENNReal.ofReal]

/-- Integrating any real function against these atoms gives its weighted sum.
No separate integrability premise is needed for a finite atomic measure. -/
theorem integral_exponentialAtomicMeasure (a b : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(exponentialAtomicMeasure a b : Measure ℝ)) =
      ∑ i, Real.exp (a i) * f (b i) := by
  rw [exponentialAtomicMeasure_toMeasure, integral_finsetSum_measure]
  · simp [integral_smul_measure, ENNReal.toReal_ofReal, (Real.exp_pos _).le]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Atoms inside `[l,u]` give a compactly supported exponential representation. -/
theorem isCompactExpRepresentation_exponentialAtomicMeasure (a b : ι → ℝ)
    {l u : ℝ} (hb : ∀ i, b i ∈ Icc l u) :
    IsCompactExpRepresentation (exponentialAtomicMeasure a b)
      (fun t => ∑ i, Real.exp (a i + t * b i)) l u := by
  constructor
  · rw [exponentialAtomicMeasure_toMeasure, ae_finsetSum_measure_iff]
    intro i _
    exact Measure.ae_smul_measure (by simpa using hb i) _
  · intro t
    rw [integral_exponentialAtomicMeasure]
    simp only [Real.exp_add]

end MeasureTheory

end

section

open MeasureTheory Set

open scoped Interval

namespace MeasureTheory

/-- The finite positive measure with density `max ρ 0` on `[a,b]` and zero
outside. Almost everywhere nonnegative densities retain their original values.
The integrability argument is used only to certify finite mass. -/
noncomputable def intervalDensityMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (ρ x)),
    isFiniteMeasure_withDensity_ofReal hρ.2⟩

/-- The underlying measure is restricted Lebesgue measure weighted by the
nonnegative part of the density. -/
theorem intervalDensityMeasure_toMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) :
    (intervalDensityMeasure ρ a b hρ : Measure ℝ) =
      (volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (ρ x)) := rfl

/-- A measure constructed from an interval density is concentrated on that
interval, including a degenerate or empty interval. -/
private theorem ae_mem_Icc_intervalDensityMeasure (ρ : ℝ → ℝ) (a b : ℝ)
    (hρ : IntegrableOn ρ (Icc a b)) :
    ∀ᵐ x ∂(intervalDensityMeasure ρ a b hρ : Measure ℝ), x ∈ Icc a b := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- Integrating against an almost everywhere nonnegative interval density is
its ordinary weighted integral. The test function is arbitrary, with Bochner
integrals interpreted using Mathlib's total integral convention. -/
theorem integral_intervalDensityMeasure {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : IntegrableOn ρ (Icc a b))
    (hpos : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ ρ x) (f : ℝ → ℝ) :
    (∫ x, f x ∂(intervalDensityMeasure ρ a b hρ : Measure ℝ)) =
      ∫ x in Icc a b, ρ x * f x := by
  rw [intervalDensityMeasure_toMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- An almost everywhere nonnegative integrable interval density gives a
compact positive exponential representation of its weighted interval integrals. -/
theorem isCompactExpRepresentation_intervalDensityMeasure
    {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : IntegrableOn ρ (Icc a b))
    (hpos : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ ρ x) :
    IsCompactExpRepresentation (intervalDensityMeasure ρ a b hρ)
      (fun t => ∫ x in a..b, Real.exp (t * x) * ρ x) a b := by
  constructor
  · exact ae_mem_Icc_intervalDensityMeasure ρ a b hρ
  · intro t
    rw [integral_intervalDensityMeasure hρ hpos,
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    congr 1
    funext x
    exact mul_comm _ _

namespace IsCompactExpRepresentation

/-- Adding two compactly supported positive exponential measures adds their
represented functions while preserving the common support interval. -/
theorem add {ν₁ ν₂ : FiniteMeasure ℝ} {F₁ F₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : IsCompactExpRepresentation ν₁ F₁ a b)
    (h₂ : IsCompactExpRepresentation ν₂ F₂ a b) :
    IsCompactExpRepresentation (ν₁ + ν₂) (fun t => F₁ t + F₂ t) a b := by
  constructor
  · exact ae_add_measure_iff.mpr ⟨h₁.ae_mem_Icc, h₂.ae_mem_Icc⟩
  · intro t
    rw [FiniteMeasure.toMeasure_add, integral_add_measure (h₁.integrable_exp t)
      (h₂.integrable_exp t), h₁.integral_exp t, h₂.integral_exp t]

end IsCompactExpRepresentation

end MeasureTheory

end
