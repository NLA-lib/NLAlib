/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Isotropic
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Rademacher variables and vectors

`NLAlib.rademacherMeasure` is the law of a random sign: `±1` with probability `1/2` each.
`NLAlib.rademacherVector n` is the law of a vector of independent signs, an `abbrev` for the
product. This file proves, for random variables with these laws, the interfaces and moments the
probability layers use: proxy `1`, `X² = 1` almost surely, `E X⁴ = 1`, the moment generating
function `cosh`, and isotropy of the vector. The law is symmetric, and flipping one coordinate of
a vector of independent signs preserves its law: the symmetries behind the Rademacher moment
recursion of the noncommutative Khintchine inequality
(`NLAlib/Probability/MatrixConcentration/Khintchine.lean`). The symmetries are stated for the
measures; statements with `HasLaw ε (rademacherVector n) μ` transport through `integral_map`.

`NLAlib.integrable_rademacherMeasure` and `NLAlib.integral_rademacherMeasure` are stated for the
measure: they are its constructors (as Mathlib's `integral_bernoulliMeasure` is), from which the
random-variable forms follow.

## Main definitions

* `NLAlib.rademacherMeasure`, `NLAlib.rademacherVector n`.

## Main results

* `NLAlib.integral_rademacherMeasure`: `∫ f = (f 1 + f (-1)) / 2`.
* `NLAlib.hasSubgaussianMGF_of_hasLaw_rademacherMeasure`: proxy `1`.
* `NLAlib.isIsotropic_of_hasLaw_rademacherVector`.
* `NLAlib.measurePreserving_neg_rademacherMeasure`,
  `NLAlib.measurePreserving_update_neg_rademacherVector`: sign-flip symmetry.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- The Rademacher law: `±1` with probability `1/2` each. It is Mathlib's
`bernoulliMeasure 1 (-1)` at `1/2`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac 1 + Measure.dirac (-1))

instance isProbabilityMeasure_rademacherMeasure : IsProbabilityMeasure rademacherMeasure := by
  constructor
  simp only [rademacherMeasure, Measure.smul_apply, Measure.add_apply, measure_univ,
    smul_eq_mul, one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The law of a vector of independent random signs. -/
noncomputable abbrev rademacherVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => rademacherMeasure

/-- Every function is integrable for the Rademacher law. -/
theorem integrable_rademacherMeasure {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f rademacherMeasure := by
  exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
    (by simp)

/-- The integral against the Rademacher law is the average of the two values. -/
theorem integral_rademacherMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂rademacherMeasure = (2 : ℝ)⁻¹ • (f 1 + f (-1)) := by
  rw [rademacherMeasure, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- A random sign is `1` or `-1` almost surely. -/
theorem ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1 := by
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  rw [← ae_map_iff hX.aemeasurable hS, hX.map_eq, rademacherMeasure]
  refine Measure.ae_smul_measure (ae_add_measure_iff.2 ⟨?_, ?_⟩) _
  · exact (ae_dirac_iff hS).2 (Or.inl rfl)
  · exact (ae_dirac_iff hS).2 (Or.inr rfl)

private theorem integral_comp_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) (f : ℝ → ℝ) :
    ∫ ω, f (X ω) ∂μ = 2⁻¹ * (f 1 + f (-1)) :=
  (hX.integral_comp (integrable_rademacherMeasure f).aestronglyMeasurable).trans
    (integral_rademacherMeasure f)

/-- The moment generating function of a random sign is `cosh`. -/
theorem mgf_of_hasLaw_rademacherMeasure {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ)
    (t : ℝ) : mgf X μ t = Real.cosh t := by
  rw [mgf, integral_comp_of_hasLaw_rademacherMeasure hX fun x => Real.exp (t * x), Real.cosh_eq,
    mul_one, mul_neg_one]
  ring

/-- A random sign is sub-Gaussian with proxy `1`. -/
theorem hasSubgaussianMGF_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : HasSubgaussianMGF X 1 μ := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact (hX.integrable_comp_iff (integrable_rademacherMeasure _).aestronglyMeasurable).2
      (integrable_rademacherMeasure fun x => Real.exp (t * x))
  · rw [mgf_of_hasLaw_rademacherMeasure hX, NNReal.coe_one, one_mul]
    exact Real.cosh_le_exp_half_sq t

/-- A random sign has mean zero. -/
theorem integral_of_hasLaw_rademacherMeasure {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) :
    ∫ ω, X ω ∂μ = 0 := by
  rw [integral_comp_of_hasLaw_rademacherMeasure hX (fun x => x)]
  norm_num

/-- The second moment of a random sign is `1`. -/
theorem integral_sq_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∫ ω, X ω ^ 2 ∂μ = 1 := by
  rw [integral_comp_of_hasLaw_rademacherMeasure hX (fun x => x ^ 2)]
  norm_num

/-- The fourth moment of a random sign is `1`. -/
theorem integral_pow_four_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∫ ω, X ω ^ 4 ∂μ = 1 := by
  rw [integral_comp_of_hasLaw_rademacherMeasure hX (fun x => x ^ 4)]
  norm_num

/-- A vector of independent random signs is isotropic. -/
theorem isIsotropic_of_hasLaw_rademacherVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsIsotropic X μ := by
  refine IsIsotropic.of_iIndepFun hX.iIndepFun_eval (fun i => ?_)
    (fun i => integral_of_hasLaw_rademacherMeasure (hX.eval i)) (fun i => ?_)
  · exact ((hX.eval i).memLp_comp_iff aestronglyMeasurable_id).2
      ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_rademacherMeasure _))
  · simp only [Real.norm_eq_abs, sq_abs]
    exact integral_sq_of_hasLaw_rademacherMeasure (hX.eval i)

/-- The squared coordinates of a vector of random signs are `1` almost surely. -/
theorem ae_sq_eq_one_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : ∀ᵐ ω ∂μ, ∀ i, X ω i ^ 2 = 1 := by
  refine ae_all_iff.2 fun i => ?_
  filter_upwards [ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure (hX.eval i)] with ω h
  rcases h with h | h <;> simp [h]

/-! ### Sign-flip symmetry -/

/-- The Rademacher law is symmetric: `x ↦ -x` preserves it. -/
theorem measurePreserving_neg_rademacherMeasure :
    MeasurePreserving (fun x : ℝ => -x) rademacherMeasure rademacherMeasure := by
  refine ⟨measurable_neg, ?_⟩
  rw [rademacherMeasure, Measure.map_smul, Measure.map_add _ _ measurable_neg,
    Measure.map_dirac' measurable_neg, Measure.map_dirac' measurable_neg, neg_neg, add_comm]

/-- Flipping the sign of one coordinate of a vector of independent random signs preserves its
law. Proof: Mathlib's `measurePreserving_pi`, with `-·` in coordinate `i` and `id` elsewhere. -/
theorem measurePreserving_update_neg_rademacherVector [DecidableEq n] (i : n) :
    MeasurePreserving (fun x : n → ℝ => Function.update x i (-x i))
      (rademacherVector n) (rademacherVector n) := by
  have h := measurePreserving_pi (fun _ : n => rademacherMeasure) (fun _ => rademacherMeasure)
    (f := fun j (x : ℝ) => if j = i then -x else x) fun j => by
      by_cases hj : j = i
      · simp only [hj, if_true]
        exact measurePreserving_neg_rademacherMeasure
      · simp only [hj, if_false]
        exact MeasurePreserving.id _
  convert h using 1
  funext x j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

end NLAlib
