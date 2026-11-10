/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance

/-!
# Mathematics of random probes: standard laws and isotropic vectors

No program occurs in this file. A real law is *standard* when it has mean zero and unit variance
(`NLAlib.Ops.IsStdLaw`: the standard Gaussian, a random sign); a law on vectors is *isotropic*
when its coordinates have mean zero and the identity as second-moment matrix
(`NLAlib.Ops.IsIsotropic`).

## Main results

* `NLAlib.Ops.isStdLaw_gaussianReal`: the standard Gaussian is standard.
* `NLAlib.Ops.IsStdLaw.isIsotropic_pi`: a vector of independent standard draws is isotropic.
* `NLAlib.Ops.IsIsotropic.integral_affine`, `integral_sqNorm_affine`: the mean and the second
  moment of `b + c g`.
* `NLAlib.Ops.IsIsotropic.integral_quadForm`: `𝔼 gᵀ A g = tr A`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops

/-- The squared Euclidean norm of a vector. -/
def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

theorem sqNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem measurable_sqNorm {n : ℕ} : Measurable (sqNorm (n := n)) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2

theorem sq_le_sqNorm {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : v i ^ 2 ≤ sqNorm v :=
  Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- The quadratic form `gᵀ A g`. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, g i * A i j * g j

theorem measurable_quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Measurable (quadForm A) :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply i).mul_const _).mul (measurable_pi_apply j)

/-- **A standard real law**: mean zero and unit variance. -/
structure IsStdLaw (γ : Measure ℝ) : Prop where
  /-- It is a probability measure. -/
  prob : IsProbabilityMeasure γ
  /-- It has a second moment. -/
  memLp : MemLp id 2 γ
  /-- Mean zero. -/
  mean : ∫ x, x ∂γ = 0
  /-- Unit variance. -/
  var : ∫ x, x ^ 2 ∂γ = 1

/-- The standard Gaussian is a standard law. -/
theorem isStdLaw_gaussianReal : IsStdLaw (gaussianReal 0 1) where
  prob := inferInstance
  memLp := memLp_id_gaussianReal 2
  mean := integral_id_gaussianReal
  var := by
    have h := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := fun x : ℝ => x)
      measurable_id.aemeasurable integral_id_gaussianReal
    rw [← h, variance_fun_id_gaussianReal]
    rfl

/-- **An isotropic law on vectors**: the coordinates have mean zero and the identity as
second-moment matrix. -/
structure IsIsotropic {n : ℕ} (ν : Measure (Fin n → ℝ)) : Prop where
  /-- It is a probability measure. -/
  prob : IsProbabilityMeasure ν
  /-- The coordinates have second moments. -/
  memLp : ∀ i, MemLp (fun g => g i) 2 ν
  /-- Mean zero. -/
  mean : ∀ i, ∫ g, g i ∂ν = 0
  /-- The second moments are the identity. -/
  cov : ∀ i j, ∫ g, g i * g j ∂ν = if i = j then 1 else 0

/-- **A vector of independent standard draws is isotropic.** -/
theorem IsStdLaw.isIsotropic_pi {γ : Measure ℝ} (h : IsStdLaw γ) (n : ℕ) :
    IsIsotropic (Measure.pi fun _ : Fin n => γ) := by
  have := h.prob
  have hev : ∀ i : Fin n, MeasurePreserving (Function.eval i) (Measure.pi fun _ : Fin n => γ) γ :=
    fun i => measurePreserving_eval (fun _ : Fin n => γ) i
  have hint : ∀ (f : ℝ → ℝ), Measurable f → ∀ i : Fin n,
      ∫ g, f (g i) ∂(Measure.pi fun _ : Fin n => γ) = ∫ x, f x ∂γ := fun f hf i => by
    have := integral_map (μ := Measure.pi fun _ : Fin n => γ)
      (measurable_pi_apply i).aemeasurable (f := f) hf.aestronglyMeasurable
    rw [(hev i).map_eq] at this
    exact this.symm
  have hmean : ∀ i : Fin n, ∫ g, g i ∂(Measure.pi fun _ : Fin n => γ) = 0 :=
    fun i => (hint id measurable_id i).trans h.mean
  refine ⟨inferInstance, fun i => h.memLp.comp_measurePreserving (hev i), hmean, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have := hint (fun x => x ^ 2) (measurable_id.pow_const 2) i
    simp only [pow_two] at this
    rw [this, ← h.var]
    simp [pow_two]
  · rw [if_neg hij]
    have hind : IndepFun (fun g : Fin n → ℝ => g i) (fun g => g j)
        (Measure.pi fun _ : Fin n => γ) :=
      (iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) fun _ => aemeasurable_id).indepFun hij
    rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable, hmean i, zero_mul]

namespace IsIsotropic

variable {n : ℕ} {ν : Measure (Fin n → ℝ)}

theorem integrable_coord (h : IsIsotropic ν) (i : Fin n) : Integrable (fun g => g i) ν :=
  have := h.prob
  (h.memLp i).integrable one_le_two

theorem integrable_mul (h : IsIsotropic ν) (i j : Fin n) : Integrable (fun g => g i * g j) ν :=
  (h.memLp i).integrable_mul (h.memLp j)

/-- The mean of `b + c g`. -/
theorem integral_affine (h : IsIsotropic ν) (b : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    ∫ g, (b i + c * g i) ∂ν = b i := by
  have := h.prob
  have h1 : Integrable (fun g : Fin n → ℝ => c * g i) ν := (h.integrable_coord i).const_mul c
  rw [integral_add (integrable_const _) h1, integral_const_mul, h.mean]
  simp

theorem integrable_sq_affine (h : IsIsotropic ν) (b : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    Integrable (fun g => (b i + c * g i) ^ 2) ν := by
  have := h.prob
  have e : (fun g : Fin n → ℝ => (b i + c * g i) ^ 2) =
      fun g => b i ^ 2 + (2 * b i * c) * g i + c ^ 2 * (g i * g i) := by
    funext g
    ring
  rw [e]
  exact ((integrable_const _).add ((h.integrable_coord i).const_mul _)).add
    ((h.integrable_mul i i).const_mul _)

theorem integrable_sqNorm_affine (h : IsIsotropic ν) (b : Fin n → ℝ) (c : ℝ) :
    Integrable (fun g => sqNorm fun i => b i + c * g i) ν :=
  integrable_finsetSum _ fun i _ => h.integrable_sq_affine b c i

/-- **The second moment of `b + c g`** is `‖b‖² + c² n`. -/
theorem integral_sqNorm_affine (h : IsIsotropic ν) (b : Fin n → ℝ) (c : ℝ) :
    ∫ g, sqNorm (fun i => b i + c * g i) ∂ν = sqNorm b + c ^ 2 * n := by
  have := h.prob
  have hi : ∀ i, ∫ g, (b i + c * g i) ^ 2 ∂ν = b i ^ 2 + c ^ 2 := fun i => by
    have e : (fun g : Fin n → ℝ => (b i + c * g i) ^ 2) =
        fun g => b i ^ 2 + (2 * b i * c) * g i + c ^ 2 * (g i * g i) := by
      funext g
      ring
    have h1 : Integrable (fun g : Fin n → ℝ => (2 * b i * c) * g i) ν :=
      (h.integrable_coord i).const_mul _
    have h2 : Integrable (fun g : Fin n → ℝ => c ^ 2 * (g i * g i)) ν :=
      (h.integrable_mul i i).const_mul _
    have h3 : Integrable (fun g : Fin n → ℝ => b i ^ 2 + (2 * b i * c) * g i) ν :=
      (integrable_const _).add h1
    rw [e, integral_add h3 h2, integral_add (integrable_const _) h1, integral_const_mul,
      integral_const_mul, h.mean, h.cov]
    simp
  simp only [sqNorm]
  rw [integral_finsetSum _ fun i _ => h.integrable_sq_affine b c i]
  simp only [hi, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem integrable_quadForm (h : IsIsotropic ν) (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (quadForm A) ν :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
    have e : (fun g : Fin n → ℝ => g i * A i j * g j) = fun g => A i j * (g i * g j) := by
      funext g
      ring
    rw [e]
    exact (h.integrable_mul i j).const_mul _

/-- **The mean of the quadratic form of an isotropic vector is the trace.** -/
theorem integral_quadForm (h : IsIsotropic ν) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ g, quadForm A g ∂ν = A.trace := by
  have e : ∀ i j, (fun g : Fin n → ℝ => g i * A i j * g j) = fun g => A i j * (g i * g j) :=
    fun i j => by
      funext g
      ring
  have hij : ∀ i j, Integrable (fun g : Fin n → ℝ => g i * A i j * g j) ν := fun i j => by
    rw [e]
    exact (h.integrable_mul i j).const_mul _
  simp only [quadForm]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
  simp only [integral_finsetSum _ fun j _ => hij _ j, e, integral_const_mul, h.cov,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

end IsIsotropic

end NLAlib.Ops
