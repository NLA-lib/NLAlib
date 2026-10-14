/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Coordinate gradients, second derivatives and bounded Hessians

A function of class `C²` whose second derivative is bounded by `C` has a derivative of linear
growth and values of quadratic growth. On `ι → ℝ`, a function given with a coordinate gradient
`g` whose coordinates have continuous gradients `H` is of class `C²`, its second derivative is
`(v, w) ↦ ∑ᵢⱼ Hᵢⱼ vⱼ wᵢ`, and a bound on the entries of `H` bounds the second derivative. These
are the regularity facts behind Gaussian interpolation arguments, whose test functions (soft
maxima) are given by explicit gradients; the coordinate forms of the product, inverse, logarithm,
sum and exponential rules compute those gradients. Upstream candidates for
`Mathlib/Analysis/Calculus/ContDiff/Bounds.lean` and `Mathlib/Analysis/Calculus/FDeriv/Pi.lean`.

## Main results

* `NLAlib.norm_fderiv_le_of_norm_iteratedFDeriv_two_le`: `‖D f x‖ ≤ ‖D f 0‖ + C ‖x‖`.
* `NLAlib.norm_sub_le_of_norm_iteratedFDeriv_two_le`: `‖f x - f 0‖ ≤ ‖D f 0‖ ‖x‖ + C ‖x‖²`.
* `NLAlib.contDiff_two_of_hasFDerivAt_sum_smul_proj`: explicit gradients give `C²`.
* `NLAlib.fderiv_fderiv_apply_of_hasFDerivAt_sum_smul_proj`: the second derivative in
  coordinates.
* `NLAlib.norm_iteratedFDeriv_two_le_of_hasFDerivAt_sum_smul_proj`: `‖D² f x‖ ≤ |ι|² K` when
  `|Hᵢⱼ| ≤ K`.
* `NLAlib.apply_eq_sum_mul_apply_single`: a linear form on `ι → ℝ` in the standard basis.
* `HasFDerivAt.mul_sum_smul_proj` and its companions: calculus rules for coordinate gradients.
-/

@[expose] public section

namespace NLAlib

section Bounded

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {C : ℝ}

/-- A second derivative bounded by `C` gives a derivative of linear growth:
`‖D f x‖ ≤ ‖D f 0‖ + C ‖x‖`. -/
theorem norm_fderiv_le_of_norm_iteratedFDeriv_two_le (hf : ContDiff ℝ 2 f)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (x : E) :
    ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ f 0‖ + C * ‖x‖ := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have hb : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
    exact hC y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hd y) (fun y _ => hb y)
    convex_univ (Set.mem_univ 0) (Set.mem_univ x)
  rw [sub_zero] at h
  linarith [norm_le_insert' (fderiv ℝ f x) (fderiv ℝ f 0)]

/-- A second derivative bounded by `C` gives quadratic growth:
`‖f x - f 0‖ ≤ ‖D f 0‖ ‖x‖ + C ‖x‖²`. -/
theorem norm_sub_le_of_norm_iteratedFDeriv_two_le (hf : ContDiff ℝ 2 f)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (x : E) :
    ‖f x - f 0‖ ≤ ‖fderiv ℝ f 0‖ * ‖x‖ + C * ‖x‖ ^ 2 := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Metric.closedBall 0 ‖x‖)
    (C := ‖fderiv ℝ f 0‖ + C * ‖x‖) (fun y _ => (hf.differentiable two_ne_zero) y)
    (fun y hy => (norm_fderiv_le_of_norm_iteratedFDeriv_two_le hf hC y).trans
      (by gcongr; exact mem_closedBall_zero_iff.1 hy))
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg _))
    (mem_closedBall_zero_iff.2 le_rfl)
  rw [sub_zero] at h
  linarith

end Bounded

section Coordinates

variable {ι : Type*} [Fintype ι]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

/-- A linear form on `ι → ℝ` in the standard basis: `L a = ∑ⱼ aⱼ L eⱼ`. -/
theorem apply_eq_sum_mul_apply_single [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℝ) :
    L a = ∑ j, a j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Pi.single j (a j) = a j • (Pi.single j 1 : ι → ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

variable {f : (ι → ℝ) → ℝ} {g : ι → (ι → ℝ) → ℝ} {H : ι → ι → (ι → ℝ) → ℝ}

/-- A function with coordinate gradient `g` (`D f x = ∑ᵢ gᵢ x • projᵢ`) whose coordinates have
continuous coordinate gradients `H` is of class `C²`. -/
theorem contDiff_two_of_hasFDerivAt_sum_smul_proj (hf : ∀ x, HasFDerivAt f (∑ i, g i x • PR i) x)
    (hg : ∀ i x, HasFDerivAt (g i) (∑ j, H i j x • PR j) x) (hH : ∀ i j, Continuous (H i j)) :
    ContDiff ℝ 2 f := by
  have hgc : ∀ i, ContDiff ℝ 1 (g i) := fun i => by
    refine contDiff_one_iff_fderiv.2 ⟨fun x => (hg i x).differentiableAt, ?_⟩
    rw [show fderiv ℝ (g i) = fun x => ∑ j, H i j x • PR j from funext fun x => (hg i x).fderiv]
    exact continuous_finsetSum _ fun j _ => (hH i j).smul continuous_const
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨fun x => (hf x).differentiableAt, fun h => by simp at h, ?_⟩
  rw [show fderiv ℝ f = fun x => ∑ i, g i x • PR i from funext fun x => (hf x).fderiv]
  exact ContDiff.sum fun i _ => (hgc i).smul contDiff_const

/-- The second derivative of a function given by coordinate gradients:
`D² f x v w = ∑ᵢ (∑ⱼ Hᵢⱼ x vⱼ) wᵢ`. -/
theorem fderiv_fderiv_apply_of_hasFDerivAt_sum_smul_proj
    (hf : ∀ x, HasFDerivAt f (∑ i, g i x • PR i) x)
    (hg : ∀ i x, HasFDerivAt (g i) (∑ j, H i j x • PR j) x) (x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = ∑ i, (∑ j, H i j x * v j) * w i := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hg i x).smul_const (PR i)
  rw [show fderiv ℝ f = fun x => ∑ i, g i x • PR i from funext fun x => (hf x).fderiv,
    h.fderiv]
  simp [smul_eq_mul]

/-- A bound `|Hᵢⱼ| ≤ K` on the coordinate Hessian bounds the second derivative by `|ι|² K`. -/
theorem norm_iteratedFDeriv_two_le_of_hasFDerivAt_sum_smul_proj
    (hf : ∀ x, HasFDerivAt f (∑ i, g i x • PR i) x)
    (hg : ∀ i x, HasFDerivAt (g i) (∑ j, H i j x • PR j) x) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ i j x, |H i j x| ≤ K) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ Fintype.card ι ^ 2 * K := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply_of_hasFDerivAt_sum_smul_proj hf hg,
    Fin.prod_univ_two, Real.norm_eq_abs]
  have hm : ∀ k j, |m k j| ≤ ‖m k‖ := fun k j => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (m k) j
  calc |∑ i, (∑ j, H i j x * m 0 j) * m 1 i| ≤ ∑ i : ι, ∑ j : ι, K * ‖m 0‖ * ‖m 1‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
          (abs_nonneg _)).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        gcongr
        · exact hK i j x
        · exact hm 0 j
        · exact hm 1 i
    _ = Fintype.card ι ^ 2 * K * (‖m 0‖ * ‖m 1‖) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ### Calculus rules for coordinate gradients -/

/-- The product rule for coordinate gradients. -/
theorem _root_.HasFDerivAt.mul_sum_smul_proj {f h : (ι → ℝ) → ℝ} {x : ι → ℝ} {c d : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hh : HasFDerivAt h (∑ b, d b • PR b) x) :
    HasFDerivAt (fun y => f y * h y) (∑ b, (f x * d b + h x * c b) • PR b) x := by
  refine (hf.fun_mul hh).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, add_smul]

/-- The square rule for coordinate gradients. -/
theorem _root_.HasFDerivAt.pow_two_sum_smul_proj {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) :
    HasFDerivAt (fun y => f y ^ 2) (∑ b, (2 * f x * c b) • PR b) x := by
  simp only [sq]
  exact (hf.mul_sum_smul_proj hf).congr_fderiv (Finset.sum_congr rfl fun b _ => by ring_nf)

/-- The inverse rule for coordinate gradients. -/
theorem _root_.HasFDerivAt.inv_sum_smul_proj {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) (∑ b, (-(f x ^ 2)⁻¹ * c b) • PR b) x := by
  refine ((hasDerivAt_inv hx).comp_hasFDerivAt x hf).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

/-- The logarithm rule for coordinate gradients. -/
theorem _root_.HasFDerivAt.log_sum_smul_proj {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => Real.log (f y)) (∑ b, ((f x)⁻¹ * c b) • PR b) x := by
  refine (hf.log hx).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

/-- Scalar multiples of coordinate gradients. -/
theorem _root_.HasFDerivAt.const_mul_sum_smul_proj {f : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ι → ℝ}
    (hf : HasFDerivAt f (∑ b, c b • PR b) x) (r : ℝ) :
    HasFDerivAt (fun y => r * f y) (∑ b, (r * c b) • PR b) x := by
  refine (hf.const_mul r).congr_fderiv ?_
  simp only [Finset.smul_sum, smul_smul]

/-- Finite sums of coordinate gradients. -/
theorem _root_.HasFDerivAt.sum_sum_smul_proj {κ : Type*} [Fintype κ] {f : κ → (ι → ℝ) → ℝ}
    {x : ι → ℝ} {c : κ → ι → ℝ} (hf : ∀ k, HasFDerivAt (f k) (∑ b, c k b • PR b) x) :
    HasFDerivAt (fun y => ∑ k, f k y) (∑ b, (∑ k, c k b) • PR b) x := by
  refine (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => hf k).congr_fderiv ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]

/-- The coordinate gradient of `y ↦ exp (β yₐ)`. -/
theorem hasFDerivAt_exp_mul_apply_sum_smul_proj [DecidableEq ι] (β : ℝ) (a : ι) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y a))
      (∑ b, (if b = a then β * Real.exp (β * x a) else 0) • PR b) x := by
  refine (((PR a).hasFDerivAt (x := x)).const_mul β).exp.congr_fderiv ?_
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  rw [mul_comm]
  rfl

end Coordinates

end NLAlib
