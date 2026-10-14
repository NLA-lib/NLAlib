/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Law

/-!
# Isotropic random vectors

A random vector `X : Ω → n → 𝕜` is isotropic when its coordinates are square integrable and its
second-moment matrix `E [X Xᴴ]` is the identity. No mean is assumed and nothing is said about
`E [X Xᵀ]`. Rademacher and standard Gaussian vectors are isotropic, and so are `√n` times a uniform
point of the unit sphere and `√n` times a column of a Haar-distributed unitary matrix.

Isotropy is what trace estimation and the second moment of a sketch use: for isotropic `X`,
`E [Xᴴ A X] = tr A` (Hutchinson) and `E ‖A X‖² = ‖A‖_F²`. Fourth moments, which the variance of
these estimators needs, are separate hypotheses where they are used.

## Main definitions

* `NLAlib.IsIsotropic X μ`: `X` has square-integrable coordinates and `E [X Xᴴ] = 1`.

## Main results

* `NLAlib.IsIsotropic.integral_quadForm`: Hutchinson's identity `E [Xᴴ A X] = tr A`.
* `NLAlib.IsIsotropic.integral_norm_mulVec_sq`: `E ‖A X‖² = ‖A‖_F²`.
* `NLAlib.IsIsotropic.integral_norm_dotProduct_sq`: `E |⟨u, X⟩|² = ‖u‖²`.
* `NLAlib.IsIsotropic.mulVec`: maps with orthonormal rows preserve isotropy.
* `NLAlib.IsIsotropic.of_iIndepFun`: independent coordinates with mean zero and unit second
  moment.
* `ProbabilityTheory.HasLaw.isIsotropic_iff`: isotropy depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n] {X : Ω → n → 𝕜}

/-- A random vector `X` in `𝕜ⁿ` is isotropic for `μ` when its coordinates are square integrable
and its second-moment matrix is the identity: `∫ X i * conj (X j) = if i = j then 1 else 0`.
No mean is assumed and nothing is said about `E [X Xᵀ]`. -/
structure IsIsotropic (X : Ω → n → 𝕜) (μ : Measure Ω) : Prop where
  /-- Each coordinate is square integrable. -/
  memLp : ∀ i, MemLp (fun ω => X ω i) 2 μ
  /-- The second-moment matrix `E [X Xᴴ]` is the identity. -/
  integral_mul_star : ∀ i j, ∫ ω, X ω i * star (X ω j) ∂μ = if i = j then 1 else 0

namespace IsIsotropic

/-- The products of two coordinates of an isotropic vector are integrable. -/
theorem integrable_mul_star (hX : IsIsotropic X μ) (i j : n) :
    Integrable (fun ω => X ω i * star (X ω j)) μ :=
  (hX.memLp i).integrable_mul (hX.memLp j).star

variable [Fintype n]

omit [DecidableEq n] in
private theorem quadForm_eq_sum_mul_star (A : Matrix n n 𝕜) (x : n → 𝕜) :
    quadForm A x = ∑ i, ∑ j, A i j * (x j * star (x i)) := by
  rw [quadForm_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of an isotropic vector is integrable. -/
theorem integrable_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    Integrable (fun ω => quadForm A (X ω)) μ := by
  simp only [quadForm_eq_sum_mul_star]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hX.integrable_mul_star j i).const_mul (A i j)

/-- **Hutchinson's identity**: for an isotropic probe `X`, the quadratic form `Xᴴ A X` is an
unbiased estimator of `tr A`.
Result: hutchinson-trace-estimator -/
theorem integral_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    ∫ ω, quadForm A (X ω) ∂μ = A.trace := by
  have h (i : n) : ∫ ω, ∑ j, A i j * (X ω j * star (X ω i)) ∂μ = A i i := by
    rw [integral_finsetSum _ fun j _ => (hX.integrable_mul_star j i).const_mul (A i j)]
    simp only [integral_const_mul, hX.integral_mul_star, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [quadForm_eq_sum_mul_star]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hX.integrable_mul_star j i).const_mul (A i j)]
  simp only [h, Matrix.trace, Matrix.diag]

/-- The squared Euclidean norm of `A X` is integrable for an isotropic `X`. -/
theorem integrable_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2) μ := by
  have h := (hX.integrable_quadForm (Aᴴ * A)).re
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re] at h
  exact h

/-- `E ‖A X‖² = ‖A‖_F²` for an isotropic `X`. -/
theorem integral_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : ∫ ω, ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2 ∂μ = frobNorm A ^ 2 := by
  have h := integral_re (hX.integrable_quadForm (Aᴴ * A))
  rw [hX.integral_quadForm] at h
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re] at h
  rw [h, frobNorm_sq_eq_re_trace]

/-- `E |⟨u, X⟩|² = ‖u‖²` for an isotropic `X`: the second moment behind the
Johnson–Lindenstrauss lemma. Over `ℝ`, `‖r‖ ^ 2 = r ^ 2` by `Real.norm_eq_abs` and `sq_abs`. -/
theorem integral_norm_dotProduct_sq (hX : IsIsotropic X μ) (u : n → 𝕜) :
    ∫ ω, ‖u ⬝ᵥ X ω‖ ^ 2 ∂μ = ‖WithLp.toLp 2 u‖ ^ 2 := by
  have key (x : n → 𝕜) :
      ‖u ⬝ᵥ x‖ ^ 2 = RCLike.re (quadForm (Matrix.vecMulVec (star u) u) x) := by
    have h := quadForm_vecMulVec_star (star u) x
    rw [star_star] at h
    rw [h, RCLike.ofReal_re]
  simp only [key]
  rw [integral_re (hX.integrable_quadForm _), hX.integral_quadForm, Matrix.trace_vecMulVec,
    EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct]

/-- The mean squared Euclidean norm of an isotropic vector is the dimension. -/
theorem integral_norm_sq (hX : IsIsotropic X μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ = Fintype.card n := by
  have key (x : n → 𝕜) : ‖WithLp.toLp 2 x‖ ^ 2 = RCLike.re (quadForm 1 x) := by
    rw [quadForm_one, RCLike.ofReal_re]
  simp only [key]
  rw [integral_re (hX.integrable_quadForm _), hX.integral_quadForm, Matrix.trace_one,
    RCLike.natCast_re]

omit [DecidableEq n] in
private theorem mulVec_mul_star_mulVec {m : Type*} (U : Matrix m n 𝕜) (x : n → 𝕜) (i j : m) :
    (U *ᵥ x) i * star ((U *ᵥ x) j) = ∑ k, ∑ l, U i k * star (U j l) * (x k * star (x l)) := by
  simp only [Matrix.mulVec, dotProduct, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul']
  ring

/-- A map with orthonormal rows preserves isotropy: if `U Uᴴ = 1` (that is,
`HasOrthonormalCols Uᴴ`), then `U X` is isotropic. Rotations of isotropic vectors, the rows of a
randomized Hadamard transform and rescaled columns of a Haar frame get their isotropy this way. -/
theorem mulVec (hX : IsIsotropic X μ) {m : Type*} [DecidableEq m]
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols Uᴴ) : IsIsotropic (fun ω => U *ᵥ X ω) μ := by
  have hU' : U * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hU.conjTranspose_mul_self
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun k _ => (hX.memLp k).const_mul (U i k)
  have h (k : n) : ∫ ω, ∑ l, U i k * star (U j l) * (X ω k * star (X ω l)) ∂μ =
      U i k * star (U j k) := by
    rw [integral_finsetSum _ fun l _ => (hX.integrable_mul_star k l).const_mul _]
    simp only [integral_const_mul, hX.integral_mul_star, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hij := congrFun (congrFun hU' i) j
  rw [Matrix.one_apply, Matrix.mul_apply] at hij
  simp only [mulVec_mul_star_mulVec]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (hX.integrable_mul_star k l).const_mul _, ← hij]
  simp only [h, Matrix.conjTranspose_apply]

omit [Fintype n] in
/-- Independent coordinates with mean zero and unit second moment form an isotropic vector. -/
theorem of_iIndepFun (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL2 : ∀ i, MemLp (fun ω => X ω i) 2 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) : IsIsotropic X μ := by
  refine ⟨hL2, fun i j => ?_⟩
  split_ifs with h
  · subst h
    have key (ω : Ω) : X ω i * star (X ω i) = ((‖X ω i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
    simp only [key]
    rw [integral_ofReal, hvar, RCLike.ofReal_one]
  · have hij := (hind.indepFun h).comp measurable_id continuous_star.measurable
    have hint := hij.integral_fun_mul_eq_mul_integral (hL2 i).1 (hL2 j).1.star
    simp only [Function.comp_apply, id_eq] at hint
    rw [hint, hmean, zero_mul]

end IsIsotropic

/-- Isotropy depends only on the law: a random vector with law `ν` is isotropic exactly when the
identity is isotropic for `ν`. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropic_iff {ν : Measure (n → 𝕜)}
    (hX : HasLaw X ν μ) : IsIsotropic X μ ↔ IsIsotropic id ν := by
  have hm (i : n) : Measurable fun x : n → 𝕜 => x i := measurable_pi_apply i
  have hint (i j : n) : ∫ ω, X ω i * star (X ω j) ∂μ = ∫ x, x i * star (x j) ∂ν :=
    hX.integral_comp ((hm i).mul (continuous_star.measurable.comp (hm j))).aestronglyMeasurable
  have hmem (i : n) : MemLp (fun ω => X ω i) 2 μ ↔ MemLp (fun x : n → 𝕜 => x i) 2 ν :=
    hX.memLp_comp_iff (hm i).aestronglyMeasurable
  constructor
  · intro h
    exact ⟨fun i => (hmem i).1 (h.memLp i),
      fun i j => (hint i j).symm.trans (h.integral_mul_star i j)⟩
  · intro h
    exact ⟨fun i => (hmem i).2 (h.memLp i),
      fun i j => (hint i j).trans (h.integral_mul_star i j)⟩

end NLAlib
