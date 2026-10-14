/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.SubGaussian.Basic
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic

/-!
# Exponential moments of linear images of sub-Gaussian vectors

For a random vector `X` with independent coordinates, each sub-Gaussian with proxy `c`, a linear
form `v ⬝ᵥ X` has moment generating function at most `exp (c s² ‖v‖² / 2)` (the lower-integral
form of `NLAlib.IsSubgaussianVector.of_iIndepFun`), and the squared norm of a linear image
satisfies `E exp (θ ‖B X‖²) ≤ exp (9/8 · c θ ‖B‖_F²)` when `18 c θ ‖B‖² ≤ 1`. The second bound
linearises the square against a standard Gaussian vector `g`,
`exp (θ ‖y‖²) = E_g exp (√(2θ) y ⬝ᵥ g)` (`NLAlib.lintegral_exp_mul_dotProduct_gaussianVector`),
applies the first bound to `X`, and computes the remaining Gaussian expectation
`E_g exp (c θ ‖Bᵀ g‖²)` in an eigenbasis of `B Bᵀ`. Both bounds are steps of the off-diagonal
part of the Hanson–Wright inequality (`NLAlib/Probability/QuadraticForm/HansonWright.lean`).

## Main results

* `NLAlib.lintegral_exp_mul_dotProduct_le`: the linear form.
* `NLAlib.lintegral_exp_mul_norm_mulVec_sq_le`: the squared norm of a linear image.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], §6.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → n → ℝ} {c : ℝ≥0}

/-- The moment generating function of a linear form of independent coordinates, each
sub-Gaussian with proxy `c`, written as a lower integral: `E exp (s (v ⬝ᵥ X)) ≤
exp (c s² ‖v‖² / 2)`. It is `IsSubgaussianVector.of_iIndepFun` in the form the conditioning
arguments of the Hanson–Wright inequality integrate. -/
theorem lintegral_exp_mul_dotProduct_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (v : n → ℝ) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (rexp (s * (v ⬝ᵥ X ω))) ∂μ ≤
      ENNReal.ofReal (rexp (c * s ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 / 2)) := by
  have hv := (IsSubgaussianVector.of_iIndepFun hind h).hasSubgaussianMGF v
  simp only [RCLike.re_to_real] at hv
  rw [← ofReal_integral_eq_lintegral_ofReal (hv.integrable_exp_mul s)
    (ae_of_all _ fun _ => (exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ((hv.mgf_le s).trans_eq ?_)
  push_cast
  ring_nf

/-- The standard Gaussian vector is invariant under the change of coordinates to an orthonormal
basis. -/
private lemma map_sum_mul_gaussianVector (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    (gaussianVector n).map (fun z j => ∑ i, z i * b i j) = gaussianVector n := by
  have h1 : (stdGaussian (EuclideanSpace ℝ n)).map WithLp.ofLp = gaussianVector n := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  have hf : (fun z : n → ℝ => fun j => ∑ i, z i * b i j) =
      WithLp.ofLp ∘ fun z : n → ℝ => ∑ i, z i • b i := by
    ext z j
    simp [WithLp.ofLp_sum]
  conv_rhs => rw [← h1, stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [Measure.map_map (by fun_prop) (by fun_prop), ← hf]

/-- In an eigenbasis of a symmetric `M`, the quadratic form is a weighted sum of squares. -/
private lemma quadForm_sum_mul_eigenvectorBasis [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.IsHermitian) (z : n → ℝ) :
    quadForm M (fun j => ∑ i, z i * hM.eigenvectorBasis i j) =
      ∑ i, hM.eigenvalues i * z i ^ 2 := by
  set U : Matrix n n ℝ := (hM.eigenvectorUnitary : Matrix n n ℝ)
  have hv : (fun j => ∑ i, z i * hM.eigenvectorBasis i j) = U *ᵥ z := by
    ext j
    simp only [Matrix.mulVec, dotProduct, U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hD : Uᴴ * M * U = Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    simpa [U, Matrix.star_eq_conjTranspose] using this
  rw [hv, ← quadForm_conjTranspose_mul_mul, hD, quadForm_diagonal]
  simp [Real.norm_eq_abs, sq_abs]

/-- `E exp (a g²) ≤ exp (9 a / 8)` for a standard Gaussian `g` and `0 ≤ a ≤ 1/18`. -/
private lemma integral_exp_mul_sq_gaussianReal_le {a : ℝ} (ha0 : 0 ≤ a) (ha : 18 * a ≤ 1) :
    ∫ x, rexp (a * x ^ 2) ∂(gaussianReal 0 1) ≤ rexp (9 / 8 * a) := by
  have hg : HasSubgaussianMGF id 1 (gaussianReal 0 1) :=
    hasSubgaussianMGF_of_hasLaw_gaussianReal ⟨aemeasurable_id, Measure.map_id⟩
  have ha' : 2 * a * ((1 : ℝ≥0) : ℝ) < 1 := by push_cast; linarith
  have h1 : ∫ x, rexp (a * x ^ 2) ∂(gaussianReal 0 1) ≤ 1 / √(1 - 2 * a) := by
    simpa using hg.integral_exp_mul_sq_le ha0 ha'
  refine h1.trans ?_
  have h2a : 0 < 1 - 2 * a := by linarith
  rw [div_le_iff₀ (sqrt_pos.mpr h2a)]
  have key : 1 ≤ (1 - 2 * a) * rexp (9 / 4 * a) := by
    have he := add_one_le_exp (9 / 4 * a)
    nlinarith [mul_le_mul_of_nonneg_left he h2a.le, mul_nonneg ha0 (by linarith : 0 ≤ 1 - 18 * a)]
  have hsq : rexp (9 / 4 * a) = rexp (9 / 8 * a) ^ 2 := by
    rw [← exp_nat_mul]
    ring_nf
  calc (1 : ℝ) = √1 := sqrt_one.symm
    _ ≤ √((1 - 2 * a) * rexp (9 / 4 * a)) := sqrt_le_sqrt key
    _ = rexp (9 / 8 * a) * √(1 - 2 * a) := by
      rw [hsq, sqrt_mul h2a.le, sqrt_sq (exp_pos _).le, mul_comm]

/-- The Gaussian case of the squared-norm bound: `E exp (τ ‖C g‖²) ≤ exp (9/8 · τ ‖C‖_F²)` for a
standard Gaussian vector `g` and `18 τ ‖C‖² ≤ 1`, by diagonalising `Cᴴ C`. -/
private lemma lintegral_exp_mul_norm_mulVec_sq_gaussianVector_le (C : Matrix m n ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hsmall : 18 * (τ * specNorm C ^ 2) ≤ 1) :
    ∫⁻ g, ENNReal.ofReal (rexp (τ * ‖WithLp.toLp 2 (C *ᵥ g)‖ ^ 2)) ∂(gaussianVector n) ≤
      ENNReal.ofReal (rexp (9 / 8 * (τ * frobNorm C ^ 2))) := by
  classical
  set M := Cᴴ * C
  have hM : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self C
  set b := hM.eigenvectorBasis
  have hnorm : ∀ g : n → ℝ, ‖WithLp.toLp 2 (C *ᵥ g)‖ ^ 2 = quadForm M g := by
    intro g
    rw [quadForm_conjTranspose_mul_self]
    rfl
  have hlam : ∀ i, hM.eigenvalues i = ‖WithLp.toLp 2 (C *ᵥ b i)‖ ^ 2 := by
    intro i
    rw [hnorm, hM.eigenvalues_eq i]
    rfl
  have hlam0 : ∀ i, 0 ≤ hM.eigenvalues i := fun i => by rw [hlam]; positivity
  have hlam1 : ∀ i, 18 * (τ * hM.eigenvalues i) ≤ 1 := by
    intro i
    have hb : ‖WithLp.toLp 2 (⇑(b i))‖ = 1 := by simp [b.orthonormal.1 i]
    have hC := norm_toLp_mulVec_le C (b i)
    rw [hb, mul_one] at hC
    have hle : hM.eigenvalues i ≤ specNorm C ^ 2 := by
      rw [hlam]
      exact pow_le_pow_left₀ (norm_nonneg _) hC 2
    nlinarith [mul_le_mul_of_nonneg_left hle hτ]
  have htr : ∑ i, hM.eigenvalues i = frobNorm C ^ 2 := by
    rw [frobNorm_sq_eq_re_trace, hM.trace_eq_sum_eigenvalues]
    simp
  rw [← map_sum_mul_gaussianVector b, lintegral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ z : n → ℝ, rexp (τ * ‖WithLp.toLp 2 (C *ᵥ fun j => ∑ i, z i * b i j)‖ ^ 2) =
      ∏ i, rexp (τ * hM.eigenvalues i * z i ^ 2) := by
    intro z
    rw [hnorm, quadForm_sum_mul_eigenvectorBasis, Finset.mul_sum, exp_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_assoc]
  simp only [hpt]
  have hint : ∀ i, Integrable (fun x : ℝ => rexp (τ * hM.eigenvalues i * x ^ 2))
      (gaussianReal 0 1) := by
    intro i
    have hg : HasSubgaussianMGF id 1 (gaussianReal 0 1) :=
      hasSubgaussianMGF_of_hasLaw_gaussianReal ⟨aemeasurable_id, Measure.map_id⟩
    have := hg.integrable_exp_mul_sq (θ := τ * hM.eigenvalues i) (by push_cast; linarith [hlam1 i])
    simpa using this
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hint)
    (ae_of_all _ fun _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_fintype_prod_eq_prod (fun i x => rexp (τ * hM.eigenvalues i * x ^ 2))]
  calc ∏ i, ∫ x, rexp (τ * hM.eigenvalues i * x ^ 2) ∂(gaussianReal 0 1) ≤
        ∏ i, rexp (9 / 8 * (τ * hM.eigenvalues i)) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (exp_pos _).le)
        fun i _ => integral_exp_mul_sq_gaussianReal_le (by positivity [hlam0 i]) (hlam1 i)
    _ = rexp (9 / 8 * (τ * frobNorm C ^ 2)) := by
      rw [← exp_sum, ← htr, Finset.mul_sum, Finset.mul_sum]

/-- The squared norm of a linear image of independent coordinates, each sub-Gaussian with proxy
`c`: `E exp (θ ‖B X‖²) ≤ exp (9/8 · c θ ‖B‖_F²)` for `θ ≥ 0` with `18 c θ ‖B‖² ≤ 1`, in
`lintegral` form. The bound is in the Frobenius norm of `B`, with no dependence on the dimension;
it is the moment generating function bound behind the tail of `‖B X‖²` of Hsu, Kakade and Zhang
(2012, Theorem 2.1), in a cruder form valid for small `θ`. -/
theorem lintegral_exp_mul_norm_mulVec_sq_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (B : Matrix m n ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : 18 * (c * θ * specNorm B ^ 2) ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 (B *ᵥ X ω)‖ ^ 2)) ∂μ ≤
      ENNReal.ofReal (rexp (9 / 8 * (c * θ * frobNorm B ^ 2))) := by
  have := hind.isProbabilityMeasure
  set s := √(2 * θ)
  have hs : s ^ 2 = 2 * θ := sq_sqrt (by linarith)
  have hpt : ∀ x : m → ℝ, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 x‖ ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (rexp (s * (x ⬝ᵥ g))) ∂(gaussianVector m) := by
    intro x
    rw [lintegral_exp_mul_dotProduct_gaussianVector, hs]
    ring_nf
  have hX : AEMeasurable X μ := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable
  have hcont : Continuous fun p : (n → ℝ) × (m → ℝ) => rexp (s * (B *ᵥ p.1 ⬝ᵥ p.2)) :=
    (continuous_const.mul ((continuous_const.matrix_mulVec continuous_fst).dotProduct
      continuous_snd)).rexp
  have hpair : AEMeasurable (fun q : Ω × (m → ℝ) => (X q.1, q.2)) (μ.prod (gaussianVector m)) :=
    hX.comp_fst.prodMk measurable_snd.aemeasurable
  have hf : Measurable fun p : (n → ℝ) × (m → ℝ) =>
      ENNReal.ofReal (rexp (s * (B *ᵥ p.1 ⬝ᵥ p.2))) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  have hmeas : AEMeasurable (Function.uncurry fun ω (g : m → ℝ) =>
      ENNReal.ofReal (rexp (s * (B *ᵥ X ω ⬝ᵥ g)))) (μ.prod (gaussianVector m)) := by
    have h' := hf.comp_aemeasurable hpair
    exact h'
  have heq : ∀ ω (g : m → ℝ), B *ᵥ X ω ⬝ᵥ g = (Bᵀ *ᵥ g) ⬝ᵥ X ω := by
    intro ω g
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * ‖WithLp.toLp 2 (B *ᵥ X ω)‖ ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (rexp (s * (B *ᵥ X ω ⬝ᵥ g))) ∂(gaussianVector m) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (rexp (s * (B *ᵥ X ω ⬝ᵥ g))) ∂μ ∂(gaussianVector m) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ g, ENNReal.ofReal (rexp ((c * θ) * ‖WithLp.toLp 2 (Bᵀ *ᵥ g)‖ ^ 2))
          ∂(gaussianVector m) := by
        refine lintegral_mono fun g => ?_
        simp only [heq]
        refine (lintegral_exp_mul_dotProduct_le hind h _ s).trans
          (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (le_of_eq ?_)))
        rw [hs]
        ring
    _ ≤ ENNReal.ofReal (rexp (9 / 8 * (c * θ * frobNorm B ^ 2))) := by
        have := lintegral_exp_mul_norm_mulVec_sq_gaussianVector_le Bᵀ (τ := c * θ)
          (by positivity) (by rwa [specNorm_transpose])
        rwa [frobNorm_transpose] at this

end NLAlib
