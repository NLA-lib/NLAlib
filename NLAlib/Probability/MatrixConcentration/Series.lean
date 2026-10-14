/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Matrix series with sub-Gaussian coefficients

For fixed Hermitian matrices `B k` and independent real coefficients `γ k` with
`HasSubgaussianMGF (γ k) (c k)`, the series `∑ γ k • B k` satisfies
`P(t ≤ λ_max) ≤ d exp (-t² / (2v))` with `v = ‖∑ c k B k²‖`, and
`E λ_max ≤ √(2 v log d)`. Rectangular coefficients go through the dilation. Gaussian and
Rademacher series are the case `c k = 1` (Tropp 2015, Theorem 4.1.1, which states the Gaussian and
Rademacher cases; the sub-Gaussian form is the same proof).

## Main results

* `NLAlib.hasMatrixMGFBound_smul_of_hasSubgaussianMGF`.
* `NLAlib.measureReal_eigenvalue_zero_sum_smul_ge_le`,
  `NLAlib.integral_eigenvalue_zero_sum_smul_le`.
* `NLAlib.measureReal_specNorm_sum_smul_ge_le`, `NLAlib.integral_specNorm_sum_smul_le`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Helpers -/

/-- The integral of a family of functions of a fixed Hermitian matrix is the function of the
matrix given by the integral: `∫ f ω (B) = (∫ f ω) (B)`, with integrability. -/
private theorem integrable_and_integral_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    Integrable (fun ω => cfc (f ω) B) μ ∧
      ∫ ω, cfc (f ω) B ∂μ = cfc (fun x => ∫ ω, f ω x ∂μ) B := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  let L : (Fin (Fintype.card n) → ℝ) →ₗ[ℝ] Matrix n n 𝕜 :=
    { toFun := fun v => U * Matrix.diagonal (fun i => ((v i : ℝ) : 𝕜)) * Uᴴ
      map_add' := fun v w => by
        simp only [Pi.add_apply, RCLike.ofReal_add, ← Matrix.diagonal_add, Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun a v => by
        have hd : (fun i => (((a • v) i : ℝ) : 𝕜)) = (a : 𝕜) • fun i => ((v i : ℝ) : 𝕜) := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
        rw [RingHom.id_apply, hd, ← Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          ← RCLike.real_smul_eq_coe_smul] }
  let Lc := LinearMap.toContinuousLinearMap L
  have hcfc : ∀ g : ℝ → ℝ, cfc g B = Lc (fun i => g (eigenvalue B i)) := fun g =>
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr hBU g
  have hv : Integrable (fun ω => fun i : Fin (Fintype.card n) => f ω (eigenvalue B i)) μ :=
    integrable_pi_iff.2 fun i => hf _
  simp only [hcfc]
  refine ⟨Lc.integrable_comp hv, ?_⟩
  rw [Lc.integral_comp_comm hv]
  congr 1
  funext i
  exact eval_integral (fun i => hf _) i

/-- The exponential of a function of a Hermitian matrix. -/
private theorem exp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian) (g : ℝ → ℝ) :
    exp (cfc g B) = cfc (fun x => Real.exp (g x)) B := by
  rw [(cfc_predicate g B : (cfc g B).IsHermitian).exp_eq_cfc,
    ← cfc_comp' Real.exp g B ((B.finite_real_spectrum.image _).continuousOn _)
      (B.finite_real_spectrum.continuousOn _) hB]

/-- The scalar optimisation behind the means: if `x ≤ a / u + b u` for every `u > 0`, with
`a, b ≥ 0`, then `x ≤ √(4ab)`. -/
private theorem le_sqrt_of_forall_le_div_add_mul {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u, 0 < u → x ≤ a / u + b * u) : x ≤ √(4 * a * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · refine le_trans ?_ (Real.sqrt_nonneg _)
    by_contra hx
    push_neg at hx
    have h1 := h (x / (2 * (b + 1))) (by positivity)
    rw [zero_div, zero_add] at h1
    have h2 : b * (x / (2 * (b + 1))) < x := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hb.eq_or_lt with rfl | hb'
  · refine le_trans ?_ (Real.sqrt_nonneg _)
    by_contra hx
    push_neg at hx
    have h1 := h (2 * a / x) (by positivity)
    rw [zero_mul, add_zero, div_div_eq_mul_div] at h1
    have h2 : a * x / (2 * a) = x / 2 := by field_simp
    linarith
  set p := √a with hp
  set q := √b with hq
  have hp0 : 0 < p := Real.sqrt_pos.2 ha'
  have hq0 : 0 < q := Real.sqrt_pos.2 hb'
  have hpa : p ^ 2 = a := Real.sq_sqrt ha
  have hqb : q ^ 2 = b := Real.sq_sqrt hb
  have h1 := h (p / q) (div_pos hp0 hq0)
  have h4 : 4 * a * b = (2 * p * q) ^ 2 := by rw [← hpa, ← hqb]; ring
  rw [h4, Real.sqrt_sq (by positivity)]
  have h5 : a / (p / q) + b * (p / q) = 2 * p * q := by
    rw [← hpa, ← hqb]
    field_simp
    ring
  linarith

/-- A sub-Gaussian coefficient times a fixed Hermitian matrix has a matrix MGF bound:
`E exp (θ γ B) ≤ exp (θ²/2 • c B²)`. -/
theorem hasMatrixMGFBound_smul_of_hasSubgaussianMGF {γ : Ω → ℝ} {c : ℝ≥0}
    (hγ : HasSubgaussianMGF γ c μ) {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    HasMatrixMGFBound (fun ω => γ ω • B) (fun θ => θ ^ 2 / 2) ((c : ℝ) • B ^ 2) Set.univ μ := by
  have hsa : IsSelfAdjoint B := hB
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ B) := fun g =>
    B.finite_real_spectrum.continuousOn g
  have hexp : ∀ (θ : ℝ) (ω : Ω),
      exp (θ • γ ω • B) = cfc (fun x => Real.exp (θ * γ ω * x)) B := fun θ ω => by
    rw [smul_smul, ← exp_cfc hB, cfc_const_mul _ (fun x => x) B (hcont _), cfc_id' ℝ B hsa]
  have hf : ∀ θ x : ℝ, Integrable (fun ω => Real.exp (θ * γ ω * x)) μ := fun θ x => by
    refine (hγ.integrable_exp_mul (θ * x)).congr (ae_of_all _ fun ω => ?_)
    simp only
    ring_nf
  refine ⟨ae_of_all _ fun ω => (IsSelfAdjoint.all _).smul hB,
    (IsSelfAdjoint.all _).smul (hB.pow 2), fun θ _ => ?_, fun θ _ => ?_⟩
  · simp only [hexp]
    exact (integrable_and_integral_cfc hB (hf θ)).1
  · simp only [hexp]
    rw [(integrable_and_integral_cfc hB (hf θ)).2]
    have hR : (θ ^ 2 / 2) • ((c : ℝ) • B ^ 2) =
        cfc (fun x : ℝ => θ ^ 2 / 2 * ((c : ℝ) * x ^ 2)) B := by
      rw [cfc_const_mul _ _ B (hcont _), cfc_const_mul _ _ B (hcont _),
        cfc_pow (fun x : ℝ => x) 2 B (hcont _) hsa, cfc_id' ℝ B hsa]
    rw [hR, exp_cfc hB]
    refine cfc_mono (fun x _ => ?_) (hcont _) (hcont _)
    have hm := hγ.mgf_le (θ * x)
    have he : ∫ ω, Real.exp (θ * γ ω * x) ∂μ = mgf γ μ (θ * x) := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      ring_nf
    rw [he]
    refine hm.trans_eq ?_
    congr 1
    ring

variable {ι : Type*} [Fintype ι] {γ : ι → Ω → ℝ} {c : ι → ℝ≥0}

/-- **The matrix series tail**, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem measureReal_eigenvalue_zero_sum_smul_ge_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, γ k ω • B k) 0} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2))) := by
  sorry

/-- The matrix series mean, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_eigenvalue_zero_sum_smul_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) :
    ∫ ω, eigenvalue (∑ k, γ k ω • B k) 0 ∂μ ≤
      √(2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2) * Real.log (Fintype.card n)) := by
  sorry

variable {m : Type*} [Fintype m] {B : ι → Matrix m n 𝕜}

/-- **The matrix series tail**, rectangular coefficients ([Tropp2015], Theorem 4.1.1), with
`v = max ‖∑ c k B k B kᴴ‖ ‖∑ c k B kᴴ B k‖`. -/
theorem measureReal_specNorm_sum_smul_ge_le [Nonempty m] [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, γ k ω • B k)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-t ^ 2 /
        (2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))))) := by
  sorry

/-- The matrix series mean, rectangular coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_specNorm_sum_smul_le [Nonempty m] [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) :
    ∫ ω, specNorm (∑ k, γ k ω • B k) ∂μ ≤
      √(2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))) *
        Real.log (Fintype.card m + Fintype.card n)) := by
  sorry

end NLAlib
