/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Real.Sqrt
public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound
public import NLAlib.Probability.MatrixIntegral
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

/-- The exponential of a function of a Hermitian matrix. -/
private theorem exp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian) (g : ℝ → ℝ) :
    exp (cfc g B) = cfc (fun x => Real.exp (g x)) B := by
  have hH : (cfc g B).IsHermitian := cfc_predicate g B
  rw [hH.exp_eq_cfc]
  exact (cfc_comp' Real.exp g B ((B.finite_real_spectrum.image _).continuousOn _)
    (B.finite_real_spectrum.continuousOn _) hB).symm

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
    exact hB.integrable_cfc (hf θ)
  · simp only [hexp]
    rw [← hB.cfc_integral (hf θ)]
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

omit [Fintype ι] in
/-- The variance matrix of a Hermitian series is Hermitian. -/
private theorem isHermitian_sum_smul_sq [Fintype ι] (c : ι → ℝ≥0) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) : (∑ k, (c k : ℝ) • B k ^ 2).IsHermitian :=
  isSelfAdjoint_sum _ fun k _ => (IsSelfAdjoint.all _).smul ((hB k).pow 2)

/-- **The matrix series tail**, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem measureReal_eigenvalue_zero_sum_smul_ge_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, γ k ω • B k) 0} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2))) := by
  have := hind.isProbabilityMeasure
  have hA := isHermitian_sum_smul_sq c hB
  have hX : iIndepFun (fun k ω => γ k ω • B k) μ :=
    hind.comp (fun k x => x • B k) fun k => measurable_id.smul_const (B k)
  set v := specNorm (∑ k, (c k : ℝ) • B k ^ 2) with hv
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hP : μ.real {ω | t ≤ eigenvalue (∑ k, γ k ω • B k) 0} ≤ 1 := measureReal_le_one
  rcases ht.eq_or_lt with rfl | ht'
  · rw [show -(0 : ℝ) ^ 2 / (2 * v) = 0 by ring, Real.exp_zero, mul_one]
    exact hP.trans hd
  rcases (show 0 ≤ v from specNorm_nonneg _).eq_or_lt with hv0 | hv0
  · rw [← hv0, mul_zero, div_zero, Real.exp_zero, mul_one]
    exact hP.trans hd
  refine (HasMatrixMGFBound.measure_eigenvalue_zero_sum_ge_le_card_mul_exp
    hX (fun k => hasMatrixMGFBound_smul_of_hasSubgaussianMGF (hγ k) (hB k))
    (Set.mem_univ (t / v)) (div_pos ht' hv0) (div_nonneg (sq_nonneg _) two_pos.le) t).trans ?_
  have hlam : eigenvalue (∑ k, (c k : ℝ) • B k ^ 2) 0 ≤ v :=
    (le_abs_self _).trans (hA.abs_eigenvalue_le_specNorm 0)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
  calc -(t / v) * t + (t / v) ^ 2 / 2 * eigenvalue (∑ k, (c k : ℝ) • B k ^ 2) 0
      ≤ -(t / v) * t + (t / v) ^ 2 / 2 * v :=
        add_le_add_right (mul_le_mul_of_nonneg_left hlam (div_nonneg (sq_nonneg _) two_pos.le)) _
    _ = -t ^ 2 / (2 * v) := by
        field_simp
        ring

/-- The matrix series mean, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_eigenvalue_zero_sum_smul_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) :
    ∫ ω, eigenvalue (∑ k, γ k ω • B k) 0 ∂μ ≤
      √(2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2) * Real.log (Fintype.card n)) := by
  have := hind.isProbabilityMeasure
  have hA := isHermitian_sum_smul_sq c hB
  have hX : iIndepFun (fun k ω => γ k ω • B k) μ :=
    hind.comp (fun k x => x • B k) fun k => measurable_id.smul_const (B k)
  set v := specNorm (∑ k, (c k : ℝ) • B k ^ 2) with hv
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hlam : eigenvalue (∑ k, (c k : ℝ) • B k ^ 2) 0 ≤ v :=
    (le_abs_self _).trans (hA.abs_eigenvalue_le_specNorm 0)
  have hbound : ∀ θ, 0 < θ → ∫ ω, eigenvalue (∑ k, γ k ω • B k) 0 ∂μ ≤
      Real.log (Fintype.card n) / θ + v / 2 * θ := by
    intro θ hθ
    refine (HasMatrixMGFBound.integral_eigenvalue_zero_sum_le hX
      (fun k => hasMatrixMGFBound_smul_of_hasSubgaussianMGF (hγ k) (hB k))
      (fun k => (hγ k).integrable.smul_const _) (Set.mem_univ θ) hθ).trans ?_
    have hM : ((θ ^ 2 / 2) • ∑ k, (c k : ℝ) • B k ^ 2).IsHermitian :=
      (IsSelfAdjoint.all _).smul hA
    have htr := hM.re_trace_exp_le_card_mul_exp
    rw [eigenvalue_real_smul _ (by positivity)] at htr
    have hle : RCLike.re (exp ((θ ^ 2 / 2) • ∑ k, (c k : ℝ) • B k ^ 2)).trace ≤
        Fintype.card n * Real.exp (θ ^ 2 / 2 * v) := htr.trans (by gcongr)
    calc θ⁻¹ * Real.log (RCLike.re (exp ((θ ^ 2 / 2) • ∑ k, (c k : ℝ) • B k ^ 2)).trace)
        ≤ θ⁻¹ * Real.log (Fintype.card n * Real.exp (θ ^ 2 / 2 * v)) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hM.re_trace_exp_pos hle) (inv_nonneg.2 hθ.le)
      _ = Real.log (Fintype.card n) / θ + v / 2 * θ := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
          field_simp
  refine (Real.le_sqrt_of_forall_le_div_add_mul (Real.log_nonneg hd)
    (div_nonneg (specNorm_nonneg _) two_pos.le) hbound).trans_eq ?_
  congr 1
  ring

section Rectangular

omit [DecidableEq n]

variable {m : Type*} [Fintype m]

omit [Fintype n] [Fintype m] in
/-- A real combination of dilations is the dilation of the combination. -/
private theorem sum_smul_dilation (a : ι → ℝ) (B : ι → Matrix m n 𝕜) :
    ∑ k, a k • dilation (B k) = dilation (∑ k, a k • B k) := by
  rw [dilation_sum]
  simp only [dilation_smul_real]

/-- A real combination of squared dilations is block diagonal. -/
private theorem sum_smul_dilation_sq [DecidableEq m] [DecidableEq n] (a : ι → ℝ)
    (B : ι → Matrix m n 𝕜) :
    ∑ k, a k • dilation (B k) ^ 2 =
      Matrix.fromBlocks (∑ k, a k • (B k * (B k)ᴴ)) 0 0 (∑ k, a k • ((B k)ᴴ * B k)) := by
  simp only [sq, dilation_mul_dilation]
  ext (i | i) (j | j) <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, smul_zero, Finset.sum_const_zero]

variable {B : ι → Matrix m n 𝕜}

/-- **The matrix series tail**, rectangular coefficients ([Tropp2015], Theorem 4.1.1), with
`v = max ‖∑ c k B k B kᴴ‖ ‖∑ c k B kᴴ B k‖`. -/
theorem measureReal_specNorm_sum_smul_ge_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, γ k ω • B k)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-t ^ 2 /
        (2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))))) := by
  classical
  have h := measureReal_eigenvalue_zero_sum_smul_ge_le (n := m ⊕ n) hind hγ
    (B := fun k => dilation (B k)) (fun k => isHermitian_dilation _) ht
  simp only [sum_smul_dilation, eigenvalue_zero_dilation, sum_smul_dilation_sq,
    specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

/-- The matrix series mean, rectangular coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_specNorm_sum_smul_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) :
    ∫ ω, specNorm (∑ k, γ k ω • B k) ∂μ ≤
      √(2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))) *
        Real.log (Fintype.card m + Fintype.card n)) := by
  classical
  have h := integral_eigenvalue_zero_sum_smul_le (n := m ⊕ n) hind hγ
    (B := fun k => dilation (B k)) (fun k => isHermitian_dilation _)
  simp only [sum_smul_dilation, eigenvalue_zero_dilation, sum_smul_dilation_sq,
    specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

end Rectangular

end NLAlib
