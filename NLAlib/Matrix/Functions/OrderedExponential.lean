/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Exponential
public import NLAlib.Matrix.Functions.Exponential

/-!
# Ordered products of matrix exponentials

The finite product preserves the supplied ordering of the Hermitian generators. Imaginary
times produce unitary factors and the norm growth depends only on the real part of time.
These are the boundary and limiting facts used in multivariate trace inequalities
[SutterBertaTomamichel2017].

## Main results

* `NLAlib.specNorm_orderedMatrixExp_le_exp_sum`: a uniform bound on the closed strip.
* `NLAlib.tendsto_abs_orderedMatrixExp_pow`: absolute-value powers converge to the exponential
  of the sum.
-/

@[expose] public section

open Matrix Complex Set
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite product of complex-time exponentials in its specified list order. -/
noncomputable def orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) : Matrix n n ℂ :=
  (H.map (fun A => NormedSpace.exp (z • A))).prod

/-- The empty product is the identity. -/
@[simp] theorem orderedMatrixExp_nil (z : ℂ) :
    orderedMatrixExp ([] : List (Matrix n n ℂ)) z = 1 := rfl

/-- The first generator gives the leftmost factor. -/
@[simp] theorem orderedMatrixExp_cons (A : Matrix n n ℂ) (H : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp (A :: H) z = NormedSpace.exp (z • A) * orderedMatrixExp H z := rfl

/-- At time zero every factor is the identity. -/
@[simp] theorem orderedMatrixExp_zero (H : List (Matrix n n ℂ)) : orderedMatrixExp H 0 = 1 := by
  induction H with
  | nil => rfl
  | cons A H ih => simp [orderedMatrixExp_cons, ih]

/-- Ordered exponential products are entire, without commutativity of the
generators or a choice of logarithmic branches. -/
theorem analyticAt_orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) :
    AnalyticAt ℂ (orderedMatrixExp H) z := by
  induction H with
  | nil => exact analyticAt_const
  | cons A H ih =>
    change AnalyticAt ℂ (fun w : ℂ => NormedSpace.exp (w • A) * orderedMatrixExp H w) z
    have he : AnalyticAt ℂ (fun w : ℂ => NormedSpace.exp (w • A)) z := by
      have hs : AnalyticAt ℂ (fun w : ℂ => w • A) z := analyticAt_id.smul analyticAt_const
      have hx : AnalyticAt ℂ (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (z • A) :=
        NormedSpace.exp_analytic _
      exact hx.comp (f := fun w : ℂ => w • A) hs
    exact he.mul ih

/-- The first derivative of the ordered product at zero is the actual sum
of its generators, without any commutation assumption. -/
theorem hasDerivAt_orderedMatrixExp_zero (H : List (Matrix n n ℂ)) :
    HasDerivAt (orderedMatrixExp H) H.sum (0 : ℂ) := by
  induction H with
  | nil =>
    convert! hasDerivAt_const (0 : ℂ) (1 : Matrix n n ℂ) using 1
  | cons A H ih =>
    have he := hasDerivAt_exp_smul_const A (0 : ℂ)
    have hp := he.mul ih
    convert! hp using 1
    simp only [List.sum_cons, zero_smul, NormedSpace.exp_zero,
      orderedMatrixExp_zero, one_mul, mul_one]

/-- Every ordered exponential product is an actual invertible matrix. -/
theorem isUnit_orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) :
    IsUnit (orderedMatrixExp H z) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  induction H with
  | nil => exact isUnit_one
  | cons A H ih => exact (NormedSpace.isUnit_exp (z • A)).mul ih

/-- The imaginary-time exponential of a Hermitian generator is unitary. -/
private theorem exp_imaginary_smul_mem_unitary {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) :
    NormedSpace.exp (((t : ℂ) * I) • A) ∈ unitary (Matrix n n ℂ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, hA.isSelfAdjoint.star_eq, mul_smul]

/-- Products of imaginary-time factors are unitary in their original order. -/
theorem orderedMatrixExp_mul_I_mem_unitary (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    orderedMatrixExp H ((t : ℂ) * I) ∈ unitary (Matrix n n ℂ) := by
  induction H with
  | nil => exact (unitary _).one_mem
  | cons A H ih =>
    exact (unitary _).mul_mem (exp_imaginary_smul_mem_unitary (hH A (by simp)) t)
      (ih (fun B hB => hH B (by simp [hB])))

/-- The imaginary part of the time parameter contributes a unitary factor. -/
private theorem norm_exp_complex_smul_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    ‖NormedSpace.exp (z • A)‖ ≤ Real.exp (|z.re| * ‖A‖) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  have hcomm := ((Commute.refl A).smul_left (z.re : ℂ)).smul_right ((z.im : ℂ) * I)
  have hunit := exp_imaginary_smul_mem_unitary hA z.im
  calc
    ‖NormedSpace.exp (z • A)‖ =
        ‖NormedSpace.exp ((z.re : ℂ) • A) * NormedSpace.exp (((z.im : ℂ) * I) • A)‖ := by
      rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul, Complex.re_add_im]
    _ = ‖NormedSpace.exp ((z.re : ℂ) • A)‖ := CStarRing.norm_mul_coe_unitary _ ⟨_, hunit⟩
    _ ≤ Real.exp (|z.re| * ‖A‖) := by
      simpa only [specNorm_eq_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs] using
        specNorm_exp_le ((z.re : ℂ) • A)

/-- Actual ordered products satisfy an explicit uniform vertical-strip
bound. No commutation of distinct factors is used. -/
private theorem norm_orderedMatrixExp_le (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (z : ℂ) :
    ‖orderedMatrixExp H z‖ ≤ Real.exp (|z.re| * (H.map (fun A => ‖A‖)).sum) := by
  induction H with
  | nil =>
    by_cases hn : Nonempty n
    · let := hn
      simp
    · let : IsEmpty n := not_nonempty_iff.mp hn
      have hzero : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
      simp [hzero]
  | cons A H ih =>
    simp only [orderedMatrixExp_cons, List.map_cons, List.sum_cons]
    calc
      _ ≤ ‖NormedSpace.exp (z • A)‖ * ‖orderedMatrixExp H z‖ := norm_mul_le _ _
      _ ≤ Real.exp (|z.re| * ‖A‖) * Real.exp (|z.re| * (H.map (fun B => ‖B‖)).sum) :=
        mul_le_mul (norm_exp_complex_smul_le (hH A (by simp)) z)
          (ih (fun B hB => hH B (by simp [hB]))) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Concatenation multiplies the products in order. -/
@[simp] theorem orderedMatrixExp_append (H K : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp (H ++ K) z = orderedMatrixExp H z * orderedMatrixExp K z := by
  simp [orderedMatrixExp, List.map_append, List.prod_append]

/-- Reversing the factors and negating time constructs an actual left
inverse; every cancellation retains its adjacent order. -/
theorem orderedMatrixExp_reverse_neg_mul (H : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp H.reverse (-z) * orderedMatrixExp H z = 1 := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  induction H with
  | nil => simp
  | cons A H ih =>
    have hcancel : NormedSpace.exp ((-z) • A) * NormedSpace.exp (z • A) = 1 := by
      simp only [neg_smul]
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (z • A)).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    rw [List.reverse_cons, orderedMatrixExp_append]
    simp only [orderedMatrixExp_cons, orderedMatrixExp_nil, mul_one]
    calc
      _ = orderedMatrixExp H.reverse (-z) *
          ((NormedSpace.exp ((-z) • A) * NormedSpace.exp (z • A)) * orderedMatrixExp H z) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hcancel, one_mul, ih]

/-- Imaginary time has no norm growth, including the empty matrix shape. -/
theorem specNorm_orderedMatrixExp_imaginary_le_one (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    specNorm (orderedMatrixExp H ((t : ℂ) * I)) ≤ 1 := by
  simpa [specNorm_eq_norm] using norm_orderedMatrixExp_le H hH ((t : ℂ) * I)

/-- The same explicit constant bounds the whole closed vertical strip. -/
theorem specNorm_orderedMatrixExp_le_exp_sum (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) {z : ℂ} (hz : |z.re| ≤ 1) :
    specNorm (orderedMatrixExp H z) ≤ Real.exp ((H.map (fun A => specNorm A)).sum) := by
  simp only [specNorm_eq_norm]
  have hs : 0 ≤ (H.map (fun A => ‖A‖)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  apply (norm_orderedMatrixExp_le H hH z).trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The explicit reverse product gives a uniform lower norm bound on the
right boundary; consequently its logarithm cannot develop a negative tail. -/
theorem exp_neg_sum_specNorm_le_specNorm_orderedMatrixExp [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    Real.exp (-(H.map (fun A => specNorm A)).sum) ≤
      specNorm (orderedMatrixExp H (1 + (t : ℂ) * I)) := by
  simp only [specNorm_eq_norm]
  have hrev : ∀ A ∈ H.reverse, A.IsHermitian := by simpa using hH
  have hInv := specNorm_orderedMatrixExp_le_exp_sum H.reverse hrev
    (z := -(1 + (t : ℂ) * I)) (by simp)
  simp only [specNorm_eq_norm, List.map_reverse, List.sum_reverse] at hInv
  have hprod := norm_mul_le (orderedMatrixExp H.reverse (-(1 + (t : ℂ) * I)))
    (orderedMatrixExp H (1 + (t : ℂ) * I))
  rw [orderedMatrixExp_reverse_neg_mul, norm_one] at hprod
  have he : 1 ≤ Real.exp ((H.map (fun A => ‖A‖)).sum) *
      ‖orderedMatrixExp H (1 + (t : ℂ) * I)‖ :=
    hprod.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
  rw [Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using he)

open Filter

/-- Native differentiability gives the genuine rescaled ordered-product
limit along reciprocal integer times. -/
private theorem tendsto_natCast_smul_orderedMatrixExp_sub_one (H : List (Matrix n n ℂ)) :
    Tendsto (fun k : ℕ => (k : ℝ) • (orderedMatrixExp H (k : ℂ)⁻¹ - 1)) atTop (𝓝 H.sum) := by
  have hzero : Tendsto (fun k : ℕ => (k : ℂ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hne : ∀ᶠ k : ℕ in atTop, (k : ℂ)⁻¹ ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hparam : Tendsto (fun k : ℕ => (k : ℂ)⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hne⟩
  have h := (hasDerivAt_orderedMatrixExp_zero H).tendsto_slope_zero.comp hparam
  simp only [zero_add, orderedMatrixExp_zero, inv_inv, Function.comp_def] at h
  simpa only [← Complex.coe_smul, Complex.ofReal_natCast] using h

/-- The actual CFC absolute values, with the same rescaling, converge to
the Hermitian sum. This discharges the matrix-specific hypothesis in the
subsequent generic Euler-power theorem. -/
private theorem tendsto_nsmul_abs_orderedMatrixExp_sub_one (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) :
    Tendsto (fun k : ℕ => k • (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹) - 1)) atTop (𝓝 H.sum) := by
  have hp : Tendsto (fun k : ℕ => orderedMatrixExp H (k : ℂ)⁻¹) atTop (𝓝 1) := by
    have h := (analyticAt_orderedMatrixExp H 0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa only [Function.comp_def, orderedMatrixExp_zero] using h
  have hsum : IsSelfAdjoint H.sum := by
    clear hp
    induction H with
    | nil => change star (0 : Matrix n n ℂ) = 0; simp
    | cons A H ih =>
      exact (hH A (by simp)).isSelfAdjoint.add (ih (fun B hB => hH B (by simp [hB])))
  have h := CFC.tendsto_smul_abs_sub_one_of_tendsto_smul_sub_one hp
    (tendsto_natCast_smul_orderedMatrixExp_sub_one H) hsum
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- Ordered products of Hermitian exponentials recover the exponential of their sum after
taking the absolute value and repeated powers. [SutterBertaTomamichel2017, Eq. (28)]. -/
theorem tendsto_abs_orderedMatrixExp_pow
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) :
    Tendsto (fun k : ℕ => (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) ^ k) atTop
      (𝓝 (NormedSpace.exp H.sum)) := by
  by_cases hn : Nonempty n
  · let := hn
    apply NormedSpace.tendsto_pow_exp_of_tangent
    simpa only [Nat.cast_smul_eq_nsmul] using tendsto_nsmul_abs_orderedMatrixExp_sub_one H hH
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have heq : (fun k : ℕ => (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) ^ k) =
        (fun _ : ℕ => NormedSpace.exp H.sum) := funext fun _ => Subsingleton.elim _ _
    rw [heq]
    exact tendsto_const_nhds

end NLAlib
