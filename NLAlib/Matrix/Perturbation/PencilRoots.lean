/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Matrix.Spectrum
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.ForMathlib.Analysis.Matrix.CharpolyRoots

/-!
# Roots of a Hermitian matrix pencil

The inverse pencil represents the spectral parameter through an ordinary matrix spectrum.
Its roots are bounded and the sum of those in the upper half-plane depends analytically on
each nonreal input.

## Main results

* `Matrix.IsHermitian.analyticAt_inversePencilUpperRootSum`.
-/

@[expose] public section

section

open Complex

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The pencil equation is precisely spectral membership in the forward pencil. This formulation
does not require invertibility of the slope matrix. [Stahl2013, §§2–5]. -/
private theorem det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum
    (A D : Matrix n n ℂ) (u z : ℂ) :
    (u • (1 : Matrix n n ℂ) - A + z • D).det = 0 ↔
      u ∈ spectrum ℂ (A - z • D) := by
  have heq : u • (1 : Matrix n n ℂ) - A + z • D =
      u • (1 : Matrix n n ℂ) - (A - z • D) := by abel
  rw [heq]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Algebra.algebraMap_eq_smul_one]

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil cannot have a real root in its slope variable at a nonreal spectral
parameter. In particular this applies throughout the open upper half-plane, without any simplicity
assumption on either matrix. [Stahl2013, §§2–5]. -/
private theorem im_ne_zero_of_det_hermitian_pencil_eq_zero
    {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {u z : ℂ} (hu : u.im ≠ 0)
    (hz : (u • (1 : Matrix n n ℂ) - A + z • D).det = 0) : z.im ≠ 0 := by
  intro hzim
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzim]
  have hreal : (A - z • D).IsHermitian := by
    rw [← hzreal]
    exact hA.sub (hD.smul (by simp [IsSelfAdjoint]))
  exact hu (hreal.isSelfAdjoint.im_eq_zero_of_mem_spectrum
    ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum A D u z).mp hz))

/-- For an invertible slope matrix, a root of the pencil is an eigenvalue of the inverse pencil.
This retains algebraic multiplicities when used through the characteristic polynomial. [Stahl2013,
§§2–5]. -/
theorem det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u z : ℂ) :
    (u • (1 : Matrix n n ℂ) - A + z • D).det = 0 ↔
      z ∈ spectrum ℂ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not, Algebra.algebraMap_eq_smul_one]
  have hfac : u • (1 : Matrix n n ℂ) - A + z • D =
      D * (z • (1 : Matrix n n ℂ) - D⁻¹ * (A - u • (1 : Matrix n n ℂ))) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left D _ (D.isUnit_iff_isUnit_det.mp hD)]
    abel
  rw [hfac, Matrix.det_mul]
  exact mul_eq_zero.trans (or_iff_right (D.isUnit_iff_isUnit_det.mp hD).ne_zero)

open scoped Matrix.Norms.L2Operator in
/-- Every root of an invertible matrix pencil has modulus at most
$\|\mathbf{D}^{-1}\|_2(\|\mathbf{A}\|_2+\lvert u\rvert)$, even at a root collision.
[Stahl2013, §§2–5]. -/
private theorem norm_le_specNorm_inv_mul_of_det_pencil_eq_zero
    (A D : Matrix n n ℂ) (hD : IsUnit D) {u z : ℂ}
    (hz : (u • (1 : Matrix n n ℂ) - A + z • D).det = 0) :
    ‖z‖ ≤ specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    simp at hz
  | inr hn =>
    have := hn
    have hspec :=
      (det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hD u z).mp hz
    calc
      ‖z‖ ≤ ‖D⁻¹ * (A - u • (1 : Matrix n n ℂ))‖ :=
        spectrum.norm_le_norm_of_mem hspec
      _ ≤ ‖D⁻¹‖ * ‖A - u • (1 : Matrix n n ℂ)‖ := norm_mul_le _ _
      _ ≤ ‖D⁻¹‖ * (‖A‖ + ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [norm_smul, norm_one, mul_one] using
          norm_sub_le A (u • (1 : Matrix n n ℂ))
      _ = _ := rfl

/-- The inverse characteristic roots have a common bound, independently of their multiplicities
and without requiring a Hermitian pencil. [Stahl2013, §§2–5]. -/
private theorem norm_le_specNorm_inv_mul_of_mem_roots_charpoly
    (A D : Matrix n n ℂ) (hD : IsUnit D) {u z : ℂ}
    (hz : z ∈ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots) :
    ‖z‖ ≤ specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  have hs := Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz)
  exact norm_le_specNorm_inv_mul_of_det_pencil_eq_zero A D hD
    ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hD u z).mpr hs)

/-- Any submultiset of inverse characteristic roots has a dimension-times-root bound. In
particular this supplies the uniform bound for the sum of all upper half-plane roots, including
collisions. [Stahl2013, §§2–5]. -/
private theorem norm_sum_le_card_mul_specNorm_inv_of_le_roots_charpoly
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u : ℂ) (roots : Multiset ℂ)
    (hroots : roots ≤ (D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots) :
    ‖roots.sum‖ ≤ (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  let C := specNorm D⁻¹ * (specNorm A + ‖u‖)
  have hC : 0 ≤ C := mul_nonneg (specNorm_nonneg _) (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
  have hcard : roots.card ≤ Fintype.card n := by
    exact (Multiset.card_le_card hroots).trans
      ((Polynomial.card_roots' _).trans (by rw [Matrix.charpoly_natDegree_eq_dim]))
  calc
    ‖roots.sum‖ ≤ (roots.map (fun z => ‖z‖)).sum := norm_multiset_sum_le roots
    _ ≤ roots.card • C := by
      simpa only [Multiset.card_map] using
        Multiset.sum_le_card_nsmul (roots.map (fun z => ‖z‖)) C (by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact norm_le_specNorm_inv_mul_of_mem_roots_charpoly A D hD
            (Multiset.mem_of_le hroots hz))
    _ ≤ (Fintype.card n : ℝ) * C := by
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard : (roots.card : ℝ) ≤ Fintype.card n) hC
    _ = _ := by dsimp [C]; ring

/-- A selected finite list of pencil roots has the same uniform bound. This form applies to
exterior branches at real parameter values as well as to the upper-root multiset at nonreal
parameters. [Stahl2013, §§2–5]. -/
theorem norm_sum_ite_le_card_mul_specNorm_inv_of_det_pencil_eq_zero
    (A D : Matrix n n ℂ) (hD : IsUnit D) (u : ℂ) (ev : n → ℂ)
    (hev : ∀ i, (u • (1 : Matrix n n ℂ) - A + ev i • D).det = 0)
    (p : n → Prop) [DecidablePred p] :
    ‖∑ i, if p i then ev i else 0‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  let C := specNorm D⁻¹ * (specNorm A + ‖u‖)
  have hC : 0 ≤ C := mul_nonneg (specNorm_nonneg _) (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
  calc
    ‖∑ i, if p i then ev i else 0‖ ≤ ∑ i, ‖if p i then ev i else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : n, C := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact norm_le_specNorm_inv_mul_of_det_pencil_eq_zero A D hD (hev i)
      · simpa only [norm_zero] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [C]; ring

end NLAlib

end

section

open Complex Set

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Sum of all upper-half-plane roots of `det (u I - A + z D)`, counted with their algebraic
multiplicities through the inverse characteristic polynomial. The root interpretation requires `D`
invertible; the expression is total. [Stahl2013, §§2–5]. -/
noncomputable def inversePencilUpperRootSum (A D : Matrix n n ℂ) (u : ℂ) : ℂ := by
  classical
  exact (((D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots).filter
    (fun z => 0 < z.im)).sum

/-- Selecting upper roots gives a nonnegative imaginary part, including at collisions and without
a choice of individual roots. [Stahl2013, §§2–5]. -/
theorem inversePencilUpperRootSum_im_nonneg (A D : Matrix n n ℂ) (u : ℂ) :
    0 ≤ (inversePencilUpperRootSum A D u).im := by
  exact Polynomial.im_sum_filter_roots_upper_nonneg _

/-- The actual upper-root sum of a Hermitian pencil is analytic throughout both nonreal
half-planes. The proof localizes the upper cluster by a fixed circle and permits arbitrary
collisions within the selected cluster. [Stahl2013, §§2–5]. -/
theorem _root_.Matrix.IsHermitian.analyticAt_inversePencilUpperRootSum
    {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hDu : IsUnit D) {u : ℂ} (hu : u.im ≠ 0) :
    AnalyticAt ℂ (inversePencilUpperRootSum A D) u := by
  have heq (v : ℂ) : D⁻¹ * (A - v • (1 : Matrix n n ℂ)) =
      D⁻¹ * A + v • (-D⁻¹) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_neg, sub_eq_add_neg]
  have h := Matrix.analyticAt_sum_filter_roots_charpoly_affine_upper
    (D⁻¹ * A) (-D⁻¹) u (by
      intro z hz
      rw [← heq] at hz
      exact im_ne_zero_of_det_hermitian_pencil_eq_zero hA hD hu
        ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hDu u z).mpr hz))
  change AnalyticAt ℂ (fun v => ((D⁻¹ * (A - v • (1 : Matrix n n ℂ))).charpoly.roots.filter
    (fun z => 0 < z.im)).sum) u
  simpa only [heq] using h

/-- The inverse-pencil upper-root sum is bounded uniformly on bounded parameter sets, with the
dimension recording all algebraic multiplicities. [Stahl2013, §§2–5]. -/
theorem norm_inversePencilUpperRootSum_le (A D : Matrix n n ℂ)
    (hD : IsUnit D) (u : ℂ) :
    ‖inversePencilUpperRootSum A D u‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  classical
  exact norm_sum_le_card_mul_specNorm_inv_of_le_roots_charpoly A D hD u _
    (Multiset.filter_le _ _)

end NLAlib

end
