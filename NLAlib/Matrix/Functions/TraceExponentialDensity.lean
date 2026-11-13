/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Spectral.SimpleSpectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import NLAlib.Matrix.Functions.TraceExponentialContour
public import NLAlib.Matrix.Perturbation.ExteriorEigenvalueBranches
public import NLAlib.Matrix.Perturbation.InversePencilBranches
public import NLAlib.ForMathlib.Analysis.Complex.EllipseIntegral
public import NLAlib.ForMathlib.Probability.Moments.CompactLaplaceTransform

/-!
# Positive density for a trace exponential

Real symmetry and the upper-half-plane sign of the inverse pencil give positivity of the contour
density. Atomic masses supply the endpoint contributions.

## Main results

* `Matrix.IsHermitian.exists_isCompactExpRepresentation_re_trace_exp_of_injective`.
-/
@[expose] public section

section
open Complex MeasureTheory
open Complex Set Metric Filter MeasureTheory

open scoped Matrix Topology ComplexConjugate

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Every actual complete exterior branch family gives the real atom-plus-density
transform identity on one fixed circle for every real parameter. This reusable
form keeps the branch family available for the separate positivity argument. -/
private theorem integral_exp_mul_re_traceExponentialCircleDensity_eq_re_trace_exp_sub_atoms
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    {R : ℝ} (hR : 0 < R) {branch : n → ℂ → ℂ}
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hspec : ∀ z, R < ‖z‖ →
      (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i z))
    {r : ℝ} (hRr : R < r) {l u : ℝ} (hlu : l ≤ u)
    (hbu : ∀ i, b i ∈ Icc l u) (t : ℝ) :
          IntervalIntegrable (fun s => Real.exp (-t * s) *
            (traceExponentialCircleDensity branch b r s).re) volume l u ∧
          (∫ s in l..u, Real.exp (-t * s) *
            (traceExponentialCircleDensity branch b r s).re) =
            (NormedSpace.exp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))).trace.re -
              ∑ i, Real.exp ((A i i).re - t * b i) := by
  have hcont (i : n) : ContinuousOn (branch i) (sphere 0 r) := by
    apply (hbranch i).1.continuousOn.mono
    intro z hz
    have heq : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    change R < ‖z‖
    rwa [heq]
  have hint : IntervalIntegrable (fun s => Complex.exp (-(t : ℂ) * s) *
      traceExponentialCircleDensity branch b r s) volume l u :=
    intervalIntegrable_exp_mul_traceExponentialCircleDensity hlu (hR.trans hRr).le hcont
  let v : ℝ := max r |t| + 1
  have hrv : r < v := by dsimp [v]; linarith [le_max_left r |t|]
  have htv : |t| < v := by dsimp [v]; linarith [le_max_right r |t|]
  have hRv : R < v := hRr.trans hrv
  have hrad (s : ℝ) : traceExponentialCircleDensity branch b r s =
      traceExponentialCircleDensity branch b v s :=
    traceExponentialCircleDensity_eq_of_differentiableOn_exterior
      (fun i => (hbranch i).1) (hR.trans hRr) (hR.trans hRv) hRr hRv s
  have hcomplex : (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
      traceExponentialCircleDensity branch b r s) =
      Matrix.trace (NormedSpace.exp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))) -
        ∑ i, Complex.exp (A i i - (t : ℂ) * b i) := by
    calc
      _ = ∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch b v s := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [hrad s]
      _ = _ := by
        apply integral_exp_mul_traceExponentialCircleDensity_eq_trace_exp_sub_atoms
          A (Matrix.diagonal (fun i => (b i : ℂ))) hlu
          (fun i => (hbu i).1) (fun i => (hbu i).2)
          (hR.trans hRv) hRv htv (fun i => (hbranch i).1) (fun i => (hbranch i).2)
        intro z hz
        have heq : ‖z‖ = v := by simpa only [mem_sphere, dist_zero_right] using hz
        have hs := hspec z (hRv.trans_eq heq.symm)
        exact (trace_exp_eq_sum_exp_of_injective_mem_spectrum _ _ hs.2 hs.1).symm
  have hweight (s : ℝ) :
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re =
      Real.exp (-t * s) * (traceExponentialCircleDensity branch b r s).re := by
    have he : Complex.exp (-(t : ℂ) * s) = (Real.exp (-t * s) : ℂ) := by
      simp
    simp only [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hintre : IntervalIntegrable (fun s =>
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re)
      volume l u := ⟨hint.1.re, hint.2.re⟩
  refine ⟨by simpa only [hweight] using hintre, ?_⟩
  have hreInt : (∫ s in l..u,
      (Complex.exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch b r s).re) =
      (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
        traceExponentialCircleDensity branch b r s).re :=
    intervalIntegral.intervalIntegral_re hint
  have hres := hreInt.trans (congrArg Complex.re hcomplex)
  have hatom (i : n) : (Complex.exp (A i i - (t : ℂ) * b i)).re =
      Real.exp ((A i i).re - t * b i) := by
    have hdiag : ((A i i).re : ℂ) = A i i := Complex.conj_eq_iff_re.mp (hA.apply i i)
    rw [← hdiag]
    simpa using Complex.exp_ofReal_re ((A i i).re - t * b i)
  simpa only [hweight, Complex.sub_re, Complex.re_sum, hatom] using hres

end NLAlib
end

section
open Complex MeasureTheory
open Complex Set Metric Filter MeasureTheory

open scoped Matrix Topology

namespace NLAlib

/-- The real atom-plus-density identity and almost everywhere nonnegativity
of its exact circle density construct a finite positive representing measure.
The underlying measure is displayed explicitly, so no measure-existence or
Laplace-transform conclusion is assumed. Positive exponential parameters here
are equivalent to the Laplace convention by substituting `-t`. -/
private theorem exists_isCompactExpRepresentation_re_trace_exp_of_circleDensity_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (branch : n → ℂ → ℂ) (r l u : ℝ)
    (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u)
    (htransform : ∀ t : ℝ,
      IntervalIntegrable (fun s => Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) volume l u ∧
      (∫ s in l..u, Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) =
        (NormedSpace.exp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))).trace.re -
          ∑ i, Real.exp ((A i i).re - t * b i))
    (hpos : ∀ᵐ s ∂volume.restrict (Icc l u),
      0 ≤ (traceExponentialCircleDensity branch b r s).re) :
    ∃ ν : FiniteMeasure ℝ,
      IsCompactExpRepresentation ν
        (fun t : ℝ => (NormedSpace.exp (A + (t : ℂ) •
            Matrix.diagonal (fun i => (b i : ℂ)))).trace.re) l u ∧
      (ν : Measure ℝ) =
        (volume.restrict (Icc l u)).withDensity
          (fun s => ENNReal.ofReal (traceExponentialCircleDensity branch b r s).re) +
          (exponentialAtomicMeasure (fun i => (A i i).re) b : Measure ℝ) := by
  let ρ : ℝ → ℝ := fun s => (traceExponentialCircleDensity branch b r s).re
  have hρint : IntervalIntegrable ρ volume l u := by
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using (htransform 0).1
  have hρ : IntegrableOn ρ (Icc l u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlu).mp hρint
  let νc : FiniteMeasure ℝ := intervalDensityMeasure ρ l u hρ
  let νa : FiniteMeasure ℝ := exponentialAtomicMeasure (fun i => (A i i).re) b
  have hrep := (isCompactExpRepresentation_intervalDensityMeasure hlu hρ hpos).add
    (isCompactExpRepresentation_exponentialAtomicMeasure (fun i => (A i i).re) b hbu)
  refine ⟨νc + νa, ?_, rfl⟩
  convert hrep using 1
  funext t
  have ht := (htransform (-t)).2
  simp only [neg_neg, neg_mul, sub_neg_eq_add, Complex.ofReal_neg, neg_smul] at ht
  dsimp only [ρ]
  linarith

/-- Nonnegativity away from the finitely many slope values already suffices
for assembling the positive measure; values at those exceptional points do not
change the density measure. The transform premise is the previously proved
real atom-plus-density formula for these exact branches. -/
private theorem exists_isCompactExpRepresentation_re_trace_exp_of_circleDensity_nonneg_off_slopes
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : n → ℝ) (branch : n → ℂ → ℂ) (r l u : ℝ)
    (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u)
    (htransform : ∀ t : ℝ,
      IntervalIntegrable (fun s => Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) volume l u ∧
      (∫ s in l..u, Real.exp (-t * s) *
        (traceExponentialCircleDensity branch b r s).re) =
        (NormedSpace.exp (A - (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)))).trace.re -
          ∑ i, Real.exp ((A i i).re - t * b i))
    (hpos : ∀ s ∈ Icc l u, s ∉ Set.range b →
      0 ≤ (traceExponentialCircleDensity branch b r s).re) :
    ∃ ν : FiniteMeasure ℝ,
      IsCompactExpRepresentation ν
        (fun t : ℝ => (NormedSpace.exp (A + (t : ℂ) •
            Matrix.diagonal (fun i => (b i : ℂ)))).trace.re) l u ∧
      (ν : Measure ℝ) =
        (volume.restrict (Icc l u)).withDensity
          (fun s => ENNReal.ofReal (traceExponentialCircleDensity branch b r s).re) +
          (exponentialAtomicMeasure (fun i => (A i i).re) b : Measure ℝ) := by
  apply exists_isCompactExpRepresentation_re_trace_exp_of_circleDensity_nonneg
    A b branch r l u hlu hbu htransform
  have hoff : ∀ᵐ s : ℝ, s ∉ Set.range b := by
    rw [ae_iff]
    convert (Set.finite_range b).measure_zero volume using 1
    congr 1
    ext s
    simp
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hoff] with s hs hsb
  exact hpos s hs hsb

end NLAlib
end

section
open Complex MeasureTheory
open Set Metric Complex Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Stahl's circle density equals the negative exponential moment of any
inverse branch family with the actual pencil spectrum and affine asymptotes.
The same-label inverse relation, contour changes, and orientation are derived
from these spectral data. This form permits the same inverse branches to be
used in the upper-root holomorphy and positivity arguments. -/
private theorem eventually_circleDensity_eq_neg_circleIntegral_of_exterior_inverse_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R S ρ : ℝ} {forward inverse : n → ℂ → ℂ}
    (hforward : ∀ i, DifferentiableOn ℂ (forward i) {z | R < ‖z‖} ∧
      Tendsto (fun z => forward i z + (b i : ℂ) * z)
        (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hinverse : ∀ i, DifferentiableOn ℂ (inverse i) {u | S < ‖u‖} ∧
        Tendsto (fun u => inverse i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hinverseSpec : ∀ u, S < ‖u‖ → ∀ i,
      u - (s : ℂ) * inverse i u ∈ spectrum ℂ
        (A - inverse i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
        traceExponentialCircleDensity forward b ρ s =
          -(2 * Real.pi * I : ℂ)⁻¹ *
            (∮ u in C(0, r), exp u * ∑ i, if b i < s then inverse i u else 0) := by
  classical
  have hcomp := eventually_inverse_branches_eq A b hb s hs
    (fun i => (hforward i).2) hforwardSpec (fun i => (hinverse i).2)
    hinverseSpec
  have hmoment : ∀ i, ∀ᶠ r : ℝ in atTop,
      (∮ z in C(0, ρ), exp (forward i z + (s : ℂ) * z)) =
        -(∮ u in C(0, r), exp u * inverse i u) := by
    intro i
    have hlim : Tendsto (fun u => inverse i u - (((s - b i)⁻¹ : ℝ) : ℂ) * u)
        (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))) := by
      simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using (hinverse i).2
    apply Complex.eventually_circleIntegral_exp_eq_neg_circleIntegral_exp_mul_of_inverse
      ((hforward i).1.add (differentiableOn_id.const_mul (s : ℂ))) (hinverse i).1
      (inv_ne_zero (sub_ne_zero.mpr (hs i))) hlim _ hρ hRρ
    exact hcomp.mono (fun u hu => hu i)
  have hmoment' : ∀ᶠ r : ℝ in atTop, ∀ i,
      (∮ z in C(0, ρ), exp (forward i z + (s : ℂ) * z)) =
        -(∮ u in C(0, r), exp u * inverse i u) := by
    simpa only [Filter.eventually_all] using hmoment
  filter_upwards [hmoment', eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S]
    with r hmoment hr hSr
  have hc : sphere (0 : ℂ) r ⊆ {u : ℂ | S < ‖u‖} := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change S < ‖u‖
    simpa only [hnorm] using hSr
  have hci (i : n) : CircleIntegrable
      (fun u => exp u * (if b i < s then inverse i u else 0)) 0 r := by
    by_cases hi : b i < s
    · simpa only [if_pos hi] using
        (Complex.continuous_exp.continuousOn.fun_mul
          ((hinverse i).1.continuousOn.mono hc)).circleIntegrable hr.le
    · simp only [if_neg hi, mul_zero]
      exact circleIntegrable_const 0 0 r
  have hsum : (∮ u in C(0, r), exp u * ∑ i, if b i < s then inverse i u else 0) =
      ∑ i, ∮ u in C(0, r), exp u * (if b i < s then inverse i u else 0) := by
    simp_rw [Finset.mul_sum]
    simpa using
      circleIntegral.integral_fun_sum (s := Finset.univ) (fun i _ => hci i)
  rw [hsum, Finset.mul_sum]
  unfold traceExponentialCircleDensity
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b i < s
  · simp only [if_pos hi]
    rw [hmoment i]
    ring
  · simp [hi, circleIntegral]

end NLAlib
end

section
open Complex MeasureTheory
open Complex Set Metric Filter MeasureTheory

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact fixed-circle density is nonnegative away from the finitely many
slopes. The proof constructs the inverse branches and actual upper-root sum;
neither a positive-density assumption nor a representing measure is used. -/
private theorem traceExponentialCircleDensity_re_nonneg_of_exterior_branches
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b)
    {R ρ : ℝ} {forward : n → ℂ → ℂ}
    (hforward : ∀ i, DifferentiableOn ℂ (forward i) {z | R < ‖z‖} ∧
      Tendsto (fun z => forward i z + (b i : ℂ) * z)
        (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hρ : 0 < ρ) (hRρ : R < ρ) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    0 ≤ (traceExponentialCircleDensity forward b ρ s).re := by
  classical
  obtain ⟨S, hS, inverse, hinverse, hinverseSpec, _, href, hroot⟩ :=
    Matrix.IsHermitian.exists_inverse_branches_root_sum hA b hb s hs
  obtain ⟨h, hdiff, hext, _, hconj, him, hbound⟩ :=
    Matrix.IsHermitian.exists_inversePencilUpperRootSum_extension hA b s hs inverse
      (fun i => (hinverse i).1) (fun u hu => (hinverseSpec u hu).1) hroot href
  have hmoment := eventually_circleDensity_eq_neg_circleIntegral_of_exterior_inverse_branches
    A b hb s hs hforward hforwardSpec hinverse (fun u hu => (hinverseSpec u hu).1) hρ hRρ
  obtain ⟨M, hmoment, hMS, hM⟩ :=
    (hmoment.and ((eventually_gt_atTop S).and (eventually_gt_atTop (0 : ℝ)))).exists
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let C := (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + M)
  have hball : ∀ z : ℂ, ‖z‖ ≤ M → ‖h z‖ ≤ C := by
    intro z hz
    exact (hbound z).trans (mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (Nat.cast_nonneg _) (specNorm_nonneg _)))
  have hpositive := Complex.neg_exp_circleIntegral_re_nonneg hM hMS
    hdiff hconj him hball
  have hdensity : traceExponentialCircleDensity forward b ρ s =
      -(2 * Real.pi * I : ℂ)⁻¹ * (∮ u in C(0, M), exp u * h u) := by
    rw [hmoment]
    congr 1
    apply circleIntegral.integral_congr hM.le
    intro u hu
    have hnorm : ‖u‖ = M := by simpa only [mem_sphere, dist_zero_right] using hu
    dsimp only
    rw [hext u (by rwa [hnorm])]
  rw [hdensity]
  simpa only [neg_mul] using hpositive

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian pencil with distinct real diagonal slopes has a positive finite
exponential representing measure on every closed interval containing those
slopes. Density positivity is proved by the planar root-sum argument, and the
atoms and density give the actual measure. -/
theorem _root_.Matrix.IsHermitian.exists_isCompactExpRepresentation_re_trace_exp_of_injective
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (hb : Function.Injective b)
    {l u : ℝ} (hlu : l ≤ u) (hbu : ∀ i, b i ∈ Icc l u) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (A + (t : ℂ) •
          Matrix.diagonal (fun i => (b i : ℂ)))).trace.re) l u := by
  obtain ⟨R, hR, forward, hforward, hspec, _⟩ :=
    Matrix.IsHermitian.exists_exterior_branches_sub_diagonal_conj_eq hA b hb
  have hr : 0 < R + 1 := by linarith
  have hRr : R < R + 1 := by linarith
  obtain ⟨ν, hν, _⟩ :=
    exists_isCompactExpRepresentation_re_trace_exp_of_circleDensity_nonneg_off_slopes
      A b forward (R + 1) l u hlu hbu
      (fun t => integral_exp_mul_re_traceExponentialCircleDensity_eq_re_trace_exp_sub_atoms
        hA b hR hforward hspec hRr hlu hbu t) (by
        intro s _ hs
        exact traceExponentialCircleDensity_re_nonneg_of_exterior_branches hA b hb
          hforward hspec hr hRr s (fun i heq => hs ⟨i, heq.symm⟩))
  exact ⟨ν, hν⟩

end NLAlib
end
