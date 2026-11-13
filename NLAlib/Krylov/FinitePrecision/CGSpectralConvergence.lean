/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGEnergy

/-!
# Finite-precision CG convergence on tiny spectral intervals

A certified Frobenius backward error puts the full run's model spectrum in a union of closed
intervals about the individual input eigenvalues. Residual polynomials bounded on any superset
of that union control physical energy, with the existing explicit initial-energy discrepancy
and rounding accumulation. The union is retained throughout the polynomial estimate.

The physical comparison uses the full-run small-roundoff hypothesis (H); localization itself
uses only the supplied Frobenius certificate. Step zero and a zero terminal residual are allowed.
[GreenbaumLiuChen2021, §1.3, (9)] motivates the tiny-interval minimax set.

## Main results

* `NLAlib.CGRun.spectrum_backwardH_subset_iUnion_Icc`: union-of-intervals localization.
* `NLAlib.CGRun.quadForm_sub_x_le_sq_mul_add_of_polynomial`: physical polynomial convergence.
* `NLAlib.CGRun.quadForm_sub_x_le_residualMinimax_sq_mul_add`: spectral-set minimax convergence.
* `NLAlib.CGRun.ρ_sq_le_mul_sq_mul_of_polynomial`: computed residual convergence.
-/

@[expose] public section

open scoped Matrix MatrixOrder Polynomial

namespace NLAlib

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The full backward model spectrum lies in the union of radius-$\delta$ closed intervals
about the valid input eigenvalues when its Frobenius backward distance is at most $\delta$. -/
theorem spectrum_backwardH_subset_iUnion_Icc {δ : ℝ}
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ) :
    spectrum ℝ C.backwardH ⊆ ⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ) :=
  C.toNormalizedLanczosData.spectrum_backwardH_subset_iUnion_Icc hgap

private theorem posDef_backwardH {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    C.backwardH.PosDef := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  exact C.isHermitian_backwardH.posDef_iff_eigenvalue_pos.mpr fun i hi =>
    (by positivity : 0 < a / 2).trans_le
      (C.isHermitian_backwardH.spectrum_subset_iff.mp hspec i hi).1

/-- **Tiny-interval polynomial convergence of computed CG.** For a successful $k$-step run,
input spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, let $S$ contain all closed radius-$\delta$
intervals about the input eigenvalues, where the Frobenius backward distance is at most
$\delta$. For $j\le k$, every real polynomial $p$ of degree at most $j$ with $p(0)=1$ and
$\lvert p\rvert\le\eta$ on $S$ gives
$$\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2
\le\eta^2(\|\mathbf{x}_\star\|_{\mathbf{A}}^2+\Delta)+\Delta+R_j\,.$$
Here $\mathbf{A}\mathbf{x}_\star=\mathbf{b}$. With
the value <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$, the initial
comparison error is $\Delta=2\|\mathbf{b}\|^2c/a^2$.
The term is <!-- value cgEnergyFactor j -->$R_j=135j^2\varepsilon\kappa\|\mathbf{b}\|^2/a$.
The model error is that of exact $\mathsf{cgIterate}$ on the full backward model.
[GreenbaumLiuChen2021, §1.3, (9)]; here a squared physical-energy statement with explicit
additive errors, rather than the qualitative tiny-interval minimax discussion.
Result: cg-tiny-interval-polynomial-convergence -/
theorem quadForm_sub_x_le_sq_mul_add_of_polynomial {a a' δ η : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ) {S : Set ℝ}
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) {p : ℝ[X]}
    (hp : p.degree ≤ j) (hp₀ : p.eval 0 = 1) (hη : ∀ x ∈ S, |p.eval x| ≤ η) :
    quadForm C.A (xs - C.x j) ≤
      η ^ 2 * (quadForm C.A xs +
        2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2) +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hPD := C.posDef_backwardH ha hs hsmall
  let ys := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hy : C.backwardH *ᵥ ys = C.dilatedRhs := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit), Matrix.one_mulVec]
  have hpoly := hPD.re_quadForm_sub_cgIterate_le
    ((C.spectrum_backwardH_subset_iUnion_Icc hgap).trans hS) hy 0 hp hp₀ hη
  simp only [RCLike.re_to_real, sub_zero] at hpoly
  have hinit := (abs_le.mp (C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx)).2
  have hphysical := C.quadForm_sub_x_le_quadForm_backwardH_sub_cgIterate_add
    ha hs hsmall hx hy hj
  apply hphysical.trans
  gcongr
  apply hpoly.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
  linarith

/-- **Computed residual convergence on tiny intervals.** For a successful $k$-step run,
input spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, let $S$ contain all closed radius-$\delta$
intervals about the input eigenvalues, with Frobenius backward distance at most $\delta$.
For $j\le k$, a real polynomial $p$ of degree at most $j$, $p(0)=1$ and
$\lvert p\rvert\le\eta$ on $S$ gives
$$\|\mathbf{r}_j\|^2\le(a'+a/2)\eta^2
(\|\mathbf{x}_\star\|_{\mathbf{A}}^2+\Delta)\,.$$
Here $\mathbf{A}\mathbf{x}_\star=\mathbf{b}$; the coefficient
is <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$ gives
$\Delta=2\|\mathbf{b}\|^2c/a^2$.
Exact $\mathsf{cgIterate}$ on the full model reproduces the computed residual norms.
[GreenbaumLiuChen2021, §1.3, (9)]; the polynomial set is retained and no residual gap is assumed.
Result: cg-tiny-interval-computed-residual -/
theorem ρ_sq_le_mul_sq_mul_of_polynomial {a a' δ η : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ) {S : Set ℝ}
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) {p : ℝ[X]}
    (hp : p.degree ≤ j) (hp₀ : p.eval 0 = 1) (hη : ∀ x ∈ S, |p.eval x| ≤ η) :
    C.ρ j ^ 2 ≤ (a' + a / 2) * η ^ 2 * (quadForm C.A xs +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2) := by
  have hPD := C.posDef_backwardH ha hs hsmall
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hu : C.backwardH ≤ (a' + a / 2) • (1 : Matrix _ _ ℝ) :=
    (C.isHermitian_backwardH.le_smul_one_iff_spectrum_subset_Iic _).mpr
      fun x hx => (hspec hx).2
  have haa' := C.isHermitian.spectrum_subset_iff.mp hs 0 (by
    simpa only [Fintype.card_fin] using C.n_pos)
  have hu0 : 0 ≤ a' + a / 2 := by linarith [haa'.1, haa'.2]
  let ys := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hy : C.backwardH *ᵥ ys = C.dilatedRhs := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit), Matrix.one_mulVec]
  have hr : (cgState C.backwardH C.dilatedRhs 0 j).r =
      C.backwardH *ᵥ (ys - cgIterate C.backwardH C.dilatedRhs 0 j) := by
    rw [cgState_r_eq, hPD.cgState_x_eq, Matrix.mulVec_sub, hy]
  have hres := hPD.posSemidef.norm_toLp_mulVec_sq_le hu
    (ys - cgIterate C.backwardH C.dilatedRhs 0 j)
  rw [← hr, C.norm_cgState_backwardH_r_of_posDef hPD hj] at hres
  have hpoly := hPD.re_quadForm_sub_cgIterate_le
    ((C.spectrum_backwardH_subset_iUnion_Icc hgap).trans hS) hy 0 hp hp₀ hη
  simp only [RCLike.re_to_real, sub_zero] at hpoly hres
  have hinit := (abs_le.mp (C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx)).2
  calc
    C.ρ j ^ 2 ≤ (a' + a / 2) *
        (η ^ 2 * quadForm C.backwardH ys) :=
      hres.trans (mul_le_mul_of_nonneg_left hpoly hu0)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hu0 (sq_nonneg η))

/-- **Tiny-interval minimax convergence of computed CG.** For a successful $k$-step run,
input spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, let a set $S$ contain all closed
radius-$\delta$ intervals about input eigenvalues, where the Frobenius backward distance
is at most $\delta$. For $j\le k$ and $\mathbf{A}\mathbf{x}_\star=\mathbf{b}$,
$$\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2\le
\mathsf{residualMinimax}(S,j)^2(\|\mathbf{x}_\star\|_{\mathbf{A}}^2+\Delta)+\Delta+R_j\,.$$
With <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$, put
$\Delta=2\|\mathbf{b}\|^2c/a^2$.
The term is <!-- value cgEnergyFactor j -->$R_j=135j^2\varepsilon\kappa\|\mathbf{b}\|^2/a$.
The error of exact $\mathsf{cgIterate}$ on the full model supplies the minimax factor.
[GreenbaumLiuChen2021, §1.3, (9)]; here squared physical energy with explicit additive errors.
Result: cg-tiny-interval-minimax-convergence -/
theorem quadForm_sub_x_le_residualMinimax_sq_mul_add {a a' δ : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ) {S : Set ℝ}
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤
      residualMinimax S j ^ 2 * (quadForm C.A xs +
        2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2) +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hPD := C.posDef_backwardH ha hs hsmall
  let ys := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hy : C.backwardH *ᵥ ys = C.dilatedRhs := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit), Matrix.one_mulVec]
  have hpoly := hPD.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul hy 0 j
  simp only [RCLike.re_to_real, sub_zero] at hpoly
  have hmono := residualMinimax_mono
    ((C.spectrum_backwardH_subset_iUnion_Icc hgap).trans hS) j
  have hE : 0 ≤ quadForm C.backwardH ys := by
    simpa only [RCLike.re_to_real] using hPD.posSemidef.re_quadForm_nonneg ys
  have hmodel := hpoly.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (residualMinimax_nonneg _ _) hmono 2) hE)
  have hinit := (abs_le.mp (C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx)).2
  have hphysical := C.quadForm_sub_x_le_quadForm_backwardH_sub_cgIterate_add
    ha hs hsmall hx hy hj
  apply hphysical.trans
  gcongr
  apply hmodel.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (residualMinimax S j))
  linarith

end CGRun

end NLAlib
