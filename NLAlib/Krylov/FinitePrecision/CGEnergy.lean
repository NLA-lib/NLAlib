/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGAccuracy

/-!
# Energy convergence of finite-precision conjugate gradients

The accumulated computed decrements control the physical energy with an additive error
that vanishes with the arithmetic precision. Comparison with exact CG on the backward
model then transfers its polynomial convergence bound without a residual-to-energy loss.

## Main results

* `NLAlib.CGRun.quadForm_sub_x_le_sub_sum_add`: physical energy and computed decrements.
* `NLAlib.CGRun.quadForm_sub_x_le_four_mul_pow_add`: direct energy convergence.
* `NLAlib.CGRun.sum_γ_mul_ρ_sq_ge`: an explicit lower bound on computed decrements.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The energy accumulation factor, currently <!-- value cgEnergyFactor j -->$135j^2$.
This is an explicit rounding budget for physical CG energy, not a literature constant. -/
noncomputable irreducible_def cgEnergyFactor (j : ℕ) : ℝ := 135 * (j : ℝ) ^ 2

/-- The energy accumulation factor is nonnegative. -/
theorem cgEnergyFactor_nonneg (j : ℕ) : 0 ≤ cgEnergyFactor j := by
  rw [cgEnergyFactor_def]
  positivity

/-- The explicit comparison for the energy accumulation factor is <!-- value cgEnergyFactor j -->
$135j^2$. -/
theorem cgEnergyFactor_le (j : ℕ) : cgEnergyFactor j ≤ 135 * (j : ℝ) ^ 2 := by
  rw [cgEnergyFactor_def]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

private theorem energy_κ_nonneg {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') : 0 ≤ a' / a := by
  have h := C.isHermitian.spectrum_subset_iff.mp hs 0 (by
    simp only [Fintype.card_fin]
    exact C.n_pos)
  exact div_nonneg (ha.le.trans (h.1.trans h.2)) ha.le

private theorem energy_weighted_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) +
      ∑ i ∈ Finset.range j, (1 - (52 * i + 6) * (C.ε * (a' / a))) *
        (C.γ i * C.ρ i ^ 2) ≤
    quadForm C.A xs + 25 * j ^ 2 * (C.ε * (a' / a)) *
      (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hz : 0 ≤ C.ε * (a' / a) := mul_nonneg C.ε_nonneg (C.energy_κ_nonneg ha hs)
  have hu : 0 ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by positivity
  induction j with
  | zero =>
    rw [C.x_zero, sub_zero, Finset.sum_range_zero]
    simp only [Nat.cast_zero, zero_pow two_ne_zero, mul_zero, zero_mul, add_zero]
    exact le_rfl
  | succ j ih =>
    have hjk : j < k := by omega
    have h := C.quadForm_sub_x_succ_le_sub_add ha hs hsmall hx hjk
    have hprevious := ih hjk.le
    rw [Finset.sum_range_succ]
    push_cast
    have herr : (36 * (j : ℝ) + 19) * (C.ε * (a' / a)) *
        (‖WithLp.toLp 2 C.b‖ ^ 2 / a) ≤
      (50 * j + 25) * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
      gcongr <;> norm_num
    nlinarith

/-- **Physical energy and computed decrements.** For a successful $k$-step CG run with
spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ satisfies for $j\le k$, with
error <!-- value cgEnergyFactor j -->
$R_j=135j^2\varepsilon\kappa\|\mathbf{b}\|^2/a$,
$$\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2\le
\|\mathbf{x}_\star\|_{\mathbf{A}}^2-\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2+R_j .$$
The coefficient of the computed decrement sum is exactly one. No printed source.
Result: cg-physical-energy-decrements -/
theorem quadForm_sub_x_le_sub_sum_add {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ quadForm C.A xs -
      ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  rcases j with _ | j
  · rw [C.x_zero, sub_zero, Finset.sum_range_zero, cgEnergyFactor_def]
    simp only [Nat.cast_zero, zero_pow two_ne_zero, mul_zero, zero_mul, sub_zero, add_zero]
    exact le_rfl
  have hz : 0 ≤ C.ε * (a' / a) := mul_nonneg C.ε_nonneg (C.energy_κ_nonneg ha hs)
  have hu : 0 ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by positivity
  have hweighted := C.energy_weighted_sum_le ha hs hsmall hx hj
  set S := ∑ i ∈ Finset.range (j + 1), C.γ i * C.ρ i ^ 2
  have hS : S ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
    have hmono : S ≤ ∑ i ∈ Finset.range k, C.γ i * C.ρ i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        (fun i hi _ => mul_nonneg (C.γ_pos (Finset.mem_range.mp hi)).le (sq_nonneg _))
    simpa only [mul_div_assoc] using hmono.trans (C.sum_γ_mul_ρ_sq_le ha hs hsmall)
  have hW : (1 - 52 * (j + 1 : ℕ) * (C.ε * (a' / a))) * S ≤
      ∑ i ∈ Finset.range (j + 1), (1 - (52 * i + 6) * (C.ε * (a' / a))) *
        (C.γ i * C.ρ i ^ 2) := by
    dsimp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hir : (i : ℝ) + 1 ≤ (j + 1 : ℕ) := by
      exact_mod_cast Finset.mem_range.mp hi
    have hγρ : 0 ≤ C.γ i * C.ρ i ^ 2 :=
      mul_nonneg (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hγρ
    nlinarith
  have hbudget := mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ 52 * (j + 1 : ℕ) * (C.ε * (a' / a)))
  have hj2 : (j + 1 : ℝ) ≤ (j + 1 : ℝ) ^ 2 := by
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    nlinarith
  have herr := mul_le_mul_of_nonneg_right hj2 (mul_nonneg hz hu)
  rw [cgEnergyFactor_def]
  push_cast at hweighted hW hbudget ⊢
  nlinarith [mul_nonneg (sq_nonneg ((j : ℝ) + 1)) (mul_nonneg hz hu)]

/-- **Physical energy compared with model energy.** For a successful $k$-step CG run with
spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, solutions
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and
$\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star=\tilde{\mathbf{b}}$ satisfy, for $j\le k$,
$$\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2\le
\|\tilde{\mathbf{x}}_\star-\mathsf{cgIterate}(\tilde{\mathbf{H}},
\tilde{\mathbf{b}},\mathbf{0},j)\|_{\tilde{\mathbf{H}}}^2+\eta+R_j .$$
Here <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$,
$\eta=2\|\mathbf{b}\|^2c/a^2$, and the rounding error is <!-- value cgEnergyFactor j -->
$R_j=135j^2\varepsilon\kappa\|\mathbf{b}\|^2/a$.
The backward model is that of the full $k$-step run. No printed source. -/
theorem quadForm_sub_x_le_quadForm_backwardH_sub_cgIterate_add {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {ys : Fin n × Fin (k + 1) → ℝ} (hy : C.backwardH *ᵥ ys = C.dilatedRhs)
    {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤
      quadForm C.backwardH (ys - cgIterate C.backwardH C.dilatedRhs 0 j) +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hmodel := C.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate
    ha hs hsmall hy (j := 0) (d := j) (by omega)
  rw [cgIterate_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at hmodel
  have hinit := C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx
  have hphysical := C.quadForm_sub_x_le_sub_sum_add ha hs hsmall hx hj
  linarith [(abs_le.mp hinit).1]

/-- **Computed decrements from energy convergence.** For a successful $k$-step CG run with
spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ satisfies, for $j\le k$,
$$\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2\ge
(1-4q^{2j})\|\mathbf{x}_\star\|_{\mathbf{A}}^2-\eta ,$$
where $q=(\sqrt{2\kappa+1}-1)/(\sqrt{2\kappa+1}+1)$, and
with <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$ and
$\eta=2\|\mathbf{b}\|^2c/a^2$.
No printed source. The exact-model Chebyshev estimate is
[Saad2003, Theorem 6.29]; this statement concerns the computed decrement sum. -/
theorem sum_γ_mul_ρ_sq_ge {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    (1 - 4 * ((Real.sqrt (2 * (a' / a) + 1) - 1) /
      (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ (2 * j)) * quadForm C.A xs -
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 ≤
      ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hPD : C.backwardH.PosDef := C.isHermitian_backwardH.posDef_iff_eigenvalue_pos.mpr
    fun i hi => (by positivity : 0 < a / 2).trans_le
      (C.isHermitian_backwardH.spectrum_subset_iff.mp hspec i hi).1
  let ys := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hy : C.backwardH *ᵥ ys = C.dilatedRhs := by
    dsimp only [ys]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit), Matrix.one_mulVec]
  have hmodel := C.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate
    ha hs hsmall hy (j := 0) (d := j) (by omega)
  rw [cgIterate_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at hmodel
  have hcheb := C.isHermitian_backwardH.re_quadForm_sub_cgIterate_le_four_mul_pow
    (by positivity : 0 < a / 2) hspec hy 0 j
  have hratio : (a' + a / 2) / (a / 2) = 2 * (a' / a) + 1 := by field_simp
  rw [hratio, sub_zero] at hcheb
  simp only [RCLike.re_to_real] at hcheb
  set Q := 4 * ((Real.sqrt (2 * (a' / a) + 1) - 1) /
    (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ (2 * j)
  set η := 2 * ‖WithLp.toLp 2 C.b‖ ^ 2 *
    (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2
  change (1 - Q) * quadForm C.A xs - η ≤ _
  have hQ0 : 0 ≤ Q := by dsimp [Q]; rw [pow_mul]; positivity
  have hinit := C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hy hx
  change |quadForm C.backwardH ys - quadForm C.A xs| ≤ η at hinit
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hinit
  have hdiff : quadForm C.A xs - quadForm C.backwardH ys ≤ η := by
    linarith [(abs_le.mp hinit).1]
  have hS0 : 0 ≤ ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg
      (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
  rcases le_total Q 1 with hQ1 | hQ1
  · have hscaled := mul_le_mul_of_nonneg_left hdiff (by linarith : 0 ≤ 1 - Q)
    have hηsmall : (1 - Q) * η ≤ η := by nlinarith
    change quadForm C.backwardH (ys - cgIterate C.backwardH C.dilatedRhs 0 j) ≤
      Q * quadForm C.backwardH ys at hcheb
    nlinarith
  · have hA : C.A.PosDef := C.isHermitian.posDef_iff_eigenvalue_pos.mpr fun i hi =>
      ha.trans_le (C.isHermitian.spectrum_subset_iff.mp hs i hi).1
    have hE0 : 0 ≤ quadForm C.A xs := by
      rw [quadForm_def]
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg xs
    have hnegative : (1 - Q) * quadForm C.A xs ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hE0
    linarith

/-- **Direct energy convergence in finite precision.** For a successful $k$-step CG run with
spectrum in $[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^2\sqrt{k}\varepsilon\kappa^2\le10^{-5}$, a solution
$\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ satisfies, for $j\le k$,
$$\|\mathbf{x}_\star-\mathbf{x}_j\|_{\mathbf{A}}^2\le
4q^{2j}\|\mathbf{x}_\star\|_{\mathbf{A}}^2+\eta+R_j ,$$
where $q=(\sqrt{2\kappa+1}-1)/(\sqrt{2\kappa+1}+1)$, and
with <!-- value cgBackwardFactor k -->$c=6000k^2\sqrt{k}\varepsilon\kappa a'$,
$\eta=2\|\mathbf{b}\|^2c/a^2$ and the rounding error is <!-- value cgEnergyFactor j -->
$R_j=135j^2\varepsilon\kappa\|\mathbf{b}\|^2/a$.
This is a finite-horizon upper envelope for the energy of the computed iterates; both additive
terms vanish at zero precision. No printed source. The exact-model Chebyshev estimate is
[Saad2003, Theorem 6.29]; the transfer uses the computed decrements directly.
Result: cg-physical-energy-convergence -/
theorem quadForm_sub_x_le_four_mul_pow_add {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤
      4 * ((Real.sqrt (2 * (a' / a) + 1) - 1) /
        (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ (2 * j) * quadForm C.A xs +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hphysical := C.quadForm_sub_x_le_sub_sum_add ha hs hsmall hx hj
  have hsum := C.sum_γ_mul_ρ_sq_ge ha hs hsmall hx hj
  nlinarith

end CGRun

end NLAlib
