/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Step
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Guards

/-!
# Spectral input margins for active rounded PCG steps

The system matrix and reference inverse preconditioner have separate spectral intervals and
precision inequalities. The preconditioner action may be nonlinear. Its existing oracle
error bound supplies the incoming numerator margin, and the system's operator error bound
supplies the curvature margin. Nonzero residual and direction remain explicit local hypotheses.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.margins_of_spectrum_subset_Icc` derives both dot margins.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.CG.HSPCG.Rounded

/-- Separate positive spectral windows for the system and inverse preconditioner, with their
precision inequalities, imply the active-step margins whenever the residual and direction
are nonzero and the stored preconditioned residual is the actual oracle output.
[StrakosTichy2002, (7.14)]. -/
theorem margins_of_spectrum_subset_Icc {n : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {s : PCGState ℝ (Fin n)} {a a' p p' e ed em : ℝ}
    (hA : Aᵀ = A) (hP : Pᵀ = P) (ha : 0 < a) (hp : 0 < p)
    (hAspec : spectrum ℝ A ⊆ Set.Icc a a') (hPspec : spectrum ℝ P ⊆ Set.Icc p p')
    (he : 0 ≤ e) (hAprec : 3 * e * a' ≤ a) (hPprec : 3 * e * p' ≤ p)
    (hd : 0 ≤ ed) (hde : ed ≤ e) (hem : em ≤ e) (hOe : O.ε ≤ e)
    (hz : s.z = O.mulVec s.r) (hr : s.r ≠ 0) (hdir : s.p ≠ 0) :
    Margins em ed A s := by
  refine ⟨?_, ?_⟩
  · apply HSCG.Carried.Rounded.curvature_margin hP hp hPspec he hPprec hd hde hOe hr
    simpa only [hz] using O.norm_sub_mulVec_le s.r
  · exact HSCG.Carried.Rounded.curvature_margin hA ha hAspec he hAprec hd hde hem hdir

/-- The zero-start PCG state satisfies both active-step margins directly from a nonzero
right-hand side and the two spectral precision windows. No trajectory premise is needed. -/
theorem margins_zero_start_of_spectrum_subset_Icc {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {b : Fin n → ℝ}
    {a a' p p' e ed em : ℝ} (hA : Aᵀ = A) (hP : Pᵀ = P) (ha : 0 < a) (hp : 0 < p)
    (hAspec : spectrum ℝ A ⊆ Set.Icc a a') (hPspec : spectrum ℝ P ⊆ Set.Icc p p')
    (he : 0 ≤ e) (hAprec : 3 * e * a' ≤ a) (hPprec : 3 * e * p' ≤ p)
    (hd : 0 ≤ ed) (hde : ed ≤ e) (hem : em ≤ e) (hOe : O.ε ≤ e) (hb : b ≠ 0) :
    Margins em ed A ⟨0, b, O.mulVec b, O.mulVec b⟩ := by
  have hdir : O.mulVec b ≠ 0 := by
    have hh := HSCG.Carried.Rounded.curvature_margin hP hp hPspec he hPprec
      (le_refl 0) he hOe hb (O.mulVec b) (O.norm_sub_mulVec_le b)
    intro hz
    simp [hz] at hh
  exact margins_of_spectrum_subset_Icc hA hP ha hp hAspec hPspec he hAprec hPprec
    hd hde hem hOe rfl hb hdir

/-- A rounded residual/preconditioned-residual dot is nonnegative under the reference
preconditioner's spectral precision window, including an exactly zero residual. -/
theorem pairing_nonneg_of_spectrum_subset_Icc {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {r z : Fin n → ℝ}
    {rho p p' e ed : ℝ} (hP : Pᵀ = P) (hp : 0 < p)
    (hs : spectrum ℝ P ⊆ Set.Icc p p') (he : 0 ≤ e) (hprec : 3 * e * p' ≤ p)
    (hd : 0 ≤ ed) (hde : ed ≤ e) (hOe : O.ε ≤ e) (hz : z = O.mulVec r)
    (hdot : |rho - r ⬝ᵥ z| ≤ ed * ∑ i, |r i * z i|) : 0 ≤ rho := by
  by_cases hr : r = 0
  · have hh : |rho| ≤ 0 := by simpa [hr] using hdot
    exact le_of_eq (abs_eq_zero.mp (le_antisymm hh (abs_nonneg rho))).symm
  · have hm := HSCG.Carried.Rounded.curvature_margin hP hp hs he hprec hd hde hOe hr z
      (by simpa only [hz] using O.norm_sub_mulVec_le r)
    have hh := (le_abs_self (r ⬝ᵥ z - rho)).trans
      (by simpa only [abs_sub_comm] using hdot)
    linarith

end NLAlib.Krylov.CG.HSPCG.Rounded
