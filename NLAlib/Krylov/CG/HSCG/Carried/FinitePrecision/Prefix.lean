/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Recurrence
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Guards

/-!
# Mathematical prefixes used by the rounded CG loop

A zero-step state is kept separate because the existing CGRun requires positive length.
Every nonzero prefix is the existing run record tied to its actual endpoint and cache.
The spectral horizon controls direction breakdown through the existing finite-precision math.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.IsPrefix.advance` appends an actual local recurrence.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.IsPrefix.direction_ne_zero` derives continuation.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open scoped Matrix

/-- Either the initial zero-step state or an existing positive-length run with the stated
matrix, right-hand side, error bound, endpoint and computed residual product. -/
def IsPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (e : ℝ)
    (j : ℕ) (s : CGState ℝ (Fin n)) (rho : ℝ) : Prop :=
  (j = 0 ∧ s = ⟨0, b, b⟩) ∨ ∃ R : CGRun n j, R.A = A ∧ R.b = b ∧ R.ε = e ∧
    (⟨R.x j, R.r j, R.p j⟩ : CGState ℝ (Fin n)) = s ∧ R.ν j = rho

/-- The new self-dot bound is part of the actual rounded recurrence. -/
theorem RoundBounds.cache_bound {n : ℕ} {em u ed ea : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {s s' : CGState ℝ (Fin n)} {rho rho' : ℝ}
    (h : RoundBounds em u ed ea A s s' rho rho') :
    |rho' - s'.r ⬝ᵥ s'.r| ≤ ed * ∑ i, |s'.r i * s'.r i| := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcache, _, _⟩ := h
  exact hcache

/-- A self-dot approximation with error below one is positive for a nonzero vector.
[Higham2002, (3.5)]. -/
theorem self_dot_pos {n : ℕ} {e rho : ℝ} {r : Fin n → ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hr : r ≠ 0) (hcache : |rho - r ⬝ᵥ r| ≤ e * ∑ i, |r i * r i|) : 0 < rho := by
  obtain ⟨theta, htheta, hthetaeq⟩ := self_dot_relative he r hcache
  have hnorm : 0 < ‖WithLp.toLp 2 r‖ := norm_pos_iff.mpr
    (fun h => hr ((WithLp.toLp_eq_zero 2).mp h))
  have htheta' := (abs_le.mp htheta).1
  rw [hthetaeq]
  exact mul_pos (sq_pos_of_pos hnorm) (by linarith)

/-- One actual rounded recurrence extends the mathematical prefix, including its first step.
The input cache envelope comes from initialization or the previous rounded dot. -/
theorem IsPrefix.advance {n j : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {em u ed ea e rho rho' : ℝ} {s s' : CGState ℝ (Fin n)}
    (h : IsPrefix A b e j s rho) (hstep : RoundBounds em u ed ea A s s' rho rho')
    (hA : Aᵀ = A) (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) (he : e ≤ 1 / 100)
    (hcache : |rho - s.r ⬝ᵥ s.r| ≤ ed * ∑ i, |s.r i * s.r i|) :
    IsPrefix A b e (j + 1) s' rho' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨R, hRA, hRb, hRe, hs, hrho⟩
  · exact Or.inr (hstep.exists_cgRun_one hA hu hd ha hem hue hde hae he hcache)
  · subst A b e s rho
    exact Or.inr (hstep.exists_cgRun_succ R hu hd ha hem hue hde hae)

/-- Input spectral precision controls the current direction at every nonconverged prefix.
No successful-execution or future-curvature premise is used. [StrakosTichy2002, §7]. -/
theorem IsPrefix.direction_ne_zero {n j cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {b : Fin n → ℝ} {e rho : ℝ} {s : CGState ℝ (Fin n)} (h : IsPrefix A b e j s rho)
    {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a') (hj : j ≤ cap)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hr : s.r ≠ 0) : s.p ≠ 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨R, hRA, hRb, hRe, hs, hrho⟩
  · exact hr
  · subst A b e s rho
    have he0 := R.ε_nonneg
    have hsmall : (j : ℝ) ^ 2 * Real.sqrt j * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
      calc
        _ ≤ (cap : ℝ) ^ 2 * Real.sqrt cap * R.ε * (a' / a) ^ 2 := by
          gcongr
        _ ≤ _ := hwindow
    exact R.p_ne_zero_of_r_ne_zero ha hspec hsmall hr

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
