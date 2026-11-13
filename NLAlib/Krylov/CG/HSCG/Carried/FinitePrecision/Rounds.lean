/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.State
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Prefix

/-!
# Successful rounded CG loops from input spectral precision

The existing carried-product loop is proved total under explicit mathematical input bounds.
Each active prefix is an existing CGRun; initial or terminal zero residuals stop before the
next division. Curvature and direction guards are derived internally from the spectrum and
precision horizon, rather than assumed along a trajectory.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.rounds_writes` extracts successful rounded prefixes.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The loop returns an initialized zero-step state or an existing run, with early exit only
at a zero decoded residual. The common error bound is an explicit envelope of local bounds. -/
theorem rounds_writes {M : Machine K} {dec : K → ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hM : StdModel u dec M)
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I)
    (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {τ : Tape K} {μ : Mem K} {x r p v : ℕ × ℕ} {rho : ℝ}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v]) (hs : StoresValues dec n x r p v ⟨0, b, b⟩ rho μ)
    (hcache : |rho - b ⬝ᵥ b| ≤ ε.dot n * ∑ i, |b i * b i|)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ Carried.rounds (Env.frame [n, cap] [x, r, p, v, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho',
        StoresValues dec n x r p v s rho' μ' ∧ IsPrefix A b e m s rho' ∧
          (m < cap → s.r = 0)) μ := by
  classical
  let F := Fp.blocks [x, r, p, v] [n, n, n, 1]
  let Inv := fun j μ' => μ'.pos = μ.pos ∧ ∃ s rho',
    StoresValues dec n x r p v s rho' μ' ∧ IsPrefix A b e j s rho' ∧
      |rho' - s.r ⬝ᵥ s.r| ≤ ε.dot n * ∑ i, |s.r i * s.r i|
  have hed : ε.dot n < 1 := lt_of_le_of_lt (hde.trans he) (by norm_num)
  refine (writes_whileFuel rfl (fun _ => F) (fun _ _ => le_rfl) ⊥ Inv _
    ⟨rfl, ⟨0, b, b⟩, rho, hs, Or.inl ⟨rfl, rfl⟩, hcache⟩ ?_ ?_).mono
      (by simp [F]) (fun _ _ h => h)
  · rintro j hj μ' hfr ⟨hpos, s, rho', hstored, hprefix, hcache'⟩
    obtain ⟨rr, hrr, hrrd⟩ := hstored.read_rho
    by_cases hactive : 0 < rho'
    · refine ⟨true, ?_, ?_⟩
      · rw [Interp.testAt_eq rfl rfl, hCmp.test_isPos hrr, hrrd]
        simp only [hactive, decide_true]
      · have hrne : s.r ≠ 0 := by
          intro hzero
          simp only [hzero, zero_dotProduct, Pi.zero_apply, abs_zero,
            Finset.sum_const_zero, mul_zero, sub_zero] at hcache'
          exact hactive.not_ge (le_trans (le_abs_self _) hcache')
        have hpne := hprefix.direction_ne_zero ha hspec (Nat.le_of_lt hj) hwindow hrne
        have hmarg := curvature_margin hAT ha hspec (hu.trans hue) hprec hd hde hem hpne
        have hl' : μ'.Live [x, r, p, v] := by simpa only [Mem.Live, hfr.length_eq] using hl
        have hz' : μ'.Room [x, r, p, v] [n, n, n, 1] := by
          simpa [Mem.Room, hfr.len_eq] using hz
        refine (writes_frame rfl rfl ((μ'.live_append _ _).mpr ⟨hl', hl'⟩)
          (step_writes hS hM hB hok hA hxr hxp hxv hrp hrv hpv hl' hstored
            hed hrne hcache' hmarg hz')).mono le_rfl ?_
        rintro μ'' _ ⟨hpos', next, nu, hstored', hbounds⟩
        exact ⟨hpos'.trans hpos, next, nu, hstored',
          hprefix.advance hbounds hAT hu hd haa hem hue hde hae he hcache', hbounds.cache_bound⟩
    · refine ⟨false, ?_, ?_⟩
      · rw [Interp.testAt_eq rfl rfl, hCmp.test_isPos hrr, hrrd]
        simp only [hactive, decide_false]
      · have hrzero : s.r = 0 := by
          by_contra hrne
          exact hactive (self_dot_pos hd hed hrne hcache')
        exact Writes.skip ⟨hpos, j, Nat.le_of_lt hj, s, rho', hstored, hprefix, fun _ => hrzero⟩
  · rintro μ' _ ⟨hpos, s, rho', hstored, hprefix, _⟩
    exact Writes.skip ⟨hpos, cap, le_rfl, s, rho', hstored, hprefix, by omega⟩

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
