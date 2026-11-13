/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzLevel

/-!
# The complete scalar Ritz-search level loop

The loop invariant identifies the actual stored start with the retained mathematical search
window. Every natural read is bounded by the original power-of-two list count. Halving reaches
zero only after the singleton has been selected and is never read by another level.

## Main results

* `NLAlib.ShiftedQR.findRitzLevels_writes`: all actual levels preserve the exact search window.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The actual level loop reaches the mathematical selected index while retaining the
source blocks. Every runtime natural-index bound follows from the power-of-two window.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzLevels_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    (hCmp : IsCmp id I) (hToNat : IsToNat id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n levels k : ℕ} {b ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hlen : shifts.length = k)
    (hk : k = 2 ^ levels) (hwords : SearchWords r 0 (k / 2) 1 m.store)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ findRitzLevels.body (Env.frame [n + 1, levels, k] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        SearchWords r (searchStart H shifts levels levels) (searchHalfLength levels levels)
          (2 ^ levels) m'.store) m := by
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_loop (N := levels) rfl (fun _ => Store.inBlock r.1 r.2 6) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
      HoldsShifts (k := k) ss shifts m'.store ∧
      SearchWords r (searchStart H shifts levels i) (searchHalfLength levels i) (2 ^ i) m'.store)
    ⟨rfl, hB, hSS, by simpa only [searchStart, searchHalfLength, Nat.sub_zero, pow_zero, hk]
      using hwords⟩ ?_
  intro i hi m' hfr ⟨hp, hB', hSS', hwords'⟩
  have hfit := (searchStart_spec H shifts levels (hlen.trans hk) i (by omega)).1
  have hspan : 2 * searchHalfLength levels i = 2 ^ (levels - i) := by
    rw [searchHalfLength_eq hi]
    conv_rhs => rw [show levels - i = (levels - i - 1) + 1 by omega, pow_succ]
    omega
  have hbound : searchStart H shifts levels i + 2 * searchHalfLength levels i ≤ k := by
    rw [hspan, ← hlen]
    exact hfit
  have he : 2 ^ i ≤ k := by
    rw [hk]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hw := findRitzLevel_writes hS hE hL hCmp hToNat (τ := τ)
    hH hB' hSS' hwords' hdet hbound (by rw [hlen]; exact hbound) (by omega) (by omega) he
    hra hrs (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hr)
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro m'' _ ⟨hp', hB'', hSS'', hnew⟩
  refine ⟨hp'.trans hp, hB'', hSS'', ?_⟩
  simpa only [searchStart, searchHalfLength_succ hi, pow_succ, Nat.mul_comm 2] using hnew

end NLAlib.ShiftedQR
