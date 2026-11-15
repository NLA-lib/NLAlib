/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Catalog.Compare

/-!
# Reporting a singular complex pivot

Two actual scalar zero tests determine whether a stored complex pivot vanishes. A zero pivot
sets the supplied flag; a nonzero pivot retains its initial zero flag. This permits a solver
to return a singular result and skip subsequent divisions.

## Main results

* `NLAlib.ShiftedQR.checkComplexPivot`: actual pivot tests and flag update.
* `NLAlib.ShiftedQR.checkComplexPivot_writes`: exact zero/nonzero reporting without a pivot premise.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Set a previously zero flag to one exactly when both stored pivot components are zero. -/
def checkComplexPivot : Impl Op Tst := opsImpl% [] (Y, Flag) → (Flag) {
  if (Has.inj CmpTst.isZero) [] (Y) {
    if (Has.inj CmpTst.isZero) [] (Y[1]) {
      call (Has.inj (ScalarOp.lit 1)) [] () → (Flag)
    } else {
      skip
    }
  } else {
    skip
  }
}

omit [Has CmpTst Tst] in
private theorem writes_setFlag {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {y f : ℕ × ℕ} (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ (.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨1, .var 1⟩])
      (Env.frame [] [y, f, f]) (Store.inBlock f.1 f.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get f.1 f.2 = some 1) m := by
  have hw : Wp .total I τ (.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨1, .var 1⟩])
      (Env.frame [] [y, f, f]) (fun μ => μ = m.updBlock f [M.lit 1]) m := by
    refine wp_call_const (hS (.lit 1)) (z := f) rfl rfl rfl trivial (by omega) ?_
    simp [Mem.updBlock, Store.updBlock, Mem.upd]
  refine (Writes.of_wp_eq_updBlock hw).mono le_rfl ?_
  rintro μ _ rfl
  have hone : M.lit 1 = 1 := by simpa using hE.lit 1
  refine ⟨rfl, ?_⟩
  simpa [Mem.store_updBlock, Store.updBlock, hone] using
    Store.get_upd_self (s := m.store) (b := f.1) (i := f.2) (by omega) (1 : ℝ)

/-- Actual component tests report either a nonzero pivot with flag zero or a zero pivot with
flag one. No assumption rules out singular inputs. Only the flag cell may be written. -/
theorem checkComplexPivot_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {y f : ℕ × ℕ} {yv : ℂ}
    (hy0 : m.store.get y.1 y.2 = some yv.re)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.im)
    (hf0 : m.store.get f.1 f.2 = some 0) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ checkComplexPivot.body (Env.frame [] [y, f, f])
      (Store.inBlock f.1 f.2 1)
      (fun μ => μ.pos = m.pos ∧
        ((μ.store.get f.1 f.2 = some 0 ∧ yv ≠ 0) ∨
          (μ.store.get f.1 f.2 = some 1 ∧ yv = 0))) m := by
  have htest0 := hCmp.test_isZero (d := []) (m := m) (x := y) hy0
  by_cases hr : yv.re = 0
  · simp only [id_eq, hr, decide_true] at htest0
    refine writes_ite rfl rfl htest0 ?_
    have htest1 := hCmp.test_isZero (d := []) (m := m) (x := (y.1, y.2 + 1)) hy1
    by_cases hi : yv.im = 0
    · simp only [id_eq, hi, decide_true] at htest1
      refine writes_ite rfl rfl htest1 ?_
      refine (writes_setFlag (τ := τ) hS hE hf).mono le_rfl ?_
      intro μ _ ⟨hp, hflag⟩
      exact ⟨hp, Or.inr ⟨hflag, Complex.ext hr hi⟩⟩
    · simp only [id_eq, hi, decide_false] at htest1
      refine writes_ite rfl rfl htest1 ?_
      refine (Writes.skip (md := .total) (I := I) (τ := τ) ?_).mono bot_le
        (fun _ _ hp => hp)
      exact ⟨rfl, Or.inl ⟨hf0, fun he => hi (by simpa using congrArg Complex.im he)⟩⟩
  · simp only [id_eq, hr, decide_false] at htest0
    refine writes_ite rfl rfl htest0 ?_
    refine (Writes.skip (md := .total) (I := I) (τ := τ) ?_).mono bot_le (fun _ _ hp => hp)
    exact ⟨rfl, Or.inl ⟨hf0, fun he => hr (by simpa using congrArg Complex.re he)⟩⟩

end NLAlib.ShiftedQR
