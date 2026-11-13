/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Catalog.Scalar

/-!
# Explicit zero-iterate initialization

The initializer writes actual scalar literals into the supplied iterate capacity. Canonical
CG problems therefore need no initialized output or numerical preprocessing.

## Main results

* `NLAlib.Krylov.CG.zeroVector`: the fixed scalar loop.
* `NLAlib.Krylov.CG.writes_zeroVector`: total initialization from capacity alone.
-/

@[expose] public section

namespace NLAlib.Krylov.CG

open Ops

/-- Fill a supplied vector with literal zero using one visible scalar call per entry. -/
def zeroVector {Op Tst : Type} [Has ScalarOp Op] : Impl Op Tst :=
  opsImpl% [n] () → (X) {
    for i < n { call (Has.inj (ScalarOp.lit 0)) [] () → (X[i]) }
  }

/-- The initializer charges one actual literal call per supplied vector entry. -/
theorem staticCost_zeroVector {Op Tst : Type} [Has ScalarOp Op] (n off : ℕ) :
    stmtCost (zeroVector (Op := Op) (Tst := Tst)).body [n, off] =
      n • Count.one (Has.inj (ScalarOp.lit 0)) [] := by
  simp [zeroVector, stmtCost, IExp.eval, useCost]

/-- Actual zero filling needs only output capacity and preserves the tape position. -/
theorem writes_zeroVector {K Op Tst : Type} [Has ScalarOp Op] {M : Machine K}
    {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K} {m : Mem K}
    {n : ℕ} {x : ℕ × ℕ} (hroom : x.2 + n ≤ m.store.len x.1) :
    Writes .total I τ (zeroVector (Op := Op) (Tst := Tst)).body (Env.frame [n] [x])
      (Store.inBlock x.1 x.2 n)
      (fun m' => m'.store.HoldsVec x.1 x.2 n (fun _ => M.lit 0) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun _ => M.lit 0) (fun _ => m.pos) rfl ?_
  intro i hi m' hfr _ hp
  have hz : x.2 + i < m'.store.len x.1 := by rw [hfr.len_eq]; omega
  refine wp_call_const (hS (.lit 0)) rfl rfl rfl trivial hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
    Store.get_upd_self hz _, hp⟩

/-- Packed readback of the same actual zero loop, including the empty vector. -/
theorem writes_zeroVector_readBlock {K Op Tst : Type} [Has ScalarOp Op] {M : Machine K}
    {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K} {m : Mem K}
    {n : ℕ} {x : ℕ × ℕ} (hroom : x.2 + n ≤ m.store.len x.1) :
    Writes .total I τ (zeroVector (Op := Op) (Tst := Tst)).body (Env.frame [n] [x])
      (Store.inBlock x.1 x.2 n)
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock x.1 x.2 n = some (List.replicate n (M.lit 0))) m := by
  refine (writes_zeroVector hS hroom).mono le_rfl ?_
  intro m' _ h
  refine ⟨h.2, Store.readBlock_eq_some_iff.mpr ⟨List.length_replicate .., ?_⟩⟩
  intro i hi
  rw [h.1 i hi]
  simp [hi]

end NLAlib.Krylov.CG
