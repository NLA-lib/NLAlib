/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpShift
public import NLAlib.Eigensolvers.SpectralBisection.UpSplit
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Actual upward metadata dispatch

The stored node kind is converted through the declared bounded natural-index query. For a
one-child node its actual execution is exactly the checked copy-and-shift subprogram.

## Main results

* `NLAlib.SpectralBisection.eval_upNode_shift`: evaluation selected by actual stored metadata.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The bounded kind query selects the one-child reconstruction for kinds two and three.
The shift's sign is represented by the supplied word at offset zero or one, respectively. -/
theorem eval_upNode_shift {K Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op]
    [Has IdxTst Tst] {dec : K → ℝ} {I : Interp Op Tst K} (hQ : IsToNat dec I)
    {τ : Tape K} {m : Mem K} {n d lo k : ℕ} {ua qa ea kd kp t : ℕ × ℕ} (side : Bool)
    {w : K} (hkind : m.store.get kd.1 (kd.2 + n * d + lo) = some w)
    (hdec : dec w = if side then (2 : ℕ) else 3) (hl : m.Live [ua, qa, ea, kd, kp, t]) :
    eval I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t]) m =
    eval I τ (upShiftResultImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [k] [(ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
        (ea.1, ea.2 + n * (d + 1) + lo), (t.1, t.2 + if side then 0 else 1),
        (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo), (ea.1, ea.2 + n * d + lo)]) m := by
  have hquery := hQ.index_eq_of_decode_nat (x := (kd.1, kd.2 + n * d + lo))
    (m := m) (n := if side then 2 else 3) hkind (by cases side <;> simpa using hdec)
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  cases side <;>
    simp [upNodeImpl, eval, iter, Stmt.ifZero, IExp.eval, IExp.evalList,
      Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, Mem.Live, hquery, hl]

/-- A stored leaf kind performs no reconstruction calls and keeps the complete memory. -/
theorem eval_upNode_leaf {K Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op]
    [Has IdxTst Tst] {dec : K → ℝ} {I : Interp Op Tst K} (hQ : IsToNat dec I)
    {τ : Tape K} {m : Mem K} {n d lo k : ℕ} {ua qa ea kd kp t : ℕ × ℕ}
    {w : K} (hkind : m.store.get kd.1 (kd.2 + n * d + lo) = some w) (hdec : dec w = 1) :
    eval I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t]) m = some m := by
  have hquery := hQ.index_eq_of_decode_nat (x := (kd.1, kd.2 + n * d + lo))
    (m := m) (n := 1) hkind (by simpa using hdec)
  simp [upNodeImpl, eval, iter, Stmt.ifZero, IExp.eval, IExp.evalList, Operand.evalList,
    Operand.eval, Env.frame, Env.pushIdx, hquery]

/-- Kind four reads the actual bounded split size and selects exactly the checked two-child
reconstruction, with the node's two strided child locations. -/
theorem eval_upNode_split {K Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op]
    [Has IdxTst Tst] {dec : K → ℝ} {I : Interp Op Tst K} (hQ : IsToNat dec I)
    {τ : Tape K} {m : Mem K} {n d lo k r : ℕ} {ua qa ea kd kp t : ℕ × ℕ}
    {kind split : K} (hkind : m.store.get kd.1 (kd.2 + n * d + lo) = some kind)
    (hdec : dec kind = 4) (hr : m.store.get kp.1 (kp.2 + n * d + lo) = some split)
    (hrdec : dec split = r) (hrbound : r ≤ k) (hl : m.Live [ua, qa, ea, kd, kp, t]) :
    eval I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t]) m =
    eval I τ (upSplitResultImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [k, r]
        [(qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
          (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * r)),
          (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
          (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * (lo + r)),
          (ea.1, ea.2 + n * (d + 1) + lo), (ea.1, ea.2 + n * (d + 1) + lo + r), t,
          (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo), (ea.1, ea.2 + n * d + lo)]) m := by
  have hquery := hQ.index_eq_of_decode_nat (x := (kd.1, kd.2 + n * d + lo))
    (m := m) (n := 4) hkind hdec
  have hrquery := hQ.index_eq_of_decode_nat (x := (kp.1, kp.2 + n * d + lo))
    (m := m) (n := r) hr hrdec
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  simp [upNodeImpl, eval, iter, Stmt.ifZero, IExp.eval, IExp.evalList, Operand.evalList,
    Operand.eval, Env.frame, Env.pushIdx, Mem.Live, hquery, hrquery, hrbound, hl]

/-- A one-child node returns its child basis and the actual scalar-shifted eigenvalues after
reading the declared stored kind. All source reads, capacities and spatial assumptions are
explicit; the selected implementation's correctness is discharged by its checked theorem. -/
theorem writes_upNode_shift {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    {τ : Tape K} {m : Mem K} {n d lo k : ℕ} {ua qa ea kd kp t : ℕ × ℕ}
    (side : Bool) (U : Matrix (Fin k) (Fin k) (K × K)) (values : List K) (s w : K)
    (hl : m.Live [ua, qa, ea, kd, kp, t])
    (hkind : m.store.get kd.1 (kd.2 + n * d + lo) = some w)
    (hdec : dec w = if side then (2 : ℕ) else 3)
    (hU : m.store.readBlock ua.1 (ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo)
      (2 * (k * k)) = some ((EntryCodec.pair K).packFinMatrix U))
    (hE : m.store.readBlock ea.1 (ea.2 + n * (d + 1) + lo) k = some values)
    (hs : m.store.get t.1 (t.2 + if side then 0 else 1) = some s)
    (hu : ua.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ m.store.len ua.1)
    (he : ea.2 + n * d + lo + k ≤ m.store.len ea.1)
    (hap : Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo),
      (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (ea.1, ea.2 + n * (d + 1) + lo), (t.1, t.2 + if side then 0 else 1)]
      [2 * (k * k), k, 2 * (k * k), k, 1]) :
    Writes .total I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t])
      (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo)] [2 * (k * k), k])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks
        [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo), (ea.1, ea.2 + n * d + lo)]
        [2 * (k * k), k] =
          some [(EntryCodec.pair K).packFinMatrix U, values.map fun v => M.add v s]) m := by
  have hev := eval_upNode_shift (τ := τ) (k := k) hQ side hkind hdec hl
  have hl' : m.Live [(ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (ea.1, ea.2 + n * (d + 1) + lo), (t.1, t.2 + if side then 0 else 1),
      (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo), (ea.1, ea.2 + n * d + lo)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.2.1, hl.2.2.2.2.2, hl.1, hl.2.2.1⟩
  simpa only [Writes, Wp, hev] using writes_upShiftResult hS U values s hl' hU hE hs hu he hap

end NLAlib.SpectralBisection
