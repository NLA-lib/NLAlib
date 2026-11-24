/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Worklist
public import NLAlib.Eigensolvers.ShiftedQR.Kernels

/-!
# Splitting and finishing ranges in the exact worklist

Splitting pushes the right range followed by the left range, so the left block is processed
next. The small separating subdiagonal is retained physically; the mathematical deflation
invariant records its removal as a perturbation between the two new blocks. Finishing writes
all roots of the small block directly to its persistent output range.

## Main results

* `NLAlib.ShiftedQR.splitPush_writes_of_isExactNatLit`: two actual bounded-query pushes, on any
  machine with exact natural literals (`NLAlib.ShiftedQR.splitPush_writes`: exact arithmetic).
* `NLAlib.ShiftedQR.finishRange_writes`: exact eigenvalues at their persistent output offset.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type}

section Stack

variable [Has IndexOp O] [Has IdxTst Q]

/-- Push right then left so the leading child is processed next by the stack worklist. -/
def splitPush : Stmt O Q := ops% [capacity, lo, d, i] (St) → () {
  run (rangePush (Op := O) (Tst := Q)) [capacity, lo + i + 1, d - i - 1] (St);
  run (rangePush (Op := O) (Tst := Q)) [capacity, lo, i + 1] (St)
}

/-- Splitting is two total stack operations on the actual stored count. The two persistent
slots have capacity before execution; the existing stack words are retained by the frame. Only
the literals written need to be exact.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem splitPush_writes_of_isExactNatLit {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hQ : IsToNat id I) {B : ℕ} (hN : IsExactNatLit id M B)
    {τ : Tape ℝ} {m : Mem ℝ} {capacity lo d i : ℕ} {b : ℕ × ℕ}
    (hli : lo + i + 1 ≤ B) (hd : d ≤ B) (hcB : capacity ≤ B)
    {rs : List (ℕ × ℕ)} (hl : m.Live [b]) (hSt : StackHolds b rs m.store)
    (hcap : rs.length + 2 ≤ capacity) (hroom : b.2 + 1 + 2 * capacity ≤ m.store.len b.1) :
    Writes .total I τ (splitPush (O := O) (Q := Q))
      (Env.frame [capacity, lo, d, i] [b]) (Store.inBlock b.1 b.2 (1 + 2 * capacity))
      (fun m' => m'.pos = m.pos ∧
        StackHolds b (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) m'.store) m := by
  unfold splitPush
  refine (rangePush_writes_of_isExactNatLit (τ := τ) hL hQ hN hli (by omega) hcB hSt
    (capacity := capacity) (lo := lo + i + 1) (size := d - i - 1) (by omega)
    hroom).frame_seq_le rfl rfl hl (by fp_sub [pushFp]) ?_
  intro m₁ hfr₁ ⟨hp₁, hSt₁⟩
  have hw := rangePush_writes_of_isExactNatLit (τ := τ) hL hQ hN (by omega) (by omega) hcB hSt₁
    (capacity := capacity) (lo := lo) (size := i + 1)
    (by simp; omega) (by rw [hfr₁.len_eq]; exact hroom)
  refine (hw.in_frame rfl rfl (hl.congr hfr₁.length_eq)).mono
    (by simp only [List.length_append, List.length_singleton]; fp_sub [pushFp]) ?_
  intro _ _ ⟨hp₂, hSt₂⟩
  exact ⟨hp₂.trans hp₁, by simpa only [List.append_assoc, List.cons_append,
    List.nil_append] using hSt₂⟩

/-- Splitting is two total stack operations on the actual stored count. The two persistent
slots have capacity before execution; the existing stack words are retained by the frame.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`
and `NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem splitPush_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {capacity lo d i : ℕ} {b : ℕ × ℕ}
    {rs : List (ℕ × ℕ)} (hl : m.Live [b]) (hSt : StackHolds b rs m.store)
    (hcap : rs.length + 2 ≤ capacity) (hroom : b.2 + 1 + 2 * capacity ≤ m.store.len b.1) :
    Writes .total I τ (splitPush (O := O) (Q := Q))
      (Env.frame [capacity, lo, d, i] [b]) (Store.inBlock b.1 b.2 (1 + 2 * capacity))
      (fun m' => m'.pos = m.pos ∧
        StackHolds b (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) m'.store) m :=
  splitPush_writes_of_isExactNatLit hL hQ (hE.isExactNatLit (lo + i + 1 + d + capacity))
    (by omega) (by omega) (by omega) hl hSt hcap hroom

end Stack

section Finished

variable [Has EigenvalueKernelOp O]

/-- Write a finished block's eigenvalue listing directly into its global output range. -/
def finishRange : Stmt O Q := ops% [N, lo, d] (W) → (Out) {
  call (Has.inj EigenvalueKernelOp.smallEig) [d] (W) → (Out[2 * lo])
}

/-- Finishing returns every root of the actual local matrix, with multiplicity, in the reserved
global output range. The global output need not be initialized. A fragment: its tree runs only
inside the tree of `NLAlib.ShiftedQR.processRange`.
A fragment of the tree `NLAlib.ShiftedQR.processRange`. -/
theorem finishRange_writes {θ : ℝ} {K : KernelRoutines θ} {I : Interp O Q ℝ}
    (hK : IsEigenvalueKernels K I) {τ : Tape ℝ} {m : Mem ℝ} {N lo d : ℕ}
    {w out : ℕ × ℕ} {B : Matrix (Fin d) (Fin d) ℂ} (hl : m.Live [w, out])
    (hB : HoldsMatrix w B m.store) (hr : lo + d ≤ N)
    (hroom : out.2 + 2 * N ≤ m.store.len out.1) :
    Writes .total I τ (finishRange (O := O) (Q := Q))
      (Env.frame [N, lo, d] [w, out]) (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix (out.1, out.2 + 2 * lo)
        (Matrix.of fun i (_ : Fin 1) => K.smallEig d B i) m'.store) m := by
  unfold finishRange
  exact smallEig_writes hK (a := w) (b := (out.1, out.2 + 2 * lo)) rfl rfl rfl
    (by simpa [Mem.Live] using hl) hB (by dsimp only; omega)

end Finished

end NLAlib.ShiftedQR
