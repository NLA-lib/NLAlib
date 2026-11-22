/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Constants
public import NLAlib.Eigensolvers.ShiftedQR.WorklistAllocation

/-!
# Exact deflation from raw parameter words

The program computes the actual absolute threshold from the raw tolerance and Frobenius
norm, stores its prepared parameters in scoped storage, and executes the allocating worklist.
The supplied inputs are the raw matrix and `[B,theta,alpha,gamma,delta]` words; output slots
and all internal work arrays need no initialized contents.

## Main results

* `NLAlib.ShiftedQR.solve`: raw-parameter exact deflation with explicit scalar initialization.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- An allocated parameter view is separate from the original matrix and output views. -/
theorem prepared_geometry {N : ℕ} {μ μ' μ'' : Mem ℝ} {a raw out : ℕ × ℕ}
    (hl : μ.Live [a, raw, out])
    (hr : μ.Room [a, raw, out] [2 * (N * N), 5, 2 * N])
    (ha : Fp.Apart [a, raw, out] [2 * (N * N), 5, 2 * N])
    (hs : μ'.store.length = μ.store.length + 1)
    (hP : μ'.store.len μ.store.length = 5)
    (hBelow : Store.Below μ.store.length μ.store μ'.store)
    (hfr : μ'.store.EqOff (Store.inBlock μ.store.length 0 5) μ''.store) :
    μ''.Live [a, (μ.store.length, 0), out] ∧
      μ''.Room [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] ∧
      Fp.Apart [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] := by
  have hla := hl a (by simp)
  have hlo := hl out (by simp)
  have hRawRoom : μ'.Room [a, raw, out] [2 * (N * N), 5, 2 * N] := by
    rw [Mem.room_eq_of_below hBelow (fun z hz => hl z hz)]
    exact hr
  have hAP : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock μ.store.length 0 5) := Fp.disj_inBlock_of_ne (by omega)
  have hPO : Fp.Disj (Store.inBlock μ.store.length 0 5)
      (Store.inBlock out.1 out.2 (2 * N)) := Fp.disj_inBlock_of_ne (by omega)
  have hAO : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N)))
      (Store.inBlock out.1 out.2 (2 * N)) := by
    simpa using ha.disj_getD (i := 0) (j := 2) (by simp) (by simp) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [hfr.length_eq, hs]
    exact ⟨hla.trans_le (by omega), by omega, hlo.trans_le (by omega)⟩
  · exact (show μ'.Room [a, (μ.store.length, 0), out] [2 * (N * N), 5, 2 * N] from
      ⟨hRawRoom.1, by simpa only [Nat.zero_add, hP] using le_rfl,
        hRawRoom.2.2.1, trivial⟩).congr hfr.len_eq
  · refine ⟨?_, ?_, Fp.disj_bot_right _, trivial⟩
    · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
        (Fp.disj_sup_right.mpr ⟨hAP, hAO⟩)
    · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hPO

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Compute all prepared parameters from raw words before mutating the global matrix.
The decoupling body is one fixed scalar implementation supplied at construction time. -/
def solve (D : Stmt O Q) : Stmt O Q := ops% [N, m, k, F, M] (A, Raw) → (Out) {
  let Params ← alloc 5;
  run (initializeParameters (Op := O) (Tst := Q)) [N] (A, Raw, Params);
  run (solveAllocated D) [N, m, k, F, M] (A, Params, Out)
}

end NLAlib.ShiftedQR
