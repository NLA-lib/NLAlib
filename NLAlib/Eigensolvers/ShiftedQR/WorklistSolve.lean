/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.BlockCopy
public import NLAlib.Eigensolvers.ShiftedQR.Scan
public import NLAlib.Eigensolvers.ShiftedQR.WorklistLoop
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Processing one active range with a scalar decoupling implementation

The range processor copies the actual global diagonal block to workspace. Small blocks use
the local eigenvalue kernel; larger blocks run a fixed scalar decoupling implementation, read
its actual scan index, copy the resulting block back, and push its two children. The
decoupling interface is a local total word theorem for that fixed implementation, not an
operation of the access model.

## Main results

* `NLAlib.ShiftedQR.DecouplingContract`: the local total interface of a fixed implementation.
* `NLAlib.ShiftedQR.WorklistGeometry`: standard liveness, room and separation of the views.
* `NLAlib.ShiftedQR.processRange`: the computable range processor.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- A fixed decoupling implementation acts on one actual Hessenberg matrix. Its local theorem
returns the stored conjugate and scan result under explicit quantitative matrix hypotheses.
The five parameter words are the actual threshold, conditioning, Ritz, promising and contraction
parameters. This is a proof interface for implementation substitution, never a primitive. -/
def DecouplingContract (θ : ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n m F M : ℕ} {τ B α γ δ : ℝ} {w p r : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → RapidDecouplingHyps H τ B θ α γ δ m F → 2 ^ m ≤ n → 0 ≤ τ →
    M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊ → 0 < M →
    HoldsMatrix w H μ.store → μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ] →
    μ.Live [w, p, w, r] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    r.2 + 5 ≤ μ.store.len r.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock r.1 r.2 5) →
    Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5) →
    Writes .total I tape D.body (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (U H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
          H' = Uᴴ * H * U ∧ IsUpperHessenberg H' ∧ IsDecoupledAbs τ H' ∧
          HoldsMatrix w H' μ'.store ∧ ScanHolds H' (τ ^ 2) n r μ'.store) μ

/-- The six actual views use ordinary liveness, capacity and pairwise spatial separation.
All conditions concern the current raw store; none asserts future execution. -/
structure WorklistGeometry (N : ℕ) (a p stack out w r : ℕ × ℕ) (μ : Mem ℝ) : Prop where
  /-- Each supplied view refers to a live buffer. -/
  live : μ.Live [a, p, stack, out, w, r]
  /-- Global matrices, parameters, stack, persistent output, workspace and scan capacity. -/
  room : μ.Room [a, p, stack, out, w, r]
    [2 * (N * N), 5, 1 + 2 * N, 2 * N, 2 * (N * N), 5]
  /-- Views may share an arena when their actual words are separate. -/
  apart : Fp.Apart [a, p, stack, out, w, r]
    [2 * (N * N), 5, 1 + 2 * N, 2 * N, 2 * (N * N), 5]

/-- Standard view geometry is retained through every spatial frame. -/
theorem WorklistGeometry.of_eqOff {N : ℕ} {a p stack out w r : ℕ × ℕ} {μ μ' : Mem ℝ}
    {F : Fp} (h : WorklistGeometry N a p stack out w r μ) (hfr : μ.store.EqOff F μ'.store) :
    WorklistGeometry N a p stack out w r μ' :=
  ⟨h.live.congr hfr.length_eq, h.room.congr hfr.len_eq, h.apart⟩

/-- Any two distinct views have disjoint word footprints by the standard apart-list API. -/
theorem WorklistGeometry.disj {N : ℕ} {a p stack out w r : ℕ × ℕ} {μ : Mem ℝ}
    (h : WorklistGeometry N a p stack out w r μ) (i j : Fin 6) (hne : i ≠ j) :
    Fp.Disj
      (Store.inBlock (([a, p, stack, out, w, r] : List (ℕ × ℕ)).getD i (0, 0)).1
        (([a, p, stack, out, w, r] : List (ℕ × ℕ)).getD i (0, 0)).2
        (([2 * (N * N), 5, 1 + 2 * N, 2 * N, 2 * (N * N), 5] : List ℕ).getD i 0))
      (Store.inBlock (([a, p, stack, out, w, r] : List (ℕ × ℕ)).getD j (0, 0)).1
        (([a, p, stack, out, w, r] : List (ℕ × ℕ)).getD j (0, 0)).2
        (([2 * (N * N), 5, 1 + 2 * N, 2 * N, 2 * (N * N), 5] : List ℕ).getD j 0)) :=
  h.apart.disj_getD (by simp) (by simp)
    (fun he => hne (Fin.ext he))

/-- The standard separated operand tuple keeps both work views outside all persistent data. -/
theorem WorklistGeometry.disj_scratch {N : ℕ} {a p stack out w r : ℕ × ℕ} {μ : Mem ℝ}
    (h : WorklistGeometry N a p stack out w r μ) :
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (N * N)) ⊔ Store.inBlock r.1 r.2 5)
      (Fp.blocks [a, p, stack, out] [2 * (N * N), 5, 1 + 2 * N, 2 * N]) := by
  simpa only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using (h.apart.take_drop rfl 4).2.2.symm

/-- Stack updates and range/scan scratch do not touch the global matrix, parameters or output. -/
theorem WorklistGeometry.disj_pop {N : ℕ} {a p stack out w r : ℕ × ℕ} {μ : Mem ℝ}
    (h : WorklistGeometry N a p stack out w r μ) :
    Fp.Disj (Store.inBlock stack.1 stack.2 (1 + 2 * N) ⊔ Store.inBlock r.1 r.2 5)
      (Fp.blocks [a, p, out] [2 * (N * N), 5, 2 * N]) := by
  simpa only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
    h.apart.disj_select [2, 5] [0, 1, 3] (by simp) (by simp) (by simp)

/-- Worklist processing leaves the actual five parameter words outside its write footprint. -/
theorem WorklistGeometry.disj_params {N : ℕ} {a p stack out w r : ℕ × ℕ} {μ : Mem ℝ}
    (h : WorklistGeometry N a p stack out w r μ) :
    Fp.Disj (worklistFp N a stack out w r) (Store.inBlock p.1 p.2 5) := by
  simpa only [worklistFp, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
    h.apart.disj_select [0, 2, 3, 4, 5] [1] (by simp) (by simp) (by simp)

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Commit a decoupled work matrix and push its right and left children. -/
def writeAndSplit : Impl O Q := opsImpl% [N, lo, d, i] (A, St, W) → () {
  run (copyToGlobal (Op := O) (Tst := Q)).body [N, lo, d] (W, A);
  run (splitPush (O := O) (Q := Q)).body [N, lo, d, i] (St)
}

/-- Process one large active block: decouple, bind its actual small-entry index, write back,
and push right then left. The supplied decoupling implementation is fixed before execution. -/
def processLarge (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M, lo, d] (A, Params, St) → (Out, W, R) {
    run D.body [d, m, k, F, M] (W, Params, W, R);
    let i ← index (Has.inj IdxTst.toNat) (R[4]) ≤ d;
    run (writeAndSplit (O := O) (Q := Q)).body [N, lo, d, i] (A, St, W)
  }

/-- The active block is copied from raw matrix storage and processed at its actual size. -/
def processRange (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M, lo, d] (A, Params, St) → (Out, W, R) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, lo, d] (A, W);
    ifPos k + 1 - d {
      run (finishRange (O := O) (Q := Q)).body [N, lo, d] (W, Out)
    };
    ifPos d - k {
      run (processLarge D).body [N, m, k, F, M, lo, d] (A, Params, St, Out, W, R)
    }
  }

/-- Pop the actual top range, bounded-read both stored natural words, and process that range. -/
def worklistRound (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (A, Params, St) → (Out, W, R) {
    run (rangePop (Op := O) (Tst := Q)).body [N] (St, R);
    let lo ← index (Has.inj IdxTst.toNat) (R) ≤ N;
    let d ← index (Has.inj IdxTst.toNat) (R[1]) ≤ N;
    run (processRange D).body [N, m, k, F, M, lo, d] (A, Params, St, Out, W, R)
  }

end Program

end NLAlib.ShiftedQR
