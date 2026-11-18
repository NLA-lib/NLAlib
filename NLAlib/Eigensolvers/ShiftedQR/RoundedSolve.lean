/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistSolve
public import NLAlib.Eigensolvers.ShiftedQR.WorklistAllocation
public import NLAlib.Matrix.QRIteration.DeflationPerturbed
public import NLAlib.Ops.Logic.BackwardFrame
public import NLAlib.Ops.Logic.Geometry
public import NLAlib.Matrix.FinitePrecision.OpsUnitarySimilarity
public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Matrix.FinitePrecision.StoredProducts

/-!
# The rounded deflation worklist

The deflation tree of [BanksGarzaVargasSrivastava2022, §6] (`ShiftedQR`, `Deflate`, Theorem 6.3)
in floating point, as a worklist of active ranges. A small block goes to a leaf routine; a larger
block goes to a decoupling implementation, which either fails, writing a failure word, or returns
a perturbed unitary similarity of the block that is upper Hessenberg and has one of its **bottom
$k$** subdiagonal entries of modulus at most $\omega$. The worklist then scans the bottom $k$
subdiagonal entries of the returned block with a rounded squared-modulus test against a threshold
word, cuts the last one that passes, and pushes the two children. The paper's `Deflate` cuts "the
bottom $k - 1$ entries smaller than $\omega$" while its loop exits at "$\le \omega$" among the
bottom $k$: with that rule a block can recurse forever on the same loop. Here the scan covers
exactly the bottom $k$ and its threshold is chosen so that an entry of modulus at most $\omega$
always passes.

The program uses the stack of the exact-arithmetic worklist (`rangePop`, `stackInit`), its block
copies, the split (`NLAlib.ShiftedQR.writeAndSplit`) and the scan visit
(`NLAlib.ShiftedQR.scanRound`). The run is
**total and capped**: the loop has the fuel $2(n+1)$ of the exact worklist; a failure of the
decoupler, a scan that finds nothing, or work left at the cap writes the failure word $1$ and
empties the stack. The backward error is composed round by round
(`NLAlib.Ops.BackwardStep.whileFuel` with the perturbed unitary similarity as backward-error
relation): a round is exact (a failure), a leaf ($\beta$), or a decoupling call and a cut
($\varepsilon(N_0) + c$).

## Main definitions

* `NLAlib.ShiftedQR.RoundedDecouplingContract`: the decoupler's contract with a failure word.
* `NLAlib.ShiftedQR.BackwardLeafContract`: a leaf routine with backward error $\beta$.
* `NLAlib.ShiftedQR.bottomScan`, `NLAlib.ShiftedQR.solveRounded`: the programs.
* `NLAlib.ShiftedQR.solveRoundedWith`, `NLAlib.ShiftedQR.liftLeaf`,
  `NLAlib.ShiftedQR.liftDecoupler`: the worklist with routines that read parameter words and a cap
  dimension [BanksGarzaVargasSrivastava2025].
* `NLAlib.ShiftedQR.RoundedWorklistState`: the state between two rounds.

## Main results

* `NLAlib.ShiftedQR.IsEigenvalueKernels.backwardLeafContract`: the exact kernel is a leaf
  routine with error $0$.
* `NLAlib.ShiftedQR.RoundedGeometry.disj_round`, `NLAlib.ShiftedQR.roundedGeometry_allocated`:
  the layout of the worklist's buffers.

The program proofs and the backward error are in
`NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- **The contract of a rounded decoupling routine** with the failure alternative `fails`, the
bottom width `k`, the iteration cap `F`, the routine cap `T`, the parameter words `ps`, the log
shape (`ns` slots of `w` entries), the coupling threshold `ω` and the backward error `ε N` for
inputs of norm at most `N`. From an upper Hessenberg matrix of order $n + 1 \ge k + 1$ stored in
place, the run is total, writes only the matrix, the one-word flag and its slotted log, and either
sets the flag to $1$ (allowed only when `fails` holds) or sets it to $0$, closes the `ns` slots of
the log (planes below $n$) and stores an upper Hessenberg perturbed similarity $\mathbf{H}'$ of
the input **by the exact unitary of the log's valid entries** (`NLAlib.givensLog`), with backward
error $\varepsilon(N)$ and one of its bottom $k$ subdiagonal entries of modulus at most $\omega$.
Nothing is assumed of the tape. The interface is `[n, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`. -/
def RoundedDecouplingRoutineContract (fails : Prop) (k F T : ℕ) (ps : List ℝ) (ns w : ℕ) (ω : ℝ)
    (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w₀ q f lg : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → IsUpperHessenberg H → specNorm H ≤ N → HoldsMatrix w₀ H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps →
    μ.Live [w₀, q, w₀, f, lg] → w₀.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w₀.1 →
    f.2 + 1 ≤ μ.store.len f.1 → lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1 →
    Fp.Apart [w₀, f, lg] [2 * ((n + 1) * (n + 1)), 1, ns * (1 + 5 * w)] →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) →
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length, F, T, ns, w] [w₀, q, w₀, f, lg])
      (Store.inBlock w₀.1 w₀.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (L : List (Option (List GivensEntry))),
            L.length = ns ∧ (∀ e ∈ slotEntries w L, e.1 + 1 < n + 1) ∧
            HoldsSlottedLog lg ns w L [] μ'.store ∧
            IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w L)) H H' (ε N) ∧
            IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
            HoldsMatrix w₀ H' μ'.store)) μ

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded bottom-$k$ scan**: reset the flag `R[3]` and the index `R[4]` to $0$ and visit
the subdiagonal entries $(N - k + j, N - k + j - 1)$, $j < k$, of the $N \times N$ matrix `A`
with `NLAlib.ShiftedQR.scanRound` (rounded squared modulus, exact comparison with the threshold
word). The interface is `[N, k] (A, Thr) → (R)`, for $k < N$. -/
def bottomScan : Impl O Q := opsImpl% [N, k] (A, Thr) → (R) {
  call (Has.inj IndexOp.lit) [0] () → (R[3]);
  call (Has.inj IndexOp.lit) [0] () → (R[4]);
  for j < k {
    run (scanRound (Op := O) (Tst := Q)).body [N, N - 1 - k + j] (A, Thr, R)
  }
}

/-- Abort: write the failure word $1$ and the stack count $0$, so that the worklist stops. -/
def roundedAbort : Impl O Q := opsImpl% [] () → (St, Fl) {
  call (Has.inj IndexOp.lit) [1] () → (Fl);
  call (Has.inj IndexOp.lit) [0] () → (St)
}

/-! ### The Schur updates of a round -/

/-- **The update after a decoupled block** $[lo, lo + d)$ of the order-$N$ matrix `A` with its
log `Lg` (`ns` slots of `w` entries) and the cut after the block row $i$: replay the log on the
rows of the right coupling (columns $lo + d, \dots, N - 1$), on the columns of the top coupling
(rows $0, \dots, lo - 1$) and on the columns $lo, \dots, lo + d - 1$ of the accumulator `U`
(`NLAlib.givensReplayRows`, `NLAlib.givensReplayColumns`), then write the exact zero at the cut
entry $(lo + i + 1, lo + i)$. The interface is `[N, lo, d, i, ns, w] (Lg) → (A, U)`. -/
def roundedDecoupleUpdate : Impl O Q := opsImpl% [N, lo, d, i, ns, w] (Lg) → (A, U) {
  run (givensReplayRows (O := O) (Q := Q)).body [N, lo, lo + d, N - lo - d, ns, w] (Lg, A, A);
  run (givensReplayColumns (O := O) (Q := Q)).body [N, lo, 0, lo, ns, w] (Lg, A, A);
  run (givensReplayColumns (O := O) (Q := Q)).body [N, lo, 0, N, ns, w] (Lg, U, U);
  call (Has.inj (ScalarOp.lit 0)) [] () → (A[2 * ((lo + i) * N + lo + i + 1)]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (A[2 * ((lo + i) * N + lo + i + 1) + 1])
}

/-- **The update after a leaf** on the block $[lo, lo + d)$ with its accumulator `Ub` (order $d$,
leading dimension $d$): the right coupling becomes $\mathbf{U}_b^{\mathsf H}$ times itself, the
top coupling and the columns $lo, \dots, lo + d - 1$ of `U` are multiplied by $\mathbf{U}_b$
(`NLAlib.matMulOn` into a scoped scratch, then copied back). The interface is
`[N, lo, d] (Ub) → (A, U)`. -/
def roundedLeafUpdate : Impl O Q := opsImpl% [N, lo, d] (Ub) → (A, U) {
  let C ← alloc (2 * (N * N));
  run (matMulOn (O := O) (Q := Q)).body [d, d, N - lo - d, d, N, d, 1]
    (Ub, A[2 * ((lo + d) * N + lo)], C);
  run (copyStrided (Op := O) (Tst := Q)).body [d, N - lo - d, d, N]
    (C, A[2 * ((lo + d) * N + lo)]);
  run (matMulOn (O := O) (Q := Q)).body [lo, d, d, N, d, lo, 0] (A[2 * (lo * N)], Ub, C);
  run (copyStrided (Op := O) (Tst := Q)).body [lo, d, lo, N] (C, A[2 * (lo * N)]);
  run (matMulOn (O := O) (Q := Q)).body [N, d, d, N, d, N, 0] (U[2 * (lo * N)], Ub, C);
  run (copyStrided (Op := O) (Tst := Q)).body [N, d, N, N] (C, U[2 * (lo * N)])
}

/-! ### The worklist with routines that read parameter words and a cap dimension -/

/-- Process one large block held in `W`: decouple with the routine
`[d, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)` into a scoped log; on failure abort; otherwise
scan its bottom $k$ couplings, and split at the index found (write back, push both children, and
update the couplings and `U`, `NLAlib.ShiftedQR.roundedDecoupleUpdate`) or abort. -/
def roundedProcessLargeWith (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w, lo, d] (A, Thr, P, St, U) → (W, R, Fl) {
    let Lg ← alloc (ns * (1 + 5 * w));
    run D.body [d, k, np, F, T, ns, w] (W, P, W, Fl, Lg);
    if (Has.inj CmpTst.isPos) [] (Fl) {
      run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
    } else {
      run (bottomScan (O := O) (Q := Q)).body [d, k] (W, Thr, R);
      if (Has.inj CmpTst.isPos) [] (R[3]) {
        let i ← index (Has.inj IdxTst.toNat) (R[4]) ≤ d;
        run (writeAndSplit (O := O) (Q := Q)).body [N, lo, d, i] (A, St, W);
        run (roundedDecoupleUpdate (O := O) (Q := Q)).body [N, lo, d, i, ns, w] (Lg, A, U)
      } else {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      }
    }
  }

/-- Copy the active block to `W`: a block of order at most $k$ goes to the Schur leaf routine
`[d, np, T] (Bk, P) → (Bk, Ub)`, whose triangular block is written back and whose accumulator
updates the couplings and `U` (`NLAlib.ShiftedQR.roundedLeafUpdate`); a larger one goes to
`NLAlib.ShiftedQR.roundedProcessLargeWith`. -/
def roundedProcessRangeWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w, lo, d] (A, Thr, P, St, U) → (W, Ub, R, Fl) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, lo, d] (A, W);
    ifPos k + 1 - d {
      run L.body [d, np, T] (W, P, W, Ub);
      run (copyToGlobal (Op := O) (Tst := Q)).body [N, lo, d] (W, A);
      run (roundedLeafUpdate (O := O) (Q := Q)).body [N, lo, d] (Ub, A, U)
    };
    ifPos d - k {
      run (roundedProcessLargeWith D).body [N, k, np, F, T, ns, w, lo, d]
        (A, Thr, P, St, U, W, R, Fl)
    }
  }

/-- Pop the top range, bounded-read its start and order, and process it. -/
def roundedWorklistRoundWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w] (A, Thr, P, St, U) → (W, Ub, R, Fl) {
    run (rangePop (Op := O) (Tst := Q)).body [N] (St, R);
    let lo ← index (Has.inj IdxTst.toNat) (R) ≤ N;
    let d ← index (Has.inj IdxTst.toNat) (R[1]) ≤ N;
    run (roundedProcessRangeWith D L).body [N, k, np, F, T, ns, w, lo, d]
      (A, Thr, P, St, U, W, Ub, R, Fl)
  }

/-- The capped worklist: clear the failure word, push the whole range, and process the top range
while the stack is not empty, for at most $2N$ rounds; work left at the cap aborts. -/
def roundedWorklistWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w] (A, Thr, P, U) → (St, W, Ub, R, Fl) {
    call (Has.inj IndexOp.lit) [0] () → (Fl);
    run (stackInit (Op := O) (Tst := Q)).body [N, 0, N] (St);
    while j < 2 * N, (Has.inj CmpTst.isPos) [] (St) {
      run (roundedWorklistRoundWith D L).body [N, k, np, F, T, ns, w]
        (A, Thr, P, St, U, W, Ub, R, Fl)
    } then {
      if (Has.inj CmpTst.isPos) [] (St) {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      } else { skip }
    }
  }

/-- **The rounded deflation worklist in Schur mode** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1], whose worklist at $k = 1$ it is; [BanksGarzaVargasSrivastava2022, Theorem 6.3],
with the Schur form): allocate the stack, the work matrix, the leaf accumulator and the scan
registers, and run the capped worklist with a decoupling routine
`[d, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)` (which writes a slotted log of `ns` slots of `w`
entries) and a Schur leaf routine `[d, np, T] (Bk, P) → (Bk, Ub)`. Each decoupled block's log is
replayed on its couplings and on the accumulator `U`, each cut entry is written as an exact zero,
and each leaf's accumulator multiplies its couplings and `U`; the stored matrix ends upper
triangular. The interface is `[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`. -/
def solveRoundedWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl) {
    let St ← alloc (1 + 2 * N);
    let W ← alloc (2 * (N * N));
    let Ub ← alloc (2 * (N * N));
    let R ← alloc 5;
    run (roundedWorklistWith D L).body [N, k, np, F, T, ns, w] (A, Thr, P, U, St, W, Ub, R, Fl)
  }

end Program

/-- The converse of re-basing: the invariant for $\mathbf{M}$ with error $\varepsilon$, where
$\mathbf{M}$ is a perturbed unitary similarity of $\mathbf{H}$ with error $\delta$, is the
invariant for $\mathbf{H}$ with error $\delta + \varepsilon$. -/
theorem _root_.NLAlib.DeflationInv.of_isPerturbedUnitarySimilar {n : ℕ}
    {H M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (hHM : IsPerturbedUnitarySimilar H M δ)
    (h : DeflationInv M ε active done A out) : DeflationInv H (δ + ε) active done A out := by
  obtain ⟨M₁, U, E, hU, hE, hM₁, hrest⟩ := h
  obtain ⟨W, G, hW, hG, hM₁'⟩ := hHM.trans ⟨U, E, hU, hE, hM₁⟩
  exact ⟨M₁, W, G, hW, hG, hM₁', hrest⟩

/-- A leaf as one perturbed similarity: at error $0$, finishing the first active block with
the listing of the block plus $\mathbf{F}$, $\|\mathbf{F}\|_2 \le \beta$, is a perturbed unitary
similarity with error $\beta$ to a matrix for which the invariant holds at error $0$. -/
theorem _root_.NLAlib.DeflationInv.exists_isPerturbedUnitarySimilar_finish {n : ℕ}
    {M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lo d : ℕ} {rest done : List (ℕ × ℕ)}
    {roots : Fin (n + 1) → ℂ} (h : DeflationInv M 0 ((lo, d) :: rest) done A roots) {β : ℝ}
    {F : Matrix (Fin d) (Fin d) ℂ} {rts : Fin d → ℂ} (hF : specNorm F ≤ β)
    (hL : IsEigenvalueListing (subBlock A (lo, d) + F) rts) :
    ∃ M', IsPerturbedUnitarySimilar M M' β ∧
      DeflationInv M' 0 rest ((lo, d) :: done) A (setSubVec roots (lo, d) rts) := by
  have hr := (h.active_block (r := (lo, d)) List.mem_cons_self).2.1
  have hfin := h.finish_of_specNorm_le (F := F) hF
    (fun j hj => setSubVec_apply_of_not_mem _ _ _ _ hj) (by
      rw [subVec_setSubVec_self roots (lo, d) rts hr]
      exact hL.charpoly_roots_eq_ofFn)
  rw [zero_add] at hfin
  exact hfin.exists_isPerturbedUnitarySimilar_rebase

/-- A cut as one perturbed similarity: at error $0$, replacing the first active block by a
perturbed unitary similarity $\mathbf{H}'$ with error $\varepsilon$, upper Hessenberg, and cutting
it at a subdiagonal entry of modulus at most $c$ is a perturbed unitary similarity with error
$\varepsilon + c$ to a matrix for which the invariant holds at error $0$. -/
theorem _root_.NLAlib.DeflationInv.exists_isPerturbedUnitarySimilar_split {n : ℕ}
    {M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lo d : ℕ} {rest done : List (ℕ × ℕ)}
    {roots : Fin (n + 1) → ℂ} (h : DeflationInv M 0 ((lo, d + 1) :: rest) done A roots)
    {ε c : ℝ} {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hB : IsPerturbedUnitarySimilar (subBlock A (lo, d + 1)) H' ε) (hHess : IsUpperHessenberg H')
    (i : Fin d) (hc : ‖H' i.succ i.castSucc‖ ≤ c) :
    ∃ M', IsPerturbedUnitarySimilar M M' (ε + c) ∧
      DeflationInv M' 0 ((lo, (i : ℕ) + 1) :: (lo + i + 1, d + 1 - i - 1) :: rest) done
        (setSubBlock A (lo, d + 1) H') roots := by
  have hr := (h.active_block (r := (lo, d + 1)) List.mem_cons_self).2.1
  have h₁ := h.setSubBlock_of_isPerturbedUnitarySimilar (r := (lo, d + 1)) List.mem_cons_self
    (B' := H') hB hHess
  have h₂ := h₁.split (i := (i : ℕ)) (τ := c) (by have := i.isLt; omega) (by
    rw [subBlock_setSubBlock_self A (lo, d + 1) H' hr]
    exact hc)
  rw [zero_add] at h₂
  exact h₂.exists_isPerturbedUnitarySimilar_rebase

end NLAlib.ShiftedQR
