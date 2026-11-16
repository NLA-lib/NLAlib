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

/-- **The contract of a rounded decoupling implementation** with the failure alternative
`fails`, the bottom width `k`, the iteration cap `F` (a runtime dimension of the call, fixed
outside the contract's quantifiers), the parameter words `ps`, the coupling threshold `ω` and the
backward error `ε N` for inputs of norm at most `N`. From an upper Hessenberg matrix of order
$n + 1 \ge k + 1$ stored in place, the run is total, writes only the matrix and the one-word
flag, and either sets the flag to $1$ (allowed only when `fails` holds) or sets it to $0$ and
stores an upper Hessenberg perturbed unitary similarity $\mathbf{H}'$ of the input with backward
error $\varepsilon(N)$ and one of its bottom $k$ subdiagonal entries of modulus at most $\omega$.
Nothing is assumed of the tape: a randomized implementation meets the contract with `fails` true.
The interface is `[n, k, np, F] (W, P) → (W, Fl)`. -/
def RoundedDecouplingContract (fails : Prop) (k F : ℕ) (ps : List ℝ) (ω : ℝ) (ε : ℝ → ℝ)
    (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w q f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → IsUpperHessenberg H → specNorm H ≤ N → HoldsMatrix w H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps →
    μ.Live [w, q, w, f] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) →
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length, F] [w, q, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (ε N) ∧
            IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
            HoldsMatrix w H' μ'.store)) μ

/-- **The contract of a leaf routine with backward error `β`**: from an upper Hessenberg matrix
$\mathbf{B}$ of order $d$, the run is total, writes only its $2d$ output words, and stores a
listing of the eigenvalues, with multiplicity, of $\mathbf{B} + \mathbf{F}$ for some
$\|\mathbf{F}\|_2 \le \beta$. The interface is `[d] (B) → (Ev)`, the output disjoint from the
input. -/
def BackwardLeafContract (β : ℝ) (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w o : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    IsUpperHessenberg B → HoldsMatrix w B μ.store → μ.Live [w, o] →
    o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape L.body (Env.frame [d] [w, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ (roots : Fin d → ℂ) (F : Matrix (Fin d) (Fin d) ℂ), specNorm F ≤ β ∧
        IsEigenvalueListing (B + F) roots ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ

/-! ### Routines with parameter words and a cap dimension -/

/-- A leaf routine `[d] (Bk) → (Ev)` as a routine with parameter words and a cap dimension,
`[d, np, T] (Bk, P) → (Ev)`: the words and the cap are ignored. -/
def liftLeaf (L : Impl O Q) : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Ev) {
  run L.body [d] (Bk, Ev)
}

/-- A decoupler `[N, k, np, F] (W, P) → (W, Fl)` as a decoupler with a cap dimension,
`[N, k, np, F, T] (W, P) → (W, Fl)`: the cap is ignored. -/
def liftDecoupler (D : Impl O Q) : Impl O Q := opsImpl% [N, k, np, F, T] (W, P) → (W, Fl) {
  run D.body [N, k, np, F] (W, P, W, Fl)
}

/-- **The contract of a rounded decoupling routine** with the cap dimension `T`:
`NLAlib.ShiftedQR.RoundedDecouplingContract` for a decoupler with the interface
`[n, k, np, F, T] (W, P) → (W, Fl)`. From an upper Hessenberg matrix of order $n + 1 \ge k + 1$
stored in place, the run is total, writes only the matrix and the flag, and either sets the flag
to $1$ (allowed only when `fails` holds) or sets it to $0$ and stores an upper Hessenberg perturbed
unitary similarity with backward error $\varepsilon(N)$ having one of its bottom $k$ subdiagonal
entries of modulus at most $\omega$. -/
def RoundedDecouplingRoutineContract (fails : Prop) (k F T : ℕ) (ps : List ℝ) (ω : ℝ)
    (ε : ℝ → ℝ) (D : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {N : ℝ} {w q f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    k ≤ n → IsUpperHessenberg H → specNorm H ≤ N → HoldsMatrix w H μ.store →
    μ.store.readBlock q.1 q.2 ps.length = some ps →
    μ.Live [w, q, w, f] → w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 →
    f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) →
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) →
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length, F, T] [w, q, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (ε N) ∧
            IsUpperHessenberg H' ∧ (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
            HoldsMatrix w H' μ'.store)) μ

/-- **The contract of a leaf routine with backward error `β`, parameter words and a cap**: from
an upper Hessenberg matrix $\mathbf{B}$ of order $d \le k_{\max}$ with
$\|\mathbf{B}\|_2 \le N_{\max}$, and the parameter words `ps` stored, the run is total, writes only
its $2d$ output words, and stores a listing of the eigenvalues, with multiplicity, of
$\mathbf{B} + \mathbf{F}$ for some $\|\mathbf{F}\|_2 \le \beta$. The interface is
`[d, np, T] (B, P) → (Ev)`. -/
def BackwardLeafRoutineContract (β : ℝ) (kmax : ℕ) (Nmax : ℝ) (ps : List ℝ) (T : ℕ)
    (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p o : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (B : Matrix (Fin d) (Fin d) ℂ),
    d ≤ kmax → IsUpperHessenberg B → specNorm B ≤ Nmax → HoldsMatrix w B μ.store →
    μ.store.readBlock p.1 p.2 ps.length = some ps → μ.Live [w, p, o] →
    o.2 + 2 * d ≤ μ.store.len o.1 →
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) →
    Fp.Disj (Store.inBlock p.1 p.2 ps.length) (Store.inBlock o.1 o.2 (2 * d)) →
    Writes .total I tape L.body (Env.frame [d, ps.length, T] [w, p, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => ∃ (roots : Fin d → ℂ) (F : Matrix (Fin d) (Fin d) ℂ), specNorm F ≤ β ∧
        IsEigenvalueListing (B + F) roots ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ

/-- A leaf routine with backward error $\beta$ (`NLAlib.ShiftedQR.BackwardLeafContract`), lifted
by `NLAlib.ShiftedQR.liftLeaf`, meets the routine contract for every order bound, norm bound,
parameter words and cap. -/
theorem BackwardLeafContract.backwardLeafRoutineContract {β : ℝ} {L : Impl O Q}
    {I : Interp O Q ℝ} (h : BackwardLeafContract β L I) (kmax : ℕ) (Nmax : ℝ) (ps : List ℝ)
    (T : ℕ) : BackwardLeafRoutineContract β kmax Nmax ps T (liftLeaf L) I := by
  intro d w p o tape μ B _ hB _ hH _ hl hroom hwo _
  unfold liftLeaf
  exact (h B hB hH (by simp_all [Mem.Live]) hroom hwo).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by simp_all [Mem.Live])

/-- A rounded decoupler (`NLAlib.ShiftedQR.RoundedDecouplingContract`), lifted by
`NLAlib.ShiftedQR.liftDecoupler`, meets the routine contract for every cap. -/
theorem RoundedDecouplingContract.roundedDecouplingRoutineContract {fails : Prop} {k F : ℕ}
    {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} {D : Impl O Q} {I : Interp O Q ℝ}
    (h : RoundedDecouplingContract fails k F ps ω ε D I) (T : ℕ) :
    RoundedDecouplingRoutineContract fails k F T ps ω ε (liftDecoupler D) I := by
  intro n N w q f tape μ H hk hH hN hW hq hl hw hf hwf hqwf
  unfold liftDecoupler
  exact (h H hk hH hN hW hq hl hw hf hwf hqwf).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by simpa [Mem.Live] using hl)

section Leaf

variable [Has EigenvalueKernelOp O]

/-- The exact small-eigenvalue kernel as a leaf routine: `[d] (Bk) → (Ev)`. -/
def smallEigLeaf : Impl O Q := opsImpl% [d] (Bk) → (Ev) {
  call (Has.inj EigenvalueKernelOp.smallEig) [d] (Bk) → (Ev)
}

/-- The exact small-eigenvalue kernel meets the leaf contract with backward error $0$. -/
theorem IsEigenvalueKernels.backwardLeafContract {θ : ℝ} {K : KernelRoutines θ}
    {I : Interp O Q ℝ} (hK : IsEigenvalueKernels K I) :
    BackwardLeafContract 0 (smallEigLeaf (O := O) (Q := Q)) I := by
  intro d w o tape μ B _ hB hl hroom _
  unfold smallEigLeaf
  refine (writes_smallEig hK rfl rfl rfl hl hB hroom).mono le_rfl ?_
  rintro μ' - ⟨-, hO⟩
  exact ⟨K.smallEig d B, 0, by rw [specNorm_zero], by simpa using K.listing d B, hO⟩

end Leaf

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

/-- Process one large block held in `W`: decouple; on failure abort; otherwise scan its bottom
$k$ couplings, and split at the index found (write back and push both children) or abort. -/
def roundedProcessLarge (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run D.body [d, k, np, F] (W, P, W, Fl);
    if (Has.inj CmpTst.isPos) [] (Fl) {
      run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
    } else {
      run (bottomScan (O := O) (Q := Q)).body [d, k] (W, Thr, R);
      if (Has.inj CmpTst.isPos) [] (R[3]) {
        let i ← index (Has.inj IdxTst.toNat) (R[4]) ≤ d;
        run (writeAndSplit (O := O) (Q := Q)).body [N, lo, d, i] (A, St, W)
      } else {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      }
    }
  }

/-- The part of `NLAlib.ShiftedQR.roundedProcessLarge` after the decoupling call: on failure
abort; otherwise scan, and split or abort. -/
def roundedLargeRest (D : Impl O Q) : Stmt O Q :=
  match (roundedProcessLarge D).body with
  | .seq _ c => c
  | c => c

/-- Copy the active block to `W`; a block of order at most $k$ goes to the leaf routine, which
writes its roots at offset $2\,lo$ of `Out`; a larger one to
`NLAlib.ShiftedQR.roundedProcessLarge`. -/
def roundedProcessRange (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, lo, d] (A, W);
    ifPos k + 1 - d {
      run L.body [d] (W, Out[2 * lo])
    };
    ifPos d - k {
      run (roundedProcessLarge D).body [N, k, np, F, lo, d] (A, Thr, P, St, Out, W, R, Fl)
    }
  }

/-- Pop the top range, bounded-read its start and order, and process it. -/
def roundedWorklistRound (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (rangePop (Op := O) (Tst := Q)).body [N] (St, R);
    let lo ← index (Has.inj IdxTst.toNat) (R) ≤ N;
    let d ← index (Has.inj IdxTst.toNat) (R[1]) ≤ N;
    run (roundedProcessRange D L).body [N, k, np, F, lo, d] (A, Thr, P, St, Out, W, R, Fl)
  }

/-- The capped worklist: clear the failure word, push the whole range, and process the top range
while the stack is not empty, for at most $2N$ rounds; work left at the cap aborts. -/
def roundedWorklist (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F] (A, Thr, P) → (St, Out, W, R, Fl) {
    call (Has.inj IndexOp.lit) [0] () → (Fl);
    run (stackInit (Op := O) (Tst := Q)).body [N, 0, N] (St);
    while j < 2 * N, (Has.inj CmpTst.isPos) [] (St) {
      run (roundedWorklistRound D L).body [N, k, np, F] (A, Thr, P, St, Out, W, R, Fl)
    } then {
      if (Has.inj CmpTst.isPos) [] (St) {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      } else { skip }
    }
  }

/-- **The rounded deflation worklist** with the decoupling implementation `D` and the leaf
routine `L`: allocate the stack, the work matrix and the scan registers, and run the capped
worklist. The interface is `[N, k, np, F] (A, Thr, P) → (Out, Fl)`, with `F` the decoupler's
iteration cap passed through: the matrix (modified in place),
the threshold word, the decoupler's `np` parameter words, the $2N$ output words and the failure
word. -/
def solveRounded (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F] (A, Thr, P) → (Out, Fl) {
    let St ← alloc (1 + 2 * N);
    let W ← alloc (2 * (N * N));
    let R ← alloc 5;
    run (roundedWorklist D L).body [N, k, np, F] (A, Thr, P, St, Out, W, R, Fl)
  }

/-! ### The worklist with routines that read parameter words and a cap dimension -/

/-- `NLAlib.ShiftedQR.roundedProcessLarge` with the cap dimension `T` passed to the decoupler
`[N, k, np, F, T] (W, P) → (W, Fl)`. -/
def roundedProcessLargeWith (D : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run D.body [d, k, np, F, T] (W, P, W, Fl);
    if (Has.inj CmpTst.isPos) [] (Fl) {
      run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
    } else {
      run (bottomScan (O := O) (Q := Q)).body [d, k] (W, Thr, R);
      if (Has.inj CmpTst.isPos) [] (R[3]) {
        let i ← index (Has.inj IdxTst.toNat) (R[4]) ≤ d;
        run (writeAndSplit (O := O) (Q := Q)).body [N, lo, d, i] (A, St, W)
      } else {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      }
    }
  }

/-- `NLAlib.ShiftedQR.roundedProcessRange` with routines that read the parameter words and the cap
dimension: a block of order at most $k$ goes to the leaf routine `[d, np, T] (Bk, P) → (Ev)`, a
larger one to `NLAlib.ShiftedQR.roundedProcessLargeWith`. -/
def roundedProcessRangeWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, lo, d] (A, W);
    ifPos k + 1 - d {
      run L.body [d, np, T] (W, P, Out[2 * lo])
    };
    ifPos d - k {
      run (roundedProcessLargeWith D).body [N, k, np, F, T, lo, d]
        (A, Thr, P, St, Out, W, R, Fl)
    }
  }

/-- `NLAlib.ShiftedQR.roundedWorklistRound` with the cap dimension `T`. -/
def roundedWorklistRoundWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (rangePop (Op := O) (Tst := Q)).body [N] (St, R);
    let lo ← index (Has.inj IdxTst.toNat) (R) ≤ N;
    let d ← index (Has.inj IdxTst.toNat) (R[1]) ≤ N;
    run (roundedProcessRangeWith D L).body [N, k, np, F, T, lo, d]
      (A, Thr, P, St, Out, W, R, Fl)
  }

/-- `NLAlib.ShiftedQR.roundedWorklist` with the cap dimension `T`. -/
def roundedWorklistWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T] (A, Thr, P) → (St, Out, W, R, Fl) {
    call (Has.inj IndexOp.lit) [0] () → (Fl);
    run (stackInit (Op := O) (Tst := Q)).body [N, 0, N] (St);
    while j < 2 * N, (Has.inj CmpTst.isPos) [] (St) {
      run (roundedWorklistRoundWith D L).body [N, k, np, F, T] (A, Thr, P, St, Out, W, R, Fl)
    } then {
      if (Has.inj CmpTst.isPos) [] (St) {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      } else { skip }
    }
  }

/-- **The rounded deflation worklist with routines** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1], whose worklist at $k = 1$ it is; [BanksGarzaVargasSrivastava2022, Theorem 6.3]):
`NLAlib.ShiftedQR.solveRounded` with a decoupling routine
`[N, k, np, F, T] (W, P) → (W, Fl)` and a leaf routine `[d, np, T] (Bk, P) → (Ev)`, both of which
read the parameter words and the cap dimension $T$ of the routines they run. The interface is
`[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`. The merged worklist is the case of the lifted routines
(`NLAlib.ShiftedQR.liftDecoupler`, `NLAlib.ShiftedQR.liftLeaf`) at $T = 0$. -/
def solveRoundedWith (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T] (A, Thr, P) → (Out, Fl) {
    let St ← alloc (1 + 2 * N);
    let W ← alloc (2 * (N * N));
    let R ← alloc 5;
    run (roundedWorklistWith D L).body [N, k, np, F, T] (A, Thr, P, St, Out, W, R, Fl)
  }

end Program

/-- The regions a round of the rounded worklist may write: the matrix, the stack, the output, the
work matrix, the scan registers and the failure word. -/
def roundedWorklistFp (N : ℕ) (a st out w r f : ℕ × ℕ) : Fp :=
  Fp.blocks [a, st, out, w, r, f] [2 * (N * N), 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1]

/-- The eight views of the rounded worklist (matrix, threshold, parameters, stack, output, work
matrix, scan registers, failure word) are live, have room and are pairwise apart
(`NLAlib.Ops.Geometry`). -/
abbrev RoundedGeometry (N np : ℕ) (a t p st out w r f : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  Geometry [a, t, p, st, out, w, r, f] [2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1] μ

/-- **The state of the rounded worklist before round `j`** at the current matrix $\mathbf{M}$,
for the input $\mathbf{H}_0$, the per-round error `e`, the threshold `thr` and the decoupler's
parameter words `ps`: the geometry holds and the threshold and parameter words are stored; and
either the run has failed (allowed only when `fails` holds; failure word $1$, stack count $0$), or
the failure word is $0$, $\|\mathbf{M}\|_2 \le \|\mathbf{H}_0\|_2 + j e$, and the deflation
invariant holds for $\mathbf{M}$ with error $0$, with the current matrix stored in `a`, the
finished outputs in `out`, the active ranges on the stack, and the progress measure $j + 1$. -/
def RoundedWorklistState {n : ℕ} (fails : Prop) (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e thr : ℝ) (ps : List ℝ) (a t p st out w r f : ℕ × ℕ) (j : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  RoundedGeometry (n + 1) ps.length a t p st out w r f μ ∧ μ.store.get t.1 t.2 = some thr ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧
    ((fails ∧ μ.store.get f.1 f.2 = some 1 ∧ μ.store.get st.1 st.2 = some 0) ∨
      (μ.store.get f.1 f.2 = some 0 ∧ specNorm M ≤ specNorm H₀ + j * e ∧
        ∃ (active done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (roots : Fin (n + 1) → ℂ),
          DeflationInv M 0 active done A roots ∧ HoldsMatrix a A μ.store ∧
            FinishedHolds out done roots μ.store ∧ StackHolds st active.reverse μ.store ∧
            2 * done.length + active.length = j + 1))

/-- The part of `NLAlib.ShiftedQR.RoundedWorklistState` that a round changes: failed (failure
word $1$, stack count $0$), or the failure word $0$, the norm bound and the deflation invariant at
error $0$ for $\mathbf{M}$ with its storage. -/
def RoundedCore {n : ℕ} (fails : Prop) (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : ℝ)
    (a st out f : ℕ × ℕ) (j : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  (fails ∧ μ.store.get f.1 f.2 = some 1 ∧ μ.store.get st.1 st.2 = some 0) ∨
    (μ.store.get f.1 f.2 = some 0 ∧ specNorm M ≤ specNorm H₀ + j * e ∧
      ∃ (active done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (roots : Fin (n + 1) → ℂ),
        DeflationInv M 0 active done A roots ∧ HoldsMatrix a A μ.store ∧
          FinishedHolds out done roots μ.store ∧ StackHolds st active.reverse μ.store ∧
          2 * done.length + active.length = j + 1)

/-- **The state of a round after the pop** of the range $(lo, d)$ before round `j`: the geometry,
the threshold and parameter words, the failure word $0$, the norm bound, and the deflation
invariant at error $0$ with $(lo, d)$ first, the remaining ranges on the stack. -/
def RoundedPopped {n : ℕ} (H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e thr : ℝ) (ps : List ℝ)
    (a t p st out w r f : ℕ × ℕ) (j : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (lo d : ℕ) (rest done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (roots : Fin (n + 1) → ℂ) (μ : Mem ℝ) : Prop :=
  RoundedGeometry (n + 1) ps.length a t p st out w r f μ ∧ μ.store.get t.1 t.2 = some thr ∧
    μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.store.get f.1 f.2 = some 0 ∧
    specNorm M ≤ specNorm H₀ + j * e ∧ DeflationInv M 0 ((lo, d) :: rest) done A roots ∧
    HoldsMatrix a A μ.store ∧ FinishedHolds out done roots μ.store ∧
    StackHolds st rest.reverse μ.store ∧ 2 * done.length + rest.length = j

/-- The eight views of the rounded worklist keep their geometry through every spatial frame. -/
theorem RoundedGeometry.of_eqOff {N np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ μ' : Mem ℝ} {F : Fp}
    (h : RoundedGeometry N np a t p st out w r f μ) (hfr : μ.store.EqOff F μ'.store) :
    RoundedGeometry N np a t p st out w r f μ' :=
  Geometry.of_eqOff h hfr

/-- Any list of the eight views of the rounded worklist is live. -/
theorem RoundedGeometry.live_of_subset {N np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ : Mem ℝ}
    (h : RoundedGeometry N np a t p st out w r f μ) {l : List (ℕ × ℕ)}
    (hl : ∀ x ∈ l, x ∈ [a, t, p, st, out, w, r, f]) : μ.Live l :=
  Geometry.live_of_subset h hl

/-- Two distinct views of the rounded worklist have disjoint words. -/
theorem RoundedGeometry.disj {N np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ : Mem ℝ}
    (h : RoundedGeometry N np a t p st out w r f μ) (i j : Fin 8) (hne : i ≠ j) :
    Fp.Disj
      (Store.inBlock (([a, t, p, st, out, w, r, f] : List (ℕ × ℕ)).getD i (0, 0)).1
        (([a, t, p, st, out, w, r, f] : List (ℕ × ℕ)).getD i (0, 0)).2
        (([2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1] : List ℕ).getD i 0))
      (Store.inBlock (([a, t, p, st, out, w, r, f] : List (ℕ × ℕ)).getD j (0, 0)).1
        (([a, t, p, st, out, w, r, f] : List (ℕ × ℕ)).getD j (0, 0)).2
        (([2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1] : List ℕ).getD j 0)) :=
  h.apart.disj_getD (by simp) (by simp) (fun he => hne (Fin.ext he))

/-- The pairs of views of the rounded worklist whose separation a round uses. -/
theorem RoundedGeometry.disj_round {n np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ : Mem ℝ}
    (h : RoundedGeometry (n + 1) np a t p st out w r f μ) :
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock t.1 t.2 1) ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock p.1 p.2 np) ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock out.1 out.2 (2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock f.1 f.2 1) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock t.1 t.2 1) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock out.1 out.2 (2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock f.1 f.2 1) ∧
      Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧
      Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock out.1 out.2 (2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock t.1 t.2 1) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock out.1 out.2 (2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Store.inBlock out.1 out.2 (2 * (n + 1))) ∧
      Fp.Disj (Store.inBlock p.1 p.2 np)
        (Store.inBlock f.1 f.2 1) :=
  ⟨by simpa using h.disj 5 0 (by simp),
    by simpa using h.disj 5 1 (by simp),
    by simpa using h.disj 5 2 (by simp),
    by simpa using h.disj 5 3 (by simp),
    by simpa using h.disj 5 4 (by simp),
    by simpa using h.disj 5 7 (by simp),
    by simpa using h.disj 6 0 (by simp),
    by simpa using h.disj 6 1 (by simp),
    by simpa using h.disj 6 3 (by simp),
    by simpa using h.disj 6 4 (by simp),
    by simpa using h.disj 6 7 (by simp),
    by simpa using h.disj 6 5 (by simp),
    by simpa using h.disj 7 0 (by simp),
    by simpa using h.disj 7 3 (by simp),
    by simpa using h.disj 7 4 (by simp),
    by simpa using h.disj 7 1 (by simp),
    by simpa using h.disj 0 3 (by simp),
    by simpa using h.disj 0 4 (by simp),
    by simpa using h.disj 3 4 (by simp),
    by simpa using h.disj 2 7 (by simp)⟩

/-- The work matrix and the scan registers are apart from the six other views. -/
theorem RoundedGeometry.disj_scratch {N np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ : Mem ℝ}
    (h : RoundedGeometry N np a t p st out w r f μ) :
    Fp.Disj (Store.inBlock w.1 w.2 (2 * (N * N)) ⊔ Store.inBlock r.1 r.2 5)
      (Fp.blocks [a, t, p, st, out, f] [2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 1]) := by
  simpa only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
    h.apart.disj_select [5, 6] [0, 1, 2, 3, 4, 7] (by simp) (by simp) (by simp)

/-- The writes of a round leave the threshold and the parameter words alone. -/
theorem RoundedGeometry.disj_params {N np : ℕ} {a t p st out w r f : ℕ × ℕ} {μ : Mem ℝ}
    (h : RoundedGeometry N np a t p st out w r f μ) :
    Fp.Disj (roundedWorklistFp N a st out w r f)
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock p.1 p.2 np) := by
  simpa only [roundedWorklistFp, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
    h.apart.disj_select [0, 3, 4, 5, 6, 7] [1, 2] (by simp) (by simp) (by simp)

/-- A state of the worklist is its geometry, its threshold and parameter words and its core; a
write inside the round footprint keeps the first three. -/
theorem RoundedWorklistState.of_core {n : ℕ} {fails : Prop}
    {H₀ M' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e thr : ℝ} {ps : List ℝ}
    {a t p st out w r f : ℕ × ℕ} {j : ℕ} {μ μ' : Mem ℝ} {F : Fp}
    (h : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfr : μ.store.EqOff F μ'.store) (hF : F ≤ roundedWorklistFp (n + 1) a st out w r f)
    (hcore : RoundedCore fails H₀ e a st out f j M' μ') :
    RoundedWorklistState fails H₀ e thr ps a t p st out w r f j M' μ' := by
  have hd := h.disj_params.mono hF le_rfl
  exact ⟨h.of_eqOff hfr, hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl le_sup_left) ht,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hd.mono le_rfl le_sup_right) hp, hcore⟩

/-- A popped state survives writes to the work matrix. -/
theorem RoundedPopped.of_eqOff_work {n j lo d : ℕ} {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {roots : Fin (n + 1) → ℂ} {e thr : ℝ} {ps : List ℝ} {a t p st out w r f : ℕ × ℕ}
    {rest done : List (ℕ × ℕ)} {μ μ' : Mem ℝ} {F : Fp}
    (h : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hfr : μ.store.EqOff F μ'.store)
    (hF : F ≤ Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) :
    RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ' := by
  obtain ⟨hG, ht, hp, hf, hnorm, hInv, hA, hOut, hSt, hj⟩ := h
  have hd (i : Fin 8) (hi : i ≠ 5) := (hG.disj 5 i (Ne.symm hi)).mono hF le_rfl
  have hrest : rest.length ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  refine ⟨hG.of_eqOff hfr,
    hfr.keep (Store.readsOnly_get _ _ _) (by simpa using hd 1 (by simp)) ht,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by simpa using hd 2 (by simp)) hp,
    hfr.keep (Store.readsOnly_get _ _ _) (by simpa using hd 7 (by simp)) hf, hnorm, hInv,
    hA.of_eqOff hfr (by simpa using hd 0 (by simp)),
    hOut.of_eqOff hfr ((by simpa using hd 4 (by simp) : Fp.Disj F
      (Store.inBlock out.1 out.2 (2 * (n + 1)))).mono le_rfl (finishedFp_le
        (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2))),
    hSt.of_eqOff hfr ((by simpa using hd 3 (by simp) : Fp.Disj F
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
        (by simp only [List.length_reverse]; fp_sub)), hj⟩

/-- In a popped state before round $j < 2(n+1)$, the popped block has norm at most $N_0$ when
$\|\mathbf{H}_0\|_2 + 2(n+1)e \le N_0$, $e \ge 0$. -/
theorem RoundedPopped.specNorm_subBlock_le {n j lo d : ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ} {e thr N₀ : ℝ}
    {ps : List ℝ} {a t p st out w r f : ℕ × ℕ} {rest done : List (ℕ × ℕ)} {μ : Mem ℝ}
    (h : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (he0 : 0 ≤ e) (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    specNorm (subBlock A (lo, d)) ≤ N₀ := by
  have h1 := h.2.2.2.2.2.1.specNorm_subBlock_le (r := (lo, d)) List.mem_cons_self
  have h2 : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
  linarith [h.2.2.2.2.1]

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

/-- The final state of the rounded worklist: failed, or the failure word $0$, every range finished
for $\mathbf{M}$ at error $0$, and the output holding the listing. -/
def RoundedFinal {n : ℕ} (fails : Prop) (out f : ℕ × ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (μ : Mem ℝ) : Prop :=
  (fails ∧ μ.store.get f.1 f.2 = some 1) ∨
    (μ.store.get f.1 f.2 = some 0 ∧ ∃ (done : List (ℕ × ℕ))
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
      DeflationInv M 0 [] done A roots ∧
        HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ.store)

/-- The stack count of a worklist state is a natural; at $0$ the state is final, and a positive
count leaves room for another round. -/
theorem RoundedWorklistState.count {n : ℕ} {fails : Prop}
    {H₀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e thr : ℝ} {ps : List ℝ}
    {a t p st out w r f : ℕ × ℕ} {j : ℕ} {μ : Mem ℝ}
    (h : RoundedWorklistState fails H₀ e thr ps a t p st out w r f j M μ) :
    ∃ cnt : ℕ, μ.store.get st.1 st.2 = some (cnt : ℝ) ∧ (cnt = 0 → RoundedFinal fails out f M μ) ∧
      (0 < cnt → j + 1 < 2 * (n + 1)) := by
  rcases h.2.2.2 with ⟨hfa, hf, hs⟩ | ⟨hf, -, active, done, A, roots, hInv, -, hOut, hSt, hj⟩
  · exact ⟨0, by simpa using hs, fun _ => Or.inl ⟨hfa, hf⟩, fun h0 => absurd h0 (lt_irrefl 0)⟩
  · refine ⟨active.length, by simpa using hSt.1, fun h0 => ?_, fun hpos => ?_⟩
    · obtain rfl := List.length_eq_zero_iff.mp h0
      have hpart : IsRangePartition (n + 1) done := by simpa using hInv.partition
      exact Or.inr ⟨hf, done, A, roots, hInv, hOut.holdsMatrix_of_partition hpart⟩
    · have := hInv.two_mul_length_add_length_lt (List.ne_nil_of_length_pos hpos)
      omega

/-- The five caller views with the three freshly allocated buffers (stack, work matrix, scan
registers) on top form the geometry of the rounded worklist. -/
theorem roundedGeometry_allocated {N np : ℕ} {μ : Mem ℝ} {a t p out f : ℕ × ℕ} {s : Store ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * (N * N), 1, np, 2 * N, 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * (N * N), 1, np, 2 * N, 1])
    (hs : s.length = μ.store.length + 3)
    (hlens : ∀ i (hi : i < ([1 + 2 * N, 2 * (N * N), 5] : List ℕ).length),
      s.len (μ.store.length + i) = ([1 + 2 * N, 2 * (N * N), 5] : List ℕ)[i])
    (hBelow : Store.Below μ.store.length μ.store s) :
    RoundedGeometry N np a t p (μ.store.length, 0) out (μ.store.length + 1, 0)
      (μ.store.length + 2, 0) f ⟨s, μ.pos⟩ := by
  let L := μ.store.length
  let ns := [1 + 2 * N, 2 * (N * N), 5]
  have hA := (show Geometry [a, t, p, out, f] [2 * (N * N), 1, np, 2 * N, 1] μ from
    ⟨hl, hr, ha⟩).allocated (ns := ns) hs hlens hBelow
  have hRoom : (⟨s, μ.pos⟩ : Mem ℝ).Room [a, t, p, out, f, (L, 0), (L + 1, 0), (L + 2, 0)]
      [2 * (N * N), 1, np, 2 * N, 1, 1 + 2 * N, 2 * (N * N), 5] := by
    simpa [ns, L, List.range_succ] using hA.room
  have hAll : Fp.Apart [a, t, p, out, f, (L, 0), (L + 1, 0), (L + 2, 0)]
      [2 * (N * N), 1, np, 2 * N, 1, 1 + 2 * N, 2 * (N * N), 5] := by
    simpa [ns, L, List.range_succ] using hA.apart
  let e : Fin 8 → Fin 8 := ![0, 1, 2, 5, 3, 6, 7, 4]
  have hReorder := hAll.subviews (fun i : Fin 8 => e i) (fun _ => 0)
    (fun i => ([2 * (N * N), 1, np, 2 * N, 1, 1 + 2 * N, 2 * (N * N), 5] : List ℕ).getD (e i) 0)
    (by intro i; simpa only [ns, List.cons_append, List.nil_append, Nat.zero_add] using
      (le_refl (([2 * (N * N), 1, np, 2 * N, 1, 1 + 2 * N, 2 * (N * N), 5] : List ℕ).getD
        (e i) 0)))
    (by
      intro i j hne he
      have hv := congrArg Fin.val he
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hne | simp [e] at hv)
  refine ⟨?_, ?_, ?_⟩
  · have hla := hl a (by simp)
    have hlt := hl t (by simp)
    have hlp := hl p (by simp)
    have hlo := hl out (by simp)
    have hlf := hl f (by simp)
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [hs]; omega)
  · exact ⟨hRoom.1, hRoom.2.1, hRoom.2.2.1, hRoom.2.2.2.2.2.1, hRoom.2.2.2.1,
      hRoom.2.2.2.2.2.2.1, hRoom.2.2.2.2.2.2.2.1, hRoom.2.2.2.2.1, trivial⟩
  · simpa [e, ns, L, List.ofFn_succ] using hReorder

/-- A listing of the eigenvalues of a square matrix by `Fin d` is its multiset of characteristic
roots. -/
theorem _root_.NLAlib.IsEigenvalueListing.charpoly_roots_eq_ofFn {d : ℕ}
    {B : Matrix (Fin d) (Fin d) ℂ} {rts : Fin d → ℂ} (h : IsEigenvalueListing B rts) :
    B.charpoly.roots = (List.ofFn rts : Multiset ℂ) := by
  rw [isEigenvalueListing_iff.mp h]
  simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
    List.prod_ofFn, Function.comp_def] using
    Polynomial.roots_multiset_prod_X_sub_C (List.ofFn rts : Multiset ℂ)

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
