/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistSolve
public import NLAlib.Eigensolvers.ShiftedQR.WorklistAllocation
public import NLAlibScaffold.Matrix.QRIteration.DeflationPerturbed
public import NLAlibScaffold.Ops.Logic.BackwardFrame

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

The program reuses the exact development's stack (`rangePop`, `stackInit`), block copies, the
split (`NLAlib.ShiftedQR.writeAndSplit`) and the scan visit (`NLAlib.ShiftedQR.scanRound`); the
exact worklist, its scan and `NLAlib.ShiftedQR.DecouplingContract` are not changed. The run is
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
* `NLAlib.ShiftedQR.RoundedWorklistState`: the state between two rounds.

## Main results

* `NLAlib.ShiftedQR.IsEigenvalueKernels.backwardLeafContract`: the exact kernel is a leaf
  routine with error $0$.
* `NLAlib.ShiftedQR.bottomScan_writes`: the rounded bottom-$k$ scan (the decision of `Deflate`).
* `NLAlib.ShiftedQR.roundedWorklistRound_backwardStep`: one round is a backward step.
* `NLAlib.ShiftedQR.solveRounded_backward`: the backward error of the rounded worklist.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

/-- **The contract of a rounded decoupling implementation** with the failure alternative
`fails`, the bottom width `k`, the parameter words `ps`, the coupling threshold `ω` and the
backward error `ε N` for inputs of norm at most `N`. From an upper Hessenberg matrix of order
$n + 1 \ge k + 1$ stored in place, the run is total, writes only the matrix and the one-word
flag, and either sets the flag to $1$ (allowed only when `fails` holds) or sets it to $0$ and
stores an upper Hessenberg perturbed unitary similarity $\mathbf{H}'$ of the input with backward
error $\varepsilon(N)$ and one of its bottom $k$ subdiagonal entries of modulus at most $\omega$.
Nothing is assumed of the tape: a randomized implementation meets the contract with `fails` true.
The interface is `[n, k, np] (W, P) → (W, Fl)`. -/
def RoundedDecouplingContract (fails : Prop) (k : ℕ) (ps : List ℝ) (ω : ℝ) (ε : ℝ → ℝ)
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
    Writes .total I tape D.body (Env.frame [n + 1, k, ps.length] [w, q, w, f])
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
  opsImpl% [N, k, np, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run D.body [d, k, np] (W, P, W, Fl);
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

/-- Copy the active block to `W`; a block of order at most $k$ goes to the leaf routine, which
writes its roots at offset $2\,lo$ of `Out`; a larger one to
`NLAlib.ShiftedQR.roundedProcessLarge`. -/
def roundedProcessRange (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, lo, d] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, lo, d] (A, W);
    ifPos k + 1 - d {
      run L.body [d] (W, Out[2 * lo])
    };
    ifPos d - k {
      run (roundedProcessLarge D).body [N, k, np, lo, d] (A, Thr, P, St, Out, W, R, Fl)
    }
  }

/-- Pop the top range, bounded-read its start and order, and process it. -/
def roundedWorklistRound (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np] (A, Thr, P, St) → (Out, W, R, Fl) {
    run (rangePop (Op := O) (Tst := Q)).body [N] (St, R);
    let lo ← index (Has.inj IdxTst.toNat) (R) ≤ N;
    let d ← index (Has.inj IdxTst.toNat) (R[1]) ≤ N;
    run (roundedProcessRange D L).body [N, k, np, lo, d] (A, Thr, P, St, Out, W, R, Fl)
  }

/-- The capped worklist: clear the failure word, push the whole range, and process the top range
while the stack is not empty, for at most $2N$ rounds; work left at the cap aborts. -/
def roundedWorklist (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np] (A, Thr, P) → (St, Out, W, R, Fl) {
    call (Has.inj IndexOp.lit) [0] () → (Fl);
    run (stackInit (Op := O) (Tst := Q)).body [N, 0, N] (St);
    while j < 2 * N, (Has.inj CmpTst.isPos) [] (St) {
      run (roundedWorklistRound D L).body [N, k, np] (A, Thr, P, St, Out, W, R, Fl)
    } then {
      if (Has.inj CmpTst.isPos) [] (St) {
        run (roundedAbort (O := O) (Q := Q)).body [] (St, Fl)
      } else { skip }
    }
  }

/-- **The rounded deflation worklist** with the decoupling implementation `D` and the leaf
routine `L`: allocate the stack, the work matrix and the scan registers, and run the capped
worklist. The interface is `[N, k, np] (A, Thr, P) → (Out, Fl)`: the matrix (modified in place),
the threshold word, the decoupler's `np` parameter words, the $2N$ output words and the failure
word. -/
def solveRounded (D L : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np] (A, Thr, P) → (Out, Fl) {
    let St ← alloc (1 + 2 * N);
    let W ← alloc (2 * (N * N));
    let R ← alloc 5;
    run (roundedWorklist D L).body [N, k, np] (A, Thr, P, St, Out, W, R, Fl)
  }

end Program

/-- The regions a round of the rounded worklist may write: the matrix, the stack, the output, the
work matrix, the scan registers and the failure word. -/
def roundedWorklistFp (N : ℕ) (a st out w r f : ℕ × ℕ) : Fp :=
  Fp.blocks [a, st, out, w, r, f] [2 * (N * N), 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1]

/-- The eight views of the rounded worklist are live, have room and are pairwise apart. -/
structure RoundedGeometry (N np : ℕ) (a t p st out w r f : ℕ × ℕ) (μ : Mem ℝ) : Prop where
  /-- Each view refers to a live buffer. -/
  live : μ.Live [a, t, p, st, out, w, r, f]
  /-- Matrix, threshold, parameters, stack, output, work matrix, scan registers, failure word. -/
  room : μ.Room [a, t, p, st, out, w, r, f]
    [2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1]
  /-- The views are pairwise apart. -/
  apart : Fp.Apart [a, t, p, st, out, w, r, f]
    [2 * (N * N), 1, np, 1 + 2 * N, 2 * N, 2 * (N * N), 5, 1]

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

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded bottom-$k$ scan** (the decision of `Deflate`, corrected): on a machine with the
standard model at $0 \le \boldsymbol{u} \le 1$ whose natural literals up to $n + 1$ are exact (the
flag and the index are such literals), for an $(n+1) \times (n+1)$ matrix $\mathbf{H}$,
$k \le n$ and the threshold word $t$, `bottomScan` writes only its five registers and either sets
the flag to $1$ and the index to some $i$ among the bottom $k$ subdiagonal positions
($n \le i + k$) with $(1 - \boldsymbol{u})^2|h_{i+1,i}|^2 \le t$, or sets the flag to $0$, and
then every bottom $k$ subdiagonal entry has $t < (1 + \boldsymbol{u})^2|h_{i+1,i}|^2$. -/
theorem bottomScan_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n)
    {a t r : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hH : HoldsMatrix a H m.store) (ht : m.store.get t.1 t.2 = some thr)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [a, t, r])
      (Store.inBlock r.1 r.2 5)
      (fun m' => m'.pos = m.pos ∧
        ((m'.store.get r.1 (r.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
            m'.store.get r.1 (r.2 + 4) = some (i : ℝ) ∧
            (1 - u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2 ≤ thr) ∨
          (m'.store.get r.1 (r.2 + 3) = some 0 ∧ ∀ i : Fin n, n ≤ (i : ℕ) + k →
            thr < (1 + u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2))) m := by
  sorry

/-- **One round of the rounded worklist is a backward step** (the per-round half of
[BanksGarzaVargasSrivastava2022, Theorem 6.3], backward error): on a machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact (the stack, the flags
and the indices are such literals), with a decoupler meeting `RoundedDecouplingContract` with the
bottom width $k$, the parameter words `ps`, the threshold $\omega$ and the error $\varepsilon$, and
a leaf routine with backward error $\beta \ge 0$, suppose the threshold word $t$ has $(1 +
\boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2 c^2$ with $c \ge 0$, $\varepsilon(N_0)
\ge 0$, $c + \varepsilon(N_0) + \beta \le e$ and $\|\mathbf{H}_0\|_2 + 2(n+1)e \le N_0$. Then for $j
< 2(n+1)$ the round is a backward step, for the perturbed unitary similarity of the current matrix
with error $e$, from the state before round $j$ with a positive stack count to the state before
round $j + 1$. -/
theorem roundedWorklistRound_backwardStep {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {j : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c e N₀ : ℝ}
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    BackwardStep .total I tape (roundedWorklistRound D L).body
      (Env.frame [n + 1, k, ps.length] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun ε A B => IsPerturbedUnitarySimilar A B ε)
      (fun M μ => RoundedWorklistState fails H₀ e thr ps a t p st out w r f j M μ ∧
        ∃ count : ℕ, μ.store.get st.1 st.2 = some (count : ℝ) ∧ 0 < count)
      (RoundedWorklistState fails H₀ e thr ps a t p st out w r f (j + 1)) e := by
  sorry

/-- **Backward error of the rounded deflation worklist** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], backward half, with the corrected `Deflate`): on a machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact (the stack, the flags
and the indices are such literals), let the decoupler `D` meet `RoundedDecouplingContract` with the
failure alternative `fails`, the bottom width $k$, the parameter words `ps`, the threshold
$\omega$ and the error $\varepsilon$, and let the leaf routine `L` have backward error
$\beta \ge 0$. Let $\mathbf{H}$ be upper Hessenberg of order $n + 1$, stored at `a`, the threshold
word $t$ satisfy $(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$ with
$c \ge 0$, and $\varepsilon(N_0) \ge 0$ with
$\|\mathbf{H}\|_2 + 2(n+1)(c + \varepsilon(N_0) + \beta) \le N_0$. Then `solveRounded D L` runs
to completion, writes only the matrix, the output and the failure word, and either fails (word
$1$, only when `fails` holds) or sets the failure word to $0$ and stores all eigenvalues, with
multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le 2(n+1)(c + \varepsilon(N_0) + \beta)$. With `fails` false the run never
fails. The views are live, have room and are pairwise apart. -/
theorem solveRounded_backward {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p out f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c N₀ : ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀) :
    Writes .total I tape (solveRounded D L).body
      (Env.frame [n + 1, k, ps.length] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
            HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
            specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
            (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))) μ := by
  sorry

end Theorems

end NLAlib.ShiftedQR
