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
public import NLAlibScaffold.Ops.Logic.Geometry
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

/-- **The converse of re-basing**: the invariant for $\mathbf{M}$ with error $\varepsilon$, where
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

/-- **A leaf as one perturbed similarity**: at error $0$, finishing the first active block with
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

/-- **A cut as one perturbed similarity**: at error $0$, replacing the first active block by a
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

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The registers of `bottomScan` after its first `j` visits: either the flag is $1$ and the
index is a bottom-$k$ position whose entry passed the rounded test, or the flag is $0$, the index
word is stored, and every visited entry failed it. -/
def BottomScanHolds {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u thr : ℝ) (k j : ℕ)
    (r : ℕ × ℕ) (st : Store ℝ) : Prop :=
  (st.get r.1 (r.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
      st.get r.1 (r.2 + 4) = some (i : ℝ) ∧ (1 - u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2 ≤ thr) ∨
    (st.get r.1 (r.2 + 3) = some 0 ∧ (∃ x, st.get r.1 (r.2 + 4) = some x) ∧
      ∀ i : Fin n, n ≤ (i : ℕ) + k → (i : ℕ) < n - k + j →
        thr < (1 + u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2)

/-- One visit of `bottomScan` advances `NLAlib.ShiftedQR.BottomScanHolds`. -/
private theorem bottomScanHolds_step {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) {n k j : ℕ} (hk : k ≤ n) (hj : j < k)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr flag index : ℝ} {r : ℕ × ℕ}
    {st st' : Store ℝ} (h : BottomScanHolds H u thr k j r st)
    (hflag : st.get r.1 (r.2 + 3) = some flag) (hindex : st.get r.1 (r.2 + 4) = some index)
    (hF : st'.get r.1 (r.2 + 3) =
      some (if subdiagonalSqWord M H (n - k + j) ≤ thr then 1 else flag))
    (hI : st'.get r.1 (r.2 + 4) =
      some (if subdiagonalSqWord M H (n - k + j) ≤ thr then ((n - k + j : ℕ) : ℝ) else index)) :
    BottomScanHolds H u thr k (j + 1) r st' := by
  let i₀ : Fin n := ⟨n - k + j, by omega⟩
  have hb := subdiagonalSqWord_bounds hM hu hu1 H i₀
  by_cases hs : subdiagonalSqWord M H (n - k + j) ≤ thr
  · rw [if_pos hs] at hF hI
    exact Or.inl ⟨hF, i₀, by simp only [i₀]; omega, hI, hb.1.trans hs⟩
  · rw [if_neg hs] at hF hI
    rcases h with ⟨h1, i, hik, hi, hthr⟩ | ⟨h0, -, hall⟩
    · rw [h1, Option.some.injEq] at hflag
      rw [hi, Option.some.injEq] at hindex
      exact Or.inl ⟨hflag ▸ hF, i, hik, hindex ▸ hI, hthr⟩
    · rw [h0, Option.some.injEq] at hflag
      refine Or.inr ⟨hflag ▸ hF, ⟨_, hI⟩, fun i hik hlt => ?_⟩
      by_cases he : (i : ℕ) = n - k + j
      · have hii : i = i₀ := Fin.ext he
        subst hii
        exact (lt_of_not_ge hs).trans_le hb.2
      · exact hall i hik (by omega)

omit [Has IdxTst Q] in
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
  have hzero : M.lit ((0 : ℕ) : ℚ) = (0 : ℝ) := by simpa using hNat 0 (Nat.zero_le _)
  unfold bottomScan
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hFlag⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIndex⟩
  have hFlag₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hFlag
  simp only [hzero] at hFlag₂ hIndex
  have hfr := (hfr₁.trans' hfr₂).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 5)
  have hH₂ := hH.of_eqOff hfr hA
  have ht₂ := hfr.keep (Store.readsOnly_get _ _ _) hT ht
  have hl₂ := hl.congr hfr.length_eq
  have hroom₂ : r.2 + 5 ≤ m₂.store.len r.1 := by rw [hfr.len_eq]; exact hroom
  refine (writes_loop rfl (fun _ => Store.inBlock r.1 r.2 5) (fun _ _ => le_rfl)
    (fun j m' => m'.pos = m₂.pos ∧ BottomScanHolds H u thr k j r m'.store)
    ⟨rfl, Or.inr ⟨hFlag₂, ⟨0, hIndex⟩, fun i hik hlt => by omega⟩⟩ ?_).mono le_rfl ?_
  · intro j hj m' hfr' ⟨hp', hs⟩
    obtain ⟨flag, hflag⟩ : ∃ x, m'.store.get r.1 (r.2 + 3) = some x := by
      rcases hs with ⟨h1, -⟩ | ⟨h0, -⟩
      exacts [⟨_, h1⟩, ⟨_, h0⟩]
    obtain ⟨index, hindex⟩ : ∃ x, m'.store.get r.1 (r.2 + 4) = some x := by
      rcases hs with ⟨-, i, -, hi, -⟩ | ⟨-, hx, -⟩
      exacts [⟨_, hi⟩, hx]
    have hw := scanRound_writes_word (τ := τ) (k := n + 1 - 1 - k + j) hS hL hC
      (hNat.mono n.le_succ)
      (by omega) (hH₂.of_eqOff hfr' hA) (hfr'.keep (Store.readsOnly_get _ _ _) hT ht₂) hflag
      hindex (hl₂.congr hfr'.length_eq) (by rw [hfr'.len_eq]; exact hroom₂) hA hT
    refine (hw.in_frame rfl rfl (hl₂.congr hfr'.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hp'', hF, hI⟩
    have he : n + 1 - 1 - k + j = n - k + j := by omega
    rw [he] at hF hI
    exact ⟨hp''.trans hp', bottomScanHolds_step hM hu hu1 hk hj hs hflag hindex hF hI⟩
  · intro m' _ ⟨hp', hs⟩
    refine ⟨hp'.trans (hp₂.trans hp₁), ?_⟩
    rcases hs with h1 | ⟨h0, -, hall⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h0, fun i hik => hall i hik (by omega)⟩

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The abort writes the failure word $1$ and the stack count $0$, on any machine whose literals
$0$ and $1$ are exact. -/
theorem roundedAbort_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hL : IsIndexLit M I) {B : ℕ}
    (hN : IsExactNatLit id M B) (hB : 1 ≤ B) {τ : Tape ℝ} {m : Mem ℝ} {st f : ℕ × ℕ}
    (hst : st.2 < m.store.len st.1) (hf : f.2 < m.store.len f.1)
    (hd : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 1)) :
    Writes .total I τ (roundedAbort (O := O) (Q := Q)).body (Env.frame [] [st, f])
      (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 1)
      (fun m' => m'.store.get f.1 f.2 = some 1 ∧ m'.store.get st.1 st.2 = some 0) m := by
  have h1 : M.lit ((1 : ℕ) : ℚ) = 1 := by simpa using hN 1 hB
  have h0 : M.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hN 0 (Nat.zero_le _)
  unfold roundedAbort
  refine (writes_indexLit hL rfl rfl (by omega)).seq_le le_sup_left ?_
  rintro m₁ hfr₁ ⟨-, hOne⟩
  refine (writes_indexLit hL rfl rfl (by rw [hfr₁.len_eq]; omega)).mono
    le_sup_right ?_
  rintro m₂ hfr₂ ⟨-, hZero⟩
  have hOne₂ := hfr₂.keep (Store.readsOnly_get _ _ _) hd.symm hOne
  exact ⟨by simpa only [h1] using hOne₂, by simpa only [h0] using hZero⟩

omit [Has CmpTst Q] in
/-- **Commit and split, memory effect**: `writeAndSplit` copies the work block $\mathbf{B}$ into
the diagonal block of the range $(lo, d)$ of the stored matrix and pushes the right child, then
the left child, on any scalar machine whose natural literals up to $n + 1$ are exact. -/
theorem writeAndSplit_writes_mem {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) {n : ℕ} (hN : IsExactNatLit id M (n + 1))
    {τ : Tape ℝ} {m : Mem ℝ} {lo d i : ℕ} {a st w : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    {rs : List (ℕ × ℕ)} (hl : m.Live [a, st, w]) (hA : HoldsMatrix a A m.store)
    (hW : HoldsMatrix w B m.store) (hSt : StackHolds st rs m.store) (hr : lo + d ≤ n + 1)
    (hi : i < d) (hcap : rs.length + 2 ≤ n + 1)
    (hroomA : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hroomS : st.2 + (1 + 2 * (n + 1)) ≤ m.store.len st.1)
    (hWA : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))) :
    Writes .total I τ (writeAndSplit (O := O) (Q := Q)).body
      (Env.frame [n + 1, lo, d, i] [a, st, w])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (setSubBlock A (lo, d) B) m'.store ∧
        StackHolds st (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) m'.store) m := by
  have hlWA : m.Live [w, a] := by
    simpa [Mem.Live] using And.intro (hl w (by simp)) (hl a (by simp))
  unfold writeAndSplit
  refine (copyToGlobal_writes (τ := τ) hS hlWA hA hW hr hroomA hWA).frame_seq_le rfl rfl hlWA
    ((blockFp_le a hr).trans le_sup_left) ?_
  intro m₁ hfr₁ ⟨hp₁, hA₁⟩
  have hSt₁ := hSt.of_eqOff hfr₁ (hAS.mono (blockFp_le a hr) (by fp_sub))
  have hlS : m₁.Live [st] := by
    simpa [Mem.Live, ← hfr₁.length_eq] using hl st (by simp)
  have hw := splitPush_writes_of_isExactNatLit (τ := τ) (lo := lo) (d := d) (i := i) hL hQ hN
    (by omega) (by omega) le_rfl hlS hSt₁ hcap
    (by rw [hfr₁.len_eq]; simpa only [Nat.add_assoc] using hroomS)
  refine (hw.in_frame rfl rfl hlS).mono le_sup_right ?_
  intro m₂ hfr₂ ⟨hp₂, hSt₂⟩
  exact ⟨hp₂.trans hp₁, hA₁.of_eqOff hfr₂ hAS.symm, hSt₂⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- **The leaf branch of a round**: the leaf routine on the copied block of the popped range
finishes it, a perturbed unitary similarity with error $\beta \le e$. -/
theorem roundedLeaf_writes {I : Interp O Q ℝ} {β : ℝ} (L : Impl O Q)
    (hLeaf : BackwardLeafContract β L I) {tape : Tape ℝ} {μ : Mem ℝ} {fails : Prop} {n j : ℕ}
    {a t p st out w r f : ℕ × ℕ} {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {roots : Fin (n + 1) → ℂ} {e thr : ℝ} {ps : List ℝ} {lo d : ℕ} {rest done : List (ℕ × ℕ)}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hW : HoldsMatrix w (subBlock A (lo, d)) μ.store) (hβe : β ≤ e) :
    Writes .total I tape L.body (Env.frame [d] [w, (out.1, out.2 + 2 * lo)])
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  obtain ⟨hG, -, -, hf, hnorm, hInv, hA, hOut, hSt, hj⟩ := hP
  have hr := hInv.active_block (r := (lo, d)) List.mem_cons_self
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hroomO : out.2 + 2 * (n + 1) ≤ μ.store.len out.1 := hG.room.2.2.2.2.1
  have houtFp : Store.inBlock out.1 (out.2 + 2 * lo) (2 * d) ≤
      Store.inBlock out.1 out.2 (2 * (n + 1)) := by have := hr.2.1; fp_sub
  have hWO : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d)) := by
    have hfull : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock out.1 out.2 (2 * (n + 1))) := by simpa using hG.disj 5 4 (by simp)
    exact hfull.mono (by fp_sub) houtFp
  have hOA : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 4 0 (by simp)
  have hOS : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by simpa using hG.disj 4 3 (by simp)
  have hOF : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1))) (Store.inBlock f.1 f.2 1) := by
    simpa using hG.disj 4 7 (by simp)
  have hlWO : μ.Live [w, (out.1, out.2 + 2 * lo)] := by
    simpa [Mem.Live] using And.intro (hG.live w (by simp)) (hG.live out (by simp))
  refine (hLeaf (subBlock A (lo, d)) hr.2.2 hW hlWO (by dsimp only; omega) hWO).mono le_rfl ?_
  rintro μ' hfr ⟨rts, F, hF, hList, hO⟩
  obtain ⟨M', hMM', hInv'⟩ := hInv.exists_isPerturbedUnitarySimilar_finish hF hList
  have hrest : rest.length ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hNew : HoldsMatrix (out.1, out.2 + 2 * lo)
      (Matrix.of fun i (_ : Fin 1) => subVec (setSubVec roots (lo, d) rts) (lo, d) i)
      μ'.store := by
    simpa only [subVec_setSubVec_self roots (lo, d) rts hr.2.1] using hO
  have hOut' := hOut.cons hfr (fun q hq => (hInv.disjoint_of_mem List.mem_cons_self hq).1)
    (fun q hq => subVec_setSubVec_of_disjoint roots (lo, d) q rts
      (hInv.disjoint_of_mem List.mem_cons_self hq).2
      (hInv.disjoint_of_mem List.mem_cons_self hq).1) hNew
  refine ⟨M', hMM'.mono hβe, Or.inr ⟨hfr.keep (Store.readsOnly_get _ _ _)
    (hOF.mono houtFp le_rfl) hf, ?_, rest, (lo, d) :: done, A, _, hInv',
    hA.of_eqOff hfr (hOA.mono houtFp le_rfl), hOut',
    hSt.of_eqOff hfr (hOS.mono houtFp (by simp only [List.length_reverse]; fp_sub)), ?_⟩⟩
  · have hle := hMM'.specNorm_le
    push_cast
    linarith
  · simp only [List.length_cons]
    omega

/-- **The cut of a round, mathematics**: after a successful decoupling call with output
$\mathbf{H}'$ (error $\varepsilon(N_0)$) and a scan that passed at $i$ with
$(1-\boldsymbol{u})^2|h'_{i+1,i}|^2 \le t \le (1-\boldsymbol{u})^2c^2$, the stored split is the
core state of the next round, reached with error $e \ge \varepsilon(N_0) + c$. -/
theorem roundedCut_core {fails : Prop} {n j lo d : ℕ} {a st out f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {u thr c e ε : ℝ} {μ' : Mem ℝ}
    {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hu1 : u < 1) (hc : 0 ≤ c)
    (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (he : c + ε ≤ e)
    (hnorm : specNorm M ≤ specNorm H₀ + j * e)
    (hInv : DeflationInv M 0 ((lo, d + 1) :: rest) done A roots)
    (hH' : IsPerturbedUnitarySimilar (subBlock A (lo, d + 1)) H' ε)
    (hHess : IsUpperHessenberg H') (i : Fin d)
    (hthr : (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ thr)
    (hf : μ'.store.get f.1 f.2 = some 0)
    (hA : HoldsMatrix a (setSubBlock A (lo, d + 1) H') μ'.store)
    (hOut : FinishedHolds out done roots μ'.store)
    (hSt : StackHolds st (rest.reverse ++ [(lo + i + 1, d + 1 - i - 1), (lo, i + 1)]) μ'.store)
    (hj : 2 * done.length + rest.length = j) :
    ∃ M', IsPerturbedUnitarySimilar M M' e ∧ RoundedCore fails H₀ e a st out f (j + 1) M' μ' := by
  have hcut' : ‖H' i.succ i.castSucc‖ ≤ c := by
    have hpos : 0 < (1 - u) ^ 2 := by have : 0 < 1 - u := by linarith
                                      positivity
    have hsq : ‖H' i.succ i.castSucc‖ ^ 2 ≤ c ^ 2 := le_of_mul_le_mul_left (hthr.trans hcut) hpos
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).mp hsq
  obtain ⟨M', hMM', hInv'⟩ := hInv.exists_isPerturbedUnitarySimilar_split hH' hHess i hcut'
  refine ⟨M', hMM'.mono (by linarith), Or.inr ⟨hf, ?_, _, done, _, roots, hInv', hA, hOut,
    by simpa [List.reverse_cons, List.append_assoc] using hSt, ?_⟩⟩
  · have hle := hMM'.specNorm_le
    push_cast
    linarith
  · simp only [List.length_cons]
    omega

/-- **The large branch of a round**: the decoupler on the copied block of the popped range
$(lo, d + 1)$, $d \ge k$, either fails (failure word $1$, stack count $0$) or is followed by the
bottom scan, which then always passes, and the cut and the push of both children; the core state of
the next round is reached with error $e \ge \varepsilon(N_0) + c$. -/
theorem roundedLarge_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k ps ω ε D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {thr c e N₀ : ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo (d + 1) rest done A roots μ)
    (hW : HoldsMatrix w (subBlock A (lo, d + 1)) μ.store) (hk : k ≤ d)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (he : c + ε N₀ ≤ e) (he0 : 0 ≤ e) (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hj : j < 2 * (n + 1)) :
    Writes .total I tape (roundedProcessLarge D).body
      (Env.frame [n + 1, k, ps.length, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  obtain ⟨hG, ht, hp, hf, hnorm, hInv, hA, hOut, hSt, hj'⟩ := id hP
  have hr := hInv.active_block (r := (lo, d + 1)) List.mem_cons_self
  have hd : d + 1 ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hrest : rest.length + 1 ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hWw : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hdone : finishedFp out done ≤ Store.inBlock out.1 out.2 (2 * (n + 1)) :=
    finishedFp_le (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)
  obtain ⟨hWA, hWT, hWP, hWS, hWO, hWF, hRA, hRT, hRS, hRO,
    hRF, hRW, hFA, hFS, hFO, hFT, hAS, hAO, hSO, hPF⟩ := hG.disj_round
  have hlD : μ.Live [w, p, w, f] := hG.live_of_subset (by simp)
  have hw := hD (tape := tape) (N := N₀) (subBlock A (lo, d + 1)) hk hr.2.2
    (hP.specNorm_subBlock_le he0 hN₀ hj) hW hp hlD
    (by have := hG.room.2.2.2.2.2.1; omega) hG.room.2.2.2.2.2.2.2.1 (hWF.mono hWw le_rfl)
    (Fp.disj_sup_right.mpr ⟨hWP.symm.mono le_rfl hWw, hPF⟩)
  have hDfp : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 :=
    sup_le_sup_right hWw _
  unfold roundedProcessLarge
  refine hw.frame_seq_le rfl rfl hlD (by fp_sub [roundedWorklistFp]) ?_
  intro μ₁ hfr₁ hD₁
  have hG₁ := hG.of_eqOff hfr₁
  have hA₁ := hA.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWA, hFA⟩).mono hDfp le_rfl)
  have hSt₁ := hSt.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWS, hFS⟩).mono hDfp
    (by simp only [List.length_reverse]; fp_sub))
  have hOut₁ := hOut.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWO, hFO⟩).mono hDfp hdone)
  have ht₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    ((Fp.disj_sup_left.mpr ⟨hWT, hFT⟩).mono hDfp le_rfl) ht
  have hlSF : μ₁.Live [st, f] := hG₁.live_of_subset (by simp)
  have habort := roundedAbort_writes (O := O) (Q := Q) (τ := tape) (m := μ₁) hL hNat
    (by omega) (st := st) (f := f) (by have := hG₁.room.2.2.2.1; omega)
    (by have := hG₁.room.2.2.2.2.2.2.2.1; omega) (hFS.mono le_rfl (by fp_sub))
  rcases hD₁ with ⟨hfails, hF1⟩ | ⟨hF0, H', hH', hHess', ⟨i₀, hi₀k, hi₀⟩, hW₁⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hF1) ?_
    have h1 : decide (0 < id (1 : ℝ)) = true := by simp
    rw [h1, if_pos rfl]
    refine (habort.in_frame rfl rfl hlSF).mono (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₂ - ⟨hF, hS0⟩
    exact ⟨M, (IsPerturbedUnitarySimilar.refl M).mono he0, Or.inl ⟨hfails, hF, hS0⟩⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hF0) ?_
    have h0 : decide (0 < id (0 : ℝ)) = false := by simp
    rw [h0, if_neg (by simp)]
    have hlS : μ₁.Live [w, t, r] := hG₁.live_of_subset (by simp)
    have hb := bottomScan_writes (τ := tape) (n := d) (k := k) hS hM hu hu1.le hL
      (hNat.mono (by omega)) hC hk hW₁ ht₁ hlS hG₁.room.2.2.2.2.2.2.1 (hRW.mono le_rfl hWw) hRT
    refine (hb.in_frame rfl rfl hlS).seq_le (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₂ hfr₂ ⟨-, hscan⟩
    have hG₂ := hG₁.of_eqOff hfr₂
    rcases hscan with ⟨hR1, i, -, hRi, hthr⟩ | ⟨-, hall⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR1) ?_
      have h1 : decide (0 < id (1 : ℝ)) = true := by simp
      rw [h1, if_pos rfl]
      refine writes_bindIdx_of_decode_nat hQ rfl rfl hRi rfl (by have := i.isLt; omega) ?_
      obtain ⟨_, -, hInvc⟩ := hInv.exists_isPerturbedUnitarySimilar_split hH' hHess' i le_rfl
      have hcap := hInvc.length_le
      simp only [List.length_append, List.length_cons] at hcap
      have hlASW : μ₂.Live [a, st, w] := hG₂.live_of_subset (by simp)
      have hsplit := writeAndSplit_writes_mem (O := O) (Q := Q) (τ := tape) (i := (i : ℕ)) hS hL
        hQ hNat hlASW (hA₁.of_eqOff hfr₂ hRA) (hW₁.of_eqOff hfr₂ (hRW.mono le_rfl hWw))
        (hSt₁.of_eqOff hfr₂ (hRS.mono le_rfl (by simp only [List.length_reverse]; fp_sub)))
        hr.2.1 (by have := i.isLt; omega) (by simp only [List.length_reverse]; omega)
        hG₂.room.1 hG₂.room.2.2.2.1 (hWA.mono hWw le_rfl) hAS
      refine (hsplit.in_frame rfl rfl hlASW).mono (by fp_sub [roundedWorklistFp]) ?_
      rintro μ₃ hfr₃ ⟨-, hA₃, hSt₃⟩
      have hfr₂₃ := hfr₂.trans' hfr₃
      exact roundedCut_core hu1 hc hcut he hnorm hInv hH' hHess' i hthr
        (hfr₂₃.keep (Store.readsOnly_get _ _ _)
          (Fp.disj_sup_left.mpr ⟨hRF, Fp.disj_sup_left.mpr ⟨hFA.symm, hFS.symm⟩⟩) hF0)
        hA₃ (hOut₁.of_eqOff hfr₂₃
          ((Fp.disj_sup_left.mpr ⟨hRO, Fp.disj_sup_left.mpr ⟨hAO, hSO⟩⟩).mono le_rfl hdone))
        hSt₃ hj'
    · exfalso
      have h1 := hall i₀ hi₀k
      have h2 : ‖H' i₀.succ i₀.castSucc‖ ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi₀ 2
      nlinarith [sq_nonneg (1 + u)]

/-- **Processing a popped range**: the copy of its block, then the leaf routine (order at most
$k$) or the large branch; the core state of the next round is reached with error $e$. -/
theorem roundedRange_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {thr c e N₀ : ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    Writes .total I tape (roundedProcessRange D L).body
      (Env.frame [n + 1, k, ps.length, lo, d] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  have hG := hP.1
  have hInv := hP.2.2.2.2.2.1
  have hr := hInv.active_block (r := (lo, d)) List.mem_cons_self
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hAW : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * (d * d))) :=
    (by simpa using hG.disj 0 5 (by simp) : Fp.Disj (Store.inBlock a.1 a.2
      (2 * ((n + 1) * (n + 1)))) (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))).mono
      le_rfl (by fp_sub)
  have hlAW : μ.Live [a, w] := hG.live_of_subset (by simp)
  have hcopy := copyToWork_writes (τ := tape) (lo := lo) (d := d) hS hlAW hP.2.2.2.2.2.2.1
    hr.2.1 (by have := hG.room.2.2.2.2.2.1; omega) hAW
  unfold roundedProcessRange
  refine hcopy.frame_seq_le rfl rfl hlAW (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hW₁⟩
  have hP₁ := hP.of_eqOff_work hfr₁ (by fp_sub)
  have hG₁ := hP₁.1
  by_cases hs : d ≤ k
  · refine (writes_ifPos (P := fun μ₂ => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
      RoundedCore fails H₀ e a st out f (j + 1) M' μ₂) (n := k + 1 - d) rfl ?_).seq_le le_rfl ?_
    · rw [if_pos (by omega)]
      have hl : μ₁.Live [w, (out.1, out.2 + 2 * lo)] := by
        simpa [Mem.Live] using And.intro (hG₁.live w (by simp)) (hG₁.live out (by simp))
      exact ((roundedLeaf_writes L hLeaf hP₁ hW₁ (by linarith)).in_frame rfl rfl hl).mono
        (by have := hr.2.1; fp_sub [roundedWorklistFp]) (fun _ _ hp => hp)
    · intro μ₂ _ hpost
      refine writes_ifPos (n := d - k) rfl ?_
      rw [if_neg (by omega)]
      exact hpost
  · refine (writes_ifPos (F := ⊥) (P := fun μ₂ => μ₂ = μ₁) (n := k + 1 - d) rfl
      (by rw [if_neg (by omega)])).seq_le bot_le ?_
    rintro μ₂ - rfl
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine writes_ifPos (n := d' + 1 - k) rfl ?_
    rw [if_pos (by omega)]
    exact (roundedLarge_writes hS hM hu hu1 hL hNat hQ hC D hD hP₁ hW₁ (by omega) hfind hcut hc
      (by linarith) (by linarith) hN₀ hj).in_frame rfl rfl hG₁.live

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
  rintro M μ ⟨⟨hG, ht, hp, hcore⟩, count, hcount, hpos⟩
  refine Writes.mono (P := fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
    RoundedCore fails H₀ e a st out f (j + 1) M' μ') ?_ le_rfl
    (fun μ' hfr ⟨M', hMM', hcore'⟩ =>
      ⟨M', hMM', RoundedWorklistState.of_core hG ht hp hfr le_rfl hcore'⟩)
  rcases hcore with ⟨-, -, hS0⟩ | ⟨hf, hnorm, active, done, A, roots, hInv, hA, hOut, hSt, hj'⟩
  · have h0 : (count : ℝ) = 0 := Option.some.inj (hcount.symm.trans hS0)
    exact absurd (by exact_mod_cast h0 : count = 0) (by omega)
  cases active with
  | nil =>
    have hc0 : st.1 = st.1 ∧ (count : ℝ) = 0 := ⟨rfl, Option.some.inj (hcount.symm.trans
      (by simpa using hSt.1))⟩
    exact absurd (by exact_mod_cast hc0.2 : count = 0) (by omega)
  | cons range rest =>
    rcases range with ⟨lo, d⟩
    have hbounds := hInv.active_block (r := (lo, d)) List.mem_cons_self
    have hrest : rest.length + 1 ≤ n + 1 := by
      have hb := hInv.length_le
      simp only [List.length_append, List.length_cons] at hb
      omega
    have htop : StackHolds st (rest.reverse ++ [(lo, d)]) μ.store := by
      simpa only [List.reverse_cons] using hSt
    have hRS : Fp.Disj (Store.inBlock r.1 r.2 2) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
      (by simpa using hG.disj 6 3 (by simp) : Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono (by fp_sub) le_rfl
    have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
    have hw := rangePop_writes_of_isExactNatLit (τ := tape) hS hL hQ hNat htop
      (by simpa using hrest) (by simpa only [Nat.add_assoc] using hG.room.2.2.2.1)
      (by have := hG.room.2.2.2.2.2.2.1; omega) hlSR hRS
    unfold roundedWorklistRound
    refine hw.frame_seq_le rfl rfl hlSR (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₁ hfr₁ ⟨-, hSt₁, hRange⟩
    have hpop : Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2 ≤
        roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
    have hpar := hG.disj_params.mono hpop le_rfl
    have hfin : finishedFp out done ≤ Store.inBlock out.1 out.2 (2 * (n + 1)) :=
      finishedFp_le (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)
    have hpd {X : Fp} (h1 : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) X)
        (h2 : Fp.Disj (Store.inBlock r.1 r.2 5) X) :
        Fp.Disj (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2) X :=
      Fp.disj_sup_left.mpr ⟨h1.mono (by fp_sub) le_rfl, h2.mono (by fp_sub) le_rfl⟩
    have hP₁ : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ₁ :=
      ⟨hG.of_eqOff hfr₁, hfr₁.keep (Store.readsOnly_get _ _ _) (hpar.mono le_rfl le_sup_left) ht,
        hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hpar.mono le_rfl le_sup_right) hp,
        hfr₁.keep (Store.readsOnly_get _ _ _) (hpd (by simpa using hG.disj 3 7 (by simp))
          (by simpa using hG.disj 6 7 (by simp))) hf,
        hnorm, hInv, hA.of_eqOff hfr₁ (hpd (by simpa using hG.disj 3 0 (by simp))
          (by simpa using hG.disj 6 0 (by simp))),
        hOut.of_eqOff hfr₁ ((hpd (by simpa using hG.disj 3 4 (by simp))
          (by simpa using hG.disj 6 4 (by simp))).mono le_rfl hfin), hSt₁,
        by simp only [List.length_cons] at hj'; omega⟩
    have hLo : μ₁.store.get r.1 r.2 = some (lo : ℝ) := by
      simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
    have hSize : μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ) := by
      simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hLo rfl (by have := hbounds.2.1; omega) ?_
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hSize rfl (by have := hbounds.2.1; omega) ?_
    exact (roundedRange_writes hS hM hu hu1 hL hNat hQ hC D hD L hLeaf hP₁ hfind hcut hc hβ hε0
      he hN₀ hj).in_frame rfl rfl hP₁.1.live

/-- **The capped loop of the rounded worklist**, from the initialized state: the rounds compose
by `NLAlib.Ops.BackwardStep.whileFuel` (C4a each), and both exits find an empty stack and skip;
the final state is reached from $\mathbf{H}$ with error $2(n+1)e$. -/
theorem roundedWorklist_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p st out w r f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c N₀ : ℝ}
    (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀) :
    Writes .total I tape (roundedWorklist D L).body
      (Env.frame [n + 1, k, ps.length] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar H M' (2 * (n + 1) * (c + ε N₀ + β)) ∧
        RoundedFinal fails out f M' μ') μ := by
  have he0 : 0 ≤ c + ε N₀ + β := by linarith
  obtain ⟨hFA, hFS⟩ : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧ Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    ⟨by simpa using hG.disj 7 0 (by simp), by simpa using hG.disj 7 3 (by simp)⟩
  have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 3 0 (by simp)
  have hpar := hG.disj_params
  unfold roundedWorklist
  refine (writes_indexLit hL rfl rfl (by have := hG.room.2.2.2.2.2.2.2.1; dsimp only; omega)).seq_le
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hF₁⟩
  have hlS : μ₁.Live [st] := (hG.of_eqOff hfr₁).live_of_subset (by simp)
  have hw := stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := tape) hL hQ hNat
    (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
    (by simpa only [Nat.add_assoc] using (hG.of_eqOff hfr₁).room.2.2.2.1)
  refine hw.frame_seq_le rfl rfl hlS (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hSt₂⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  have h01 : Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 (1 + 2 * (n + 1)) ≤
      roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
  have hS0 : RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f 0 H μ₂ := by
    refine RoundedWorklistState.of_core hG ht hp hfr₁₂ h01 (Or.inr ⟨?_, by simp, [(0, n + 1)],
      [], H, fun _ => 0, hHess.deflationInv_init _,
      hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩),
      fun _ hq => by simp at hq, by simpa using hSt₂, by simp⟩)
    have h0 : Mch.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
    have := hfr₂.keep (Store.readsOnly_get _ _ _) hFS.symm hF₁
    simpa only [h0] using this
  have hR := isBackwardErrorRel_isPerturbedUnitarySimilar (𝕜 := ℂ) (n := Fin (n + 1))
  have hexit : ∀ i, ∀ M μ', RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f
      i M μ' → μ'.store.get st.1 st.2 = some 0 →
      Writes .total I tape (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 3, off := IExp.var 6 }]
        (Stmt.frame [] [{ buf := 3, off := IExp.var 6 }, { buf := 7, off := IExp.var 10 }]
          (roundedAbort (O := O) (Q := Q)).body) Stmt.skip)
        ((Env.frame [n + 1, k, ps.length] [a, t, p, st, out, w, r, f]).pushIdx i) ⊥
        (fun μ'' => ∃ M', IsPerturbedUnitarySimilar M M' 0 ∧ RoundedFinal fails out f M' μ'')
        μ' := by
    intro i M μ' hS' h0
    obtain ⟨cnt, hcnt, hfin, -⟩ := hS'.count
    have hc0 : cnt = 0 := by exact_mod_cast Option.some.inj (hcnt.symm.trans h0)
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) h0) ?_
    rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
    exact Writes.skip ⟨M, IsPerturbedUnitarySimilar.refl M, hfin hc0⟩
  refine ((BackwardStep.whileFuel (F := roundedWorklistFp (n + 1) a st out w r f) (G := ⊥)
    (S' := fun M μ => RoundedFinal fails out f M μ) (ε' := 0) hR rfl
    (fun i M μ => RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f i M μ)
    (fun _ b _ μ => ∃ cnt : ℕ, μ.store.get st.1 st.2 = some (cnt : ℝ) ∧
      b = decide (0 < (cnt : ℝ)))
    (fun _ => c + ε N₀ + β) (fun _ _ => he0) ?_ ?_ ?_ ?_) H μ₂ hS0).mono
    (by simp) ?_
  · intro i _ M μ' hS'
    obtain ⟨cnt, hcnt, -, -⟩ := hS'.count
    rw [Interp.testAt_eq rfl rfl, hC.test_isPos hcnt]
    exact Mode.holds_some ⟨cnt, hcnt, rfl⟩
  · intro i hi
    refine BackwardStep.in_frame (fun M μ' ⟨hS', cnt, hcnt, hb⟩ =>
      roundedWorklistRound_backwardStep hS hM hu hu1 hL hNat hQ hC D hD L hLeaf hfind hcut hc
        hβ hε0 le_rfl hN₀ hi M μ' ⟨hS', cnt, hcnt, ?_⟩) rfl rfl
      (fun _ _ hx => hx.1.1.live)
    have : (0 : ℝ) < cnt := by simpa using hb.symm
    exact_mod_cast this
  · intro i _ M μ' ⟨hS', cnt, hcnt, hb⟩
    have hc0 : cnt = 0 := by
      by_contra hne
      have : (0 : ℝ) < cnt := by exact_mod_cast Nat.pos_of_ne_zero hne
      simp [this] at hb
    subst hc0
    exact hexit i M μ' hS' (by simpa using hcnt)
  · intro M μ' hS'
    obtain ⟨cnt, hcnt, -, hlt⟩ := hS'.count
    have hc0 : cnt = 0 := by by_contra hne; have := hlt (Nat.pos_of_ne_zero hne); omega
    subst hc0
    exact hexit _ M μ' hS' (by simpa using hcnt)
  · rintro μ' - ⟨M', hHM, hfin⟩
    refine ⟨M', hHM.mono (le_of_eq ?_), hfin⟩
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero]
    push_cast
    ring

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
  unfold solveRounded
  refine writes_allocs_preserving_post
    (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0), .const 5])
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 5]) rfl ?_ ?_
  · intro s s' pos hBelow h
    rcases h with ⟨hfa, hf⟩ | ⟨hf, roots, E, hOut, hE, hR⟩
    · exact Or.inl ⟨hfa, hBelow.get_of (hl f (by simp)) hf⟩
    · exact Or.inr ⟨hBelow.get_of (hl f (by simp)) hf, roots, E,
        hOut.of_below hBelow (hl out (by simp)), hE, hR⟩
  · intro s hs hlens hBelow
    have hG := roundedGeometry_allocated (np := ps.length) hl hr ha hs hlens hBelow
    have hA' := hA.of_below hBelow (hl a (by simp))
    have ht' := hBelow.get_of (hl t (by simp)) ht
    have hp' := (hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp
    have hw := roundedWorklist_writes hS hM hu hu1 hL hNat hQ hC D hD L hLeaf (tape := tape) hG
      hHess hA' ht' hp' hfind hcut hc hβ hε0 hN₀
    refine (hw.in_frame rfl rfl hG.live).mono (by fp_sub [roundedWorklistFp]) ?_
    rintro μ' - ⟨M', hHM, hfin⟩
    rcases hfin with h1 | ⟨hf, done, A, roots, hInv, hOut⟩
    · exact Or.inl h1
    · obtain ⟨E, hE, hR⟩ := (hInv.of_isPerturbedUnitarySimilar hHM).exists_roots_eq
      exact Or.inr ⟨hf, roots, E, hOut, by simpa using hE, hR⟩

end Theorems

end NLAlib.ShiftedQR
