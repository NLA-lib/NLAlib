/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedShTermination

/-!
# Termination of the rounded decoupling loop

The termination-only counterpart of the decoupler's contract: `NLAlib.ShiftedQR.roundedDecouple`
(the loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] with `Regularize` and
$\mathrm{Sh}_{k,B}$) runs to completion on every tape and from every stored matrix. Nothing
numerical is assumed: the matrix need not be upper Hessenberg, the machine need not round
well, the shifts may be arbitrary words.

## Main results

* `NLAlib.ShiftedQR.shIteration_terminates`: one iteration (`Regularize`, then
  $\mathrm{Sh}_{k,B}$).
* `NLAlib.ShiftedQR.roundedDecoupleLoopWith_terminates`: the capped loop.
* `NLAlib.ShiftedQR.roundedDecoupleWith_terminatingDecouplerRoutine_at`: the decoupler is a
  `NLAlib.ShiftedQR.TerminatingDecoupler`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-! ### The decoupling loop on any matrix -/

section Decouple

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] {n : ℕ}

omit [Has EigenvalueKernelOp O] in
/-- One iteration with a terminating small-eigenvalue routine terminates on any matrix, with the
word count `nq` apart from the words `qs` (`NLAlib.ShiftedQR.TerminatingSmallEigAt`) stored at
`qw` apart from the matrix and the flag: `NLAlib.ShiftedQR.shIteration_terminates` for
`NLAlib.ShiftedQR.shIterationWith`. On a scalar machine with exact comparisons,
index literals, index conversion and exact natural literals up to $n + 1$, a `SmallEig` kernel
meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler, for $k = 2^q \le n$, from
any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, `wg`, `wr`, `ww`, `wp`, the
net words of `NLAlib.ShiftedQR.excNet ε` at `g` and room for the flag, the matrix and the flag
apart from each other and from the inputs, `NLAlib.ShiftedQR.shIteration` (`Regularize`, then
`Sh`) writes only the matrix and the flag and leaves both stored, on every tape. -/
theorem shIterationWith_terminates_at {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ}
    {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cv tv cg cr cw cp : ℝ}
    (hl : m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cv)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hwg : m.store.get wg.1 wg.2 = some cg)
    (hwr : m.store.get wr.1 wr.2 = some cr) (hww : m.store.get ww.1 ww.2 = some cw)
    (hwp : m.store.get wp.1 wp.2 = some cp)
    (hg : m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im])) (hrf : f.2 < m.store.len f.1)
    {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q} (hSE : TerminatingSmallEigAt k nq T qs SE I)
    {qw : ℕ × ℕ} (hlq : qw.1 < m.store.length)
    (hq : m.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store)
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) :
    Writes .total I τ (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (k + 1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

/-- One iteration terminates on any matrix: on a scalar machine with exact comparisons,
index literals, index conversion and exact natural literals up to $n + 1$, a `SmallEig` kernel
meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler, for $k = 2^q \le n$, from
any matrix of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, `wg`, `wr`, `ww`, `wp`, the
net words of `NLAlib.ShiftedQR.excNet ε` at `g` and room for the flag, the matrix and the flag
apart from each other and from the inputs, `NLAlib.ShiftedQR.shIteration` (`Regularize`, then
`Sh`) writes only the matrix and the flag and leaves both stored, on every tape. -/
theorem shIteration_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ}
    {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cv tv cg cr cw cp : ℝ}
    (hl : m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cv)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hwg : m.store.get wg.1 wg.2 = some cg)
    (hwr : m.store.get wr.1 wr.2 = some cr) (hww : m.store.get ww.1 ww.2 = some cw)
    (hwp : m.store.get wp.1 wp.2 = some cp)
    (hg : m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im])) (hrf : f.2 < m.store.len f.1)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w LL [] m.store)
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) :
    Writes .total I τ (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length, w, LL.length]
          [a, rd, c, thr, wg, wr, ww, wp, g, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ (Ls : List (Option (List GivensEntry)))
            (P' : List GivensEntry), Ls.length ≤ (k + 1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := sorry

omit [Has EigenvalueKernelOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The scan of the decoupling loop on any matrix keeps the loop's operands and stores the scan
flag. -/
theorem roundedDecoupleScan_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ}
    {μ : Mem ℝ} {k L : ℕ} (hk : k ≤ n) {w q f : ℕ × ℕ} {ps : List ℝ} (hps0 : 0 < ps.length)
    (hctx : DecoupleLoopCtx n L w q f ps μ) (hW : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      HoldsMatrix w H μ.store) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [w, q, (L, 0)])
      (Store.inBlock L 0 5)
      (fun μ' => DecoupleLoopCtx n L w q f ps μ' ∧
        (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) ∧
        ∃ x, μ'.store.get L 3 = some x) μ := by
  obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hctx
  obtain ⟨H, hH⟩ := hW
  have hRW : Fp.Disj (Store.inBlock (L, 0).1 (L, 0).2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) := Fp.disj_inBlock_of_ne (by simp; omega)
  have ht := Store.get_of_readBlock hp hps0 0
  rw [Nat.add_zero] at ht
  refine (bottomScan_terminates (τ := τ) hS hL hNat hC hk hH ht (hl.mono (by simp))
    (by simpa using hrL) hRW (Fp.disj_inBlock_of_ne (by simp; omega))).mono le_rfl ?_
  rintro μ' hfr ⟨-, hscan⟩
  refine ⟨hctx.of_eqOff (by simp) hfr, ⟨H, hH.of_eqOff hfr hRW⟩, ?_⟩
  rcases hscan with ⟨h1, -⟩ | ⟨h0, -⟩
  exacts [⟨_, by simpa using h1⟩, ⟨_, by simpa using h0⟩]

omit [Has ScalarOp O] [Has EigenvalueKernelOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The exit of the decoupling loop on any scan flag stores the flag and keeps the matrix. -/
theorem roundedDecoupleExit_terminates {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} {w p f : ℕ × ℕ}
    {ps : List ℝ} (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hW : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H μ.store) {x : ℝ}
    (hx : μ.store.get L 3 = some x) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ := by
  obtain ⟨H, hW⟩ := hW
  have hrf := hctx.2.2.2.2.2.2.1
  have hWF := hctx.2.2.2.2.2.2.2.2.1
  unfold roundedDecoupleExit
  refine writes_ite (a := [(L, 3)]) rfl rfl (hC.test_isPos hx) ?_
  split_ifs <;>
  · refine (writes_indexLit hL rfl rfl (by omega)).mono le_rfl ?_
    rintro μ' hfr ⟨-, hF⟩
    exact ⟨⟨_, hF⟩, H, hW.of_eqOff hfr hWF.symm⟩

omit [Has EigenvalueKernelOp O] in
/-- The decoupling loop terminates on any matrix: on a scalar machine with exact comparisons,
index literals, index conversion and exact natural literals up to $n + 1$, a `SmallEig` kernel
meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler, for $k = 2^q \le n$, with
parameter words `ps` of length $10 + 2\lvert\mathrm{net}\rvert$ whose words from offset $10$ are
the net `NLAlib.ShiftedQR.excNet ε` (the layout of `NLAlib.ShiftedQR.roundedDecoupleParams`),
from the operands of the loop `NLAlib.ShiftedQR.DecoupleLoopCtx` and any matrix at `w`,
`NLAlib.ShiftedQR.roundedDecoupleLoopWith` with a routine that terminates on orders at most $k$
with the word count $12$ and the words `qs` (none, or the last $12$ parameter words) writes only
the matrix, the flag and its registers and leaves the matrix and the flag stored. -/
theorem roundedDecoupleLoopWith_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {μ : Mem ℝ} {k q F L T : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ} {w p f : ℕ × ℕ}
    {ps qs : List ℝ} {SE : Impl O Q} (hSE : TerminatingSmallEigAt k 12 T qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12)
    (hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length)
    (hnet : ps.drop 10 = ((excNet ε).flatMap fun z => [z.re, z.im]) ++ qs)
    (hctx : DecoupleLoopCtx n L w p f ps μ) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hW : HoldsMatrix w H μ.store)
    {ns ws : ℕ} {lg : ℕ × ℕ} 
    (hlog : HoldsSlottedLog lg ns ws [] [] μ.store) (hj : F * (k + 1 + (excNet ε).length) ≤ ns)
        (hw : k * n ≤ ws)
    (hlgl : μ.Live [lg]) (hlgL : lg.1 < L) :
    Writes .total I τ (roundedDecoupleLoopWith SE).body
      (Env.frame [n + 1, k, ps.length, F, T, q, (excNet ε).length, ws] [w, p, (L, 0), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ ns ∧
          (∀ x ∈ slotEntries ws Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns ws Ls P' μ'.store) μ := sorry

omit [Has EigenvalueKernelOp O] in
/-- **The rounded decoupling loop with a terminating small-eigenvalue routine terminates**, with
the parameter words `NLAlib.ShiftedQR.roundedDecoupleParams` followed by the routine's words `qs`
(none, or $12$) and the routine meeting `NLAlib.ShiftedQR.TerminatingSmallEigAt` with the word
count $12$: `NLAlib.ShiftedQR.roundedDecoupleWith_terminatingDecouplerRoutine_at` for
`NLAlib.ShiftedQR.roundedDecoupleWith`. The rounded decoupling loop terminates on every tape and
every matrix
([BanksGarzaVargasSrivastava2022, Lemma 6.4], termination only): on a scalar machine with exact
comparisons, index literals, index conversion and exact natural literals up to $n_{\max} + 1$, a
`SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
`NLAlib.ShiftedQR.roundedDecouple` with the parameter words
`NLAlib.ShiftedQR.roundedDecoupleParams` and $k = 2^q$ is a
`NLAlib.ShiftedQR.TerminatingDecoupler` for orders up to $n_{\max} + 1$, with any iteration cap
$F$. No numerical hypothesis is needed: the loop is capped, every operation succeeds on stored
operands, and the two index words $q \le k$ and $\lvert\mathrm{net}\rvert \le n_p$ are exact. -/
theorem roundedDecoupleWith_terminatingDecouplerRoutine_at {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    {k q F : ℕ} (hkq : k = 2 ^ q) (tL R tv γ B α ε : ℝ) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : TerminatingSmallEigAt k 12 T qs SE I) (hq12 : qs = [] ∨ qs.length = 12)
    {ps : List ℝ} (hps : ps = roundedDecoupleParams tL R tv γ B α ε k q ++ qs) {ns ws : ℕ}
    (hns : F * (k + 1 + ps.length) ≤ ns) (hws : k * nmax ≤ ws) :
    TerminatingDecouplerRoutine nmax k F T ps ns ws (roundedDecoupleWith SE) I := sorry

end Decouple

end NLAlib.ShiftedQR
