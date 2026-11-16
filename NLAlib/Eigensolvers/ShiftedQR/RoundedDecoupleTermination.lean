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
* `NLAlib.ShiftedQR.roundedDecouple_terminatingDecoupler`: the decoupler is a
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
      (Store.inBlock qw.1 qw.2 qs.length)) :
    Writes .total I τ (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ : a.1 < m.store.length ∧
      rd.1 < m.store.length ∧ c.1 < m.store.length ∧ thr.1 < m.store.length ∧
      wg.1 < m.store.length ∧ wr.1 < m.store.length ∧ ww.1 < m.store.length ∧
      wp.1 < m.store.length ∧ g.1 < m.store.length ∧ f.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 2] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * k]) rfl
    (fun hBelow ⟨⟨H', hA'⟩, x, hF'⟩ => ⟨⟨H', hA'.of_below hBelow h1⟩,
      x, hBelow.get_of h10 hF'⟩) ?_
  intro store hlen hlens hBelow
  set L := m.store.length
  have hsl : store.len L = 2 * k := by simpa using hlens 0 (by simp)
  have hLs : store.length = L + 1 := by simpa using hlen
  have hS0 : ∀ {z : ℕ × ℕ} {l : ℕ}, z.1 < L →
      Fp.Disj (Store.inBlock L 0 (2 * k)) (Store.inBlock z.1 z.2 l) :=
    fun hz => Fp.disj_inBlock_of_ne (by omega)
  have hfI : Fp.Disj (Store.inBlock f.1 f.2 1) _ := hio.mono le_sup_right le_rfl
  have hAI : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) _ :=
    hio.mono le_sup_left le_rfl
  refine Writes.in_frame (Writes.mono (F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock L 0 (2 * k) ⊔ Store.inBlock f.1 f.2 1) ?_ (by fp_sub) fun _ _ h => h) rfl rfl
    (by simp [Mem.Live, hLs]; omega)
  unfold shIterationWithScratchWith
  have hqw' : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length) := by
    have := hS0 hlq (l := qs.length)
    simp only [Fp.disj_sup_left] at hqw ⊢
    exact ⟨⟨hqw.1, this⟩, hqw.2⟩
  refine (regularizeWith_terminates_at (τ := τ) (s := (L, 0)) hS hL hNat hC hD hkn
    (hS0 h1).symm haf (hS0 h10)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hAI.mono le_rfl (by fp_sub),
      Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hS0 h2, hS0 h3⟩, hS0 h4⟩⟩,
      hfI.mono le_rfl (by fp_sub)⟩)
    (by simp [Mem.Live, hLs]; omega) (hA.of_below hBelow h1) (hBelow.get_of h2 hrd)
    (hBelow.get_of h3 hc) (hBelow.get_of h4 hthr) (by simp [hsl])
    (by rw [(hBelow f.1 h10).1]; exact hrf) hSE (by simp [hLs]; omega)
    ((hBelow.readBlock hlq qw.2 qs.length).trans hq) hqw').frame_seq_le rfl rfl
    (by simp [Mem.Live, hLs]; omega) le_rfl ?_
  rintro m₁ hfr₁ ⟨⟨H₁, hA₁⟩, ⟨xs, hS₁⟩, ⟨x, hF₁⟩⟩
  have hk : ∀ {z : ℕ × ℕ} {v : ℝ}, z.1 < L → Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock z.1 z.2 1) → Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 1) → m.store.get z.1 z.2 = some v →
      m₁.store.get z.1 z.2 = some v := fun hz hf ha hv =>
    hfr₁.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
      ⟨ha, hS0 hz⟩, hf⟩) (hBelow.get_of hz hv)
  refine writes_ite rfl rfl (hC.test_isZero (d := []) (x := f) hF₁) ?_
  split_ifs
  · refine ((shStep_terminates (τ := τ) (s := (L, 0)) hS hL hNat hC hQ hD hkq hkn haf
      (Fp.disj_sup_right.mpr ⟨?_, hio⟩ |>.mono le_rfl (by fp_sub))
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega) hA₁ hS₁
      (hk h5 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwg)
      (hk h6 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwr)
      (hk h7 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hww)
      (hk h8 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hwp)
      (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
        ⟨hAI.mono le_rfl (by fp_sub), hS0 h9⟩, hfI.mono le_rfl (by fp_sub)⟩)
        (hBelow.readBlock_of h9 hg))
      (hk h4 (hfI.mono le_rfl (by fp_sub)) (hAI.mono le_rfl (by fp_sub)) hthr)
      (by rw [hfr₁.len_eq, (hBelow f.1 h10).1]; exact hrf)).in_frame rfl rfl
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega)).mono (by fp_sub) fun _ _ h => h
    exact Fp.disj_sup_left.mpr ⟨(hS0 h1).symm, (hS0 h10).symm⟩
  · exact (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hF₁⟩⟩).mono bot_le fun _ _ h => h

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
      some ((excNet ε).flatMap fun z => [z.re, z.im])) (hrf : f.2 < m.store.len f.1) :
    Writes .total I τ (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [a, rd, c, thr, wg, wr, ww, wp, g, a, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x) m := by
  unfold shIteration
  exact (shIterationWith_terminates_at hS hL hNat hC hQ hD hkq hkn haf hio hl hA hrd hc hthr hwg
    hwr hww hwp hg hrf (hSE.terminatingSmallEigAt k 0 0 []) (qw := rd) (hl rd (by simp))
    (by simp) (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega)).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl ⊢
      tauto)

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
    (hW : HoldsMatrix w H μ.store) :
    Writes .total I τ (roundedDecoupleLoopWith SE).body
      (Env.frame [n + 1, k, ps.length, F, T, q, (excNet ε).length] [w, p, (L, 0), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) μ := by
  have hps0 : 0 < ps.length := by omega
  set Inv : ℕ → Mem ℝ → Prop := fun _ μ' => DecoupleLoopCtx n L w p f ps μ' ∧
    (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) ∧
    ∃ x, μ'.store.get L 3 = some x
  have hfl : ((excNet ε).flatMap fun z => [z.re, z.im]).length = 2 * (excNet ε).length := by
    simp [List.length_flatMap, mul_comm]
  have hsub : ps.length - 12 + qs.length ≤ ps.length := by
    rcases hq12 with rfl | h
    · simp
    · rw [hlen, h]; omega
  have hqs : (ps.drop (ps.length - 12)).take qs.length = qs := by
    rcases hq12 with rfl | h
    · simp
    · have e : ps.length - 12 = 10 + 2 * (excNet ε).length := by rw [hlen, h]; omega
      rw [e, ← List.drop_drop, hnet, List.drop_append_of_le_length (by omega), ← hfl,
        List.drop_length, List.nil_append, List.take_length]
  unfold roundedDecoupleLoopWith
  refine (roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hctx ⟨H, hW⟩).frame_seq_le
    rfl rfl (hctx.2.2.2.1.mono (by simp)) (by fp_sub) ?_
  rintro μ₁ - hinv₁
  refine (writes_whileFuel (N := F) rfl (fun _ => Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))
    ⊔ Store.inBlock f.1 f.2 1 ⊔ Store.inBlock L 0 5) (fun _ _ => le_rfl)
    (Store.inBlock f.1 f.2 1) Inv _ hinv₁ ?_ ?_).mono (by fp_sub) fun _ _ h => h
  · rintro i - μ' - ⟨hc, hW', x, hx⟩
    refine ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero hx), ?_⟩
    dsimp only
    split_ifs
    · obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hc
      obtain ⟨H', hW'⟩ := hW'
      have hget : ∀ j < 10, μ'.store.get p.1 (p.2 + j) = some (ps.getD j 0) :=
        fun j hj => Store.get_of_readBlock hp (by omega) 0
      have hnet' : μ'.store.readBlock p.1 (p.2 + 10) (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) := by
        rw [Store.readBlock_sub hp (by omega), hnet, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
      have hPd : ∀ j < 10, Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock f.1 f.2 1) (Store.inBlock p.1 (p.2 + j) 1) := fun j hj =>
        hPWF.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))
      have hit := shIterationWith_terminates_at (τ := τ) (ε := ε) (a := w) (rd := (p.1, p.2 + 1))
        (c := (p.1, p.2 + 2)) (thr := (p.1, p.2 + 3)) (wg := (p.1, p.2 + 4))
        (wr := (p.1, p.2 + 5)) (ww := (p.1, p.2 + 6)) (wp := (p.1, p.2 + 7))
        (g := (p.1, p.2 + 10)) (f := f) hS hL hNat hC hQ hD hkq hkn hWF
        (by
          refine hPWF.symm.mono le_rfl ?_
          refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_)
            ?_ <;> exact Fp.inBlock_le_inBlock (by dsimp only; omega) (by dsimp only; omega))
        (by have := hl; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto)
        hW' (hget 1 (by omega)) (hget 2 (by omega)) (hget 3 (by omega)) (hget 4 (by omega))
        (hget 5 (by omega)) (hget 6 (by omega)) (hget 7 (by omega)) hnet' (by omega) hSE
        (qw := (p.1, p.2 + (ps.length - 12))) (hl p (by simp))
        (by rw [Store.readBlock_sub hp hsub, hqs])
        (hPWF.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega)))
      refine hit.frame_seq_le rfl rfl (by
        have := hl; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto) (by fp_sub) ?_
      rintro μ₂ hfr₂ ⟨hW₂, -⟩
      have hc₂ := hc.of_eqOff (by fp_sub) hfr₂
      refine ((roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hc₂
        hW₂).in_frame rfl rfl (hc₂.2.2.2.1.mono (by simp))).mono (by fp_sub) fun _ _ h => h
    · exact (roundedDecoupleExit_terminates hL hC hc hW' hx).in_frame rfl rfl
        (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto)
  · rintro μ' - ⟨hc, hW', x, hx⟩
    exact (roundedDecoupleExit_terminates hL hC hc hW' hx).in_frame rfl rfl
      (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at this ⊢; tauto)

/-- **The rounded decoupling loop with a terminating small-eigenvalue routine terminates**, with
the parameter words `NLAlib.ShiftedQR.roundedDecoupleParams` followed by the routine's words `qs`
(none, or $12$) and the routine meeting `NLAlib.ShiftedQR.TerminatingSmallEigAt` with the word
count $12$: `NLAlib.ShiftedQR.roundedDecouple_terminatingDecoupler` for
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
    (hSE : TerminatingSmallEigAt k 12 T qs SE I) (hq12 : qs = [] ∨ qs.length = 12) :
    TerminatingDecouplerRoutine nmax k F T (roundedDecoupleParams tL R tv γ B α ε k q ++ qs)
      (roundedDecoupleWith SE) I := by
  intro n w p f tape μ H hk hn hW hp hl hrw hrf hWF hPWF
  set ps := roundedDecoupleParams tL R tv γ B α ε k q ++ qs with hps
  have hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length := by
    rw [hps, List.length_append, length_roundedDecoupleParams]
  have hnet : ps.drop 10 = ((excNet ε).flatMap fun z => [z.re, z.im]) ++ qs := by
    simp [ps, roundedDecoupleParams]
  have hqk : q ≤ k := hkq ▸ (Nat.lt_two_pow_self).le
  have hNat' : IsExactNatLit id M (n + 1) := hNat.mono (by omega)
  have h1 : w.1 < μ.store.length := hl w (by simp)
  have h2 : p.1 < μ.store.length := hl p (by simp)
  have h3 : f.1 < μ.store.length := hl f (by simp)
  unfold roundedDecoupleWith
  change Writes .total I tape (Stmt.allocs [.const 5] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [5]) rfl
    (fun hBelow ⟨⟨x, hF'⟩, H', hW'⟩ => ⟨⟨x, hBelow.get_of h3 hF'⟩, H', hW'.of_below hBelow h1⟩) ?_
  intro s₁ hlen' hlens hBelow
  set L := μ.store.length
  have hl0 := hlens 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hlen'
  have hctx : DecoupleLoopCtx n L w p f ps ⟨s₁, μ.pos⟩ := by
    refine ⟨h1, h2, h3, ?_, hBelow.readBlock_of h2 hp, by rw [(hBelow w.1 h1).1]; exact hrw,
      by rw [(hBelow f.1 h3).1]; exact hrf, by simpa using hl0.ge, hWF, hPWF⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hlen']
    omega
  have hget : ∀ j < 10, s₁.get p.1 (p.2 + j) = some (ps.getD j 0) :=
    fun j hj => Store.get_of_readBlock hctx.2.2.2.2.1 (by omega) 0
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 8 (by omega)) (by
    simp [ps, roundedDecoupleParams, List.getD_append _ _ _ _ (show 8 < 10 + _ by omega)]) hqk ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by
    simp [ps, roundedDecoupleParams, List.getD_append _ _ _ _ (show 9 < 10 + _ by omega)])
    (show (excNet ε).length ≤ ps.length by omega) ?_
  refine ((roundedDecoupleLoopWith_terminates (τ := tape) (F := F) hS hL hNat' hC hQ hD hkq hk hSE
    hq12 hlen hnet hctx (hW.of_below hBelow h1)).in_frame rfl rfl ?_).mono ?_ fun _ _ h => h
  · exact hctx.2.2.2.1.mono (by simp)
  · exact sup_le le_sup_left (fun b i h => Or.inr (show L ≤ b from h.1 ▸ le_rfl))

/-- **The rounded decoupling loop terminates on every tape and every matrix**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], termination only): on a scalar machine with exact
comparisons, index literals, index conversion and exact natural literals up to $n_{\max} + 1$, a
`SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar sampler,
`NLAlib.ShiftedQR.roundedDecouple` with the parameter words
`NLAlib.ShiftedQR.roundedDecoupleParams` and $k = 2^q$ is a
`NLAlib.ShiftedQR.TerminatingDecoupler` for orders up to $n_{\max} + 1$, with any iteration cap
$F$. No numerical hypothesis is needed: the loop is capped, every operation succeeds on stored
operands, and the two index words $q \le k$ and $\lvert\mathrm{net}\rvert \le n_p$ are exact. -/
theorem roundedDecouple_terminatingDecoupler {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) {law : ℕ → MeasureTheory.Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I) (hD : IsPolarDiskSampler s₀ I)
    {k q F : ℕ} (hkq : k = 2 ^ q) (tL R tv γ B α ε : ℝ) :
    TerminatingDecoupler nmax k F (roundedDecoupleParams tL R tv γ B α ε k q)
      (roundedDecouple (O := O) (Q := Q)) I := by
  intro n w p f tape μ H hk hn hW hp hl hrw hrf hWF hPWF
  have hc := roundedDecoupleWith_terminatingDecouplerRoutine_at hS hL hNat hC hQ hD (F := F) hkq tL
    R tv γ B α ε (T := 0) (hSE.terminatingSmallEigAt k 12 0 []) (Or.inl rfl)
  simp only [List.append_nil] at hc
  unfold roundedDecouple
  exact (hc H hk hn hW hp hl hrw hrf hWF hPWF).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by simpa [Mem.Live] using hl)

end Decouple

end NLAlib.ShiftedQR
