/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedShTermination
public import NLAlib.Matrix.FinitePrecision.GivensLogClose

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
    (hlgl : m.Live [lg]) (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, nq, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k + 1 + (excNet ε).length ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ : a.1 < m.store.length ∧ rd.1 < m.store.length ∧
      c.1 < m.store.length ∧ thr.1 < m.store.length ∧ wg.1 < m.store.length ∧
      wr.1 < m.store.length ∧ ww.1 < m.store.length ∧ wp.1 < m.store.length ∧
      g.1 < m.store.length ∧ f.1 < m.store.length := by simpa [Mem.Live] using hl
  have hlg : lg.1 < m.store.length := hlgl lg (by simp)
  change Writes .total I τ (Stmt.allocs [.const 2 * .var 2] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * k]) rfl
    (fun hBelow ⟨⟨H', hA'⟩, x, hF', Ls, hLs, hpl, hlog'⟩ => ⟨⟨H', hA'.of_below hBelow h1⟩,
      x, hBelow.get_of h10 hF', Ls, hLs, hpl, hlog'.of_below hBelow hlg⟩) ?_
  intro store hlen hlens hBelow
  set L := m.store.length
  have hsl : store.len L = 2 * k := by simpa using hlens 0 (by simp)
  have hLs : store.length = L + 1 := by simpa using hlen
  have hS0 : ∀ {z : ℕ × ℕ} {l : ℕ}, z.1 < L →
      Fp.Disj (Store.inBlock L 0 (2 * k)) (Store.inBlock z.1 z.2 l) :=
    fun hz => Fp.disj_inBlock_of_ne (by omega)
  refine Writes.in_frame (Writes.mono (F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock L 0 (2 * k) ⊔ Store.inBlock f.1 f.2 1 ⊔
      Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
    ?_ (by fp_sub) fun _ _ h => h) rfl rfl
    (by simp [Mem.Live, hLs]; omega)
  unfold shIterationWithScratchWith
  have hqw' : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock (L, 0).1 (L, 0).2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length) := by
    simp only [Fp.disj_sup_left] at hqw ⊢; exact ⟨⟨hqw.1, hS0 hlq⟩, hqw.2⟩
  have hlgb : ∀ b ∈ [a, rd, c, thr, qw, (L, 0), f], b.1 ≠ lg.1 := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp only; omega) | exact hlgv _ (by simp)
  refine (regularizeWith_terminates_at (τ := τ) (s := (L, 0)) hS hL hNat hC hD hkn
    (hS0 h1).symm haf (hS0 h10)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hio.mono le_sup_left (by fp_sub),
      Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hS0 h2, hS0 h3⟩, hS0 h4⟩⟩,
      hio.mono le_sup_right (by fp_sub)⟩)
    (by simp [Mem.Live, hLs]; omega) (hA.of_below hBelow h1) (hBelow.get_of h2 hrd)
    (hBelow.get_of h3 hc) (hBelow.get_of h4 hthr) (by simp [hsl])
    (by rw [(hBelow f.1 h10).1]; exact hrf) hSE (by simp [hLs]; omega)
    ((hBelow.readBlock hlq qw.2 qs.length).trans hq) hqw' (hlog.of_below hBelow hlg)
    (by omega) hw (by simp [Mem.Live, hLs]; omega) hlgb).frame_seq_le rfl rfl
    (by simp [Mem.Live, hLs]; omega) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨⟨H₁, hA₁⟩, ⟨xs, hS₁⟩, ⟨x, hF₁, Ls₁, hLs₁, hpl₁, hlog₁⟩⟩
  have hk : ∀ {z : ℕ × ℕ} {v : ℝ}, z.1 < L → z.1 ≠ lg.1 → Fp.Disj (Store.inBlock a.1 a.2
      (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) (Store.inBlock z.1 z.2 1) →
      m.store.get z.1 z.2 = some v → m₁.store.get z.1 z.2 = some v := fun hz hzl hd hv =>
    hfr₁.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
      ⟨Fp.disj_sup_left.mpr ⟨hd.mono le_sup_left le_rfl, hS0 hz⟩, hd.mono le_sup_right le_rfl⟩,
        Fp.disj_inBlock_of_ne hzl.symm⟩) (hBelow.get_of hz hv)
  refine writes_ite rfl rfl (hC.test_isZero (d := []) (x := f) hF₁) ?_
  split_ifs
  · have hsh := shStep_terminates (τ := τ) (s := (L, 0)) (LL := LL ++ Ls₁) hS hL hNat hC hQ hD hkq
      hkn haf
      (Fp.disj_sup_right.mpr ⟨Fp.disj_sup_left.mpr ⟨(hS0 h1).symm, (hS0 h10).symm⟩, hio⟩ |>.mono
        le_rfl (by fp_sub))
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega) hA₁ hS₁
      (hk h5 (hlgv _ (by simp)) (hio.mono le_rfl (by fp_sub)) hwg)
      (hk h6 (hlgv _ (by simp)) (hio.mono le_rfl (by fp_sub)) hwr)
      (hk h7 (hlgv _ (by simp)) (hio.mono le_rfl (by fp_sub)) hww)
      (hk h8 (hlgv _ (by simp)) (hio.mono le_rfl (by fp_sub)) hwp)
      (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
        ⟨Fp.disj_sup_left.mpr ⟨hio.mono le_sup_left (by fp_sub), hS0 h9⟩,
          hio.mono le_sup_right (by fp_sub)⟩, Fp.disj_inBlock_of_ne (hlgv _ (by simp)).symm⟩)
        (hBelow.readBlock_of h9 hg))
      (hk h4 (hlgv _ (by simp)) (hio.mono le_rfl (by fp_sub)) hthr)
      (by rw [hfr₁.len_eq, (hBelow f.1 h10).1]; exact hrf) hlog₁
      (by simp only [List.length_append, hLs₁]; omega) hw
      (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega) fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | (simp only; omega) | exact hlgv _ (by simp)
    rw [List.length_append, hLs₁] at hsh
    refine (hsh.in_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hLs]; omega)).mono
      (by fp_sub) ?_
    rintro m₂ - ⟨hA₂, x₂, hF₂, Ls₂, hLs₂, hpl₂, hlog₂⟩
    rw [List.append_assoc] at hlog₂
    exact ⟨hA₂, x₂, hF₂, Ls₁ ++ Ls₂, by simp only [List.length_append]; omega, fun e he => by
      rw [slotEntries_append, List.mem_append] at he; exact he.elim (hpl₁ e) (hpl₂ e), hlog₂⟩
  · refine (Writes.skip ⟨⟨_, hA₁⟩, ⟨_, hF₁, Ls₁ ++ List.replicate (1 + (excNet ε).length) none,
      by simp; omega, by simpa using hpl₁, by
        rw [← List.append_assoc]; exact hlog₁.rejects (by simp; omega)⟩⟩).mono bot_le fun _ _ h => h

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
    (hlgl : m.Live [lg]) (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, f], b.1 ≠ lg.1) :
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
          HoldsSlottedLog lg ns w (LL ++ Ls) P' m'.store) m := by
  unfold shIteration
  exact ((shIterationWith_terminates_at hS hL hNat hC hQ hD hkq hkn haf hio hl hA hrd hc hthr hwg
    hwr hww hwp hg hrf (hSE.terminatingSmallEigAt k 0 0 []) (qw := rd) (hl rd (by simp))
    (by simp) (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega) hlog hj hw hlgl
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlgv ⊢
      rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        exact hlgv _ (by simp))).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) (by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl hlgl ⊢
      tauto)).mono le_rfl fun _ _ ⟨hA', x, hx, Ls, hLs, hpl, hlog'⟩ =>
      ⟨hA', x, hx, Ls, [], hLs.le, by simpa using hpl, hlog'⟩

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

/-- The words of the routine sit at the tail of the parameter words of the loop. -/
private theorem routine_words_of_layout {ε : ℝ} {ps qs : List ℝ}
    (hq12 : qs = [] ∨ qs.length = 12)
    (hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length)
    (hnet : ps.drop 10 = ((excNet ε).flatMap fun z => [z.re, z.im]) ++ qs) :
    ps.length - 12 + qs.length ≤ ps.length ∧ (ps.drop (ps.length - 12)).take qs.length = qs := by
  have hfl : ((excNet ε).flatMap fun z => [z.re, z.im]).length = 2 * (excNet ε).length := by
    simp [List.length_flatMap, mul_comm]
  rcases hq12 with rfl | h
  · simp
  · have e : ps.length - 12 = 10 + 2 * (excNet ε).length := by rw [hlen, h]; omega
    refine ⟨by rw [hlen, h]; omega, ?_⟩
    rw [e, ← List.drop_drop, hnet, List.drop_append_of_le_length (by omega), ← hfl,
      List.drop_length, List.nil_append, List.take_length]

omit [Has ScalarOp O] [Has EigenvalueKernelOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The exit of the decoupling loop on any scan flag keeps a closed log of at most `ns` slots
in a buffer apart from the flag. -/
private theorem roundedDecoupleExit_terminates_log {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {L : ℕ} {w p f lg : ℕ × ℕ}
    {ps : List ℝ} {ns ws : ℕ} {Ls : List (Option (List GivensEntry))}
    (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hW : ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H μ.store)
    (hx : ∃ x, μ.store.get L 3 = some x) (hlog : HoldsSlottedLog lg ns ws Ls [] μ.store)
    (hpl : ∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) (hLs : Ls.length ≤ ns) (hfl : f.1 ≠ lg.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ ns ∧
          (∀ x ∈ slotEntries ws Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns ws Ls P' μ'.store) μ := by
  obtain ⟨x, hx⟩ := hx
  refine (roundedDecoupleExit_terminates hL hC hctx hW hx).mono le_rfl ?_
  rintro μ' hfr ⟨hF, H', hW'⟩
  exact ⟨hF, H', hW', Ls, [], hLs, by simpa using hpl,
    hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hfl) hlog⟩

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
    (hlgl : μ.Live [lg]) (hlgL : lg.1 < L) (hlgv : ∀ b ∈ [w, p, f], b.1 ≠ lg.1) :
    Writes .total I τ (roundedDecoupleLoopWith SE).body
      (Env.frame [n + 1, k, ps.length, F, T, q, (excNet ε).length, ws] [w, p, (L, 0), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ' => (∃ x, μ'.store.get f.1 f.2 = some x) ∧
        ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store ∧
        ∃ (Ls : List (Option (List GivensEntry))) (P' : List GivensEntry), Ls.length ≤ ns ∧
          (∀ x ∈ slotEntries ws Ls ++ P', x.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns ws Ls P' μ'.store) μ := by
  have hps0 : 0 < ps.length := by omega
  have hpl : p.1 ≠ lg.1 := hlgv p (by simp)
  have hlgL' : lg.1 ≠ L := by omega
  set s := k + 1 + (excNet ε).length with hs
  set Inv : ℕ → Mem ℝ → Prop := fun i μ' => DecoupleLoopCtx n L w p f ps μ' ∧
    (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w H' μ'.store) ∧
    (∃ x, μ'.store.get L 3 = some x) ∧ μ'.Live [lg] ∧
    ∃ Ls : List (Option (List GivensEntry)), Ls.length = i * s ∧
      (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns ws Ls [] μ'.store
  obtain ⟨hsub, hqs⟩ := routine_words_of_layout hq12 hlen hnet
  unfold roundedDecoupleLoopWith
  refine (roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hctx ⟨H, hW⟩).frame_seq_le
    rfl rfl (hctx.2.2.2.1.mono (by simp)) (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨hc₁, hW₁, hx₁⟩
  refine (writes_whileFuel (N := F) rfl (fun _ => Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))
    ⊔ Store.inBlock f.1 f.2 1 ⊔ Store.inBlock L 0 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
    (fun _ _ => le_rfl) (Store.inBlock f.1 f.2 1) Inv _
      ⟨hc₁, hW₁, hx₁, hlgl.congr hfr₁.length_eq, [], by simp, by simp [slotEntries],
        hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hlgL'.symm) hlog⟩
      ?_ ?_).mono (by fp_sub) fun _ _ h => h
  · rintro i hi μ' - ⟨hc, hW', ⟨x, hx⟩, hlgl', Ls, hLs, hplLs, hlog'⟩
    refine ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero hx), ?_⟩
    dsimp only
    split_ifs
    · obtain ⟨hw', hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hc
      obtain ⟨H', hW'⟩ := hW'
      have hget : ∀ j < 10, μ'.store.get p.1 (p.2 + j) = some (ps.getD j 0) :=
        fun j hj => Store.get_of_readBlock hp (by omega) 0
      have hfl : ((excNet ε).flatMap fun z => [z.re, z.im]).length = 2 * (excNet ε).length := by
        simp [List.length_flatMap, mul_comm]
      have hnet' : μ'.store.readBlock p.1 (p.2 + 10) (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) := by
        rw [Store.readBlock_sub hp (by omega), hnet, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
      have hit := shIterationWith_terminates_at (τ := τ) (ε := ε) (a := w) (rd := (p.1, p.2 + 1))
        (c := (p.1, p.2 + 2)) (thr := (p.1, p.2 + 3)) (wg := (p.1, p.2 + 4))
        (wr := (p.1, p.2 + 5)) (ww := (p.1, p.2 + 6)) (wp := (p.1, p.2 + 7))
        (g := (p.1, p.2 + 10)) (f := f) (LL := Ls) hS hL hNat hC hQ hD hkq hkn hWF
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
        hlog' (by rw [hLs, ← hs, ← Nat.succ_mul]; exact (Nat.mul_le_mul_right _ hi).trans hj) hw
        hlgl' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
            first | exact hpl | exact hlgv _ (by simp))
      rw [hLs] at hit
      refine hit.frame_seq_le rfl rfl (by
        have := hl; have := hlgl'; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at * ; tauto) (by fp_sub) ?_
      rintro μ₂ hfr₂ ⟨hW₂, -, -, Ls₂, hLs₂, hpl₂, hlog₂⟩
      have hc₂ := hc.of_eqOff_log hpl (by fp_sub) hfr₂
      refine ((roundedDecoupleScan_terminates (τ := τ) hS hL hNat hC hkn hps0 hc₂
        hW₂).in_frame rfl rfl (hc₂.2.2.2.1.mono (by simp))).mono (by fp_sub) ?_
      rintro μ₃ hfr₃ ⟨hc₃, hW₃, hx₃⟩
      refine ⟨hc₃, hW₃, hx₃, (hlgl'.congr hfr₂.length_eq).congr hfr₃.length_eq, Ls ++ Ls₂,
        by simp only [List.length_append, hLs, hLs₂]; ring, ?_,
        hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hlgL'.symm) hlog₂⟩
      intro e he
      rw [slotEntries_append, List.mem_append] at he
      exact he.elim (hplLs e) (hpl₂ e)
    · exact (roundedDecoupleExit_terminates_log (τ := τ) hL hC hc hW' ⟨x, hx⟩ hlog' hplLs
        (by rw [hLs]; exact (Nat.mul_le_mul_right _ hi.le).trans hj) (hlgv f (by simp))).in_frame
        rfl rfl
        (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at this ⊢; tauto)
  · rintro μ' - hinv
    obtain ⟨hc, hW', hx, -, Ls, hLs, hplLs, hlog'⟩ := hinv
    exact (roundedDecoupleExit_terminates_log (τ := τ) hL hC hc hW' hx hlog' hplLs
      (by rw [hLs]; exact hj) (hlgv f (by simp))).in_frame rfl rfl
      (by have := hc.2.2.2.1; simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at this ⊢; tauto)

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
    (hns : F * (k + 1 + (excNet ε).length) ≤ ns) (hws : k * nmax ≤ ws) :
    TerminatingDecouplerRoutine nmax k F T ps ns ws (roundedDecoupleWith SE) I := by
  intro n w p f lg tape μ H hk hn hW hp hl hrw hrf hrlg hv hap hpd
  have hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length := by
    rw [hps, List.length_append, length_roundedDecoupleParams]
  have hnet : ps.drop 10 = ((excNet ε).flatMap fun z => [z.re, z.im]) ++ qs := by
    simp [hps, roundedDecoupleParams]
  have hqk : q ≤ k := hkq ▸ (Nat.lt_two_pow_self).le
  have hNat' : IsExactNatLit id M (n + 1) := hNat.mono (by omega)
  have h0 : M.lit 0 = 0 := by simpa using hNat 0 (Nat.zero_le _)
  have h1 : w.1 < μ.store.length := hl w (by simp)
  have h2 : p.1 < μ.store.length := hl p (by simp)
  have h3 : f.1 < μ.store.length := hl f (by simp)
  have h4 : lg.1 < μ.store.length := hl lg (by simp)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hap
  have hWF := hap.1.1
  have hPWF : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1) :=
    hpd.mono le_rfl le_sup_left
  unfold roundedDecoupleWith
  change Writes .total I tape (Stmt.allocs [.const 5] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [5]) rfl
    (fun hBelow ⟨⟨x, hF'⟩, ⟨H', hW'⟩, L', hL', hpl', hlog'⟩ => ⟨⟨x, hBelow.get_of h3 hF'⟩,
      ⟨H', hW'.of_below hBelow h1⟩, L', hL', hpl', hlog'.of_below hBelow h4⟩) ?_
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
    rw [hps, List.getD_append _ _ _ _ (by rw [length_roundedDecoupleParams]; omega)]
    simp [roundedDecoupleParams]) hqk ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by
    rw [hps, List.getD_append _ _ _ _ (by rw [length_roundedDecoupleParams]; omega)]
    simp [roundedDecoupleParams])
    (show (excNet ε).length ≤ ps.length by omega) ?_
  have hpl : p.1 ≠ lg.1 := hv p (by simp)
  have hwl : w.1 ≠ lg.1 := hv w (by simp)
  -- open the log
  refine (slottedLogOpen_writes_of_lit_zero (τ := tape) (μ := ⟨s₁, μ.pos⟩) (ns := ns) (w := ws)
    (lg := lg) hS h0 (by rw [(hBelow lg.1 h4).1]; exact hrlg)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen']; omega) (le_sup_right.trans le_sup_left) ?_
  rintro μ₁ hfr₁ ⟨-, hlog₁⟩
  have hctx₁ := hctx.of_eqOff_log hpl (le_sup_right) hfr₁
  have hW₁ := (hW.of_below hBelow h1).of_eqOff hfr₁ (Fp.disj_inBlock_of_ne (Ne.symm hwl))
  refine ((roundedDecoupleLoopWith_terminates (τ := tape) (F := F) hS hL hNat' hC hQ hD hkq hk hSE
    hq12 hlen hnet hctx₁ hW₁ hlog₁ hns ((Nat.mul_le_mul_left k hn).trans hws)
    (by simp [Mem.Live, hfr₁.length_eq, hlen']; omega) (by omega) hv).in_frame rfl rfl
    ?_).mono ?_ ?_
  · have := hctx₁.2.2.2.1
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hfr₁.length_eq, hlen'] at this ⊢
    omega
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left)
      (fun b i h => Or.inr (show L ≤ b from h.1 ▸ le_rfl))) (le_sup_right.trans le_sup_left)
  · rintro μ₂ - ⟨hF, H', hW', Ls, P', hLs, hpl', hlog'⟩
    refine ⟨hF, ⟨H', hW'⟩, ?_⟩
    rcases Nat.lt_or_eq_of_le hLs with hlt | heq
    · refine ⟨Ls ++ List.replicate (ns - Ls.length - 1 + 1) none, by simp; omega, ?_,
        hlog'.reject_pending (by omega)⟩
      rw [slotEntries_append_replicate_none]
      exact fun e he => hpl' e (List.mem_append_left _ he)
    · exact ⟨Ls, heq, fun e he => hpl' e (List.mem_append_left _ he),
        hlog'.of_length_eq heq⟩

end Decouple

end NLAlib.ShiftedQR
