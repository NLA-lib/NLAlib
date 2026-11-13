/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownSlots
public import NLAlib.Eigensolvers.SpectralBisection.DownPrepare
public import NLAlib.Eigensolvers.SpectralBisection.DownFrame
public import NLAlib.Eigensolvers.SpectralBisection.DownPrepareReads
public import NLAlib.Ops.Logic.EntryPacking

/-!
# Actual words of a complete downward level

The level updates its parameters, stores both sample batches, and visits actual size slots.
Shared read footprints retain its mathematical inputs through preparation.

## Main results

* `NLAlib.SpectralBisection.writes_downLevelImpl`: total caller-owned downward level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The complete level performs both sampling batches before its actual active-slot scan.
It returns all rounded step outcomes and the next parameter pair, with an exact write frame. -/
theorem writes_downLevelImpl {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I) {τ : Tape K} {μ : Mem K} {n L fuel d : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (ks : ℕ → ℕ) (A : (lo : ℕ) → Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (R0 eps0 beta R eps : K)
    (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (hintervals : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (Finset.Ico i (i + ks i)) (Finset.Ico j (j + ks j)))
    (hexact : IsExactNatLit dec M (max n 4))
    (hsizes : ∀ lo < n, μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ)))
    (hmat : ∀ lo < n, 0 < ks lo →
      μ.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
        (2 * (ks lo * ks lo)) = some ((EntryCodec.pair K).packFinMatrix (A lo)))
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hlv : μ.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hGeometry : DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c t μ.store) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let U := fun lo => vec (τ.window Stream.unif μ.pos n) lo
    let S := fun i j => (EntryCodec.pair K).entry
      (τ.window Stream.gauss (μ.pos + n) (4 * (n * n))) (j * n + i)
    let steps := fun lo => eighStep N n fuel R0 beta (A lo) R eps (L + d)
      (storedNodeSample n lo (U lo) S)
    Writes .total I τ (downLevelImpl (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
      (downPrepareFp n d lv su sg t ⊔
        (Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp (steps lo)) n ⊔
          Store.inBlock t.1 (t.2 + 4) 1))
      (fun ν => ν.pos = μ.pos + levelSampleSize n ∧
        ν.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
          some [M.mul (M.add (M.div (M.lit 1) (M.lit 2))
            (M.div (M.lit 2) (M.lit (L + d : ℕ)))) R,
            M.mul (M.sub (M.lit 1) (M.div (M.lit 1) (M.lit (L + d : ℕ)))) eps] ∧
        ∀ lo < n, 0 < ks lo → StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) ν) μ := by
  classical
  rcases hGeometry with ⟨hl, ht, hPrepareAP, hv, hu, hg, hPrepareRead, hNext, hAP,
    hscratch, hpending, hgeometry, _⟩
  dsimp only
  have hLive0 := hl
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hLive0
  rcases hLive0 with ⟨hlpar, hllv, hlsu, hlsg, hlma, hlua, hlqa, hlea, hlsz, hlkd, hlkp, hlc, hlt⟩
  have hLP := writes_downPrepare (τ := τ) (L := L) hS hL hSample
    (M.lit 1) (M.lit 2) (M.div (M.lit 1) (M.lit 2)) R eps
    (by room) hPrepareAP
    (by simpa using (Store.readBlock_sub hc (o := 0) (n := 3) (by omega))) hlv hv hu hg (by omega)
  change Writes .total I τ _ _ (downPrepareFp n d lv su sg t) _ μ at hLP
  refine (hLP.in_frame rfl rfl (by room)).seq fun ν hfr hPrep => ?_
  obtain ⟨hsizes', hread'⟩ := downScan_inputs_of_prepare M ks A R0 eps0 beta R eps
    (τ.window Stream.unif μ.pos n) (τ.window Stream.gauss (μ.pos + n) (4 * (n * n)))
    hslot hsizes hmat hpar hlv hc hPrepareRead hfr hPrep.2.2.1 hPrep.2.2.2
  have hLive : ν.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t] := by
    simpa only [Mem.Live, hfr.length_eq] using hl
  have hScan := writes_downNodes M dec mm qr (τ := τ) (L := L) (fuel := fuel) hS hL hC hMM hQR hQ
    ks A R0 beta R eps (fun lo => vec (τ.window Stream.unif μ.pos n) lo)
    (fun i j => (EntryCodec.pair K).entry
      (τ.window Stream.gauss (μ.pos + n) (4 * (n * n))) (j * n + i))
    hslot hintervals hexact hLive (by rw [hfr.len_eq]; exact ht) hsizes' hread'
    hAP hscratch hpending (fun lo hi hp =>
      ⟨⟨(hgeometry lo hi hp).1.1.congr hfr.len_eq, (hgeometry lo hi hp).1.2⟩,
        fun r hr => ⟨((hgeometry lo hi hp).2 r hr).1.congr hfr.len_eq,
          ((hgeometry lo hi hp).2 r hr).2⟩⟩)
  have hSub := activeStepPrefix_le_downLevel M dec mm qr (d := d) (fuel := fuel)
    (ell := L + d) ks A hslot R0 beta R eps
    (fun lo => vec (τ.window Stream.unif μ.pos n) lo)
    (fun i j => (EntryCodec.pair K).entry
      (τ.window Stream.gauss (μ.pos + n) (4 * (n * n))) (j * n + i)) ma ua qa ea sz kd kp
  refine ((hScan.in_frame rfl rfl hLive).keep
    (Store.readsOnly_readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 _)
    (hNext.mono (sup_le_sup_right hSub _) le_rfl) hPrep.2.1).mono le_rfl ?_
  intro ξ _ h
  exact ⟨h.1.1.trans hPrep.1, h.2, h.1.2⟩

end NLAlib.SpectralBisection
