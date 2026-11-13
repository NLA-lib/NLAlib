/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.ProjectPacked
public import NLAlib.Estimation.Trace.HutchPlusPlus.Evaluate
public import NLAlib.Ops.Logic.Allocation

/-!
# Scoped evaluation of prepared Hutch++ samples

The basis/probe matrix is projected before the operator-output workspace is allocated.
Generic allocation rules preserve the output while removing every scoped scratch buffer.

## Main results

* `NLAlib.HutchPlusPlus.writes_finish`: total evaluation from the packed prepared samples.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  [Has StoredOperatorOp Op] [Has IndexOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜}
  {dataLength : ℕ → ℕ → ℕ}
  {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}

/-- Zero supplies defaults for the ordinary scalar matrix codec. -/
local instance instInhabitedFinish : Inhabited 𝕜 := ⟨0⟩

private theorem writes_evaluation_workspace
    (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) (hB : RCLikeBlas.IsExact I)
    (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I)
    (hI : StoredOperator.IsExact dataLength matrix I)
    {n k ell : ℕ} {data b out : ℕ × ℕ} {t : ℕ} {m : Mem 𝕜} (as : List 𝕜)
    (S : Matrix (Fin n) (Fin k) 𝕜) (G : Matrix (Fin n) (Fin ell) 𝕜)
    (hl : m.Live [data, b, (t, 0), out])
    (hAP : Fp.Apart [data, b, (t, 0), out] [dataLength n n, (k + ell) * n, 2, 1])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hInput : m.store.readBlock b.1 b.2 ((k + ell) * n) = some
      ((EntryCodec.scalar 𝕜).packFinMatrix
        (projectedBasis (gramSchmidtQ (matrix n n as * S)) G)))
    (ht : 2 ≤ m.store.len t) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ
      (.alloc (.var 0 * (.var 1 + .var 2))
        (.frame [.var 0, .var 1, .var 2]
          [⟨0, .var 3⟩, ⟨1, .var 4⟩, ⟨3, .const 0⟩, ⟨4, .const 0⟩, ⟨2, .var 5⟩]
          evaluate.body))
      ⟨[n, k, ell, data.2, b.2, out.2], [data.1, b.1, out.1, t]⟩
      (Store.inBlock t 0 2 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [hutchpp (matrix n n as) S G]) m := by
  have hd := hl data (by simp)
  have hb := hl b (by simp)
  have htl := hl (t, 0) (by simp)
  have hol := hl out (by simp)
  apply writes_allocs_preserving_post (lens := [.var 0 * (.var 1 + .var 2)])
    (ns := [n * (k + ell)]) rfl
    (fun hBelow hp => ⟨hp.1, (hBelow.readBlock hol out.2 1).trans hp.2⟩)
  intro store hlength hlens hBelow
  simp only [List.length_cons, List.length_nil] at hlength
  have hc := hlens 0 (by simp)
  change store.len (m.store.length + 0) = n * (k + ell) at hc
  have hLive : (Mem.mk store m.pos).Live [data, b, (t, 0), (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, by omega, trivial⟩
  have hAP' : Fp.Apart [data, b, (t, 0), (m.store.length, 0), out]
      [dataLength n n, (k + ell) * n, 2, (k + ell) * n, 1] := by
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
      Fp.disj_bot_right, and_true] at hAP ⊢
    rcases hAP with ⟨⟨hdb, hdt, hdo⟩, ⟨hbt, hbo⟩, hto⟩
    (repeat' constructor) <;> first | assumption | disjoint
  have hRun := writes_evaluate (m := ⟨store, m.pos⟩) (τ := τ)
    (data := data) (b := b) (t := (t, 0)) (c := (m.store.length, 0)) (out := out)
    hS hB hLit hI as S G hLive hAP' (by kept) (by kept)
    (by simpa only [(hBelow t htl).1, Nat.zero_add] using ht)
    (by simpa [Nat.mul_comm] using hc.ge)
    (by simpa only [(hBelow out.1 hol).1] using ho)
  exact (hRun.in_frame rfl rfl hLive).mono
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left) (fun _ _ h => h)

/-- Finish the estimator from its actual prepared basis and probe matrix. Both workspaces
are allocated at their source positions and released; no rank assumption is needed. -/
theorem writes_finish
    (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) (hB : RCLikeBlas.IsExact I)
    (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I)
    (hI : StoredOperator.IsExact dataLength matrix I)
    {n k ell : ℕ} {data b out : ℕ × ℕ} {m : Mem 𝕜} (as : List 𝕜)
    (S : Matrix (Fin n) (Fin k) 𝕜) (G : Matrix (Fin n) (Fin ell) 𝕜)
    (hl : m.Live [data, b, out])
    (hAP : Fp.Apart [data, b, out] [dataLength n n, (k + ell) * n, 1])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hInput : m.store.readBlock b.1 b.2 ((k + ell) * n) = some
      ((EntryCodec.scalar 𝕜).packFinMatrix
        (basisProbes (gramSchmidtQ (matrix n n as * S)) G)))
    (hb : b.2 + (k + ell) * n ≤ m.store.len b.1)
    (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ finish.body (Env.frame [n, k, ell] [data, b, out])
      (Store.inBlock b.1 b.2 ((k + ell) * n) ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [hutchpp (matrix n n as) S G]) m := by
  have hd := hl data (by simp)
  have hbl := hl b (by simp)
  have hol := hl out (by simp)
  have hTail : Store.inBlock b.1 (b.2 + n * k) (ell * n) ≤
      Store.inBlock b.1 b.2 ((k + ell) * n) :=
    Fp.inBlock_le_inBlock (by omega) (by nlinarith)
  have hdb : Fp.Disj (Store.inBlock data.1 data.2 (dataLength n n))
      (Store.inBlock b.1 b.2 ((k + ell) * n)) := by
    simpa using hAP.disj_getD (i := 0) (j := 1) (by simp) (by simp) (by omega)
  unfold finish
  dsimp only
  apply writes_allocs_preserving_post (lens := [.const 2]) (ns := [2]) rfl
    (fun hBelow hp => ⟨hp.1, (hBelow.readBlock hol out.2 1).trans hp.2⟩)
  intro store hlength hlens hBelow
  simp only [List.length_cons, List.length_nil] at hlength
  have ht := hlens 0 (by simp)
  change store.len (m.store.length + 0) = 2 at ht
  have hLive : (Mem.mk store m.pos).Live [data, b, (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, trivial⟩
  have hAP' : Fp.Apart [data, b, (m.store.length, 0), out]
      [dataLength n n, (k + ell) * n, 2, 1] := by
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
      Fp.disj_bot_right, and_true] at hAP ⊢
    rcases hAP with ⟨⟨hdb, hdo⟩, hbo⟩
    (repeat' constructor) <;> first | assumption | disjoint
  have hProtect : Fp.Disj
      (Store.inBlock b.1 (b.2 + n * k) (ell * n) ⊔ Store.inBlock m.store.length 0 2)
      (Store.inBlock data.1 data.2 (dataLength n n)) :=
    Fp.disj_sup_left.mpr ⟨hdb.symm.mono hTail le_rfl, Fp.disj_inBlock_of_ne (by omega)⟩
  have hProj := writes_projectProbes_packed (m := ⟨store, m.pos⟩) (τ := τ)
    (n := n) (k := k) (ell := ell) (b := b) (t := (m.store.length, 0)) hS hB
    (gramSchmidtQ (matrix n n as * S)) G
    (by simp only [Mem.live_cons, Mem.live_nil]; exact ⟨by omega, by omega, trivial⟩)
    (by kept) (Fp.disj_inBlock_of_ne (by omega)) (by simpa using ht.ge)
    (by simpa only [(hBelow b.1 hbl).1] using hb)
  refine Writes.seq_le (hProj.in_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil]; exact ⟨by omega, by omega, trivial⟩))
    (sup_le (hTail.trans (le_sup_left.trans le_sup_left))
      (Fp.inBlock_le_sup_above le_rfl)) ?_
  intro ν hfr hp
  have hA' := hfr.keep (Store.readsOnly_readBlock _ _ _ as) hProtect
    ((hBelow.readBlock hd data.2 (dataLength n n)).trans hA)
  have hRun := writes_evaluation_workspace (m := ν) (τ := τ)
    (n := n) (k := k) (ell := ell) (data := data) (b := b) (out := out)
    (t := m.store.length) hS hB hLit hI as S G
    (hLive.congr hfr.length_eq) hAP' hA' hp.2
    (by simpa only [hfr.len_eq, Nat.add_zero] using ht.ge)
    (by simpa only [hfr.len_eq, (hBelow out.1 hol).1] using ho)
  exact hRun.mono
    (sup_le (Fp.inBlock_le_sup_above le_rfl) (le_sup_right.trans le_sup_left))
    (fun _ _ h => ⟨h.1.trans hp.1, h.2⟩)

end NLAlib.HutchPlusPlus
