/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.EntryRows

/-!
# Scalar copies between interleaved matrix views

A pair-codec matrix region is copied entry by entry using scalar copy. The two views have
independent leading dimensions and arbitrary word offsets. Only the actual destination entry
words are written, so the frame retains padding and other submatrices in the same arena.

## Main results

* `NLAlib.Ops.copyStrided` is a computable scalar implementation.
* `NLAlib.Ops.writes_copyStrided` proves total word-level copying between separate views.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]

/-- Copy interleaved entries between two rectangular views, counting both component copies. -/
def copyStrided : Impl Op Tst := opsImpl% [rows, cols, srcLd, dstLd] (X) → (Y) {
  for j < cols { for i < rows {
    run (unaryMap (Has.inj ScalarOp.copy)).body [2]
      (X[2 * (j * srcLd + i)], Y[2 * (j * dstLd + i)])
  } }
}

/-- Scalar copies fill exactly the actual pair-codec destination entries. The input is
readable, the destination has capacity, and their actual entry regions are disjoint;
source and destination may belong to the same underlying buffer. -/
theorem writes_copyStrided {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {m : Mem K} {rows cols srcLd dstLd : ℕ} {x y : ℕ × ℕ}
    (A : ℕ → ℕ → K × K) (hl : m.Live [x, y])
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, rows, cols, srcLd⟩ A)
    (hyL : rows ≤ dstLd)
    (hy : ∀ j < cols, ∀ i < rows, y.2 + 2 * (j * dstLd + i) + 2 ≤ m.store.len y.1)
    (hxy : Fp.Disj
      ((EntryCodec.pair K).regionFp x.1 x.2 cols (fun i j => j * srcLd + i) (fun _ => rows))
      ((EntryCodec.pair K).regionFp y.1 y.2 cols (fun i j => j * dstLd + i) (fun _ => rows))) :
    Writes .total I τ (copyStrided (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols, srcLd, dstLd] [x, y])
      ((EntryCodec.pair K).regionFp y.1 y.2 cols (fun i j => j * dstLd + i) (fun _ => rows))
      (fun m' => m'.store.HoldsEntries (EntryCodec.pair K)
        ⟨y.1, y.2, rows, cols, dstLd⟩ A ∧ m'.pos = m.pos) m := by
  let C := EntryCodec.pair K
  suffices hfill : Writes .total I τ (copyStrided (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols, srcLd, dstLd] [x, y])
      (C.regionFp y.1 y.2 cols (fun i j => j * dstLd + i) (fun _ => rows))
      (fun m' => m'.store.HoldsEntryRegion C y.1 y.2 cols
        (fun i j => j * dstLd + i) (fun _ => rows) A ∧ m'.pos = m.pos) m by
    exact hfill.mono le_rfl fun _ _ hp => ⟨fun i hi j hj z => hp.1 j hj i hi z, hp.2⟩
  unfold copyStrided
  refine writes_fillEntryRegion C y.1 y.2 cols (fun i j => j * dstLd + i)
    (fun _ => rows) ?_ rfl (fun _ => rfl) A (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hd := congrArg (· / dstLd) he
    have hm := congrArg (· % dstLd) he
    simp only [Idx.div_add (hp.2.trans_le hyL), Idx.div_add (hq.2.trans_le hyL)] at hd
    simp only [Idx.mod_add (hp.2.trans_le hyL), Idx.mod_add (hq.2.trans_le hyL)] at hm
    exact Prod.ext hm hd
  · intro j hj i hi m' hfr hp
    have hfr' := hfr.mono (C.regionUpto_le_regionFp y.1 y.2 cols
      (fun i j => j * dstLd + i) (fun _ => rows) hj hi.le)
    have hinput : m'.store.HoldsEntries C ⟨x.1, x.2, rows, cols, srcLd⟩ A := by
      intro r hr c hc z
      change m'.store.get x.1 (x.2 + C.width * (c * srcLd + r) + z) = _
      rw [hfr'.get_eq ?_]
      · exact hX r hr c hc z
      · intro hw
        apply hxy _ _ ?_ hw
        refine ⟨r, c, Or.inl ⟨hc, hr⟩, rfl, ?_, ?_⟩ <;>
          have hz : (z : ℕ) < 2 := z.isLt <;> dsimp only [C, EntryCodec.pair] <;> omega
    have hr := hinput.readBlock_entry hi hj
    have hsource : C.entryBlock x.1 x.2 (j * srcLd + i) ≤
        C.regionFp x.1 x.2 cols (fun i j => j * srcLd + i) (fun _ => rows) :=
      fun _ _ hw => ⟨i, j, Or.inl ⟨hj, hi⟩, hw⟩
    have htarget : C.entryBlock y.1 y.2 (j * dstLd + i) ≤
        C.regionFp y.1 y.2 cols (fun i j => j * dstLd + i) (fun _ => rows) :=
      fun _ _ hw => ⟨i, j, Or.inl ⟨hj, hi⟩, hw⟩
    have hsep : Fp.Disj (Store.inBlock x.1 (x.2 + 2 * (j * srcLd + i)) 2)
        (Store.inBlock y.1 (y.2 + 2 * (j * dstLd + i)) 2) :=
      hxy.mono hsource htarget
    have hroom : y.2 + 2 * (j * dstLd + i) + 2 ≤ m'.store.len y.1 := by
      rw [hfr'.len_eq]
      exact hy j hj i hi
    have hw := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ) (f := id) (m := m')
      (x := (x.1, x.2 + 2 * (j * srcLd + i)))
      (y := (y.1, y.2 + 2 * (j * dstLd + i))) (n := 2) (hS .copy)
      (Or.inl hsep) hr hroom
    simp only [List.map_id] at hw
    refine (hw.in_frame (by rfl) (by rfl)
      (by simpa [Mem.Live] using hl.congr hfr.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hpos, hread⟩
    refine ⟨fun z => ?_, hpos.trans hp⟩
    have hg := Store.get_of_readBlock hread z.isLt default
    fin_cases z <;> simpa [vec, C, EntryCodec.pair] using hg

end NLAlib.Ops
