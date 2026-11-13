/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Matrix.FinitePrecision.OpsMatrix
public import NLAlib.Ops.Logic.Step

/-!
# Actual rounded and clamped split-index words

The node accumulates the real projector trace, adds the stored half word, materializes zero
and its size, and clamps the computed word before its bounded natural query. The sparse
footprint preserves the half-radii and sampled shift stored elsewhere in the same temporary
buffer. Exact endpoint decoding makes the existing generic clamp conversion rule total.

## Main results

* `NLAlib.SpectralBisection.writes_nodeSplitIndex`: exact computed clamp word and sparse frame.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The four temporary cells written by the actual trace, addition, literals and clamp. -/
def indexCells (t : ℕ × ℕ) : Fp :=
  Fp.blocks [(t.1, t.2 + 5), (t.1, t.2 + 6), (t.1, t.2 + 2), (t.1, t.2 + 3)] [1, 1, 1, 1]

/-- The executed index preparation returns the exact clamped rounded trace on actual words.
Only its four declared cells may change; in particular the node's half-radii and sampled
shift remain available to the selected child or split branch. -/
theorem writes_nodeSplitIndex {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] [Has CmpTst Tst] {M : Machine K} (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K)
    (normal : Sg → K × K) {I : Interp Op Tst K} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp dec I) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {pp c t : ℕ × ℕ} (Pp : Matrix (Fin k) (Fin k) (K × K)) (half : K)
    (hl : μ.Live [pp, c, t])
    (hPp : μ.store.readBlock pp.1 pp.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix Pp))
    (hhalf : μ.store.get c.1 (c.2 + 2) = some half)
    (hroom : t.2 + 7 ≤ μ.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 7)
      (Fp.blocks [pp, (c.1, c.2 + 2)] [2 * (k * k), 1])) :
    Writes .total I τ (nodeSplitIndex (Op := Op) (Tst := Tst)).body
      (Env.frame [k] [pp, c, t]) (indexCells t)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.get t.1 (t.2 + 6) =
        some (clampWord dec (M.lit 0) (M.lit (k : ℚ))
          (M.add ((M.toFloatMachine dec mm qr unif normal).traceRe Pp) half))) μ := by
  have hpp := hl pp (by simp)
  have hc := hl c (by simp)
  have ht := hl t (by simp)
  refine (writes_frame rfl rfl (by room) (PairMatrix.writes_traceRe_packed
    (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal) hS Pp hPp
    (by room) (hsep.mono (by fp_sub) (by fp_sub)))).seq_le (by fp_sub [indexCells]) ?_
  intro μ₁ hfr₁ ⟨hp₁, htrace⟩
  have hhalf₁ := hfr₁.keep (Store.readsOnly_get c.1 (c.2 + 2) half)
    (hsep.mono (by fp_sub) (by fp_sub)) hhalf
  refine (writes_call_bin (hS .add) rfl rfl trivial htrace hhalf₁ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub [indexCells]) ?_
  intro μ₂ hfr₂ ⟨hp₂, hsum⟩
  refine (writes_indexLit hL rfl rfl (by room)).seq_le (by fp_sub [indexCells]) ?_
  intro μ₃ hfr₃ ⟨hp₃, hzero⟩
  refine (writes_indexLit hL rfl rfl (by room)).seq_le (by fp_sub [indexCells]) ?_
  intro μ₄ hfr₄ ⟨hp₄, hsize⟩
  refine (writes_frame rfl rfl (by room) (writes_clamp hS hC
    (by kept) (by kept) (by kept) (by room))).mono (by fp_sub [indexCells]) ?_
  intro μ₅ _ ⟨hp₅, hword⟩
  exact ⟨hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))), hword⟩

end NLAlib.SpectralBisection
