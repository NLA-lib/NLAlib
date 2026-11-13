/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Prepare
public import NLAlib.Estimation.Trace.HutchPlusPlus.Finish

/-!
# Total allocated Hutch++ estimator

The full program draws the actual sketch and probe windows, performs zero-safe MGS,
projects the probes and evaluates the existing mathematical estimator. Every temporary
allocation is released by the shared scoped-allocation rules.

## Main results

* `NLAlib.HutchPlusPlus.writes_estimate`: total output for every input matrix and tape.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  [Has CmpTst Tst] [Has StoredOperatorOp Op] [Has SampleOp Op] [Has IndexOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies the default needed by the scalar matrix codec. -/
local instance instInhabitedSolve : Inhabited 𝕜 := ⟨0⟩

/-- The actual complete estimator returns the mathematical Hutch++ value on its actual
adjacent sample windows. Storage separation, capacity and local primitive contracts suffice,
including rank-deficient sketches and zero dimensions; no observed successful run is assumed. -/
theorem writes_estimate (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I) (hSample : IsSample I)
    (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I) (stream : ℕ)
    {n k ell : ℕ} {data out : ℕ × ℕ} (as : List 𝕜) (hl : m.Live [data, out])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hDO : Fp.Disj (Store.inBlock data.1 data.2 (dataLength n n))
      (Store.inBlock out.1 out.2 1)) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ (estimate stream).body (Env.frame [n, k, ell] [data, out])
      (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos + n * (k + ell) ∧
        m'.store.readBlock out.1 out.2 1 = some [hutchpp (matrix n n as)
          ((EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k)))
          ((EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell)))])
      m := by
  have hd := hl data (by simp)
  have hol := hl out (by simp)
  unfold estimate
  dsimp only
  apply writes_allocs_readBlock_at (lens := [.var 0 * (.var 1 + .var 2)])
    (ns := [n * (k + ell)]) rfl hol
  intro store hlength hlens hBelow
  simp only [List.length_cons, List.length_nil] at hlength
  have hb := hlens 0 (by simp)
  change store.len (m.store.length + 0) = n * (k + ell) at hb
  have hLive : (Mem.mk store m.pos).Live [data, (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, trivial⟩
  have hPrep := writes_prepare (m := ⟨store, m.pos⟩) (τ := τ)
    (n := n) (k := k) (ell := ell) (data := data) (b := (m.store.length, 0))
    hS hB hC hI hSample stream as
    (by simp only [Mem.live_cons, Mem.live_nil]; exact ⟨by omega, by omega, trivial⟩)
    (by kept) (Fp.disj_inBlock_of_ne (by omega)) (by simpa [Nat.mul_comm] using hb.ge)
  refine Writes.seq_le (hPrep.in_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil]; exact ⟨by omega, by omega, trivial⟩))
    (Fp.inBlock_le_sup_above le_rfl) ?_
  intro ν hfr hp
  have hA' := hfr.keep (Store.readsOnly_readBlock _ _ _ as)
    (Fp.disj_inBlock_of_ne (by omega))
    ((hBelow.readBlock hd data.2 (dataLength n n)).trans hA)
  have hAP : Fp.Apart [data, (m.store.length, 0), out]
      [dataLength n n, (k + ell) * n, 1] := by
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
      Fp.disj_bot_right, and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), hDO⟩, Fp.disj_inBlock_of_ne (by omega)⟩
  have hRun := writes_finish (m := ν) (τ := τ) hS hB hLit hI as
    ((EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k)))
    ((EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell)))
    (hLive.congr hfr.length_eq) hAP hA' hp.2
    (by simpa [hfr.len_eq, Nat.mul_comm] using hb.ge)
    (by simpa only [hfr.len_eq, (hBelow out.1 hol).1] using ho)
  exact (hRun.in_frame rfl rfl (hLive.congr hfr.length_eq)).mono
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left)
    (fun _ _ h => ⟨h.1.trans hp.1, h.2⟩)

end NLAlib.HutchPlusPlus
