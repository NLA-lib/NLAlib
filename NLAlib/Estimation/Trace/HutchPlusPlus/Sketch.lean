/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Apply
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Tactic

/-!
# Sampling and applying a Hutch++ sketch

The actual tape window is decoded as a column-major matrix. Its temporary storage is
released before later workspaces are allocated. Execution needs no distributional law.

## Main results

* `NLAlib.HutchPlusPlus.writes_sketch` returns the image of the actual sampled sketch.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has StoredOperatorOp Op] [Has SampleOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies the raw word padding convention in this module. -/
local instance instInhabitedSketch : Inhabited 𝕜 := ⟨0⟩

/-- Draw and apply a sketch, retaining its exact tape window and removing its scratch.
The statement includes zero dimensions and does not assume sample independence. -/
theorem writes_sketch {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I) (hSample : IsSample I) (stream : ℕ)
    {n k : ℕ} {data b : ℕ × ℕ} (as : List 𝕜) (hl : m.Live [data, b])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hBA : Fp.Disj (Store.inBlock b.1 b.2 (k * n))
      (Store.inBlock data.1 data.2 (dataLength n n)))
    (hb : b.2 + k * n ≤ m.store.len b.1) :
    Writes .total I τ (sketch stream).body (Env.frame [n, k] [data, b])
      (Store.inBlock b.1 b.2 (k * n))
      (fun m' => m'.pos = m.pos + n * k ∧ m'.store.readBlock b.1 b.2 (k * n) =
        some ((EntryCodec.scalar 𝕜).packFinMatrix (matrix n n as *
          (EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k))))) m := by
  have hdata : data.1 < m.store.length := hl data (by simp)
  have hbuf : b.1 < m.store.length := hl b (by simp)
  refine writes_allocs_preserving_post (lens := [.var 0 * .var 1]) (ns := [n * k]) rfl
    (fun hBelow hp => ⟨hp.1, (hBelow.readBlock hbuf b.2 (k * n)).trans hp.2⟩) ?_
  intro store hlength hlens hBelow
  have hlen : store.length = m.store.length + 1 := by simpa using hlength
  have hs : store.len m.store.length = n * k := by simpa using hlens 0 (by simp)
  have hLive : (Mem.mk store m.pos).Live [(m.store.length, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, trivial⟩
  refine Writes.seq_le ((writes_sampleVector hSample stream (by simpa using hs.ge)).in_frame
    rfl rfl hLive) (by fp_sub) ?_
  intro m₁ hfr ⟨hS, hp⟩
  let S := (EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k))
  have hSPack : m₁.store.readBlock m.store.length 0 (k * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix S) := by
    have he : (EntryCodec.scalar 𝕜).packFinMatrix S = τ.window stream m.pos (n * k) := by
      apply EntryCodec.packFinMatrix_matrix
      simp [Tape.window, Nat.mul_comm]
    simpa only [he, Nat.mul_comm n k, Nat.add_zero] using hS
  have hA₀ : store.readBlock data.1 data.2 (dataLength n n) = some as := by kept
  have hA₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ as)
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hdata))) hA₀
  have hLive₁ : m₁.Live [data, (m.store.length, 0), b] := by
    simp only [Mem.live_cons, Mem.live_nil]
    rw [hfr.length_eq]
    exact ⟨by change data.1 < store.length; omega,
      by change m.store.length < store.length; omega,
      by change b.1 < store.length; omega, trivial⟩
  refine ((writes_applyColumns hI as S hLive₁ hA₁ hSPack
    (Fp.disj_inBlock_of_ne (Nat.ne_of_lt hbuf)) hBA
    (by rw [hfr.len_eq]; simpa only [(hBelow b.1 hbuf).1] using hb)).in_frame
      rfl rfl hLive₁).mono (by fp_sub) ?_
  intro m₂ _ ⟨hp₂, hB⟩
  exact ⟨hp₂.trans hp, hB⟩

end NLAlib.HutchPlusPlus
