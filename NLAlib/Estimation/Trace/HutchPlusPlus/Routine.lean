/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Prepare
public import NLAlib.Estimation.Trace.HutchPlusPlus.Finish
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Hutch++ as a routine with declared draws

`NLAlib.HutchPlusPlus.estimateRoutine` is
`[n, k, ell] (data : read) → (out : write 1)` drawing `n * (k + ell)` tape positions, with
operands separated by block: the output cell may be in the buffer of the operator data. Its
specification names the draws relative to the position of the call: the first `n * k` words of
the stream are the sketch and the next `n * ell` the probes.

The tree allocates the sketch buffer, prepares it (`NLAlib.HutchPlusPlus.prepare`: sketch,
zero-safe MGS) and finishes (`NLAlib.HutchPlusPlus.finish`: project the probes and evaluate the
estimator). Those trees and the ones they run are fragments of this routine: each works on the
operands of `estimate` and the buffers it allocates, and is run only inside its tree.

## Main definitions

* `NLAlib.HutchPlusPlus.estimateRoutine`, `NLAlib.HutchPlusPlus.estimateSpec`.

## Main results

* `NLAlib.HutchPlusPlus.estimateRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  [Has CmpTst Tst] [Has StoredOperatorOp Op] [Has SampleOp Op] [Has IndexOp Op]
  {I : Interp Op Tst 𝕜}

/-- Zero supplies the default needed by the scalar matrix codec. -/
local instance instInhabitedRoutine : Inhabited 𝕜 := ⟨0⟩

/-- Hutch++: `[n, k, ell] (data : read) → (out : write 1)`, drawing `n * (k + ell)` tape
positions. Operands are separated by block, so the output cell may be in the buffer of the
operator data. -/
def estimateRoutine (stream : ℕ) (dataLength : ℕ → ℕ → ℕ) : Routine Op Tst :=
  routine% [n, k, ell] (data : ↑(dataLength n n)) → (out : 1)
    draws n * (k + ell)
    by blocks := estimate stream

/-- At the dimensions `[n, k, ell]` the written cell is the Hutch++ value of the stored operator
for the sketch in the first `n * k` words drawn from the stream and the probes in the next
`n * ell`. -/
noncomputable def estimateSpec (stream : ℕ)
    (matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜) : Routine.Spec 𝕜 :=
  spec% [n, k, ell] tape ω (as) → ([v]) ensures
    v = hutchpp (matrix n n as)
      ((EntryCodec.scalar 𝕜).matrix n k (ω.window stream 0 (n * k)))
      ((EntryCodec.scalar 𝕜).matrix n ell (ω.window stream (n * k) (n * ell)))

/-- Hutch++ meets its specification for every exact operation interpretation, at every
dimension, including rank-deficient sketches and zero dimensions: the tree draws the sketch and
probe windows, performs zero-safe MGS, projects the probes and evaluates the estimator, releasing
every allocation. -/
theorem estimateRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I)
    {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I) (hSample : IsSample I)
    (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I) (stream : ℕ) :
    (estimateRoutine (Op := Op) (Tst := Tst) stream dataLength).Meets I
      (estimateSpec stream matrix) := by
  routine_intro [n, k, ell] (data, out) reads (as)
  have hDO : Fp.Disj (Store.inBlock data.1 data.2 (dataLength n n))
      (Store.inBlock out.1 out.2 1) := by
    simpa using hblocks.2.1.symm
  have hd := hlive data (by simp)
  have hol := hlive out (by simp)
  have hrun : Writes .total I τ (estimate stream) (Env.frame [n, k, ell] [data, out])
      (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos + n * (k + ell) ∧
        m'.store.readBlock out.1 out.2 1 = some [hutchpp (matrix n n as)
          ((EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k)))
          ((EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell)))])
      m := by
    unfold estimate
    apply writes_allocs_readBlock_at (lens := [.var 0 * (.var 1 + .var 2)])
      (ns := [n * (k + ell)]) rfl hol
    intro store hlength hlens hBelow
    simp only [List.length_cons, List.length_nil] at hlength
    have hb := hlens 0 (by simp)
    change store.len (m.store.length + 0) = n * (k + ell) at hb
    have hLive : (Mem.mk store m.pos).Live [data, (m.store.length, 0), out] := by
      simp only [Mem.live_cons, Mem.live_nil]
      exact ⟨by omega, by omega, by omega, trivial⟩
    have hPrep := prepare_writes (m := ⟨store, m.pos⟩) (τ := τ)
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
      ((hBelow.readBlock hd data.2 (dataLength n n)).trans has)
    have hAP : Fp.Apart [data, (m.store.length, 0), out]
        [dataLength n n, (k + ell) * n, 1] := by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
        Fp.disj_bot_right, and_true]
      exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), hDO⟩, Fp.disj_inBlock_of_ne (by omega)⟩
    have hRun := finish_writes (m := ν) (τ := τ) hS hB hLit hI as
      ((EntryCodec.scalar 𝕜).matrix n k (τ.window stream m.pos (n * k)))
      ((EntryCodec.scalar 𝕜).matrix n ell (τ.window stream (m.pos + n * k) (n * ell)))
      (hLive.congr hfr.length_eq) hAP hA' hp.2
      (by simpa [hfr.len_eq, Nat.mul_comm] using hb.ge)
      (by simpa only [hfr.len_eq, (hBelow out.1 hol).1] using hroom)
    exact (hRun.in_frame rfl rfl (hLive.congr hfr.length_eq)).mono
      (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left)
      (fun _ _ h => ⟨h.1.trans hp.1, h.2⟩)
  refine hrun.mono (by fp_sub) ?_
  rintro μ' - ⟨hpos, hread⟩
  routine_exit
  change _ = hutchpp (matrix n n as)
    ((EntryCodec.scalar 𝕜).matrix n k ((τ.shift m.pos).window stream 0 (n * k)))
    ((EntryCodec.scalar 𝕜).matrix n ell ((τ.shift m.pos).window stream (n * k) (n * ell)))
  rw [Tape.window_shift, Tape.window_shift]
  rfl

end NLAlib.HutchPlusPlus
