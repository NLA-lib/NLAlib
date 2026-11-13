/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Sampling
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop

/-!
# Vector sampling by explicit scalar draws

A batch is a loop of ordinary sample calls. Its theorem identifies the actual stored tape
window and final shared position; no distribution or independence is assumed for execution.
Probability theorems can therefore use the actual consumed coordinates when composing batches
from different streams.

## Main results

* `NLAlib.Ops.sampleVector` implements a batch using scalar sample operations.
* `NLAlib.Ops.writes_sampleVector` writes precisely the current window and advances by its size.
* `NLAlib.Ops.stmtCost_sampleVector` counts every scalar draw.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has SampleOp Op]

/-- Draw `n` stored words from a named stream into an output vector. The stream is fixed in
the program, while the batch length is an evaluated dimension. -/
def sampleVector (stream : ℕ) : Impl Op Tst := opsImpl% [n] () → (Y) {
  for i < n { call (Has.inj (SampleOp.draw stream)) [] () → (Y[i]) }
}

/-- A batch executes exactly one primitive draw per stored word. -/
theorem stmtCost_sampleVector (stream n y : ℕ) :
    stmtCost (sampleVector (Op := Op) (Tst := Tst) stream).body [n, y] =
      n • Count.one (Has.inj (SampleOp.draw stream)) [] := by
  simp [sampleVector, stmtCost, useCost]

/-- A sample batch writes the actual contiguous window at the current shared tape position.
Its output need not be initialized. All input buffers and cells outside the vector are framed.
This is total correctness under the scalar sample contracts, without a tape-law assumption. -/
theorem writes_sampleVector {I : Interp Op Tst K} (hI : IsSample I) {τ : Tape K}
    (stream : ℕ) {n : ℕ} {y : ℕ × ℕ} {m : Mem K}
    (hroom : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (sampleVector stream).body (Env.frame [n] [y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.readBlock y.1 y.2 n = some (τ.window stream m.pos n) ∧
        m'.pos = m.pos + n) m := by
  refine (writes_fill rfl (fun i => τ (m.pos + i) stream) (fun i => m.pos + i)
    (by simp) fun i hi m' hfr _ hpos => ?_).mono le_rfl ?_
  · have hz : y.2 + i < m'.store.len y.1 := by
      rw [hfr.len_eq]
      omega
    refine (writes_call_fn1 (hI stream) (xs := []) (y := [τ m'.pos stream])
      rfl rfl rfl rfl rfl trivial ?_ rfl (by simp [BlockFn.draw, Tape.window_one])
      rfl (by change y.2 + i + 1 ≤ m'.store.len y.1; omega)).mono le_rfl ?_
    · simpa using Store.lt_length_of_lt_len hz
    · intro m'' _ ⟨hp, hr⟩
      have hg := Store.get_of_readBlock hr (show 0 < 1 by omega) (τ m'.pos stream)
      simp only [List.getD_cons_zero, Nat.add_zero] at hg
      exact ⟨by simpa [hpos] using hg, by simpa [hpos, Nat.add_assoc] using hp⟩
  · intro m' _ ⟨hv, hp⟩
    exact ⟨Store.holdsVec_iff_readBlock.mp hv, hp⟩

end NLAlib.Ops
