/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Static

/-!
# From a framed block statement to counted runs and block-relation posts

Routines are specified by `NLAlib.Ops.Routine.Meets`, whose conclusion is a `NLAlib.Ops.Writes`
statement: a frame, the tape position and the written blocks read back. Counted statements and
operation contracts are phrased with `NLAlib.Ops.BlockRel.Post`, the exact update equation. This
file passes from the first form to the second.

## Main results

* `NLAlib.Ops.BlockRel.post_of_eqOff`: a frame and the blocks read back give the update equation.
* `NLAlib.Ops.Writes.runs_post`: a framed block statement is a run within the static count and
  workspace of the tree, with the update equation.
* `NLAlib.Ops.Writes.contract_post`: the same statement with the postcondition of the contract in
  operand form.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- A frame off the output blocks, the position advanced by the window and the output blocks
read back, related to the inputs, give the update equation of the relation. -/
theorem BlockRel.post_of_eqOff {B : BlockRel K} {d : List ℕ} {xs : List (List K)}
    {outs : List (ℕ × ℕ)} {w : List K} {m m' : Mem K}
    (hfr : m.store.EqOff (Fp.blocks outs (B.outLens d)) m'.store)
    (hpos : m'.pos = m.pos + B.win d) {ys : List (List K)}
    (hys : m'.readBlocks outs (B.outLens d) = some ys) (hrel : B.rel d xs w ys) :
    B.Post d xs outs w m m' := by
  refine ⟨ys, Mem.map_length_of_readBlocks hys, hrel, ?_⟩
  have h₀ : (⟨m'.store, m.pos⟩ : Mem K) = m.updBlocks outs ys :=
    Mem.eq_updBlocks_of_eqOff (m := m) (m' := ⟨m'.store, m.pos⟩) hfr
      ((Mem.readBlocks_congr (m := m') (m' := ⟨m'.store, m.pos⟩) rfl _ _).trans hys) rfl
  rw [← h₀]
  cases m'
  simp only [Mem.advance, Mem.mk.injEq, true_and]
  exact hpos

/-- A framed block statement is a run within the static count and workspace of the tree, whose
final memory satisfies the update equation of the relation. -/
theorem Writes.runs_post {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env}
    {m : Mem K} (W : Op → List ℕ → ℕ) {B : BlockRel K} {d : List ℕ} {xs : List (List K)}
    {outs : List (ℕ × ℕ)} {w : List K}
    (h : Writes .total I τ s ρ (Fp.blocks outs (B.outLens d))
      (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys,
        m'.readBlocks outs (B.outLens d) = some ys ∧ B.rel d xs w ys) m) :
    ConditionalRuns I W τ s ρ m (stmtCost s ρ.idx) (stmtPeak W s ρ.idx)
      (B.Post d xs outs w m) := by
  obtain ⟨m', hrun, hfr, hpos, ys, hys, hrel⟩ := h
  exact ConditionalRuns.of_run hrun (BlockRel.post_of_eqOff hfr hpos hys hrel) W

/-- A framed block statement on inputs `xs` read with room for the outputs gives the
postcondition of the contract of the relation in operand form. -/
theorem Writes.contract_post {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env}
    {m : Mem K} {B : BlockRel K} {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {xs : List (List K)}
    (hr : m.readBlocks ins (B.inLens d) = some xs) (hz : m.Room outs (B.outLens d))
    (h : Writes .total I τ s ρ (Fp.blocks outs (B.outLens d))
      (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys,
        m'.readBlocks outs (B.outLens d) = some ys ∧
          B.rel d xs (τ.window B.stream m.pos (B.win d)) ys) m) :
    Writes .total I τ s ρ (Fp.blocks outs (B.outLens d))
      (((B.spec adm).on .total d ins outs τ m).post m) m :=
  h.mono le_rfl fun _ hfr ⟨hpos, _, hys, hrel⟩ =>
    ⟨xs, hr, hz, BlockRel.post_of_eqOff hfr hpos hys hrel⟩

end NLAlib.Ops
