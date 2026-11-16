/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Sampling
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Writes

/-!
# Draws of a stream into a buffer

The Gaussian samples of the small-eigenvalue program of [BanksGarzaVargasSrivastava2025] (the
perturbation of the input and the random direction of `RHess`) are $m$ consecutive draws of one
tape stream, stored in a buffer: the window of $m$ entries of the stream at the current position,
which the run then advances by $m$.

## Main definitions

* `NLAlib.SmallEig.gaussDraws`: the program `[m] () → (G)`.

## Main results

* `NLAlib.SmallEig.gaussDraws_writes`: the stored words are the window.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Ops

variable {O Q : Type} [Has SampleOp O]

/-- **$m$ draws of the stream `sG`** into the buffer `G`: one `NLAlib.Ops.SampleOp.draw` per
word. The interface is `[m] () → (G)`. -/
def gaussDraws (sG : ℕ) : Impl O Q := opsImpl% [m] () → (G) {
  for i < m {
    call (Has.inj (SampleOp.draw sG)) [] () → (G[i])
  }
}

/-- On an interpretation whose draws store the tape entry (`NLAlib.Ops.IsSample`), with room for
$m$ words at `g`, `NLAlib.SmallEig.gaussDraws` writes only those words, stores the window of $m$
entries of the stream `sG` at the current position, and advances the position by $m$. -/
theorem gaussDraws_writes {I : Interp O Q ℝ} (hSmp : IsSample I) {sG m : ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} {g : ℕ × ℕ} (hl : μ.Live [g]) (hg : g.2 + m ≤ μ.store.len g.1) :
    Writes .total I τ (gaussDraws (O := O) (Q := Q) sG).body (Env.frame [m] [g])
      (Store.inBlock g.1 g.2 m)
      (fun μ' => μ'.pos = μ.pos + m ∧ μ'.store.readBlock g.1 g.2 m = some (τ.window sG μ.pos m))
      μ := by
  sorry

end NLAlib.SmallEig
