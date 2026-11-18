/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog

/-!
# The words of a Givens log replayed on a range

The replay of a closed Givens log (`NLAlib.givensReplayRows`, `NLAlib.givensReplayColumns`) on a
range of columns or rows stores, on every tape, the left fold of the machine's replay step
(`NLAlib.replayRowStep`, `NLAlib.replayColumnStep`) over the valid entries. These are the word
forms behind `NLAlib.givensReplayRows_specNorm_sub_le` and
`NLAlib.givensReplayColumns_specNorm_sub_le`, for callers that replay on a part of a matrix.

## Main results

* `NLAlib.givensReplayRows_writes_word`, `NLAlib.givensReplayColumns_writes_word`: the words of a
  replay on a range.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IndexOp O] in
/-- **The words of a row replay**: on a scalar machine with exact `toNat` and comparisons and
every tape, the replay of a closed log whose entries have their two rows `lo + r, lo + r + 1`
in range, on the columns $j_0, \dots, j_0 + n_c - 1$ of the matrix at `x`, writes only the matrix
and stores the left fold of `NLAlib.replayRowStep` over the valid entries. -/
theorem givensReplayRows_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {N lo j0 nc ns w : ℕ}
    (hj : j0 + nc ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayRows (O := O) (Q := Q)).body
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix x ((slotEntries w L).foldl (replayRowStep Mch lo j0 nc) X) μ'.store) μ :=
  givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateRowsOn_writes_word hS hk hj hY hc hs hca
        hsa hta htc hts ht) hrow hlog hlen hX hl hd

omit [Has IndexOp O] in
/-- **The words of a column replay**: as `NLAlib.givensReplayRows_writes_word`, on the rows
$i_0, \dots, i_0 + n_r - 1$, the replay stores the left fold of `NLAlib.replayColumnStep`. -/
theorem givensReplayColumns_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {N lo i0 nr ns w : ℕ}
    (hi : i0 + nr ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q)).body
      (Env.frame [N, lo, i0, nr, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix x ((slotEntries w L).foldl (replayColumnStep Mch lo i0 nr) X) μ'.store) μ :=
  givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv i0 nr Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateColumnsOn_writes_word hS hk hi hY hc hs hca
        hsa hta htc hts ht) hrow hlog hlen hX hl hd

end NLAlib
