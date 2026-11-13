/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodeData
public import NLAlib.Eigensolvers.SpectralBisection.SlotNodes

/-!
# Reading a node from shared level inputs

The shared parameter, constant and sample blocks supply each node's actual operands. A stored
level supplies its packed matrix; no inspection of the node's implementation is involved.

## Main results

* `NLAlib.SpectralBisection.nodeInputs_of_reads`: assemble the existing actual input tuple.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The actual shared input blocks and one packed matrix determine the complete node tuple. -/
theorem nodeInputs_of_reads {K : Type} {M : Machine K} {m : Mem K} {n d lo k : ℕ}
    {par lv su sg ma c : ℕ × ℕ} {R0 eps0 beta R eps U : K}
    {S : ℕ → ℕ → K × K} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hpar : m.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hlv : m.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hu : m.store.get su.1 (su.2 + lo) = some U)
    (hg : m.store.readBlock sg.1 sg.2 (2 * ((2 * n) * n)) =
      some ((EntryCodec.pair K).packMatrix n (2 * n) S))
    (ha : m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
      (2 * (k * k)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hc : m.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf]) :
    m.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A) := by
  have hp0 := Store.get_of_readBlock hpar (j := 0) (by simp) R0
  have hp2 := Store.get_of_readBlock hpar (j := 2) (by simp) R0
  have hv0 := Store.get_of_readBlock hlv (j := 0) (by simp) R
  have hv1 := Store.get_of_readBlock hlv (j := 1) (by simp) R
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at hp0 hp2 hv0 hv1
  have hp0' : m.store.readBlock par.1 par.2 1 = some [R0] := by
    simp [Store.readBlock_succ, hp0]
  have hp2' : m.store.readBlock par.1 (par.2 + 2) 1 = some [beta] := by
    simp [Store.readBlock_succ, hp2]
  have hv0' : m.store.readBlock lv.1 (lv.2 + 2 * d) 1 = some [R] := by
    simp [Store.readBlock_succ, hv0]
  have hv1' : m.store.readBlock lv.1 (lv.2 + 2 * d + 1) 1 = some [eps] := by
    simp [Store.readBlock_succ, hv1]
  have hu' : m.store.readBlock su.1 (su.2 + lo) 1 = some [U] := by
    simp [Store.readBlock_succ, hu]
  simp only [nodeInputs, nodeInputLengths, nodeInputWords, Mem.readBlocks,
    hp0', hp2', hv0', hv1', hu', hg, ha, hc, Option.bind_some, Option.map_some]

end NLAlib.SpectralBisection
