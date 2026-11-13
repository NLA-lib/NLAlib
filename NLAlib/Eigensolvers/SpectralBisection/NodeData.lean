/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.State

/-!
# Actual input and scratch regions of a bisection node

The node reads the root radius, sign tolerance, current radius and tolerance, one uniform
word, the level's Gaussian words, its matrix and the shared constant words. Scratch capacities
are declared separately and are not initialized inputs or precomputed mathematical outputs.

## Main definitions

* `NLAlib.SpectralBisection.nodeInputs`: the eight actual readable input regions.
* `NLAlib.SpectralBisection.nodeScratchLengths`: the seven scoped scratch capacities.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The eight actual readable regions used to identify the mathematical node step. -/
def nodeInputs (n d lo : ℕ) (par lv su sg ma c : ℕ × ℕ) : List (ℕ × ℕ) :=
  [par, (par.1, par.2 + 2), (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * d + 1),
    (su.1, su.2 + lo), sg, (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo), c]

/-- Word lengths of the eight actual readable regions. -/
def nodeInputLengths (n k : ℕ) : List ℕ :=
  [1, 1, 1, 1, 1, 2 * ((2 * n) * n), 2 * (k * k), 5]

/-- The input words, with the shared constants produced by the scalar machine itself. -/
def nodeInputWords {K : Type} (M : Machine K) (n : ℕ) {k : ℕ} (R0 beta R eps U : K)
    (S : ℕ → ℕ → K × K) (A : Matrix (Fin k) (Fin k) (K × K)) : List (List K) :=
  [[R0], [beta], [R], [eps], [U], (EntryCodec.pair K).packMatrix n (2 * n) S,
    (EntryCodec.pair K).packFinMatrix A,
    [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf]]

/-- Capacities of the scalar temporaries and the five size-k matrix scratch buffers. -/
def nodeScratchLengths (k : ℕ) : List ℕ :=
  [7, 2, 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k), 2 * (k * k)]

/-- Project the actual scalar and packed matrix reads from the node's input tuple. -/
theorem nodeInputs_reads {K : Type} {M : Machine K} {m : Mem K} {n d lo k : ℕ}
    {par lv su sg ma c : ℕ × ℕ} {R0 beta R eps U : K}
    {S : ℕ → ℕ → K × K} {A : Matrix (Fin k) (Fin k) (K × K)}
    (h : m.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A)) :
    m.store.get par.1 par.2 = some R0 ∧ m.store.get par.1 (par.2 + 2) = some beta ∧
      m.store.get lv.1 (lv.2 + 2 * d) = some R ∧
      m.store.get lv.1 (lv.2 + 2 * d + 1) = some eps ∧
      m.store.get su.1 (su.2 + lo) = some U ∧
      m.store.readBlock sg.1 sg.2 (2 * ((2 * n) * n)) =
        some ((EntryCodec.pair K).packMatrix n (2 * n) S) ∧
      m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) =
        some ((EntryCodec.pair K).packFinMatrix A) ∧
      m.store.readBlock c.1 c.2 5 = some
        [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kept

end NLAlib.SpectralBisection
