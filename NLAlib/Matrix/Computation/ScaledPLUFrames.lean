/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUFrames
public import NLAlib.Matrix.Computation.ScaledPartialPivot
public import NLAlib.Matrix.Computation.RowScales

/-!
# Packed workspace frames for fixed-scale LU

The residual and the permuted original row scales share one scoped buffer. Its whole contents
are private workspace; the only external writes are the lower factor, upper factor and log.

## Main definitions

* `NLAlib.Computation.ScaledPLU.Frame`: packed workspace and three-output footprint.

## Main results

* `NLAlib.Computation.ScaledPLU.Frame.writeBlocks`: writes inside the footprint retain it.
-/

@[expose] public section

namespace NLAlib.Computation.ScaledPLU

variable {P K : Type} [DecidableEq P]

/-- The complete packed workspace may change, together with the two square factor windows
and the pivot-log window. Every other cell, at every precision tag, retains its value. -/
structure Frame (base : Store P K) (N S L U H lo uo ho : ℕ) (s : Store P K) : Prop where
  /-- Allocations, capacities and precision tags are retained. -/
  shape : s.shape = base.shape
  /-- All cells outside the scoped workspace and output windows are retained. -/
  outside : ∀ q b i, b ≠ S → (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
    (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
    (b ≠ H ∨ i < ho ∨ ho + N ≤ i) → s.read q b i = base.read q b i

variable {base s s' : Store P K} {N S L U H lo uo ho : ℕ} {tag : P}

/-- The original store satisfies the packed-workspace footprint. -/
theorem Frame.refl (base : Store P K) (N S L U H lo uo ho : ℕ) :
    Frame base N S L U H lo uo ho base := ⟨rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- Any successful block writes whose cells lie inside the declared workspace or outputs
preserve the complete external footprint. The block list is concrete at each consumer. -/
theorem Frame.writeBlocks (h : Frame base N S L U H lo uo ho s)
    {blocks : List (ℕ × ℕ × ℕ)} {words : List (Array K)}
    (hw : s.writeBlocks tag blocks words = some s')
    (hblocks : ∀ block ∈ blocks, ∀ b i, b ≠ S →
      (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
      (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
      (b ≠ H ∨ i < ho ∨ ho + N ≤ i) →
      b ≠ block.1 ∨ i < block.2.1 ∨ block.2.1 + block.2.2 ≤ i) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlocks_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlocks_eq_some_of_forall hw
    (fun block hb => hblocks block hb b i hbS hbL hbU hbH)]
  exact h.outside q b i hbS hbL hbU hbH

/-- A write confined to the private packed workspace preserves all external cells. -/
theorem Frame.write_workspace (h : Frame base N S L U H lo uo ho s)
    {off : ℕ} {W : Array K} (hw : s.writeBlock tag S off W = some s') :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hbS)]
  exact h.outside q b i hbS hbL hbU hbH

/-- A full lower-factor write preserves the packed-workspace footprint. -/
theorem Frame.write_lower (h : Frame base N S L U H lo uo ho s)
    {W : Array K} (hw : s.writeBlock tag L lo W = some s') (hlen : W.size = N * N) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (hlen ▸ hbL)]
  exact h.outside q b i hbS hbL hbU hbH

/-- Materializing both factor blocks preserves the packed-workspace footprint. -/
theorem Frame.write_factors (h : Frame base N S L U H lo uo ho s) {LW UW : Array K}
    (hw : s.writeBlocks tag [(L, lo, N * N), (U, uo, N * N)] [LW, UW] = some s') :
    Frame base N S L U H lo uo ho s' := by
  apply h.writeBlocks hw
  intro block hb b i hbS hbL hbU _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact hbL
  · exact hbU

end NLAlib.Computation.ScaledPLU
