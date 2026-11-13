/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout

/-!
# Repacking decoded entry blocks

The entry codec is invertible on every component vector. A correctly sized word block can
therefore be decoded as a natural-indexed matrix and repacked without changing its words.

## Main results

* `NLAlib.Ops.EntryCodec.packMatrix_entry`: natural-indexed decoding and packing cancel.
-/

@[expose] public section

namespace NLAlib.Ops.EntryCodec

/-- Repacking the natural-indexed decoding of a correctly sized block preserves every word. -/
theorem packMatrix_entry {K E : Type} [Inhabited K] (C : EntryCodec K E)
    (rows cols : ℕ) (xs : List K) (hlen : xs.length = cols * rows * C.width) :
    C.packMatrix rows cols (fun i j => C.entry xs (j * rows + i)) = xs := by
  rw [← C.packFinMatrix_eq_packMatrix]
  exact C.packFinMatrix_matrix rows cols xs hlen

end NLAlib.Ops.EntryCodec
