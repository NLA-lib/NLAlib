/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Interval
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Matrix component meaning of a word interval scan

The scalar scan over packed matrix storage tests exactly the actual components of every
matrix entry. This bridge uses the generic finite packing theorem and introduces no matrix
operation or additional execution assumptions.

## Main results

* `NLAlib.Ops.inInterval_packFinMatrix_iff`: interval membership word by word or entry by entry.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Scanning a packed finite matrix is equivalent to testing every component of its entries
against the same decoded bounds, including empty matrices. -/
theorem inInterval_packFinMatrix_iff {K E : Type} [Inhabited K] (C : EntryCodec K E)
    (dec : K → ℝ) (a b : K) {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) E) :
    InInterval dec a b (vec (C.packFinMatrix A)) (cols * rows * C.width) ↔
      ∀ i j z, dec a ≤ dec (C.words (A i j) z) ∧ dec (C.words (A i j) z) ≤ dec b :=
  C.forall_vec_packFinMatrix_iff A (fun w => dec a ≤ dec w ∧ dec w ≤ dec b)

end NLAlib.Ops
