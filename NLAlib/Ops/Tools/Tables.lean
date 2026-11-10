/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Examples.NoisyLinked
import NLAlib.Ops.Profiles.Blas

/-!
# Tools: computable tables of the profiles

Outside the trusted base. A `Profile` is a noncomputable structure (its cost field is a
`Count`), so `#eval` cannot project its table. The tables themselves are computable; this file
names them and proves each equal to the table of its profile, so that the program linked here is
the program of the corollaries.

* `NLAlib.Ops.Tools.seqTable`: `Blas.seq.table` (`NLAlib.Ops.Tools.seqTable_eq`).
* `NLAlib.Ops.Tools.pairwiseTable k`: `(Blas.pairwise k).table`
  (`NLAlib.Ops.Tools.pairwiseTable_eq`).
* `NLAlib.Ops.Tools.gaussTable`: `Rand.gaussLoop.table`.
* `NLAlib.Ops.Tools.noisyTable σ`, `NLAlib.Ops.Tools.noisyDrawsTable σ`: the tables of
  `Examples.noisy σ` and `Examples.noisyDraws σ`.
-/

namespace NLAlib.Ops.Tools

open NLAlib.Ops NLAlib.Ops.Examples

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- The table of sequential summation. -/
def seqTable : Table Op Op Tst := Blas.level1Table.comp Blas.sumSeqTable

theorem seqTable_eq : (Blas.seq (Op := Op) (Tst := Tst)).table = seqTable := rfl

/-- The table of pairwise summation of depth `k`. -/
def pairwiseTable (k : ℕ) : Table Op Op Tst := Blas.level1Table.comp (Blas.sumPairwiseTable.iter k)

theorem pairwiseTable_eq (k : ℕ) :
    (Blas.pairwise (Op := Op) (Tst := Tst) k).table = pairwiseTable k := by
  simp [Blas.pairwise, Profile.over, pairwiseTable, Blas.sumPairwise, Blas.level1]

omit [Has ScalarOp Op] [Has Blas1Op Op]

/-- The table of the vector draw by scalar draws. -/
def gaussTable : Table ROp ROp Tst := Rand.gaussTable

theorem gaussTable_eq : (Rand.gaussLoop (Tst := Tst)).table = gaussTable := rfl

/-- The table of the noisy product by a drawn probe. -/
def noisyTable (σ : ℚ) : Table NOp ROp Tst := fun _ => .inl (nmvImpl σ)

theorem noisyTable_eq (σ : ℚ) : (noisy (Tst := Tst) σ).table = noisyTable σ := rfl

/-- The table of the noisy product with the probe drawn entry by entry. -/
def noisyDrawsTable (σ : ℚ) : Table NOp ROp Tst := (noisyTable σ).comp gaussTable

theorem noisyDrawsTable_eq (σ : ℚ) : (noisyDraws (Tst := Tst) σ).table = noisyDrawsTable σ := rfl

end NLAlib.Ops.Tools
