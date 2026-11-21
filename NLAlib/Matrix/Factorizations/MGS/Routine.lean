/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Factor
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# In-place modified Gram–Schmidt

`NLAlib.MGS.factorRoutine` (defined with its tree in `NLAlib/Matrix/Factorizations/MGS/Alg.lean`)
is `[n, k] (Y : update k * n)`: it replaces a packed $n \times k$ matrix by its Gram–Schmidt
factor in place. Inside it, each column is swept against its predecessors by the routine
`NLAlib.MGS.sweepRoutine` and then normalized; the column loop and the normalization are fragments
of this routine, with statements in operand form.

## Main definitions

* `NLAlib.MGS.factorSpec`.

## Main results

* `NLAlib.MGS.factorRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜]

/-- Zero supplies the raw word padding convention for the matrix layout. -/
local instance instInhabitedRoutine : Inhabited 𝕜 := ⟨0⟩

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] {I : Interp Op Tst 𝕜}

/-- At the dimensions `[n, k]`, the block written is the packed Gram–Schmidt factor of the
matrix that the block read packs. -/
noncomputable def factorSpec (𝕜 : Type) [RCLike 𝕜] : Routine.Spec 𝕜 :=
  spec% [n, k] (as) → (qs) ensures
    qs = (EntryCodec.scalar 𝕜).packFinMatrix
      (gramSchmidtQ ((EntryCodec.scalar 𝕜).matrix n k as))

/-- In-place modified Gram–Schmidt meets its specification for every exact operation
interpretation, at every dimension and rank: it is total on every readable matrix, its scratch
is scoped, and no rank assumption is needed. -/
theorem factorRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hC : IsCmp RCLike.re I) :
    (factorRoutine (Op := Op) (Tst := Tst)).Meets I (factorSpec 𝕜) := by
  routine_intro [n, k] (y) reads (as)
  have hlen' : as.length = k * n * (EntryCodec.scalar 𝕜).width := by
    simpa [EntryCodec.scalar] using Store.length_of_readBlock has
  have hA : m.store.readBlock y.1 y.2 (k * n) = some ((EntryCodec.scalar 𝕜).packFinMatrix
      ((EntryCodec.scalar 𝕜).matrix n k as)) := by
    rw [EntryCodec.packFinMatrix_matrix _ n k as hlen']
    exact has
  refine Writes.mono (F := Store.inBlock y.1 y.2 (k * n))
    (P := fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 (k * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix
        (gramSchmidtQ ((EntryCodec.scalar 𝕜).matrix n k as)))) ?_ (by fp_sub) ?_
  · apply writes_allocs_readBlock (lens := [.const 2]) (ns := [2]) rfl hl
    intro store hlength hlens hBelow
    have ht : store.len m.store.length = 2 := by simpa using hlens 0 (by simp)
    have hNew : m.store.length < store.length :=
      Store.lt_length_of_lt_len (show 0 < store.len m.store.length by rw [ht]; omega)
    have hLive : (Mem.mk store m.pos).Live [y, (m.store.length, 0)] := by
      simp only [Mem.live_cons, Mem.live_nil]
      exact ⟨by omega, hNew, trivial⟩
    refine ((writes_factorWithScratch hS hB hC _ hLive (by kept)
      (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hl)))
      (by simpa using ht.ge) (by simpa only [(hBelow y.1 hl).1] using hroom)).in_frame
        rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
  · rintro μ' - ⟨hpos, hread⟩
    routine_exit
    exact rfl

end NLAlib.MGS
