/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.ScalarProducts
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.ViewBlock

/-!
# A routine for streamed products of strided vectors

The existing scalar product fragment is exposed through a view interface. Its caller supplies
one unreported temporary cell, which a matrix multiplication reuses across all entries.
The word judgment includes literal zero and every multiplication and addition, including
empty inner dimensions.

## Main results

* `NLAlib.Ops.ScalarProducts.sumRoutine_meets`: the actual streamed scalar word result.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarProducts

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Sum products of two strided input views, with one caller-supplied temporary cell.
The inputs may share their source buffer; both written cells are separate from them. -/
def sumRoutine : Routine Op Tst :=
  routine% [n, sx, sy] (x : n every sx, y : n every sy) → (z : 1, unreported t : 1) {
    run (sum (Op := Op) (Tst := Tst)) [n, sx, sy] (x, y, t, z)
  }

variable [Inhabited K]

/-- The output is the actual literal-zero, multiply-add recurrence on the supplied words. -/
def sumSpec (M : Machine K) : Routine.Spec K :=
  spec% [n, _sx, _sy] (xs, ys) → ([z]) ensures z = sumWord M (vec xs) (vec ys) n

/-- The view routine meets its machine-word specification, by the shared scalar fragment
judgment. It consumes no tape and writes only the output and its declared temporary. -/
theorem sumRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (sumRoutine (Op := Op) (Tst := Tst)).Meets I (sumSpec M) := by
  routine_intro [n, sx, sy] (x, y, z, t) reads (xs, ys)
  obtain ⟨hlx, hly, hlz, hlt⟩ := hl
  obtain ⟨hzroom, htroom⟩ := hroom
  have hxs' : ∀ j < n, m.store.readBlock x.1 (x.2 + sx * j) 1 = some [vec xs j] := by
    intro j hj
    apply Store.readBlock_one_of_get
    simpa only [View.offset_runs_one] using
      Store.getD_of_readView hxs (by simpa using hj) default
  have hys' : ∀ j < n, m.store.readBlock y.1 (y.2 + sy * j) 1 = some [vec ys j] := by
    intro j hj
    apply Store.readBlock_one_of_get
    simpa only [View.offset_runs_one] using
      Store.getD_of_readView hys (by simpa using hj) default
  have hl' : m.Live [x, y, t, z] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using
      And.intro hlx (And.intro hly (And.intro hlt hlz))
  refine ((sum_writes_word hI (vec xs) (vec ys) hl' hxs' hys' ?_ ?_ ?_
    htroom hzroom).in_frame rfl rfl hl').mono (by fp_sub) ?_
  · intro j hj b q hw hx
    rcases hw with ht | hz
    · exact hxt (hx.1.symm.trans ht.1)
    · exact hxz (hx.1.symm.trans hz.1)
  · intro j hj b q hw hy
    rcases hw with ht | hz
    · exact hyt (hy.1.symm.trans ht.1)
    · exact hyz (hy.1.symm.trans hz.1)
  · intro b q ht hz
    exact hzt (hz.1.symm.trans ht.1)
  · intro m' _ ⟨hp, hz⟩
    exact ⟨hp, [[sumWord M (vec xs) (vec ys) n]],
      (Mem.readViews_blocks m' [z] [1]).trans (Mem.readBlocks_of_cons hz rfl), rfl⟩

end NLAlib.Ops.ScalarProducts
