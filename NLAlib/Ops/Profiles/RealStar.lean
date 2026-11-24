/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeStar
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.RoutineSyntax

/-!
# Real scalar conjugation by copying

The scalar conjugation group is useful for a common real-or-complex source program.
Over real words its operation lowers to one ordinary scalar copy, with no conjugation
primitive in the implementing tree and no additional workspace.

## Main results

* `NLAlib.Ops.RealStar.conjRoutine_meets`, `NLAlib.Ops.RealStar.conjInPlaceRoutine_meets`: the
  copy as a routine out of place and in place.
* `NLAlib.Ops.RealStar.satisfies_impl` realizes the real conjugation contract by copying.
-/

@[expose] public section

namespace NLAlib.Ops.RealStar

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One scalar copy implements conjugation on real words. -/
def impl : Stmt Op Tst := ops% [] (x) → (y) {
  call (Has.inj ScalarOp.copy) [] (x) → (y)
}

/-- Conjugation of a real word out of place: `(x : read 1) → (y : write 1)`, separated by
block. -/
def conjRoutine : Routine Op Tst :=
  routine% [] (x : 1) → (y : 1) by blocks := impl

/-- A fixed table eliminates the scalar conjugation group over real words. -/
def table : Table StarOp Op Tst := fun _ => .inl conjRoutine.impl

/-- Conjugation of a real word in place: `(x : update 1)`, the same tree with both buffer
variables on `x`. -/
def conjInPlaceRoutine : Routine Op Tst :=
  routine% [] (x : 1) → (x) by blocks := impl

/-- The run of the copy on a cell `x` and a cell `y`, which may be `x`, as the blocks of the
exact real conjugation. -/
theorem conj_blocks {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) {x y : ℕ × ℕ}
    {τ : Tape ℝ} {μ : Mem ℝ} {vals : List (List ℝ)} (hl : μ.Live [x, y])
    (hread : μ.readBlocks [x] [1] = some vals) (hy : y.2 + 1 ≤ μ.store.len y.1) :
    Writes .total I τ (impl (Op := Op) (Tst := Tst)) (Env.frame [] [x, y])
      (Fp.blocks [y] [1])
      (fun μ' => μ'.pos = μ.pos + 0 ∧ ∃ ys, μ'.readBlocks [y] [1] = some ys ∧
        (RCLikeStar.functions (𝕜 := ℝ) .conj).rel.rel [] vals [] ys) μ := by
  obtain ⟨x', xs, he, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain rfl : x = x' := by simpa using he
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hx)
  refine (writes_call_fn1 (hS .copy) (xs := [[v]]) rfl rfl rfl rfl rfl trivial hl
    (by simp [Machine.fn, Mem.readBlocks, hx]) rfl rfl hy).mono le_sup_left fun μ' _ h => ?_
  exact ⟨h.1, [[v]], Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩,
    by simp [RCLikeStar.functions, BlockFn.rel]⟩

/-- Real conjugation out of place meets the specification read off the exact conjugation. -/
theorem conjRoutine_meets {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    (conjRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeStar.functions (𝕜 := ℝ) .conj).rel fun _ => True) := by
  routine_intro [] (x, y)
  exact conj_blocks hS hlive hr hroom

/-- Real conjugation in place meets the specification read off the exact conjugation. -/
theorem conjInPlaceRoutine_meets {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    (conjInPlaceRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeStar.functions (𝕜 := ℝ) .conj).rel fun _ => True) := by
  routine_intro [] (x)
  exact conj_blocks hS (by simpa only [Mem.live_cons, Mem.live_nil] using ⟨hl, hl, trivial⟩) hr
    hroom

/-- Two different cells are disjoint blocks of length one. -/
theorem disj_cell_of_ne {x y : ℕ × ℕ} (h : x ≠ y) :
    Fp.Disj (Store.inBlock y.1 y.2 1) (Store.inBlock x.1 x.2 1) := fun b i hy hx =>
  h (Prod.ext (hx.1.symm.trans hy.1) (by have := hx.2; have := hy.2; omega))

/-- Real conjugation has a total implementation by exact scalar copying, on any two cells: by
cases, from the routine out of place for two different cells and the routine in place for one
cell. -/
theorem satisfies_impl {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    (conjRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeStar.functions .conj).rel.spec AnyOperands) := by
  refine Impl.satisfies_of_writes fun d ins outs tape mem vals hnd _ hl hread hdom hroom => ?_
  obtain rfl : d = [] := List.length_eq_zero_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hroom
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact (conjInPlaceRoutine_meets hS).writes_ofRel (args := [x]) rfl rfl
      (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [conjInPlaceRoutine, Access.isIsolated])
        ⟨fun _ _ _ h => False.elim h, trivial⟩ (fun _ _ _ h => False.elim h)))
      hread trivial hdom hroom rfl
  · exact (conjRoutine_meets hS).writes_ofRel (args := [x, y]) rfl rfl hl
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [conjRoutine, Access.isIsolated]) ⟨fun _ _ _ h => False.elim h, trivial⟩
        (by
          change Fp.Disj (Fp.blocks [y] [1]) (Fp.blocks [x] [1])
          simpa using disj_cell_of_ne hxy)))
      hread trivial hdom hroom rfl

/-- The induced interpretation satisfies exact real conjugation without any lower star
operation or an execution premise. -/
theorem isExact_link {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    RCLikeStar.IsExact (I.link table) :=
  Interp.link_satisfies rfl (satisfies_impl hS)

/-- Real conjugation by copying has no additional stored workspace. -/
theorem impl_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (impl (Op := Op) (Tst := Tst)) idx = 0 :=
  stmtPeak_zero_of_allocationFree (by rfl) idx

/-- Real conjugation emits exactly one ordinary scalar copy. -/
theorem stmtCost_impl (x y : ℕ) :
    stmtCost (impl (Op := Op) (Tst := Tst)) [x, y] =
      Count.one (Has.inj ScalarOp.copy) [] := by
  simp [impl, stmtCost, useCost]

end NLAlib.Ops.RealStar
