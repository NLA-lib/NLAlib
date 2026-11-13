/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeStar
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.AllocationFree

/-!
# Real scalar conjugation by copying

The scalar conjugation group is useful for a common real-or-complex source program.
Over real words its operation lowers to one ordinary scalar copy, with no conjugation
primitive in the implementing tree and no additional workspace.

## Main results

* `NLAlib.Ops.RealStar.meets_impl` realizes the real conjugation contract by copying.
-/

@[expose] public section

namespace NLAlib.Ops.RealStar

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One scalar copy implements conjugation on real words. -/
def impl : Impl Op Tst := opsImpl% [] (x) → (y) {
  call (Has.inj ScalarOp.copy) [] (x) → (y)
}

/-- A fixed table eliminates the scalar conjugation group over real words. -/
def table : Table StarOp Op Tst := fun _ => .inl impl

/-- Real conjugation has a total implementation by exact scalar copying, including alias. -/
theorem meets_impl {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    (impl (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeStar.functions .conj).rel.spec AnyOperands) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd _ hl hread _ hroom => ?_
  obtain rfl : d = [] := List.length_eq_zero_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hroom
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hx)
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_call_fn1 (hS .copy) (xs := [[v]])
    rfl rfl rfl rfl rfl trivial hl
    (by simp [Machine.fn, Mem.readBlocks, hx]) rfl rfl hy).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [[v]], ?_, ?_⟩
  · exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩
  · simp [RCLikeStar.functions, BlockFn.rel]

/-- The induced interpretation satisfies exact real conjugation without any lower star
operation or an execution premise. -/
theorem isExact_link {I : Interp Op Tst ℝ} (hS : IsScalar RCLikeBlas.machine I) :
    RCLikeStar.IsExact (I.link table) :=
  Interp.link_meets rfl (meets_impl hS)

/-- Real conjugation by copying has no additional stored workspace. -/
theorem impl_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (impl (Op := Op) (Tst := Tst)).body idx = 0 :=
  stmtPeak_zero_of_allocationFree (by rfl) idx

/-- Real conjugation emits exactly one ordinary scalar copy. -/
theorem stmtCost_impl (x y : ℕ) :
    stmtCost (impl (Op := Op) (Tst := Tst)).body [x, y] =
      Count.one (Has.inj ScalarOp.copy) [] := by
  simp [impl, stmtCost, useCost]

end NLAlib.Ops.RealStar
