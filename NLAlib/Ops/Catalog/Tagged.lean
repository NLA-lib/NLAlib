/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar

/-!
# Catalog: precision tags and casts

**A precision tag is a copy of a group of operations.** `NLAlib.Ops.Tagged π G` is the group `G`
at the tag `π` (a type used as a name: `Single`, `Double`). A signature with two precisions
contains `Tagged Lo ScalarOp` and `Tagged Hi ScalarOp`; a call of `add` at the tag `π` is the
operation `NLAlib.Ops.Tagged.inj π ScalarOp.add`.

* **Counts are per tag**: the count of a run is keyed by the operation, and the operations of
  two tags are different names (`NLAlib.Ops.Tagged.inj_ne`).
* **Contracts are per tag**: `NLAlib.Ops.IsScalarAt π M I` says the scalar operations at the
  tag `π` are the functions of the machine `M`; a mixed-precision algorithm has one machine,
  one standard model and one parameter record per tag.
* **Nothing is rewritten for a tag.** An algorithm, an implementation or a table is written for
  any signature with the groups it uses (`[Has G Op]`). At a tag it is the same definition with
  the instance `NLAlib.Ops.Tagged.has π`, and its certificate is the same theorem
  (`NLAlib.Ops.IsScalarAt.isScalar`). The untagged group is the default precision.
* **Casts** between two tags are the group `NLAlib.Ops.CastOp π ρ`, with the functional
  contract `NLAlib.Ops.IsCast` and the model `NLAlib.Ops.CastModel` (rounding to the target
  precision; a widening cast is exact, `u = 0`).

Memory is counted in cells of one size: a workspace per tag would need the tag on `alloc` and in
the state of the counted run, which is a change of the evaluator and is not made here.

## Main results

* `NLAlib.Ops.Tagged`, `NLAlib.Ops.Tagged.has`, `NLAlib.Ops.Tagged.inj`: tags.
* `NLAlib.Ops.IsScalarAt`, `NLAlib.Ops.IsScalarAt.isScalar`: scalar arithmetic at a tag.
* `NLAlib.Ops.CastOp`, `NLAlib.Ops.IsCast`, `NLAlib.Ops.CastModel`: casts.
-/

@[expose] public section

namespace NLAlib.Ops

/-- **The group `G` at the precision tag `π`.** The tag is a type used as a name. -/
structure Tagged (π : Type) (G : Type) where
  /-- The operation of the group. -/
  op : G
  deriving DecidableEq

variable {K Op Tst G : Type}

/-- The operation `g` of the group `G` at the tag `π`, in a signature that contains the tagged
group. -/
def Tagged.inj (π : Type) [Has (Tagged π G) Op] (g : G) : Op := Has.inj (Tagged.mk g : Tagged π G)

/-- **A signature that contains the group `G` at the tag `π` contains `G`**, through the tag.
With this instance, every definition written for a signature with the group `G` is a definition
at the tag `π`. It is not a global instance: a signature may contain several tags. -/
@[reducible] def Tagged.has (π : Type) [Has (Tagged π G) Op] : Has G Op where
  inj := Tagged.inj π
  proj o := (Has.proj (G := Tagged π G) o).map Tagged.op
  proj_inj g := by simp [Tagged.inj]
  inj_of_proj o g h := by
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Has.inj_of_proj o t ht

/-- **The operations of two tags are different names**, so their counts are kept apart. -/
theorem Tagged.inj_ne {π ρ : Type} [Has (Tagged π G) Op] [Has (Tagged ρ G) Op]
    [Apart (Tagged π G) (Tagged ρ G) Op] (g g' : G) :
    (Tagged.inj π g : Op) ≠ Tagged.inj ρ g' := by
  intro h
  have h1 := Has.proj_inj (Op := Op) (Tagged.mk g : Tagged π G)
  have h2 := Apart.proj_inj (G := Tagged π G) (Op := Op) (Tagged.mk g' : Tagged ρ G)
  rw [show (Has.inj (Tagged.mk g : Tagged π G) : Op) = Has.inj (Tagged.mk g' : Tagged ρ G) from h,
    h2] at h1
  cases h1

/-- **The functional contract of scalar arithmetic at the tag `π`**: every scalar operation at
the tag is the function of the machine `M`, on all operands. -/
def IsScalarAt (π : Type) [Has (Tagged π ScalarOp) Op] (M : Machine K) (I : Interp Op Tst K) :
    Prop :=
  ∀ a : ScalarOp, I.IsFn .total (Tagged.inj π a) (M.fn a) AnyOperands

/-- Scalar arithmetic at a tag is scalar arithmetic for the instance of the tag: every theorem
under `IsScalar` holds at the tag. -/
theorem IsScalarAt.isScalar {π : Type} [Has (Tagged π ScalarOp) Op] {M : Machine K}
    {I : Interp Op Tst K} (h : IsScalarAt π M I) :
    @IsScalar K Op Tst (Tagged.has π) M I := h

/-- **A cast** from the precision `π` to the precision `ρ`. -/
inductive CastOp (π ρ : Type) where
  /-- `cast [] [x] [z]`: the word `x` of the precision `π`, as a word of the precision `ρ`. -/
  | cast
  deriving DecidableEq

/-- **The functional contract of a cast**: it is the function `c` on words. -/
def IsCast (π ρ : Type) [Has (CastOp π ρ) Op] (c : K → K) (I : Interp Op Tst K) : Prop :=
  I.IsFn .total (Has.inj (CastOp.cast : CastOp π ρ)) (.un fun a => some (c a)) AnyOperands

/-- **The model of a cast**: rounding to the target precision, with the unit roundoff `u` of the
target. A widening cast is exact: `u = 0`. -/
def CastModel (u : ℝ) (dec : K → ℝ) (c : K → K) : Prop :=
  ∀ a, |dec (c a) - dec a| ≤ u * |dec a|

/-- An exact cast keeps the value. -/
theorem CastModel.eq_of_zero {dec : K → ℝ} {c : K → K} (h : CastModel 0 dec c) (a : K) :
    dec (c a) = dec a := by
  have := h a
  rw [zero_mul] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

end NLAlib.Ops
