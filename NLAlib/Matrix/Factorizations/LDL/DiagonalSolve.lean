/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Catalog.Orth

/-!
# Actual division by a stored diagonal

The shared binary scalar map divides the right-hand side by the stored diagonal in place.
The word contract holds for every scalar machine. Exact division with nonzero original
stored diagonal entries gives the diagonal-system equation needed by LDL solves.

## Main results

* `NLAlib.LDL.divideDiagonal_meets`: the shared actual scalar map's word contract.
* `NLAlib.LDL.diagonal_mulVec_eq_of_divideDiagonalSpec`: exact numerical readback.
-/

@[expose] public section

namespace NLAlib.LDL

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Divide the vector by a read-only stored diagonal, using the shared scalar binary map.
The vector is updated exactly in place; no scratch cell is allocated. -/
def divideDiagonal : Routine Op Tst :=
  routine% [n] (d : n, x : n) → (x) by blocks :=
    .frame [.var 0] [⟨1, .var 2⟩, ⟨0, .var 1⟩, ⟨2, .var 3⟩]
      (binaryMap (Has.inj ScalarOp.div))

variable [Inhabited K]

/-- Every output word is the actual scalar quotient of its input and stored diagonal word. -/
def divideDiagonalSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (ds, xs) → (ys) ensures
    ys = (List.range n).map fun i => M.div (vec xs i) (vec ds i)

/-- The actual scalar binary map computes the complete quotient vector and retains the
stored diagonal, all other memory and the tape position. -/
theorem divideDiagonal_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (divideDiagonal (Op := Op) (Tst := Tst)).Meets I (divideDiagonalSpec M) := by
  routine_intro [n] (d, x) reads (ds, xs)
  have hdisj : Fp.Disj (Store.inBlock d.1 d.2 n) (Store.inBlock x.1 x.2 n) := by
    simpa only [Fp.blocks, sup_bot_eq] using hblocks.2.1.symm
  have hlive' : m.Live [x, d, x] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using And.intro hl.2 ⟨hl.1, hl.2⟩
  have hrun := binaryMap_writes (τ := τ) (hI .div)
    (Store.holdsVec_of_readBlock hxs) (Store.holdsVec_of_readBlock hds) hroom
    (Or.inr rfl) (Or.inl hdisj)
  refine (hrun.in_frame rfl rfl hlive').mono (by fp_sub) ?_
  rintro μ hfr ⟨hwords, hpos⟩
  exact ⟨hpos, [(List.range n).map fun i => M.div (vec xs i) (vec ds i)],
    Mem.readBlocks_of_cons (Store.holdsVec_iff_readBlock.mp hwords) rfl, rfl⟩

omit [Has ScalarOp Op] in
/-- Exact scalar division with a nonzero stored diagonal solves its diagonal system. No
success hypothesis is supplied: this consumes the actual word contract proved above. -/
theorem diagonal_mulVec_eq_of_divideDiagonalSpec {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {n : ℕ} {τ : Tape K} {ds xs ys : List K}
    (hd : ∀ i : Fin n, dec (vec ds i.val) ≠ 0)
    (hpost : (divideDiagonalSpec M).post [n] τ [ds, xs] [ys]) :
    Matrix.diagonal (decv dec n ds) *ᵥ decv dec n ys = decv dec n xs := by
  have hy : ys = (List.range n).map fun i => M.div (vec xs i) (vec ds i) := hpost
  ext i
  rw [Matrix.mulVec_diagonal]
  simp only [decv, hy, vec, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.isLt, Option.map_some, Option.getD_some]
  change dec (vec ds i.val) * dec (M.div (vec xs i.val) (vec ds i.val)) = dec (vec xs i.val)
  rw [hM.div _ _ (hd i)]
  exact mul_div_cancel₀ _ (hd i)

end NLAlib.LDL
