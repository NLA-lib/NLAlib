/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Window

/-!
# Catalog: draws, an operator and exact level-1 operations

The group `NLAlib.Ops.ROp` of the randomized examples: a scalar and a vector Gaussian draw, the
product by a fixed matrix, and the level-1 operations they need. The contracts
(`NLAlib.Ops.IsRandLin`) are those of exact arithmetic, stated on decoded vectors
(`NLAlib.Ops.decv`): the result decodes to the exact value. The vector draw has the contract
`NLAlib.Ops.drawRel` of visible randomness.

## Main results

* `NLAlib.Ops.IsRandBase`: the contracts without the vector draw, over which it is implemented.
* `NLAlib.Ops.IsRandLin`: the contracts of the randomized examples.
* `NLAlib.Ops.randWindow`: the tape windows of the operations, registered with the access model.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Tst : Type}

/-- Draws, an operator and exact level-1 operations. -/
inductive ROp where
  /-- `draw [] [] [z]`: the next entry of the Gaussian stream, in the cell `z`. -/
  | draw
  /-- `gauss [n] [] [g]`: the next `n` entries of the Gaussian stream, in the block `g`. -/
  | gauss
  /-- An operation from the linear operator catalog. -/
  | operator (op : OperatorOp)
  /-- `dot [n] [x, y] [z]`. -/
  | dot
  /-- `add [] [a, b] [z]`. -/
  | add
  /-- `nrm2 [n] [x] [z]`. -/
  | nrm2
  /-- `mulc q [] [a] [z]`: `z := q a`, for a rational constant `q` of the tree. -/
  | mulc (q : ℚ)
  /-- `axpy [n] [α, x, y] [y]`: `y := y + α x`, in place. -/
  | axpy
  deriving DecidableEq

instance : Has OperatorOp ROp where
  inj := .operator
  proj
    | .operator o => some o
    | _ => none
  proj_inj _ := rfl
  inj_of_proj r o h := by
    cases r <;> first | exact congrArg ROp.operator (Option.some.inj h).symm | cases h

variable [Inhabited K]

omit [Inhabited K] in
/-- An entry of a window. -/
theorem vec_window [Inhabited K] (τ : Tape K) (s p : ℕ) {k i : ℕ} (hi : i < k) :
    vec (τ.window s p k) i = τ (p + i) s := by
  simp [vec, Tape.window, List.getD_eq_getElem?_getD, hi]

omit [Inhabited K] in
/-- `add`, exactly. -/
@[simps (attr := storeNF)]
def addExRel (dec : K → ℝ) : BlockRel K where
  nd := 0
  inLens _ := [1, 1]
  outLens _ := [1]
  rel _ X _ ys := match X, ys with
    | [[a], [b]], [[v]] => dec v = dec a + dec b
    | _, _ => False

omit [Inhabited K] in
/-- `mulc q`: the product by the constant `q`, exactly. -/
@[simps (attr := storeNF)]
def mulcRel (dec : K → ℝ) (q : ℚ) : BlockRel K where
  nd := 0
  inLens _ := [1]
  outLens _ := [1]
  rel _ X _ ys := match X, ys with
    | [[a]], [[v]] => dec v = q * dec a
    | _, _ => False

/-- **The contracts of the operator and of the exact level-1 operations**, with the scalar draw:
what the vector draw is implemented over. -/
structure IsRandBase (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (J : Interp ROp Tst K) : Prop where
  /-- `draw` is the draw of the model, in the Gaussian stream. -/
  draw : J.IsFn .total .draw (.draw Stream.gauss) AnyOperands
  /-- `matvec`. -/
  matvec : IsExactMatvec dec A J
  /-- `dot`. -/
  dot : J.Meets .total .dot ((dotExactRel dec).spec (OutApart (· = n)))
  /-- `add`. -/
  add : J.Meets .total .add ((addExRel dec).spec AnyOperands)
  /-- `nrm2`. -/
  nrm2 : J.Meets .total .nrm2 ((nrm2ExactRel dec).spec (OutApart (· = n)))
  /-- `mulc`. -/
  mulc : ∀ q, J.Meets .total (.mulc q) ((mulcRel dec q).spec AnyOperands)
  /-- `axpy`. -/
  axpy : J.Meets .total .axpy ((axpyExactRel dec).spec (InPlace (· = n)))

/-- **The contracts of the randomized examples**: the base and the vector draw. -/
structure IsRandLin (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (J : Interp ROp Tst K) : Prop extends IsRandBase dec A J where
  /-- `gauss` is the vector draw: its output is the window. -/
  gauss : J.Meets .total .gauss ((drawRel Stream.gauss).spec (OutApart (· = n)))

/-- The tape windows of the operations: one entry for `draw`, `n` for `gauss` at the length `n`,
none for the others. -/
def randWindow : ROp → List ℕ → ℕ
  | .draw, _ => 1
  | .gauss, d => d.headD 0
  | _, _ => 0

end NLAlib.Ops
