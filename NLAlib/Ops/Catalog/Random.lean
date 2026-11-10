/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import NLAlib.Ops.Catalog.Blas1
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
  /-- `matvec [n] [x] [y]`: `y := A x`. -/
  | matvec
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

variable [Inhabited K]

/-- A block of `n` words, decoded, as a vector. -/
def decv (dec : K → ℝ) (n : ℕ) (xs : List K) : Fin n → ℝ := fun i => dec (vec xs i)

omit [Inhabited K] in
/-- An entry of a window. -/
theorem vec_window [Inhabited K] (τ : Tape K) (s p : ℕ) {k i : ℕ} (hi : i < k) :
    vec (τ.window s p k) i = τ (p + i) s := by
  simp [vec, Tape.window, List.getD_eq_getElem?_getD, hi]

/-- `matvec`: the product by the matrix `A`, exactly. -/
def matvecRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLen d := d.headD 0
  rel _ X ys := match X with
    | [xs] => decv dec n ys = A.mulVec (decv dec n xs)
    | _ => False

/-- `dot`, exactly, at the length `n`. -/
def dotExRel (dec : K → ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLen _ := 1
  rel _ X ys := match X, ys with
    | [xs, zs], [v] => dec v = ∑ i, decv dec n xs i * decv dec n zs i
    | _, _ => False

omit [Inhabited K] in
/-- `add`, exactly. -/
def addExRel (dec : K → ℝ) : BlockRel K where
  nd := 0
  inLens _ := [1, 1]
  outLen _ := 1
  rel _ X ys := match X, ys with
    | [[a], [b]], [v] => dec v = dec a + dec b
    | _, _ => False

/-- `nrm2`, exactly, at the length `n`. -/
def nrm2ExRel (dec : K → ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLen _ := 1
  rel _ X ys := match X, ys with
    | [xs], [v] => dec v = √(∑ i, decv dec n xs i ^ 2)
    | _, _ => False

omit [Inhabited K] in
/-- `mulc q`: the product by the constant `q`, exactly. -/
def mulcRel (dec : K → ℝ) (q : ℚ) : BlockRel K where
  nd := 0
  inLens _ := [1]
  outLen _ := 1
  rel _ X ys := match X, ys with
    | [[a]], [v] => dec v = q * dec a
    | _, _ => False

/-- `axpy`, exactly, at the length `n`. -/
def axpyExRel (dec : K → ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0, d.headD 0]
  outLen d := d.headD 0
  rel _ X zs := match X with
    | [[a], xs, ys] => decv dec n zs = fun i => decv dec n ys i + dec a * decv dec n xs i
    | _ => False

@[storeNF] theorem matvecRel_inLens (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : List ℕ) : (matvecRel dec A).inLens d = [d.headD 0] := rfl

@[storeNF] theorem matvecRel_outLen (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : List ℕ) : (matvecRel dec A).outLen d = d.headD 0 := rfl

@[storeNF] theorem dotExRel_inLens (dec : K → ℝ) (n : ℕ) (d : List ℕ) :
    (dotExRel dec n).inLens d = [d.headD 0, d.headD 0] := rfl

omit [Inhabited K] in
@[storeNF] theorem addExRel_inLens (dec : K → ℝ) (d : List ℕ) :
    (addExRel dec).inLens d = [1, 1] := rfl

@[storeNF] theorem nrm2ExRel_inLens (dec : K → ℝ) (n : ℕ) (d : List ℕ) :
    (nrm2ExRel dec n).inLens d = [d.headD 0] := rfl

omit [Inhabited K] in
@[storeNF] theorem mulcRel_inLens (dec : K → ℝ) (q : ℚ) (d : List ℕ) :
    (mulcRel dec q).inLens d = [1] := rfl

@[storeNF] theorem axpyExRel_inLens (dec : K → ℝ) (n : ℕ) (d : List ℕ) :
    (axpyExRel dec n).inLens d = [1, d.headD 0, d.headD 0] := rfl

@[storeNF] theorem axpyExRel_outLen (dec : K → ℝ) (n : ℕ) (d : List ℕ) :
    (axpyExRel dec n).outLen d = d.headD 0 := rfl

/-- **The contracts of the operator and of the exact level-1 operations**, with the scalar draw:
what the vector draw is implemented over. -/
structure IsRandBase (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (J : Interp ROp Tst K) : Prop where
  /-- `draw` is the draw of the model, in the Gaussian stream. -/
  draw : J.IsFn .total .draw (.draw Stream.gauss) AnyOperands
  /-- `matvec`. -/
  matvec : J.Meets .total .matvec ((matvecRel dec A).spec (OutApart (· = n)))
  /-- `dot`. -/
  dot : J.Meets .total .dot ((dotExRel dec n).spec (OutApart (· = n)))
  /-- `add`. -/
  add : J.Meets .total .add ((addExRel dec).spec AnyOperands)
  /-- `nrm2`. -/
  nrm2 : J.Meets .total .nrm2 ((nrm2ExRel dec n).spec (OutApart (· = n)))
  /-- `mulc`. -/
  mulc : ∀ q, J.Meets .total (.mulc q) ((mulcRel dec q).spec AnyOperands)
  /-- `axpy`. -/
  axpy : J.Meets .total .axpy ((axpyExRel dec n).spec (InPlace (· = n)))

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
