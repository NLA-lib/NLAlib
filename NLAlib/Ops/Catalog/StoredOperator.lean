/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import NLAlib.Ops.Catalog.Scalar
public import NLAlib.Ops.Logic.Footprint

/-!
# Matrix-vector application with explicit read-only data

An operation reads an operator-data block and a vector, then writes their matrix-vector
product. Both blocks are declared operands, so a linked dense or sparse implementation
can access the data without hidden environment reads. An oracle model uses an empty
data block and a matrix fixed by its operation model.

## Main definitions

* `NLAlib.Ops.StoredOperator.functions` gives local matrix-vector block functions.
* `NLAlib.Ops.StoredOperator.denseMatrix` decodes actual column-major words.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Matrix operations with an explicit read-only representation operand. -/
inductive StoredOperatorOp where
  /-- `matvec [m,n] (data,x) → y`, with data length supplied by the storage model. -/
  | matvec
  deriving DecidableEq

namespace StoredOperator

variable {K Op Tst : Type} [Semiring K]

/-- Matrix entries stored column-major, one word per entry. Out-of-range padding
only totalizes the mathematical decoder; block contracts check actual input lengths. -/
def denseMatrix (m n : ℕ) (data : List K) : Matrix (Fin m) (Fin n) K :=
  Matrix.of fun i j => data.getD (j * m + i) 0

/-- Local functions for an explicitly represented family of rectangular matrices.
The matrix semantics depend only on the declared dimensions and data words. -/
def functions (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List K → Matrix (Fin m) (Fin n) K) :
    StoredOperatorOp → BlockFn K
  | .matvec => {
      nd := 2
      inLens d := [dataLength (d.headD 0) (d.getD 1 0), d.getD 1 0]
      outLens d := [d.headD 0]
      fn d _ xs := match xs with
        | [data, x] => some [List.ofFn fun i : Fin (d.headD 0) =>
            ∑ j : Fin (d.getD 1 0), matrix _ _ data i j * x.getD j 0]
        | _ => none }

/-- The output span is disjoint from the supplied data and vector spans. This spatial
admission permits disjoint subviews of one buffer and constant-workspace lowerings. -/
@[admNF] def OutApart (dataLength : ℕ → ℕ → ℕ) (d : List ℕ)
    (ins outs : List (ℕ × ℕ)) : Prop :=
  Fp.Disj (Fp.blocks outs [d.headD 0])
    (Fp.blocks ins [dataLength (d.headD 0) (d.getD 1 0), d.getD 1 0])

/-- The exact local contract for explicit-data matrix-vector application. Output
separation is part of the primitive operation model, independently of algorithm success. -/
def IsExact [Has StoredOperatorOp Op] (dataLength : ℕ → ℕ → ℕ)
    (matrix : (m n : ℕ) → List K → Matrix (Fin m) (Fin n) K)
    (I : Interp Op Tst K) : Prop :=
  I.IsFn .total (Has.inj StoredOperatorOp.matvec)
    (functions dataLength matrix .matvec) (OutApart dataLength)

/-- The dense model reads all `m*n` supplied matrix words. -/
def denseFunctions : StoredOperatorOp → BlockFn K :=
  functions (fun m n => m * n) denseMatrix

/-- A fixed coordinate pattern and its supplied values define a rectangular matrix.
Repeated coordinates add. Coordinates outside the current shape contribute no entry. -/
def cooMatrix (pattern : List (ℕ × ℕ)) (rows cols : ℕ) (data : List K) :
    Matrix (Fin rows) (Fin cols) K :=
  Matrix.of fun i j => ∑ e ∈ Finset.range pattern.length,
    if pattern[e]? = some ((i : ℕ), (j : ℕ)) then data.getD e 0 else 0

/-- The coordinate-storage model reads one actual value per fixed public pattern entry.
Its tree may depend on that configuration, but not on runtime dimensions or data words. -/
def cooFunctions (pattern : List (ℕ × ℕ)) : StoredOperatorOp → BlockFn K :=
  functions (fun _ _ => pattern.length) (cooMatrix pattern)

/-- The oracle model declares an empty data block and a matrix fixed by the model.
It cannot read undeclared memory. -/
def oracleFunctions (matrix : (m n : ℕ) → Matrix (Fin m) (Fin n) K) :
    StoredOperatorOp → BlockFn K :=
  functions (fun _ _ => 0) (fun m n _ => matrix m n)

end StoredOperator
end NLAlib.Ops
