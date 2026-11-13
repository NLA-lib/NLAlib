/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Catalog.Scalar

/-!
# Functional contracts for matrix multiplication and QR

The ordinary operations here apply routines to matrices of stored entries. The entry codec
specifies their actual word buffers, including interleaved pairs. Numerical accuracy is a
separate property of the routines: no algorithm or convergence theorem is built into a kernel.
Every routine gives a joint realization of these functional contracts on the same codec.

## Main results

* `NLAlib.Ops.IsMatrixMul` and `NLAlib.Ops.IsMatrixQR` specify functional matrix kernels.
* `NLAlib.Ops.matrixInterp` jointly realizes both contracts for arbitrary routines.
* `NLAlib.Ops.matrixMulFn_fn` and `NLAlib.Ops.matrixQRFn_fn` expose the actual packed outputs.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Matrix kernels on packed entries. Their work, span and scratch belong to the resource
model, independently of these functional contracts. -/
inductive MatrixOp where
  /-- `mul [l,m,n] [A,B] [C]` multiplies compatible rectangular matrices. -/
  | mul
  /-- `qr [m,n] [A] [Q,R]` computes a full square Q and a rectangular R. -/
  | qr
  deriving DecidableEq

variable {K E Op Tst : Type} [Inhabited K]

/-- A matrix multiplication routine lifted to ordinary operand blocks. Inputs may alias the
output: the operation reads both complete inputs before writing its result. -/
def matrixMulFn (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E) : BlockFn K where
  nd := 3
  inLens d := match d with
    | [l, m, n] => [m * l * C.width, n * m * C.width]
    | _ => []
  outLens d := match d with
    | [l, _, n] => [n * l * C.width]
    | _ => []
  fn d _ xs := match d, xs with
    | [l, m, n], [as, bs] => some [C.packFinMatrix (mm (C.matrix l m as) (C.matrix m n bs))]
    | _, _ => none

/-- A full QR routine lifted to ordinary operand blocks. The contract describes simultaneous
mathematical outputs; a caller reading both back supplies disjoint output footprints. -/
def matrixQRFn (C : EntryCodec K E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) : BlockFn K where
  nd := 2
  inLens d := match d with
    | [m, n] => [n * m * C.width]
    | _ => []
  outLens d := match d with
    | [m, n] => [m * m * C.width, n * m * C.width]
    | _ => []
  fn d _ xs := match d, xs with
    | [m, n], [as] =>
      let result := qr (C.matrix m n as)
      some [C.packFinMatrix result.1, C.packFinMatrix result.2]
    | _, _ => none

/-- The multiplication operation computes its supplied word-level matrix routine. No
assumption that the routine is exact, stable or convergent is implicit. -/
def IsMatrixMul [Has MatrixOp Op] (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E) (I : Interp Op Tst K) : Prop :=
  I.IsFn .total (Has.inj MatrixOp.mul) (matrixMulFn C mm) AnyOperands

/-- The QR operation computes its supplied word-level full QR routine. Numerical QR
hypotheses are properties of that routine, supplied by consumers. -/
def IsMatrixQR [Has MatrixOp Op] (C : EntryCodec K E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (I : Interp Op Tst K) : Prop :=
  I.IsFn .total (Has.inj MatrixOp.qr) (matrixQRFn C qr) AnyOperands

/-- A multiplication call packs exactly the result of its actual decoded input blocks. -/
@[simp] theorem matrixMulFn_fn (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E) (l m n : ℕ) (as bs w : List K) :
    (matrixMulFn C mm).fn [l, m, n] w [as, bs] =
      some [C.packFinMatrix (mm (C.matrix l m as) (C.matrix m n bs))] := rfl

/-- A QR call packs both factors of the same routine on its actual input block. -/
@[simp] theorem matrixQRFn_fn (C : EntryCodec K E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E)
    (m n : ℕ) (as w : List K) :
    (matrixQRFn C qr).fn [m, n] w [as] =
      some [C.packFinMatrix (qr (C.matrix m n as)).1,
        C.packFinMatrix (qr (C.matrix m n as)).2] := rfl

/-- Both kernels on one codec are realized together, for arbitrary word-level routines,
including zero-dimensional matrices. This interpreter makes no numerical accuracy claim. -/
def matrixInterp (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) : Interp MatrixOp Tst K :=
  Interp.ofFns fun
    | .mul => matrixMulFn C mm
    | .qr => matrixQRFn C qr

/-- The joint interpretation satisfies the multiplication contract. -/
theorem isMatrixMul_matrixInterp (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) :
    IsMatrixMul C mm (matrixInterp (Tst := Tst) C mm qr) :=
  Interp.ofFns_isFn (Tst := Tst) (fun o : MatrixOp => match o with
    | .mul => matrixMulFn C mm
    | .qr => matrixQRFn C qr) .total .mul AnyOperands

/-- The same interpretation satisfies the QR contract. -/
theorem isMatrixQR_matrixInterp (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) :
    IsMatrixQR C qr (matrixInterp (Tst := Tst) C mm qr) :=
  Interp.ofFns_isFn (Tst := Tst) (fun o : MatrixOp => match o with
    | .mul => matrixMulFn C mm
    | .qr => matrixQRFn C qr) .total .qr AnyOperands

end NLAlib.Ops
