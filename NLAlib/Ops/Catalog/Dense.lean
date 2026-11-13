/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Matrix
public import NLAlib.Ops.Catalog.Sampling

/-!
# A standard signature for dense numerical programs

The signature combines scalar arithmetic, dimension literals, multiplication/QR kernels and
visible scalar samples. Its queries are exact scalar comparisons and bounded natural-index
conversion. Each group has an explicit injection and projection; no algorithm-specific
primitive or global success predicate is included.

A reference interpretation realizes all functional contracts simultaneously on the same
machine and stored-entry codec. Numerical accuracy and probability laws remain separate
assumptions on that machine, those routines and the tape.

## Main results

* `NLAlib.Ops.DenseOp` is the combined operation signature.
* `NLAlib.Ops.denseInterp` supplies all operations and queries jointly.
* `NLAlib.Ops.denseInterp_contracts` proves every functional group contract together.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A standardized collection of primitive operations for dense matrix algorithms. -/
inductive DenseOp where
  /-- Scalar arithmetic on words. -/
  | scalar (op : ScalarOp)
  /-- Evaluated dimensions written as scalar literals. -/
  | index (op : IndexOp)
  /-- Matrix multiplication and QR. -/
  | matrix (op : MatrixOp)
  /-- Explicit draws of stored words. -/
  | sample (op : SampleOp)
  deriving DecidableEq

instance : Has ScalarOp DenseOp where
  inj := .scalar
  proj | .scalar op => some op | _ => none
  proj_inj _ := rfl
  inj_of_proj op g h := by
    cases op <;> cases h
    rfl

instance : Has IndexOp DenseOp where
  inj := .index
  proj | .index op => some op | _ => none
  proj_inj _ := rfl
  inj_of_proj op g h := by
    cases op <;> cases h
    rfl

instance : Has MatrixOp DenseOp where
  inj := .matrix
  proj | .matrix op => some op | _ => none
  proj_inj _ := rfl
  inj_of_proj op g h := by
    cases op <;> cases h
    rfl

instance : Has SampleOp DenseOp where
  inj := .sample
  proj | .sample op => some op | _ => none
  proj_inj _ := rfl
  inj_of_proj op g h := by
    cases op <;> cases h
    rfl

variable {K E : Type} [Inhabited K]

/-- One canonical assignment of each dense operation to its local word/block function.
The reference interpretation and access-model contracts use this same assignment. -/
def denseFunctions (M : Machine K) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) : DenseOp → BlockFn K
  | .scalar o => M.fn o
  | .index _ => M.indexFn
  | .matrix .mul => matrixMulFn C mm
  | .matrix .qr => matrixQRFn C qr
  | .sample (.draw stream) => .draw stream

/-- The combined functional interpretation. Each primitive reads its declared operands and
sample window; only its output blocks are written. Queries read actual stored cells. -/
noncomputable def denseInterp (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) :
    Interp DenseOp (CmpTst ⊕ IdxTst) K where
  call op := (Interp.ofFns (Tst := CmpTst ⊕ IdxTst) (denseFunctions M C mm qr)).call op
  test q _ a m := match q with
    | .inl c => (m.readBlocks a c.lens).map (c.fn dec)
    | .inr _ => none
  index q a m := match q with
    | .inr .toNat => (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten
    | .inl _ => none

/-- The standard dense signature's functional contracts are jointly realizable for every
machine, codec and pair of matrix routines. Accuracy and distribution are not inferred. -/
theorem denseInterp_contracts (M : Machine K) (dec : K → ℝ) (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) :
    let I := denseInterp M dec C mm qr
    IsScalar M I ∧ IsIndexLit M I ∧ IsMatrixMul C mm I ∧ IsMatrixQR C qr I ∧
      IsSample I ∧ IsCmp dec I ∧ IsToNat dec I := by
  let F := denseFunctions M C mm qr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o
    exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst) F .total (.scalar o) AnyOperands
  · exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst) F .total (.index .lit) AnyOperands
  · exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst) F .total (.matrix .mul) AnyOperands
  · exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst) F .total (.matrix .qr) AnyOperands
  · intro stream
    exact Interp.ofFns_isFn (Tst := CmpTst ⊕ IdxTst) F .total (.sample (.draw stream)) AnyOperands
  · intro c d a m xs h
    change (m.readBlocks a c.lens).map (c.fn dec) = _
    rw [h]
    rfl
  · intro a m xs h
    change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten) = _
    rw [h]
    rfl

end NLAlib.Ops
