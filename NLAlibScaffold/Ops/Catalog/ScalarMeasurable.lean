/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Catalog.Index
public import NLAlibScaffold.Ops.Logic.Probabilistic

/-!
# Measurable catalog operations

`NLAlib.Ops.Interp.IsMeasurable` asks that every call, test and index of an interpretation be
measurable in the tape and the memory, everywhere: also off the operands and memories that the
catalog contracts (`NLAlib.Ops.IsScalar`, `NLAlib.Ops.IsCmp`, …) speak about, where a contract
leaves the interpretation free. So a contract does not give measurability; the **canonical**
meanings do. A machine whose word functions are measurable (`NLAlib.Ops.Machine.IsMeasurable`)
gives measurable canonical scalar and index calls, a measurable decoding gives measurable
canonical comparisons and conversions, and an interpretation of a sum of operation types is
measurable when each summand's operations are.

## Main definitions

* `NLAlib.Ops.Machine.IsMeasurable`, `NLAlib.Ops.Interp.IsMeasurableCall`.

## Main results

* `NLAlib.Ops.Machine.IsMeasurable.isMeasurableCall_ofFns`: each scalar operation of the canonical
  interpretation of a measurable machine.
* `NLAlib.Ops.Machine.isMeasurableCall_ofFns_indexFn`: the dimension literal.
* `NLAlib.Ops.CmpTst.measurable_readBlocks_fn`, `NLAlib.Ops.measurable_toNatFn_readBlocks`: the
  canonical comparison and conversion of a measurable decoding.
* `NLAlib.Ops.Interp.isMeasurable_of_sum`: the assembly over `O₁ ⊕ O₂`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- **A measurable machine**: its binary word functions are measurable on pairs and its unary
word functions are measurable, on every word (division by zero included). Literals are
constants. -/
structure Machine.IsMeasurable [MeasurableSpace K] (M : Machine K) : Prop where
  /-- Addition. -/
  add : Measurable fun x : K × K => M.add x.1 x.2
  /-- Subtraction. -/
  sub : Measurable fun x : K × K => M.sub x.1 x.2
  /-- Multiplication. -/
  mul : Measurable fun x : K × K => M.mul x.1 x.2
  /-- Division. -/
  div : Measurable fun x : K × K => M.div x.1 x.2
  /-- Negation. -/
  neg : Measurable M.neg
  /-- Square root. -/
  sqrt : Measurable M.sqrt

/-- **A measurable operation** of an interpretation: at all dimensions and operands, the success
flag and the result of its call are measurable in the tape and the memory. -/
def Interp.IsMeasurableCall [Inhabited K] [MeasurableSpace K] (I : Interp Op Tst K) (o : Op) :
    Prop :=
  ∀ d ins outs, Measurable (fun x : Tape K × Mem K => (I.call o d ins outs x.1 x.2).isSome) ∧
    Measurable (fun x : Tape K × Mem K => (I.call o d ins outs x.1 x.2).getD x.2)

variable [Inhabited K] [MeasurableSpace K]

/-- **The scalar operations of a measurable machine** (PL4): every scalar operation of the
canonical interpretation `Interp.ofFns M.fn` is measurable. -/
theorem Machine.IsMeasurable.isMeasurableCall_ofFns {M : Machine K} (hM : M.IsMeasurable)
    (a : ScalarOp) : (Interp.ofFns M.fn : Interp ScalarOp Tst K).IsMeasurableCall a := by
  sorry

/-- **The dimension literal** (PL4) of the canonical interpretation is measurable, for every
machine: it writes a constant word. -/
theorem Machine.isMeasurableCall_ofFns_indexFn (M : Machine K) :
    (Interp.ofFns fun _ : IndexOp => M.indexFn : Interp IndexOp Tst K).IsMeasurableCall
      IndexOp.lit := by
  sorry

/-- **The canonical comparison** (PL4) of a measurable decoding, read from the operand cells, is
measurable in the memory. -/
theorem CmpTst.measurable_readBlocks_fn {dec : K → ℝ} (hdec : Measurable dec) (c : CmpTst)
    (a : List (ℕ × ℕ)) :
    Measurable (fun m : Mem K => ((m.readBlocks a c.lens).map (c.fn dec)).isSome) ∧
      Measurable (fun m : Mem K => ((m.readBlocks a c.lens).map (c.fn dec)).getD false) := by
  sorry

/-- **The canonical conversion to an index** (PL4) of a measurable decoding is measurable in the
memory. -/
theorem measurable_toNatFn_readBlocks {dec : K → ℝ} (hdec : Measurable dec)
    (a : List (ℕ × ℕ)) :
    Measurable (fun m : Mem K =>
        ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten).isSome) ∧
      Measurable (fun m : Mem K =>
        ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten).getD 0) := by
  sorry

/-- **Assembly over a sum of operation types** (PL4): an interpretation of `O₁ ⊕ O₂` whose
operations of each summand are measurable, with measurable tests and indices, is measurable. -/
theorem Interp.isMeasurable_of_sum {O₁ O₂ : Type} {I : Interp (O₁ ⊕ O₂) Tst K}
    (h₁ : ∀ o, I.IsMeasurableCall (.inl o)) (h₂ : ∀ o, I.IsMeasurableCall (.inr o))
    (ht : ∀ q d ins, Measurable (fun m : Mem K => (I.test q d ins m).isSome) ∧
      Measurable (fun m : Mem K => (I.test q d ins m).getD false))
    (hi : ∀ q ins, Measurable (fun m : Mem K => (I.index q ins m).isSome) ∧
      Measurable (fun m : Mem K => (I.index q ins m).getD 0)) :
    I.IsMeasurable := by
  sorry

end NLAlib.Ops
