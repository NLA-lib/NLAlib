/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Window
public import NLAlib.Ops.Catalog.Scalar

/-!
# Catalog: scalar samples from named tape streams

A scalar sample is an explicit operation with no input operand and one output cell. It consumes
one position of a declared stream. Its functional contract specifies the actual stored word;
it imposes no distribution. Probability assumptions on the tape are separate from execution.

## Main results

* `NLAlib.Ops.IsSample`: the functional sample contract for every stream.
* `NLAlib.Ops.isSample_ofFns`: the existing functional interpreter realizes all sample operations.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A draw of one stored word from the named tape stream. -/
inductive SampleOp where
  /-- `draw stream [] [] [out]` stores one fresh sample and advances the tape by one position. -/
  | draw (stream : ℕ)
  deriving DecidableEq

/-- The tape window consumed by a scalar sample. -/
def sampleWindow (_op : SampleOp) (_dims : List ℕ) : ℕ := 1

/-- The declared stream of a scalar sample. -/
def sampleStream : SampleOp → ℕ
  | .draw stream => stream

/-- Every scalar sample stores the word at its current tape position from its named stream. -/
def IsSample {Op Tst K : Type} [Has SampleOp Op] (I : Interp Op Tst K) : Prop :=
  ∀ stream, I.IsFn .total (Has.inj (SampleOp.draw stream)) (.draw stream) AnyOperands

/-- The existing generic functional interpreter realizes all stream contracts on the same tape.
No stream distribution is part of this functional realization. -/
theorem isSample_ofFns {Tst K : Type} :
    IsSample (Interp.ofFns (Tst := Tst) (K := K)
      (fun op : SampleOp => .draw (sampleStream op))) := by
  intro stream
  exact Interp.ofFns_isFn (fun op : SampleOp => .draw (sampleStream op))
    .total (.draw stream) AnyOperands

end NLAlib.Ops
