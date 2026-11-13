/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.State
public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Ops.Blas.IntervalMatrix

/-!
# Matrix meaning of the executed Newton–Schulz stopping test

The scalar word scan checks the same component comparisons as the mathematical stopping
test. Its input is the matrix formed by the actual multiplication and Hermitian shift;
there is no additional matrix-level test primitive.

## Main results

* `NLAlib.Sign.newtonSchulzTest_eq_true_iff_inInterval`: the finite matrix test and the packed
  scalar scan have the same predicate, including dimension zero.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

/-- The actual packed scalar interval predicate equals the existing mathematical matrix
stopping test. Both compare every real and imaginary component against the same computed
threshold and its machine negation. No numerical rounding assumption is needed. -/
theorem newtonSchulzTest_eq_true_iff_inInterval {K Su Sg : Type} [Inhabited K]
    (M : Ops.Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) {n : ℕ}
    (η : K) (A : Matrix (Fin n) (Fin n) (K × K)) :
    newtonSchulzTest (M.toFloatMachine dec mm qr unif normal) η A = true ↔
      InInterval dec (M.neg η) η
        (vec ((EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermShift (mm A A) (M.lit 1))))
        (2 * (n * n)) := by
  rw [show 2 * (n * n) = n * n * (EntryCodec.pair K).width from Nat.mul_comm _ _]
  rw [inInterval_packFinMatrix_iff]
  simp [newtonSchulzTest, Machine.toFloatMachine, List.all_eq_true,
    Fin.forall_fin_two, EntryCodec.pair, and_assoc]

end NLAlib.Sign
