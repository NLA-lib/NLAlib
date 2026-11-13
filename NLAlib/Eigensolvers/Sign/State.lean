/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign.Iteration
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Stored state of the capped Newton–Schulz iteration

The loop's mathematical state is its current matrix. The stored representation additionally
contains the square cached by the stopping test and the actual threshold/flag words. No
condition asserts that the test passes, that a rounded step is accurate, or that the program
succeeds. Those facts are proved separately from the input and operation model.

## Main results

* `NLAlib.Sign.LoopState` represents the mathematical iterate in the actual word store.
* `NLAlib.Sign.LoopState.flag_ne_one` identifies the inactive flag under distinct zero/one
  decodings.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Su Sg : Type}

/-- The current iterate and the square left by its actual stopping test. The five-word
scalar workspace stores threshold, failure flag, temporary literal, one, and negated threshold.
The temporary literal is intentionally unconstrained between iterations. -/
structure LoopState (M : FloatMachine K Su Sg) {n : ℕ} (x w t : ℕ × ℕ) (η : K)
    (A : Matrix (Fin n) (Fin n) (K × K)) (s : Store K) : Prop where
  /-- Actual packed iterate. -/
  matrix : s.readBlock x.1 x.2 (n * n * 2) = some ((EntryCodec.pair K).packFinMatrix A)
  /-- Actual cached square of this same iterate. -/
  square : s.readBlock w.1 w.2 (n * n * 2) =
    some ((EntryCodec.pair K).packFinMatrix (M.mm A A))
  /-- Computed stored threshold. -/
  threshold : s.get t.1 t.2 = some η
  /-- Stored word one used by the loop query. -/
  one : s.get t.1 (t.2 + 3) = some M.one
  /-- Actual negation of the threshold. -/
  lower : s.get t.1 (t.2 + 4) = some (M.neg η)
  /-- Actual zero/one word selected by the stopping test. -/
  flag : s.get t.1 (t.2 + 1) =
    some (if newtonSchulzTest M η A then M.zero else M.one)

/-- The stored flag's decoding differs from one exactly when the matrix stopping test passes.
Only distinct decodings of the machine's zero and one are required. -/
theorem LoopState.flag_ne_one {M : FloatMachine K Su Sg} {n : ℕ} {x w t : ℕ × ℕ}
    {η : K} {A : Matrix (Fin n) (Fin n) (K × K)} {s : Store K}
    (h : LoopState M x w t η A s) {dec : K → ℝ} (h01 : dec M.zero ≠ dec M.one) :
    ∃ flag, s.get t.1 (t.2 + 1) = some flag ∧
      (dec flag ≠ dec M.one ↔ newtonSchulzTest M η A = true) := by
  refine ⟨_, h.flag, ?_⟩
  cases newtonSchulzTest M η A <;> simp [h01]

/-- The actual equality query on the stored failure flag returns the negated matrix stopping
test. Distinct zero/one decodings suffice; no successful-execution premise is introduced. -/
theorem LoopState.test_eq {Op Tst : Type} [Has CmpTst Tst]
    {M : FloatMachine K Su Sg} {n : ℕ} {x w t : ℕ × ℕ} {η : K}
    {A : Matrix (Fin n) (Fin n) (K × K)} {s : Store K}
    (h : LoopState M x w t η A s) {dec : K → ℝ} {I : Interp Op Tst K}
    (hC : IsCmp dec I) (h01 : dec M.zero ≠ dec M.one) (pos : ℕ) :
    I.test (Has.inj CmpTst.eq) [] [(t.1, t.2 + 1), (t.1, t.2 + 3)] ⟨s, pos⟩ =
      some (!(newtonSchulzTest M η A)) := by
  rw [hC.test_eq h.flag h.one]
  cases newtonSchulzTest M η A <;> simp [h01]

end NLAlib.Sign
