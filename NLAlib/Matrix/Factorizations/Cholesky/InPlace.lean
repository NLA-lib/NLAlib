/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightLooking
public import NLAlib.Matrix.Factorizations.Cholesky.Semidefinite

/-!
# In-place interfaces of copied-residual Cholesky

These ordinary Ops interfaces overwrite their sole matrix operand with its factor. They run
exactly the same copy-first scalar bodies as the separate-output routines. Their proofs use
the shared scoped operand judgments, so coincident source and output require no extra
admission predicate or assumed successful run. An empty operand still has a live handle.

## Main results

* `NLAlib.Cholesky.rightLookingInPlace_meets`: positive definite in-place factorization.
* `NLAlib.Cholesky.semidefiniteRightLookingInPlace_meets`: zero-safe semidefinite factorization.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Overwrite a positive definite matrix by its Cholesky factor using the copied-residual
scalar routine. Copying precedes the first output write. -/
def rightLookingInPlace : Routine Op Tst := routine% [n] (A : n * n) → (A) {
  ifPos n {
    run rightLooking [n] (A, A)
  }
}

/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_rightLookingInPlace_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (rightLookingInPlace (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The in-place routine has the same canonical numerical and actual-word postcondition as
its separate-output counterpart, including literal upper zeros and restored scratch. -/
theorem rightLookingInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (rightLookingInPlace (Op := Op) (Tst := Tst)).Meets I (rightLookingSpec M dec) := by
  routine_intro [n] (A) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlAA : m.Live [A, A] := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true, and_self] using hlive
    refine ((rightLooking_writes hI hM hlAA has hpre hroom).in_frame
      rfl rfl hlAA).mono (by fp_sub) ?_
    rintro m' hfr ⟨hpos, ls, hls, hnum, hupper⟩
    refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, hnum, ?_, hupper⟩
    rw [hnum]
    exact hpre.isCholesky_choleskyLower
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    exact ⟨rfl, [[]],
      Mem.readBlocks_of_cons rfl rfl,
      rightLookingSpec_empty M dec as (τ.shift m.pos)⟩

variable [Has CmpTst Tst]

/-- Overwrite a positive semidefinite matrix using the zero-safe scalar routine. A zero
residual pivot writes zero factor words and executes no division. -/
def semidefiniteRightLookingInPlace : Routine Op Tst := routine% [n] (A : n * n) → (A) {
  ifPos n {
    run semidefiniteRightLooking [n] (A, A)
  }
}

omit [Inhabited K] in
/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_semidefiniteRightLookingInPlace_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (semidefiniteRightLookingInPlace (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

/-- The actual in-place result is lower triangular with nonnegative diagonal and the exact
Gram identity. Singular inputs retain this semidefinite contract. -/
theorem semidefiniteRightLookingInPlace_meets {M : Machine K} {I : Interp Op Tst K}
    {dec : K → ℝ} (hI : IsScalar M I) (hM : ExactModel dec M) (hcmp : IsCmp dec I) :
    (semidefiniteRightLookingInPlace (Op := Op) (Tst := Tst)).Meets I
      (semidefiniteRightLookingSpec M dec) := by
  routine_intro [n] (A) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlAA : m.Live [A, A] := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true, and_self] using hlive
    refine ((semidefiniteRightLooking_writes hI hM hcmp hlAA has hpre hroom).in_frame
      rfl rfl hlAA).mono (by fp_sub) ?_
    rintro m' hfr ⟨hpos, ls, hls, hnum, hupper⟩
    refine ⟨by omega, [ls], Mem.readBlocks_of_cons hls rfl, hnum, ?_, ?_, ?_, hupper⟩
    · rw [hnum]
      exact isLowerTriangular_choleskyLower _
    · intro i
      rw [hnum]
      exact hpre.isHermitian.choleskyLower_apply_self_nonneg i
    · rw [hnum]
      exact hpre.eq_choleskyLower_mul_conjTranspose
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    exact ⟨rfl, [[]],
      Mem.readBlocks_of_cons rfl rfl,
      semidefiniteRightLookingSpec_empty M dec as (τ.shift m.pos)⟩


end NLAlib.Cholesky
