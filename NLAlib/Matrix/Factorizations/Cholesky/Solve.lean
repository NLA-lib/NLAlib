/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightLooking
public import NLAlib.Matrix.Factorizations.TriangularSolve.Cholesky

/-!
# Right-looking Cholesky followed by a solve

Factor the actual stored positive definite matrix, then apply forward and transposed-lower
back substitution to a copy of the right-hand side. One scoped matrix stores the factor;
the original matrix and right-hand side remain read operands.

## Main results

* `NLAlib.Cholesky.solve_meets`: the computed vector satisfies the original system.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Compute a scoped Cholesky factor and solve with it using the actual scalar substitutions.
The outer dimension guard bypasses every allocation and operand frame at order zero. -/
def solve : Routine Op Tst := routine% [n] (A : n * n, b : n) → (x : n) {
  ifPos n {
    let L ← alloc (n * n);
    run rightLooking [n] (A, L);
    run TriangularSolve.cholesky [n] (L, b, x)
  }
}

/-- Empty execution reads no operands and restores the complete memory for arbitrary
handles, offsets and aliases, independently of all scalar laws. -/
theorem eval_solve_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (solve (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The stored positive definite matrix maps the output to the original right-hand side.
The matrix may have order zero. -/
def solveSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as, bs) → (xs) requires (decodeMatrix dec n n as).PosDef ensures
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs

/-- Positive definiteness of the original stored matrix proves success and the exact system
equation for the actual factorization and solve, without assuming any run succeeds. -/
theorem solve_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec dec) := by
  routine_intro [n] (A, b, x) reads (as, bs)
  change Writes .total I τ _ (Env.frame [n] [A, b, x]) (Fp.blocks [x] [n]) _ m
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as L
    have hAL : A.1 ≠ L := by change A.1 ≠ m.store.length + 0; omega
    have hbL : b.1 ≠ L := by change b.1 ≠ m.store.length + 0; omega
    have hxL : x.1 ≠ L := by change x.1 ≠ m.store.length + 0; omega
    call (rightLooking_meets hI hM) [n] (A, (L, 0)) (pre := hpre)
      as m₁ hfr₁ hpos₁ (ls) hfactor
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_L.length ∧ m.store.length < s_L.length
      simp only [List.length_singleton] at hlen_L
      omega
    case' hroom =>
      change (0 + n * n ≤ s_L.len L) ∧ True
      exact ⟨by simpa only [Nat.zero_add] using hL.ge, trivial⟩
    have hf : IsCholesky (decodeMatrix dec n n as) (decodeMatrix dec n n ls) := hfactor.2.1
    have htri : (TriangularSolve.choleskySpec dec).pre [n] (τ.shift m₁.pos) [ls, bs] := by
      refine ⟨hf.isLowerTriangular, ?_⟩
      intro i hi
      have hp := hf.apply_self_pos (⟨i, hi⟩ : Fin n)
      simpa only [decodeMatrix_apply] using hp.ne'
    call (TriangularSolve.cholesky_meets hI hM) [n] ((L, 0), b, x)
      (pre := htri) as m₂ hfr₂ hpos₂ (xs) hsolve
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change m.store.length < m₁.store.length ∧ b.1 < m₁.store.length ∧ x.1 < m₁.store.length
      simp only [List.length_singleton] at hlen_L
      omega
    intro s₂ hs₂ hB₂
    refine ⟨?_, [xs], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
    · change m₂.pos = m.pos + 0
      omega
    · exact Store.Below.readBlock_of hB₂ hl.2.2 hxs
    · change decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs
      rw [hf.eq_mul_conjTranspose]
      exact hsolve
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [[]], Mem.readBlocks_of_cons rfl rfl, ?_⟩
    ext i
    exact i.elim0

end NLAlib.Cholesky
