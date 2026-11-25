/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Routine
public import NLAlib.Matrix.Factorizations.TriangularSolve.Factors

/-!
# Scalar LU factorization followed by a solve

The routine allocates its own factors, runs stored Gaussian elimination, and solves their
product system through the shared triangular routines. The original matrix and right-hand
side are read operands. Nonzero canonical pivots suffice for every scalar division.

## Main results

* `NLAlib.LU.solve_meets`: the computed solution satisfies the original matrix equation.
-/

@[expose] public section

namespace NLAlib.LU

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute fresh LU factors and solve their triangular systems into a fresh output vector.
Both factor matrices are scoped scratch and are released before return.
The outer dimension guard bypasses every allocation and operand frame at order zero. -/
def solve : Routine Op Tst := routine% [n] (A : n * n, b : n) → (x : n) {
  ifPos n {
    let L ← alloc (n * n);
    let U ← alloc (n * n);
    run factor [n] (A, L, U);
    run TriangularSolve.factors [n] (L, U, b, x)
  }
}

/-- Empty execution reads no operands and restores the complete memory for arbitrary
handles, offsets and aliases, independently of all scalar laws. -/
theorem eval_solve_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (solve (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The actual decoded matrix maps the output to the original right-hand side. The only
matrix-domain restriction is nonzero canonical Gaussian pivots, vacuous at order zero. -/
def solveSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as, bs) → (xs) requires
    (∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) ensures
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- Canonical factors returned by the actual LU word specification satisfy the shared
stored triangular-solve precondition under the original Gaussian nonzero-pivot condition. -/
theorem factorsSpec_pre_of_factorSpec {dec : K → ℝ} {n : ℕ} {as ls us : List K}
    {τ : Tape K} (hpost : (factorSpec dec).post [n] τ [as] [ls, us])
    (hp : ∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) :
    (TriangularSolve.factorsSpec dec).pre [n] τ [ls, us, []] := by
  obtain ⟨hL, hU⟩ := hpost
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact (isUnitLowerTriangular_luLower _).isLowerTriangular
  · rw [hU]
    exact isUpperTriangular_luUpper _
  · intro i hi
    have hdiag := (isUnitLowerTriangular_luLower (decodeMatrix dec n n as)).apply_self
      (⟨i, hi⟩ : Fin n)
    have he : dec (vec ls (i * n + i)) = 1 := by
      simpa only [← hL, decodeMatrix_apply] using hdiag
    rw [he]
    exact one_ne_zero
  · intro i hi
    have he : decodeMatrix dec n n us ⟨i, hi⟩ ⟨i, hi⟩ ≠ 0 := by
      rw [hU, luUpper_apply_self]
      exact hp ⟨i, hi⟩
    simpa only [decodeMatrix_apply] using he

/-- The actual factorization and substitutions compute a solution under exact scalar
arithmetic and decoded comparisons. Input nonbreakdown is stated on the matrix, rather than
assumed as a successful execution. -/
theorem solve_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec dec) := by
  routine_intro [n] (A, b, x) reads (as, bs)
  change Writes .total I τ _ (Env.frame [n] [A, b, x]) (Fp.blocks [x] [n]) _ m
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as L U
    have hAL : A.1 ≠ L := by change A.1 ≠ m.store.length + 0; omega
    have hAU : A.1 ≠ U := by change A.1 ≠ m.store.length + 1; omega
    have hbL : b.1 ≠ L := by change b.1 ≠ m.store.length + 0; omega
    have hbU : b.1 ≠ U := by change b.1 ≠ m.store.length + 1; omega
    have hxL : x.1 ≠ L := by change x.1 ≠ m.store.length + 0; omega
    have hxU : x.1 ≠ U := by change x.1 ≠ m.store.length + 1; omega
    have hLU : L ≠ U := by change m.store.length + 0 ≠ m.store.length + 1; omega
    call (factor_meets hI hcmp hM) [n] (A, (L, 0), (U, 0)) (pre := hpre)
      as m₁ hfr₁ hpos₁ (ls, us) hfactor
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_L.length ∧ m.store.length < s_L.length ∧ m.store.length + 1 < s_L.length
      simp only [List.length_cons, List.length_nil] at hlen_L
      omega
    case' hroom =>
      change (0 + n * n ≤ s_L.len L) ∧ (0 + n * n ≤ s_L.len U) ∧ True
      exact ⟨by simpa only [Nat.zero_add] using hL.ge,
        by simpa only [Nat.zero_add] using hU.ge, trivial⟩
    have hpreFactors : (TriangularSolve.factorsSpec dec).pre [n] (τ.shift m₁.pos)
        [ls, us, bs] := factorsSpec_pre_of_factorSpec (τ := τ.shift m.pos) hfactor hpre
    call (TriangularSolve.factors_meets hI hM) [n] ((L, 0), (U, 0), b, x)
      (pre := hpreFactors) as m₂ hfr₂ hpos₂ (xs) hsolve
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change m.store.length < m₁.store.length ∧ m.store.length + 1 < m₁.store.length ∧
        b.1 < m₁.store.length ∧ x.1 < m₁.store.length
      simp only [List.length_cons, List.length_nil] at hlen_L
      omega
    intro s₂ hs₂ hB₂
    refine ⟨?_, [xs], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
    · change m₂.pos = m.pos + 0
      omega
    · exact Store.Below.readBlock_of hB₂ hl.2.2 hxs
    · change decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs
      have hLUmat := isLU_luLower_luUpper (A := decodeMatrix dec n n as)
        (fun i _ => by rw [luUpper_apply_self]; exact hpre i)
      rw [hLUmat.eq_mul]
      have hs : (decodeMatrix dec n n ls * decodeMatrix dec n n us) *ᵥ decv dec n xs =
          decv dec n bs := hsolve
      simpa only [hfactor.1, hfactor.2] using hs
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [[]], Mem.readBlocks_of_cons rfl rfl, ?_⟩
    ext i
    exact i.elim0

end NLAlib.LU
