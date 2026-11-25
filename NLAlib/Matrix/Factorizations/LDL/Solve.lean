/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LDL.Routine
public import NLAlib.Matrix.Factorizations.TriangularSolve.LDL
public import NLAlib.Matrix.Perturbation.ComponentwiseBackward

/-!
# LDL factorization followed by an actual scalar solve

The routine computes its own canonical unit lower factor and pivot vector, then performs
forward substitution, stored diagonal division and transposed-lower substitution. Its domain
is the original Hermitian matrix with nonzero canonical Gaussian pivots; indefinite inputs
are admitted. A dimension guard precedes all allocation and operand frames at order zero.

## Main results

* `NLAlib.LDL.solve_meets`: actual factorization and scalar solution of the original system.
* `NLAlib.LDL.eval_solve_zero`: arbitrary-handle empty execution.
* `NLAlib.LDL.isComponentwiseBackwardSolution_of_solveSpec_post`: existing zero-error contract.
-/

@[expose] public section

namespace NLAlib.LDL

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute LDL factors in caller-provided scratch and solve their three-factor system. -/
def solveWithScratch : Routine Op Tst :=
  routine% [n] (A : n * n, b : n) → (x : n, unreported L : n * n, unreported d : n) {
    run factor [n] (A, L, d);
    run TriangularSolve.ldlFactors [n] (L, d, b, x)
  }

/-- Compute and release the actual LDL factors, retaining only the solution vector. The
empty dimension reads no handle and allocates no workspace. -/
def solve : Routine Op Tst := routine% [n] (A : n * n, b : n) → (x : n) {
  ifPos n {
    let L ← alloc (n * n);
    let d ← alloc n;
    run solveWithScratch [n] (A, b, x, L, d)
  }
}

/-- Empty execution restores the complete memory for arbitrary handles, offsets and aliases,
independently of arithmetic laws or live-buffer assumptions. -/
theorem eval_solve_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (solve (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The only numerical conditions are original Hermitian symmetry and nonzero original
Gaussian pivots. The actual decoded output solves the original matrix equation. -/
def solveSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as, bs) → (xs) requires
    (decodeMatrix dec n n as).IsHermitian ∧
      (∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) ensures
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs

/-- Actual LDL factors and substitutions solve the original stored system. Scratch capacities
are caller-provided here; no mathematical result is assumed of an execution. -/
theorem solveWithScratch_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (solveWithScratch (Op := Op) (Tst := Tst)).Meets I (solveSpec dec) := by
  routine_intro [n] (A, b, x, L, d) reads (as, bs)
  obtain ⟨hherm, hp⟩ := hpre
  call (factor_meets hI hcmp hM) [n] (A, L, d) (pre := ⟨hherm, hp⟩)
    as m₁ hfr₁ hpos₁ (ls, ds) hfactor
  obtain ⟨hcanonical, hdiag, hf⟩ := hfactor
  have htri : (TriangularSolve.ldlFactorsSpec dec).pre [n] (τ.shift m₁.pos)
      [ls, ds, bs] := by
    refine ⟨hf.isUnitLowerTriangular.isLowerTriangular, ?_, fun i => ?_⟩
    · intro i hi
      have hunit := hf.isUnitLowerTriangular.apply_self (⟨i, hi⟩ : Fin n)
      have he : dec (vec ls (i * n + i)) = 1 := by
        simpa only [decodeMatrix_apply] using hunit
      rw [he]
      exact one_ne_zero
    · rw [hdiag i]
      exact hp i
  call (TriangularSolve.ldlFactors_meets hI hM) [n] (L, d, b, x) (pre := htri)
    as m₂ hfr₂ hpos₂ (xs) hsolve
  routine_exit
  change decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs
  rw [hf.eq_mul]
  exact hsolve

/-- Original matrix conditions prove full success of the guarded, scoped LDL solve. All
factor storage is released, and only the reported solution block can change. -/
theorem solve_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hM : ExactModel dec M) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec dec) := by
  routine_intro [n] (A, b, x) reads (as, bs)
  change Writes .total I τ _ (Env.frame [n] [A, b, x]) (Fp.blocks [x] [n]) _ m
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as L d
    have hAL : A.1 ≠ L := by change A.1 ≠ m.store.length + 0; omega
    have hAd : A.1 ≠ d := by change A.1 ≠ m.store.length + 1; omega
    have hbL : b.1 ≠ L := by change b.1 ≠ m.store.length + 0; omega
    have hbd : b.1 ≠ d := by change b.1 ≠ m.store.length + 1; omega
    have hxL : x.1 ≠ L := by change x.1 ≠ m.store.length + 0; omega
    have hxd : x.1 ≠ d := by change x.1 ≠ m.store.length + 1; omega
    have hLd : L ≠ d := by change m.store.length + 0 ≠ m.store.length + 1; omega
    call (solveWithScratch_meets hI hcmp hM) [n] (A, b, x, (L, 0), (d, 0))
      (pre := hpre) as μ hfr hpos (xs) hpost
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_L.length ∧ b.1 < s_L.length ∧ x.1 < s_L.length ∧
        m.store.length < s_L.length ∧ m.store.length + 1 < s_L.length
      simp only [List.length_cons, List.length_nil] at hlen_L
      omega
    case' hroom =>
      change (x.2 + n ≤ s_L.len x.1) ∧ (0 + n * n ≤ s_L.len L) ∧
        (0 + n ≤ s_L.len d) ∧ True
      refine ⟨?_, by simpa only [Nat.zero_add] using hL.ge,
        by simpa only [Nat.zero_add] using hd.ge, trivial⟩
      rw [(hbelow_L x.1 hl.2.2).1]
      exact hroom
    intro s₂ hs₂ hB₂
    exact ⟨by simpa only [Nat.add_zero] using hpos, [xs],
      Mem.readBlocks_of_cons (Store.Below.readBlock_of hB₂ hl.2.2 hxs) rfl, hpost⟩
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [[]], Mem.readBlocks_of_cons rfl rfl, ?_⟩
    ext i
    exact i.elim0

omit [Has ScalarOp Op] [Has CmpTst Tst] in
/-- The exact original-system postcondition is the existing componentwise backward-solution
predicate at zero relative allowance and zero diagonal floor. -/
theorem isComponentwiseBackwardSolution_of_solveSpec_post {dec : K → ℝ} {n : ℕ}
    {τ : Tape K} {as bs xs : List K}
    (hpost : (solveSpec dec).post [n] τ [as, bs] [xs]) :
    IsComponentwiseBackwardSolution 0 0 (decodeMatrix dec n n as) (decv dec n bs)
      (decv dec n xs) :=
  IsComponentwiseBackwardSolution.of_mulVec_eq le_rfl le_rfl hpost

end NLAlib.LDL
