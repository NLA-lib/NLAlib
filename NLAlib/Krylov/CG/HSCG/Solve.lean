/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Initialization
public import NLAlib.Krylov.CG.HSCG.Rounds

/-!
# Exact fixed-horizon Hestenes–Stiefel conjugate gradient

The complete program initializes its residual and direction, then invokes the certified
round loop. For a positive-definite matrix and a horizon at most the initial Krylov grade,
the output is the existing mathematical CG iterate. The horizon condition ensures that
every executed scalar division has a nonzero divisor, including when the final round reaches
the exact solution.

## Main results

* `NLAlib.Krylov.CG.HSCG.solveRoutine_meets` certifies the complete program.
* `NLAlib.Krylov.CG.HSCG.runs_solve` states the CG iterate and evaluated operation budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The solver as a routine: the right-hand side is read, the iterate updated in place, the
residual and the direction written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, k] (b : n, x : n) → (x, r : n, p : n) := solve

/-- At the dimension of the matrix and a horizon at most the Krylov grade of the initial
residual, the written state is the conjugate gradient state at the horizon. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, k] (bs, xs) → (xs', rs, ps)
    requires m = n ∧ k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)
    ensures decodedState dec n xs' rs ps = cgState A (decv dec n bs) (decv dec n xs) k

/-- The complete program meets its specification for every exact operation interpretation and
every positive-definite matrix: initialization, then the rounds, each used by its judgment. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) (hPos : A.PosDef) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A) := by
  routine_intro [n', k] (b, x, r, p) reads (bs, xs)
  obtain ⟨hn, hk⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hinit := initializeRoutine_meets (Op := Op) (Tst := Tst) (A := A) hS hM hB hA
  have hrounds := roundsRoutine_meets (Op := Op) (Tst := Tst) hS hM hB hA
  call hinit [n] (b, x, r, p) (pre := rfl) as m₁ hfr₁ hpos₁ (xs₁, rs₁, ps₁) hst₁
  have hst₁ : decodedState dec n xs₁ rs₁ ps₁ = cgState A (decv dec n bs) (decv dec n xs) 0 :=
    hst₁
  have hnb (j : ℕ) (hj : j < k) :
      Nonbreakdown A ((cgStep A)^[j] (decodedState dec n xs₁ rs₁ ps₁)) := by
    rw [hst₁, iterate_cgStep_cgState, Nat.zero_add]
    exact hPos.cgState_nonbreakdown _ _ (by omega)
  call hrounds [n, k] (x, r, p) (pre := ⟨rfl, hnb⟩) as m₂ hfr₂ hpos₂ (xs₂, rs₂, ps₂) hst₂
  routine_exit
  have hst₂ : decodedState dec n xs₂ rs₂ ps₂ =
      (cgStep A)^[k] (decodedState dec n xs₁ rs₁ ps₁) := hst₂
  rw [hst₁, iterate_cgStep_cgState, Nat.zero_add] at hst₂
  exact hst₂

/-- For any exact interpretation, the fixed-horizon program computes the CG iterate, with
the evaluator-derived operation counts and workspace. The horizon may reach the initial
residual's Krylov grade. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs) k) := by
  have hw := (solveRoutine_meets hS hM hB hA hPos) [n, k] [b, x, r, p] τ μ [bs, xs] rfl rfl hl
    (by routine_sep) (by reads) ⟨rfl, hk⟩ hz
  obtain ⟨μ', hrun, hpos, ys, hys, hrel⟩ := hw.wp fun _ _ h => h
  routine_nf at hys
  split_reads hys as (xs', rs, ps)
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧
    ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
      decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs) k)
    hrun ⟨hpos, xs', hxs', ?_⟩ W).mono (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) fun _ h => h
  exact (congrArg CGState.x hrel).trans (hPos.cgState_x_eq _ _ _)

end NLAlib.Krylov.CG.HSCG
