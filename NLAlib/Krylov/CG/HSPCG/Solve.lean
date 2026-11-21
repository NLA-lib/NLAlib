/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Initialization
public import NLAlib.Krylov.CG.HSPCG.Rounds

/-!
# Exact fixed-horizon preconditioned conjugate gradient

The complete program initializes its residual and direction, then invokes the certified
round loop. For a positive-definite matrix and a horizon at most the initial Krylov grade,
the output is the existing mathematical PCG iterate. The horizon condition ensures that
every executed scalar division has a nonzero divisor, including when the final round reaches
the exact solution.

## Main results

* `NLAlib.Krylov.CG.HSPCG.solveRoutine_meets` certifies the complete program.
* `NLAlib.Krylov.CG.HSPCG.runs_solve` states the PCG iterate and evaluated operation budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The solver as a routine: the right-hand side is read, the iterate updated in place, the
residual, the preconditioned residual and the direction written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, k] (b : n, x : n) → (x, r : n, z : n, p : n) := solve

/-- At the dimension of the matrix and a horizon at most the Krylov grade of the preconditioned
initial residual, the written state is the preconditioned state at the horizon. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, k] (bs, xs) → (xs', rs, zs, ps)
    requires m = n ∧
      k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs))
    ensures decodedState dec n xs' rs zs ps =
      pcgState A P (decv dec n bs) (decv dec n xs) k

/-- The complete program meets its specification for every exact operation interpretation and
every positive-definite matrix and preconditioner: initialization, then the rounds, each used
by its judgment. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A P) := by
  routine_intro [n', k] (b, x, r, z, p) reads (bs, xs)
  obtain ⟨hn, hk⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hinit := initializeRoutine_meets (Op := Op) (Tst := Tst) (A := A) hS hM hB hA hP
  have hrounds := roundsRoutine_meets (Op := Op) (Tst := Tst) hS hM hB hA hP
  call hinit [n] (b, x, r, z, p) (pre := rfl) as m₁ hfr₁ hpos₁ (xs₁, rs₁, zs₁, ps₁) hst₁
  have hst₁ : decodedState dec n xs₁ rs₁ zs₁ ps₁ =
      pcgState A P (decv dec n bs) (decv dec n xs) 0 := hst₁
  have hnb (j : ℕ) (hj : j < k) :
      Nonbreakdown A ((pcgStep A P)^[j] (decodedState dec n xs₁ rs₁ zs₁ ps₁)) := by
    rw [hst₁, iterate_pcgStep_pcgState, Nat.zero_add]
    exact hPos.pcgState_nonbreakdown hPPos _ _ (by omega)
  call hrounds [n, k] (x, r, z, p) (pre := ⟨rfl, hnb⟩)
    as m₂ hfr₂ hpos₂ (xs₂, rs₂, zs₂, ps₂) hst₂
  routine_exit
  have hst₂ : decodedState dec n xs₂ rs₂ zs₂ ps₂ =
      (pcgStep A P)^[k] (decodedState dec n xs₁ rs₁ zs₁ ps₁) := hst₂
  rw [hst₁, iterate_pcgStep_pcgState, Nat.zero_add] at hst₂
  exact hst₂

/-- For any exact interpretation, the fixed-horizon program computes the PCG iterate, with
the evaluator-derived operation counts and workspace. The horizon may reach the initial
residual's Krylov grade. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, z, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = pcgIterate A P (decv dec n bs) (decv dec n xs) k) := by
  have hw := (solveRoutine_meets hS hM hB hA hP hPos hPPos) [n, k] [b, x, r, z, p] τ μ [bs, xs]
    rfl rfl hl (by routine_sep) (by reads) ⟨rfl, hk⟩ hz
  obtain ⟨μ', hrun, hpos, ys, hys, hrel⟩ := hw.wp fun _ _ h => h
  routine_nf at hys
  split_reads hys as (xs', rs, zs, ps)
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧
    ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
      decv dec n ys = pcgIterate A P (decv dec n bs) (decv dec n xs) k)
    hrun ⟨hpos, xs', hxs', ?_⟩ W).mono (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) fun _ h => h
  exact (congrArg PCGState.x hrel).trans (hPos.pcgState_x_eq hPPos _ _ _)

end NLAlib.Krylov.CG.HSPCG
