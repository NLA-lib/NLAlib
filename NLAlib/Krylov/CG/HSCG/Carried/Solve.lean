/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Initialization
public import NLAlib.Krylov.CG.HSCG.Carried.Rounds

/-!
# Total exact CG with early convergence before an arbitrary cap

The program initializes all state from the right-hand side and initial iterate. Positive
definiteness and the exact operation models imply successful execution for every cap. The
loop stops at a zero residual before evaluating another division, so the cap may exceed the
initial Krylov grade. [HestenesStiefel1952, (3:1)].

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.solveRoutine_meets` certifies total successful execution.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve` gives the computed iterate and operation budget.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve_dim` solves the SPD system with cap equal to dimension.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The capped solver as a routine: the right-hand side is read, the iterate updated in place,
the residual, the direction and the cell of the retained residual product written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n, x : n) → (x, r : n, p : n, rho : 1) := solve

/-- At the dimension of the matrix, the written state is the recurrence at the earlier of the
cap and exact convergence, with its retained residual product. -/
noncomputable def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, cap] (bs, xs) → (xs', rs, ps, [v])
    requires m = n
    ensures decodedState dec n xs' rs ps = cgState A (decv dec n bs) (decv dec n xs)
        (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))) ∧
      dec v = decv dec n rs ⬝ᵥ decv dec n rs

/-- The complete solver is total for every SPD input and cap under the stated operation models;
there is no success premise or restriction on the cap. Initialization, then the capped loop,
each used by its judgment. -/
theorem solveRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) :
    (solveRoutine (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A) := by
  routine_intro [n', cap] (b, x, r, p, v) reads (bs, xs)
  obtain rfl : n = n' := hpre.symm
  call (initializeRoutine_meets (Tst := Tst) (A := A) hS hM hB hA) [n] (b, x, r, p, v)
    (pre := rfl) as m₁ hfr₁ hpos₁ (xs₁, rs₁, ps₁, vs₁) hst₁
  obtain ⟨rr₁, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs₁)
  have hst₁ : decodedState dec n xs₁ rs₁ ps₁ = cgState A (decv dec n bs) (decv dec n xs) 0 ∧
      dec rr₁ = decv dec n rs₁ ⬝ᵥ decv dec n rs₁ := hst₁
  call (roundsRoutine_meets hS hM hB hA hCmp hPos (decv dec n bs) (decv dec n xs)) [n, cap]
    (x, r, p, v) (pre := ⟨rfl, hst₁.1, hst₁.2⟩) as m₂ hfr₂ hpos₂ (xs₂, rs₂, ps₂, vs₂) hst₂
  obtain ⟨rr₂, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs₂)
  routine_exit
  exact hst₂

/-- From ordinary inputs, the capped early-exit program successfully computes the CG iterate
at the earlier of cap and convergence, within its static operation and scratch budget. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {cap : ℕ} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [b, x, x, r, p, v]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) := by
  have hw := (solveRoutine_meets hS hM hB hA hCmp hPos) [n, cap] [b, x, r, p, v] τ μ [bs, xs]
    rfl rfl hl (by routine_sep) (by reads) rfl hz
  obtain ⟨μ', hrun, hpos, ys, hys, hrel⟩ := hw.wp fun _ _ h => h
  routine_nf at hys
  split_reads hys as (xs', rs, ps, vs)
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧
    ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
      decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
        (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))))
    hrun ⟨hpos, xs', hxs', ?_⟩ W).mono (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) fun _ h => h
  exact (congrArg CGState.x hrel.1).trans (hPos.cgState_x_eq _ _ _)

/-- With the vector dimension as cap, SPD CG successfully returns a solution of `A*x=b`.
Exact convergence may stop it earlier, including before the first round. -/
theorem runs_solve_dim {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I W τ solve (Env.frame [n, n] [b, x, x, r, p, v]) μ
      (solveCount n n) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        A *ᵥ decv dec n ys = decv dec n bs) := by
  refine (runs_solve hS hM hB hA hCmp hPos W (τ := τ) (cap := n)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  have hg : krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs) ≤ n := by
    simpa using krylovGrade_le_card A (decv dec n bs - A *ᵥ decv dec n xs)
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.mulVec_cgIterate_eq_of_krylovGrade_le _ _ (Nat.le_min.mpr ⟨hg, le_rfl⟩)

end NLAlib.Krylov.CG.HSCG.Carried
