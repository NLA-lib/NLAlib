/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Solve
public import NLAlib.Ops.Profiles.ContextLinearGuarded
public import NLAlib.Ops.RoutineData
public import NLAlib.Ops.Blas.Fill

/-!
# Conjugate gradient on a stored dense matrix

`NLAlib.Krylov.CG.HSCG.Stored.zeroStartRoutine` reads a matrix stored as `n * n` words and a
right-hand side, and writes the iterate, the residual and the direction: it fills the iterate
with literal zeros and runs the fixed-horizon solver on the stored matrix. That solver is the
matrix-free one on stored data (`NLAlib.Ops.Routine.withData`): the matrix is an isolated
operand, in any buffer different from those of the other operands, forwarded to every product.

## Main definitions

* `NLAlib.Krylov.CG.HSCG.Stored.solveRoutine`: the solver on a stored matrix.
* `NLAlib.Krylov.CG.HSCG.Stored.zeroStartRoutine`, `NLAlib.Krylov.CG.HSCG.Stored.zeroStartSpec`: the
  routine from the zero iterate and its specification.

## Main results

* `NLAlib.Krylov.CG.HSCG.Stored.solveRoutine_meets`: the stored solver meets the
  specification of the matrix-free solver at the matrix decoded from the stored words.
* `NLAlib.Krylov.CG.HSCG.Stored.zeroStartRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.CG.HSCG.Stored

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ}

/-- The fixed-horizon solver on a stored matrix: the matrix-free solver with the matrix words,
`n * n` of them, a new isolated leading operand forwarded to every product. -/
def solveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (HSCG.solveRoutine (Op := Standard.Operation) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0] (ContextLinear.table 1 0)

/-- Zero the iterate, then solve on the stored matrix. Index variables: `n`, `cap`, then the
offsets of `A`, `b`, `x`, `r`, `p`. -/
def zeroStart : Stmt RCLikeBlas.Operation CmpTst := ops% [n, cap] (A, B) → (X, R, P) {
  run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n] (X);
  run solveRoutine [n, cap] (A, B, X, R, P)
}

/-- The specification of the solver on a stored matrix: for a positive-definite matrix decoded
from the stored words, that of the matrix-free solver at that matrix. -/
noncomputable def solveSpec : Routine.Spec ℝ :=
  .onData 1
    (fun d raws =>
      (StoredOperator.denseMatrix (d.headD 0) (d.headD 0) (raws.headD [])).PosDef)
    (fun d raws =>
      HSCG.solveSpec id (StoredOperator.denseMatrix (d.headD 0) (d.headD 0) (raws.headD [])))

/-- The stored solver meets its specification: it is the matrix-free solver on stored data, and
under the interpretation in which a product reads the stored words that solver meets its own
specification at the decoded matrix (`NLAlib.Ops.Routine.Meets.withData`). -/
theorem solveRoutine_meets (hS : IsScalar RCLikeBlas.machine I)
    (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I) :
    solveRoutine.Meets I solveSpec :=
  Routine.Meets.withData _ _
    (fun d raws =>
      ContextLinear.relation (StoredOperator.denseMatrix (d.headD 0) (d.headD 0) (raws.headD [])))
    (fun d => ContextLinear.admissible (d.headD 0))
    (fun d raws =>
      ContextLinear.fallback (StoredOperator.denseMatrix (d.headD 0) (d.headD 0) (raws.headD [])))
    rfl rfl
    (fun d ctx m raws hc hr _ => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      exact ContextLinear.guarded_satisfies hS hB [a] ⟨0, by simp⟩ m.store raw
        (fun z hz => List.mem_map_of_mem hz) hraw)
    (fun d ctx m raws hc hr hPos => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
      split_reads hr as (raw)
      obtain ⟨hs, hb', hA, -⟩ := ContextLinear.guarded_laws hS hB hCmp [a] ⟨0, by simp⟩
        m.store raw (fun z hz => List.mem_map_of_mem hz) hraw
      exact HSCG.solveRoutine_meets hs RCLikeBlas.exactModel_real hb' hA hPos)

/-- Conjugate gradient on a stored dense matrix from the zero iterate: the matrix words are
isolated, the right-hand side is read, and the iterate, the residual and the direction are
written. -/
def zeroStartRoutine : Routine RCLikeBlas.Operation CmpTst :=
  routine% [n, k] (isolated A : n * n, b : n) → (x : n, r : n, p : n) := zeroStart

/-- For a positive-definite matrix decoded from the stored words and a horizon `k` at most the
Krylov grade of the right-hand side, the three written vectors are the conjugate gradient state
after `k` steps from the zero iterate. -/
noncomputable def zeroStartSpec (n : ℕ) : Routine.Spec ℝ :=
  spec% [m, k] (raw, bs) → (xs, rs, ps)
    requires m = n ∧ (StoredOperator.denseMatrix n n raw).PosDef ∧
      k ≤ krylovGrade (StoredOperator.denseMatrix n n raw) (decv id n bs)
    ensures HSCG.decodedState id n xs rs ps =
      cgState (StoredOperator.denseMatrix n n raw) (decv id n bs) 0 k

/-- Conjugate gradient on a stored matrix meets its specification for every exact scalar and
vector interpretation: the iterate is zeroed, then the stored solver runs, each used by its
judgment. -/
theorem zeroStartRoutine_meets (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (hCmp : IsCmp id I) {n : ℕ} : zeroStartRoutine.Meets I (zeroStartSpec n) := by
  routine_intro [n', k] (a, b, x, r, p) reads (raw, bs)
  obtain ⟨hn, hPos, hk⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hx0 : decv id n (List.replicate n (RCLikeBlas.machine.lit 0)) = (0 : Fin n → ℝ) := by
    ext i
    simp [decv, vec, i.isLt, RCLikeBlas.machine]
  have hk' : k ≤ krylovGrade (StoredOperator.denseMatrix n n raw)
      (decv id n bs - StoredOperator.denseMatrix n n raw *ᵥ
        decv id n (List.replicate n (RCLikeBlas.machine.lit 0))) := by
    rw [hx0, Matrix.mulVec_zero, sub_zero]
    exact hk
  call (fillRoutine_meets (Tst := CmpTst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (RCLikeBlas.machine.lit 0) := hzero
  call (solveRoutine_meets hS hB hCmp) [n, k] (a, b, x, r, p)
    (pre := ⟨hPos, rfl, hk'⟩) as m₂ hfr₂ hpos₂ (xs', rs, ps) hst
  routine_exit
  have hst : HSCG.decodedState id n xs' rs ps = cgState (StoredOperator.denseMatrix n n raw)
      (decv id n bs) (decv id n (List.replicate n (RCLikeBlas.machine.lit 0))) k := hst
  rw [hx0] at hst
  exact hst

end NLAlib.Krylov.CG.HSCG.Stored
