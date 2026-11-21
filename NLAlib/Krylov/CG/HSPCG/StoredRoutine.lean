/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Solve
public import NLAlib.Krylov.CG.HSPCG.StoredContext
public import NLAlib.Ops.RoutineData
public import NLAlib.Ops.Blas.Fill

/-!
# Preconditioned conjugate gradient on stored dense matrices

`NLAlib.Krylov.CG.HSPCG.Stored.storedRoutine` reads a system matrix and an inverse
preconditioner, each stored as `n * n` words, and a right-hand side, and writes the iterate, the
residual, the preconditioned residual and the direction: it fills the iterate with literal zeros
and runs the fixed-horizon solver on the stored matrices. That solver is the matrix-free one on
stored data (`NLAlib.Ops.Routine.withData`): the two matrices are isolated operands, in any
buffers different from those of the other operands, each forwarded to its products.

## Main definitions

* `NLAlib.Krylov.CG.HSPCG.Stored.linkedSolveRoutine`: the solver on stored matrices.
* `NLAlib.Krylov.CG.HSPCG.Stored.storedRoutine`, `NLAlib.Krylov.CG.HSPCG.Stored.storedSpec`: the
  routine from the zero iterate and its specification.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Stored.linkedSolveRoutine_meets`: the stored solver meets the
  specification of the matrix-free solver at the matrices decoded from the stored words.
* `NLAlib.Krylov.CG.HSPCG.Stored.storedRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.CG.HSPCG.Stored

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ}

/-- The fixed-horizon solver on stored matrices: the matrix-free solver with the words of the
system matrix and of the inverse preconditioner, `n * n` each, new isolated leading operands
forwarded to their products. -/
def linkedSolveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (HSPCG.solveRoutine (Op := Signature) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0, fun d => d.headD 0 * d.headD 0]
    (StoredContext.table 2 0 1)

/-- Zero the iterate, then solve on the stored matrices. Index variables: `n`, `cap`, then the
offsets of `A`, `P`, `b`, `x`, `r`, `z`, `p`. -/
def zeroStart : Stmt RCLikeBlas.Operation CmpTst := ops% [n, cap] (A, Pm, B) → (X, R, Z, P) {
  run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n] (X);
  run linkedSolveRoutine [n, cap] (A, Pm, B, X, R, Z, P)
}

/-- The matrix of order `d.headD 0` decoded from the `i`-th stored block. -/
noncomputable abbrev storedMatrix (d : List ℕ) (raws : List (List ℝ)) (i : ℕ) :
    Matrix (Fin (d.headD 0)) (Fin (d.headD 0)) ℝ :=
  StoredOperator.denseMatrix (d.headD 0) (d.headD 0) (raws.getD i [])

/-- The specification of the solver on stored matrices: for positive-definite system and
inverse-preconditioner matrices decoded from the stored words, that of the matrix-free solver
at those matrices. -/
noncomputable def linkedSolveSpec : Routine.Spec ℝ :=
  .onData 2 (fun d raws => (storedMatrix d raws 0).PosDef ∧ (storedMatrix d raws 1).PosDef)
    (fun d raws => HSPCG.solveSpec id (storedMatrix d raws 0) (storedMatrix d raws 1))

/-- The stored solver meets its specification: it is the matrix-free solver on stored data, and
under the interpretation in which each product reads the stored words of its matrix that solver
meets its own specification at the decoded matrices (`NLAlib.Ops.Routine.Meets.withData`). -/
theorem linkedSolveRoutine_meets (hS : IsScalar RCLikeBlas.machine I)
    (hB : RCLikeBlas.IsExact I) : linkedSolveRoutine.Meets I linkedSolveSpec :=
  Routine.Meets.withData _ _
    (fun d raws => StoredContext.relation (storedMatrix d raws 0) (storedMatrix d raws 1))
    (fun d => StoredContext.admissible (d.headD 0))
    (fun d raws => StoredContext.fallback (storedMatrix d raws 0) (storedMatrix d raws 1))
    rfl rfl
    (fun d ctx m raws hc hr _ => by
      obtain ⟨a, pm, rfl⟩ := List.length_eq_two.mp hc
      split_reads hr as (rawA, rawP)
      exact StoredContext.guarded_satisfies hS hB [a, pm] ⟨0, by simp⟩ ⟨1, by simp⟩ m.store
        rawA rawP (fun z hz => List.mem_map_of_mem hz) hrawA hrawP)
    (fun d ctx m raws hc hr hPos => by
      obtain ⟨a, pm, rfl⟩ := List.length_eq_two.mp hc
      split_reads hr as (rawA, rawP)
      obtain ⟨hs, hb', hA, hP⟩ := StoredContext.guarded_laws hS hB [a, pm] ⟨0, by simp⟩
        ⟨1, by simp⟩ m.store rawA rawP (fun z hz => List.mem_map_of_mem hz) hrawA hrawP
      exact HSPCG.solveRoutine_meets hs RCLikeBlas.exactModel_real hb' hA hP hPos.1 hPos.2)

/-- Preconditioned conjugate gradient on stored dense matrices from the zero iterate: the words
of the two matrices are isolated, the right-hand side is read, and the iterate, the residual, the
preconditioned residual and the direction are written. -/
def storedRoutine : Routine RCLikeBlas.Operation CmpTst :=
  routine% [n, k] (isolated A : n * n, isolated P : n * n, b : n) →
      (x : n, r : n, z : n, p : n) := zeroStart

/-- For positive-definite system and inverse-preconditioner matrices decoded from the stored
words and a horizon at most the Krylov grade of the preconditioned right-hand side, the written
vectors are the preconditioned conjugate gradient state from the zero iterate. -/
noncomputable def storedSpec (n : ℕ) : Routine.Spec ℝ :=
  spec% [m, k] (rawA, rawP, bs) → (xs', rs, zs, ps)
    requires m = n ∧ (StoredOperator.denseMatrix n n rawA).PosDef ∧
      (StoredOperator.denseMatrix n n rawP).PosDef ∧
      k ≤ krylovGrade
        (StoredOperator.denseMatrix n n rawP * StoredOperator.denseMatrix n n rawA)
        (StoredOperator.denseMatrix n n rawP *ᵥ decv id n bs)
    ensures decodedState id n xs' rs zs ps =
      pcgState (StoredOperator.denseMatrix n n rawA) (StoredOperator.denseMatrix n n rawP)
        (decv id n bs) 0 k

/-- Preconditioned conjugate gradient on stored matrices meets its specification for every
exact scalar and vector interpretation: the iterate is zeroed, then the stored solver runs,
each used by its judgment. -/
theorem storedRoutine_meets (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    {n : ℕ} : storedRoutine.Meets I (storedSpec n) := by
  routine_intro [n', k] (a, pm, b, x, r, z, p) reads (rawA, rawP, bs)
  obtain ⟨hn, hPos, hPPos, hk⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hx0 : decv id n (List.replicate n (RCLikeBlas.machine.lit 0)) = (0 : Fin n → ℝ) := by
    ext i
    simp [decv, vec, i.isLt, RCLikeBlas.machine]
  have hk' : k ≤ krylovGrade
      (StoredOperator.denseMatrix n n rawP * StoredOperator.denseMatrix n n rawA)
      (StoredOperator.denseMatrix n n rawP *ᵥ
        (decv id n bs - StoredOperator.denseMatrix n n rawA *ᵥ
          decv id n (List.replicate n (RCLikeBlas.machine.lit 0)))) := by
    rw [hx0, Matrix.mulVec_zero, sub_zero]
    exact hk
  call (fillRoutine_meets (Tst := CmpTst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (RCLikeBlas.machine.lit 0) := hzero
  call (linkedSolveRoutine_meets hS hB) [n, k] (a, pm, b, x, r, z, p)
    (pre := ⟨⟨hPos, hPPos⟩, rfl, hk'⟩) as m₂ hfr₂ hpos₂ (xs', rs, zs, ps) hst
  routine_exit
  have hst : decodedState id n xs' rs zs ps =
      pcgState (StoredOperator.denseMatrix n n rawA) (StoredOperator.denseMatrix n n rawP)
        (decv id n bs) (decv id n (List.replicate n (RCLikeBlas.machine.lit 0))) k := hst
  rw [hx0] at hst
  exact hst

end NLAlib.Krylov.CG.HSPCG.Stored
