/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Krylov.CG.HSPCG.ZeroStart

/-!
# Canonical exact fixed-horizon PCG

Raw RHS admissibility states the existing mathematical grade restriction and has an explicit
inhabitant at each admitted size. The program initializes its iterate, applies both distinct
operators, and returns the actual PCG state with full canonical resource accounting.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Certification.algorithm`: total fixed-horizon PCG certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Certification

open Ops
open scoped Matrix

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- The inputs at the sizes: the matrix, the inverse preconditioner and the right-hand side. -/
abbrev System (d : Fin 2 → ℕ) : Type :=
  Matrix (Fin (d 0)) (Fin (d 0)) ℝ × Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)

/-- The admitted systems: the matrix and the inverse preconditioner are positive definite and
the horizon is at most the preconditioned Krylov grade of the right-hand side. -/
def accepts (d : Fin 2 → ℕ) (x : System d) : Prop :=
  x.1.PosDef ∧ x.2.1.PosDef ∧ d 1 ≤ krylovGrade (x.2.1 * x.1) (x.2.1 *ᵥ x.2.2)

variable (supply : ∀ d, domain d → ∃ x : System d, accepts d x)

/-- The admitted inputs of preconditioned conjugate gradient: at the sizes of `domain`, every
positive-definite matrix and inverse preconditioner and every right-hand side whose
preconditioned Krylov grade is at least the horizon. The right-hand side is held by the first
operand; the four state vectors are blank. The two matrices are the declared unstored inputs:
they are in no buffer and are reached only through their products
(`NLAlib.Krylov.CG.HSPCG.Certification.oracles`). -/
noncomputable def inputs : (zeroStartRoutine (Op := Signature) (Tst := Empty)).Domain ℝ 2 5 where
  valid := domain
  In := System
  accepts := accepts
  slot d := ![.stored (Codec.vector (d 0)) (fun x => x.2.2), .blank (d 0), .blank (d 0),
    .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  Unstored d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × Matrix (Fin (d 0)) (Fin (d 0)) ℝ
  unstored _ x := (x.1, x.2.1)
  faithful d x y hu h := Prod.ext (Prod.ext_iff.mp hu).1 (Prod.ext (Prod.ext_iff.mp hu).2
    ((Codec.vector (d 0)).encode_injective (by
      have h0 := h 0
      simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] using h0)))
  admitted := admitted
  inhabited := supply

/-- The right-hand side and four blank state vectors: the problem of preconditioned conjugate
gradient. -/
noncomputable abbrev problem : Problem ℝ 2 5 := (inputs domain admitted supply).problem

/-- One fixed PCG tree, including visible zero-iterate initialization. -/
def program : Program Signature Empty 2 5 := zeroStartRoutine.close 2 5

/-- The fixed wrapper uses exactly the declared scalar, BLAS and two operator signatures. -/
theorem wellTyped_program (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    program.wellTyped (Model.resources cost aw ap sw sp) (fun _ => .cell) = true := by
  rfl

/-- Full canonical original, query and structural instruction budget. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) : Count (Signature ⊕ Bookkeeping) Empty :=
  staticCost program d

/-- The original-operation projection retains the explicit zero loop and solver budget.
Structural and addressing charges remain in the full canonical manifest. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) =
      (d 0) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
        solveCount (Op := Signature) (Tst := Empty) (d 0) (d 1) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat,
    zeroStartRoutine, zeroStart, solveRoutine, Program.environment, List.ofFn_succ,
    stmtCost, IExp.evalList,
    IExp.eval, fillRoutine, stmtCost_fillMap,
    staticCost_solve]

/-- The declared initial vector payload occupies five length-n buffers. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = 5 * d 0 := by
  refine ((inputs domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, List.ofFn_succ]
  omega

/-- The same counted run returns the full physical PCG state at the prescribed horizon. -/
noncomputable def specification (R : ResourceModel Signature Empty) :
    Specification Signature Empty (problem domain admitted supply) where
  budget := staticBudget
  scratch := staticPeak R program
  work d := R.work (staticBudget d)
  span d := R.span (staticBudget d)
  memory d := 5 * d 0 + staticPeak R program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (1, 0) (2, 0) (3, 0) (4, 0)
    (pcgState x.val.1.1 x.val.1.2.1 x.val.1.2.2 0 (d 1)) m

/-- Preconditioned conjugate gradient succeeds on every admitted system: positive-definite
matrix and inverse preconditioner, and a right-hand side whose preconditioned Krylov grade is at
least the horizon. No success or numerical execution witness is an assumption. Both operators
retain separate charges. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    Algorithm
      (Model.exactModel (problem domain admitted supply) (fun d => d 0)
        (fun _ X => X.val.1.1) (fun _ X => X.val.1.2.1) (Model.resources cost aw ap sw sp))
      (specification domain admitted supply (Model.resources cost aw ap sw sp)) := by
  refine (inputs domain admitted supply).algorithm
    (fun d x => zeroStartSpec id x.1 x.2.1) (ht := wellTyped_program ..) ?_ ?_ ?_
    (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, hPrec⟩ := Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp hPrec x.property.1.1
      x.property.1.2.1
  · intro d hd x hx τ
    refine ⟨rfl, ?_⟩
    exact le_of_le_of_eq hx.2.2 (congrArg (fun v => krylovGrade (x.2.1 * x.1) (x.2.1 *ᵥ v))
      (decv_ofFn (n := d 0) x.2.2).symm)
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, zs, ps)
    have h : decodedState id (d 0) xs' rs zs ps =
        pcgState x.val.1.1 x.val.1.2.1 x.val.1.2.2 0 (d 1) :=
      Eq.trans hrel (congrArg (fun v => pcgState x.val.1.1 x.val.1.2.1 v 0 (d 1))
        (decv_ofFn (n := d 0) x.val.1.2.2))
    exact ⟨hpos, xs', rs, zs, ps,
      Mem.readBlocks_of_cons hxs' (Mem.readBlocks_of_cons hrs
        (Mem.readBlocks_of_cons hzs (Mem.readBlocks_of_cons hps rfl))), h⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-- The oracles of the model. The matrix and the inverse preconditioner are the unstored
inputs: they are in no buffer and are reached only through their two products. Scalar arithmetic
and the vector operations have one contract at every size and input, and the contract of a
product depends on the input only through the two matrices. The cost of the certificate is
counted in calls of the two products. -/
noncomputable def oracles (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    (inputs domain admitted supply).Oracles
      (Model.exactModel (problem domain admitted supply) (fun d => d 0)
        (fun _ X => X.val.1.1) (fun _ X => X.val.1.2.1) (Model.resources cost aw ap sw sp)) where
  ops := [.operator, .preconditioner]
  operation o ho d x d' x' := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator => exact absurd (by simp) ho
    | preconditioner => exact absurd (by simp) ho
  query _ _ _ _ q := nomatch q
  through o _ d X Y h := by
    have h' : (X.val.1.1, X.val.1.2.1) = (Y.val.1.1, Y.val.1.2.1) := h
    have hA : X.val.1.1 = Y.val.1.1 := (Prod.ext_iff.mp h').1
    have hB : X.val.1.2.1 = Y.val.1.2.1 := (Prod.ext_iff.mp h').2
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator =>
      change (matvecRel id X.val.1.1).spec _ = (matvecRel id Y.val.1.1).spec _
      rw [hA]
    | preconditioner =>
      change (matvecRel id X.val.1.2.1).spec _ = (matvecRel id Y.val.1.2.1).spec _
      rw [hB]

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Inputs.Checked`). The matrix and the preconditioner are in no buffer:
they are reached only through the two product operations, and the work is counted in calls of
them (`NLAlib.Krylov.CG.HSPCG.Certification.oracles`). -/
theorem algorithm_checked (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    (inputs domain admitted supply).Checked
      (algorithm domain admitted supply cost aw ap sw sp) :=
  (inputs domain admitted supply).checked_all _

end NLAlib.Krylov.CG.HSPCG.Certification
