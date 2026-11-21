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

variable (A B : (d : Fin 2 → ℕ) → Matrix (Fin (d 0)) (Fin (d 0)) ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- The admitted right-hand sides: the horizon is at most the preconditioned Krylov grade. -/
def accepts (d : Fin 2 → ℕ) (rhs : Fin (d 0) → ℝ) : Prop :=
  d 1 ≤ krylovGrade (B d * A d) ((B d) *ᵥ rhs)

variable (supply : ∀ d, domain d → ∃ rhs : Fin (d 0) → ℝ, accepts A B d rhs)

/-- The admitted inputs of preconditioned conjugate gradient: at the sizes of `domain`, every
right-hand side whose preconditioned Krylov grade is at least the horizon, held by the first
operand; the four state vectors are blank. The matrices `A d` and `B d` are not stored: they
are parameters of the model. -/
noncomputable def inputs : (zeroStartRoutine (Op := Signature) (Tst := Empty)).Domain ℝ 2 5 where
  valid := domain
  In d := Fin (d 0) → ℝ
  accepts := accepts A B
  slot d := ![.stored (Codec.vector (d 0)) id, .blank (d 0), .blank (d 0), .blank (d 0),
    .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := (Codec.vector (d 0)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := admitted
  inhabited := supply

/-- The right-hand side and four blank state vectors: the problem of preconditioned conjugate
gradient. -/
noncomputable abbrev problem : Problem ℝ 2 5 := (inputs A B domain admitted supply).problem

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
    (x : (problem A B domain admitted supply).Input d) :
    (problem A B domain admitted supply).initialBytes d x = 5 * d 0 := by
  refine ((inputs A B domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, List.ofFn_succ]
  omega

/-- The same counted run returns the full physical PCG state at the prescribed horizon. -/
noncomputable def specification (R : ResourceModel Signature Empty) :
    Specification Signature Empty (problem A B domain admitted supply) where
  budget := staticBudget
  scratch := staticPeak R program
  work d := R.work (staticBudget d)
  span d := R.span (staticBudget d)
  memory d := 5 * d 0 + staticPeak R program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (1, 0) (2, 0) (3, 0) (4, 0)
    (pcgState (A d) (B d) x.val.1 0 (d 1)) m

/-- Positive-definite system and inverse preconditioner matrices give successful canonical
PCG for every raw input in its explicitly inhabited grade-bounded horizon domain. No success
or numerical execution witness is an assumption. Both operators retain separate charges. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ)
    (hA : ∀ d, domain d → (A d).PosDef) (hB : ∀ d, domain d → (B d).PosDef) :
    Algorithm
      (Model.exactModel (problem A B domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun d _ => B d) (Model.resources cost aw ap sw sp))
      (specification A B domain admitted supply (Model.resources cost aw ap sw sp)) := by
  refine (inputs A B domain admitted supply).algorithm
    (fun d _ => zeroStartSpec id (A d) (B d)) (ht := wellTyped_program ..) ?_ ?_ ?_
    (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, hPrec⟩ := Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp hPrec (hA d hd) (hB d hd)
  · intro d hd x hx τ
    refine ⟨rfl, ?_⟩
    exact le_of_le_of_eq hx (congrArg (fun v => krylovGrade (B d * A d) ((B d) *ᵥ v))
      (decv_ofFn (n := d 0) x).symm)
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, zs, ps)
    have h : decodedState id (d 0) xs' rs zs ps = pcgState (A d) (B d) x.val.1 0 (d 1) :=
      Eq.trans hrel (congrArg (fun v => pcgState (A d) (B d) v 0 (d 1))
        (decv_ofFn (n := d 0) x.val.1))
    exact ⟨hpos, xs', rs, zs, ps,
      Mem.readBlocks_of_cons hxs' (Mem.readBlocks_of_cons hrs
        (Mem.readBlocks_of_cons hzs (Mem.readBlocks_of_cons hps rfl))), h⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-- **The oracles of the model.** The matrix `A d` and the preconditioner `B d` are in no
buffer: they are parameters of the certificate, reached only through their two products. Scalar
arithmetic and the vector operations have one contract at every size and input, and the
contract of a product does not depend on the input of the problem. The cost of the certificate
is counted in calls of the two products. -/
noncomputable def oracles (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    (inputs A B domain admitted supply).Oracles
      (Model.exactModel (problem A B domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun d _ => B d) (Model.resources cost aw ap sw sp)) where
  ops := [.operator, .preconditioner]
  operation o ho d x d' x' := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator => exact absurd (by simp) ho
    | preconditioner => exact absurd (by simp) ho
  query _ _ _ _ q := nomatch q
  through o _ d X Y _ := by cases o <;> rfl

end NLAlib.Krylov.CG.HSPCG.Certification
