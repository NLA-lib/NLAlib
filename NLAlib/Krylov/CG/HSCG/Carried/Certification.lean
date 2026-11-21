/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve
public import NLAlib.Krylov.CG.Standard
public import NLAlib.Krylov.CG.HSCG.Carried.ZeroStart
public import NLAlib.Ops.RoutineProblem

/-!
# Canonical exact carried conjugate gradient

The actual zero-start program stops at the earlier of the cap and exact convergence. A
jointly realized exact standard model and positive-definite operator suffice for every raw
right-hand side. Its mathematical state and full resource bounds concern one execution.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Certification.algorithm`: total exact certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Certification

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- The admitted inputs: at the sizes of `domain`, every right-hand side, a vector of `d 0`
words held by the first operand; the iterate, the residual, the direction and the scalar cache
are blank. The matrix is not stored: it is a parameter of the model. -/
def inputs (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    (zeroStartRoutine (Op := Standard.Operation) (Tst := CmpTst)).Domain K 2 5 where
  valid := domain
  In d := Fin (d 0) → K
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) id, .blank (d 0), .blank (d 0), .blank (d 0),
    .blank 1]
  fits := by domain_fits
  faithful d x y _ h := (Codec.vector (d 0)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := admitted
  inhabited _ _ := ⟨fun _ => default, trivial⟩

/-- The right-hand side and the blank state of the solver: its problem. -/
abbrev problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 5 :=
  (inputs (K := K) domain admitted).problem

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- One fixed exact solver, with actual literal-zero initialization. -/
def program : Program Standard.Operation CmpTst 2 5 := zeroStartRoutine.close 2 5

/-- All calls and allocations use the standard signatures and declared cell storage. -/
theorem wellTyped_program (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    program.wellTyped (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- The full canonical budget, including initialization and structural instructions. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (Standard.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- The original-operation projection retains the explicit zero loop and solver budget.
Structural and addressing charges remain in the full canonical manifest. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) =
      (d 0) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
        solveCount (Op := Standard.Operation) (Tst := CmpTst) (d 0) (d 1) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat,
    zeroStartRoutine, zeroStart, solveRoutine, Program.environment, List.ofFn_succ,
    stmtCost, IExp.evalList,
    IExp.eval, fillRoutine, stmtCost_fillMap,
    staticCost_solve]

/-- The RHS and all supplied output slots occupy `4*n+1` abstract cells. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x = 4 * d 0 + 1 := by
  refine ((inputs (K := K) domain admitted).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, List.ofFn_succ]
  omega

/-- The physical state is the exact recurrence at the earlier of cap and convergence. -/
noncomputable def specification
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0)) :
    Specification Standard.Operation CmpTst (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch := staticPeak model.resources program
  work d := model.resources.work (staticBudget d)
  span d := model.resources.span (staticBudget d)
  memory d := 4 * d 0 + 1 + staticPeak model.resources program d
  good d x _ _ m := m.pos = 0 ∧ StoresState model.decode (d 0)
    (1, 0) (2, 0) (3, 0) (4, 0)
    (cgState (model.matrix d x) (fun i => model.decode (x.val.1 i)) 0
      (min (d 1) (krylovGrade (model.matrix d x) (fun i => model.decode (x.val.1 i))))) m

/-- Exact local contracts and positive definiteness give total canonical CG for every cap
and supplied RHS. Exact convergence is a successful exit before any further division. -/
noncomputable def algorithm
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (hExact : model.scheme = .exact) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ)
    (hresources : model.resources = Standard.resources model.scheme cost work scratch)
    (hPos : ∀ d, domain d → ∀ x, (model.matrix d x).PosDef) :
    Algorithm model.access (specification model) := by
  refine (inputs (K := K) domain admitted).algorithmAt
    (fun d x => zeroStartSpec model.decode (model.matrix d x))
    (ht := by
      change program.wellTyped model.resources (fun _ => .cell) = true
      rw [hresources]; exact wellTyped_program ..) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hM, hBX, hAX, hC⟩ := CG.exact_laws model hExact hI
    exact zeroStartRoutine_meets hS hM hBX hAX hC (hPos d hd x)
  · intro d hd x τ
    exact rfl
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps, vs)
    have hb : decv model.decode (d 0) (List.ofFn x.val.1) =
        fun i => model.decode (x.val.1 i) := decv_ofFn_apply _ _
    rcases vs with _ | ⟨rr, _ | ⟨_, _⟩⟩ <;>
      first
        | exact ⟨hpos, xs', rs, ps, rr, hys, hb ▸ hrel⟩
        | exact False.elim hrel
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Carried.Certification
