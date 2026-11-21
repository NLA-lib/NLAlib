/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Krylov.CG.HorizonProblem
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

/-- Admissible raw words satisfy only the fixed-horizon mathematical grade restriction. -/
def accepts (d : Fin 2 → ℕ) (rhs : List ℝ) : Prop :=
  d 1 ≤ krylovGrade (B d * A d) ((B d) *ᵥ decv id (d 0) rhs)

variable (supply : ∀ d, domain d → ∃ rhs : List ℝ, rhs.length = d 0 ∧ accepts A B d rhs)

/-- RHS plus four uninitialized state vectors, with an explicitly inhabited input domain. -/
noncomputable def problem : Problem ℝ 2 5 :=
  CG.RawProblem.restricted (fun d => ![0, d 0, d 0, d 0, d 0]) domain admitted
    (accepts A B) supply

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
  change (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0, d 0]) domain admitted).initialBytes
    d (CG.RawProblem.forgetInput x) = _
  rw [CG.RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
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
    (pcgState (A d) (B d) (decv id (d 0) x.val.1) 0 (d 1)) m

/-- Positive-definite system and inverse preconditioner matrices give successful canonical
PCG for every raw input in its explicitly inhabited grade-bounded horizon domain. No success
or numerical execution witness is an assumption. Both operators retain separate charges. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ)
    (hA : ∀ d, domain d → (A d).PosDef) (hB : ∀ d, domain d → (B d).PosDef) :
    Algorithm
      (Model.exactModel (problem A B domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun d _ => B d) (Model.resources cost aw ap sw sp))
      (specification A B domain admitted supply (Model.resources cost aw ap sw sp)) := by
  refine Routine.algorithm (r := 2) (b := 5) zeroStartRoutine
    (fun d _ => zeroStartSpec id (A d) (B d))
    (fun _ x => [x.val.1]) (ht := wellTyped_program ..) ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, hPrec⟩ := Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp hPrec (hA d hd) (hB d hd)
  · intro d hd x
    let μ := (problem A B domain admitted supply).initial d x
    let raw := CG.RawProblem.forgetInput x
    have hμ :
        (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0, d 0]) domain admitted).initial d raw =
          μ :=
      rfl
    have hlen (i : Fin 5) : μ.store.len i = if i = 0 then d 0 else ![0, d 0, d 0, d 0, d 0] i := by
      rw [← hμ]
      exact CG.RawProblem.initial_len d raw i
    refine ⟨Mem.readBlocks_of_cons (CG.RawProblem.initial_readBlock d raw) rfl,
      fun _ => ⟨rfl, x.property.2⟩, ?_⟩
    change μ.Room [(1, 0), (2, 0), (3, 0), (4, 0)] [d 0, d 0, d 0, d 0]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ, raw] using (hlen 1).ge, by simpa [μ, raw] using (hlen 2).ge,
      by simpa [μ, raw] using (hlen 3).ge, by simpa [μ, raw] using (hlen 4).ge⟩
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, zs, ps)
    exact ⟨hpos, xs', rs, zs, ps, hys, hrel⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSPCG.Certification
