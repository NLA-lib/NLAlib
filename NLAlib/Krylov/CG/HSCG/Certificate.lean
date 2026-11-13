/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Krylov.CG.HSCG.Solve
public import NLAlib.Krylov.CG.HorizonProblem
public import NLAlib.Krylov.CG.ZeroStart

/-!
# Canonical exact fixed-horizon conjugate gradient

Raw RHS admissibility states the existing mathematical grade restriction and has an explicit
inhabitant at each admitted size. The program initializes its iterate, applies both distinct
operator, and returns the actual CG state with full canonical resource accounting.

## Main results

* `NLAlib.Krylov.CG.HSCG.Certification.algorithm`: total fixed-horizon CG certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Certification

open Ops
open scoped Matrix

variable (A : (d : Fin 2 → ℕ) → Matrix (Fin (d 0)) (Fin (d 0)) ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- Admissible raw words satisfy only the fixed-horizon mathematical grade restriction. -/
def accepts (d : Fin 2 → ℕ) (rhs : List ℝ) : Prop :=
  d 1 ≤ krylovGrade (A d) (decv id (d 0) rhs)

variable (supply : ∀ d, domain d → ∃ rhs : List ℝ, rhs.length = d 0 ∧ accepts A d rhs)

/-- RHS plus three uninitialized state vectors, with an explicitly inhabited input domain. -/
noncomputable def problem : Problem ℝ 2 4 :=
  CG.RawProblem.restricted (fun d => ![0, d 0, d 0, d 0]) domain admitted
    (accepts A) supply

/-- One fixed CG tree, including visible zero-iterate initialization. -/
def program : Program HSPCG.Signature Empty 2 4 :=
  ⟨.seq (.frame [.var 0] [⟨1, .var 3⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩ ]
      solve)⟩

/-- The fixed wrapper uses exactly the declared scalar, BLAS and two operator signatures. -/
theorem wellTyped_program (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    program.wellTyped (HSPCG.Model.resources cost aw ap sw sp) (fun _ => .cell) = true := by
  rfl

/-- Full canonical original, query and structural instruction budget. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) : Count (HSPCG.Signature ⊕ Bookkeeping) Empty :=
  staticCost program d

/-- The original-operation projection retains the explicit zero loop and solver budget.
Structural and addressing charges remain in the full canonical manifest. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) =
      (d 0) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
        solveCount (Op := HSPCG.Signature) (Tst := Empty) (d 0) (d 1) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  simp [program, Program.environment, List.ofFn_succ, stmtCost, IExp.evalList,
    IExp.eval, CG.staticCost_zeroVector,
    staticCost_solve]

/-- The declared initial vector payload occupies four length-n buffers. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem A domain admitted supply).Input d) :
    (problem A domain admitted supply).initialBytes d x = 4 * d 0 := by
  change (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted).initialBytes
    d (CG.RawProblem.forgetInput x) = _
  rw [CG.RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
  omega

/-- The same counted run returns the full physical CG state at the prescribed horizon. -/
noncomputable def specification (R : ResourceModel HSPCG.Signature Empty) :
    Specification HSPCG.Signature Empty (problem A domain admitted supply) where
  budget := staticBudget
  scratch := staticPeak R program
  work d := R.work (staticBudget d)
  span d := R.span (staticBudget d)
  memory d := 4 * d 0 + staticPeak R program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (1, 0) (2, 0) (3, 0)
    (cgState (A d) (decv id (d 0) x.val.1) 0 (d 1)) m

/-- A positive-definite system matrix give successful canonical
CG for every raw input in its explicitly inhabited grade-bounded horizon domain. No success
or numerical execution witness is an assumption. The unused preconditioner primitive has
no executed charge. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ)
    (hA : ∀ d, domain d → (A d).PosDef) :
    Algorithm
      (HSPCG.Model.exactModel (problem A domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun _ _ => 1) (HSPCG.Model.resources cost aw ap sw sp))
      (specification A domain admitted supply (HSPCG.Model.resources cost aw ap sw sp)) := by
  refine Algorithm.ofWp program (wellTyped_program ..) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    let μ := (problem A domain admitted supply).initial d x
    let raw := CG.RawProblem.forgetInput x
    have hμ :
        (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted).initial d raw = μ :=
      rfl
    have hlen (i : Fin 4) : μ.store.len i = if i = 0 then d 0 else ![0, d 0, d 0, d 0] i := by
      rw [← hμ]
      exact CG.RawProblem.initial_len d raw i
    obtain ⟨hS, hBlas, hOp, -⟩ := HSPCG.Model.laws hI
    have hz := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (1, 0)) hS (by simpa [μ, raw] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hz.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz'
    have hrhs : ν.store.readBlock 0 0 (d 0) = some x.val.1 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (CG.RawProblem.initial_readBlock d raw)
    have hx0 : decv id (d 0) (List.replicate (d 0) (exactMachine.lit 0)) = 0 := by
      ext i
      simp [decv, vec, i.isLt, exactMachine]
    have hgrade := x.property.2
    have hRun := solve_writes hS exactModel_exactMachine hBlas hOp (hA d hd)
      (τ := τ) (μ := ν) (k := d 1) (b := (0, 0)) (x := (1, 0))
      (r := (2, 0)) (p := (3, 0))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hrhs hz'.2
      (by rw [hx0, Matrix.mulVec_zero, sub_zero]; exact hgrade) (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ, raw] using (hlen 1).ge,
          by simpa [μ, raw] using (hlen 2).ge,
          by simpa [μ, raw] using (hlen 3).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hRun.wp fun m _ h c _ => by
      simpa [specification, hx0, μ, Problem.initial] using And.intro (h.1.trans hz'.1) h.2
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Certification
