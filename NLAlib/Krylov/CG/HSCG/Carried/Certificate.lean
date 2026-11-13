/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve
public import NLAlib.Krylov.CG.Standard
public import NLAlib.Krylov.CG.ZeroStart
public import NLAlib.Krylov.CG.BufferProblem

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

/-- Raw RHS and uninitialized iterate, residual, direction and scalar-cache capacities. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 5 :=
  CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0, 1]) domain admitted

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- One fixed exact solver, with actual literal-zero initialization. -/
def program : Program Standard.Operation CmpTst 2 5 :=
  ⟨.seq (.frame [.var 0] [⟨1, .var 3⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩]
      solve)⟩

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
  simp [program, Program.environment, List.ofFn_succ, stmtCost, IExp.evalList,
    IExp.eval, CG.staticCost_zeroVector,
    staticCost_solve]

/-- The RHS and all supplied output slots occupy `4*n+1` abstract cells. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x = 4 * d 0 + 1 := by
  calc
    _ = (List.ofFn fun i : Fin 5 => if i = 0 then d 0 else ![0, d 0, d 0, d 0, 1] i).sum :=
      CG.RawProblem.initialBytes_eq d x
    _ = _ := by simp [List.ofFn_succ]; omega

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
    (cgState (model.matrix d x) (decv model.decode (d 0) x.val.1) 0
      (min (d 1) (krylovGrade (model.matrix d x) (decv model.decode (d 0) x.val.1)))) m

/-- Exact local contracts and positive definiteness give total canonical CG for every cap
and supplied RHS. Exact convergence is a successful exit before any further division. -/
noncomputable def algorithm
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (hExact : model.scheme = .exact) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ)
    (hresources : model.resources = Standard.resources model.scheme cost work scratch)
    (hPos : ∀ d, domain d → ∀ x, (model.matrix d x).PosDef) :
    Algorithm model.access (specification model) := by
  refine Algorithm.ofWp program (by
    change program.wellTyped model.resources (fun _ => .cell) = true
    rw [hresources]; exact wellTyped_program ..) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    let μ := (problem (K := K) domain admitted).initial d x
    obtain ⟨hS, hM, hBX, hAX, hC⟩ := CG.exact_laws model hExact hI
    have hlen (i : Fin 5) := CG.RawProblem.initial_len d x i
    have hz := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (1, 0)) hS (by simpa [μ, problem] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hz.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz'
    have hB' : ν.store.readBlock 0 0 (d 0) = some x.val.1 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (CG.RawProblem.initial_readBlock d x)
    have hx0 : decv model.decode (d 0) (List.replicate (d 0) (model.machine.lit 0)) = 0 := by
      ext i
      simp [decv, vec, i.isLt, model.scalar.zero]
    have hRun := solve_writes hS hM hBX hAX hC (hPos d hd x)
      (τ := τ) (μ := ν) (cap := d 1) (b := (0, 0)) (x := (1, 0))
      (r := (2, 0)) (p := (3, 0)) (v := (4, 0))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hB' hz'.2 (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ, problem] using (hlen 1).ge,
          by simpa [μ, problem] using (hlen 2).ge,
          by simpa [μ, problem] using (hlen 3).ge,
          by simpa [μ, problem] using (hlen 4).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hRun.wp fun m _ h c _ => by
      simpa [specification, hx0, μ, Problem.initial] using And.intro (h.1.trans hz'.1) h.2
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Carried.Certification
