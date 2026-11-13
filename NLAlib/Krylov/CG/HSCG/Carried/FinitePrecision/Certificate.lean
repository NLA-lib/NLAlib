/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Standard
public import NLAlib.Krylov.CG.BufferProblem
public import NLAlib.Krylov.CG.ZeroStart

/-!
# Canonical rounded zero-start CG

The fixed program initializes its own zero iterate, then invokes the existing total carried
CG solver. Raw inputs contain only the right-hand side and uninitialized output capacities.
The same execution supplies stored numerical stability, full counts, work, span and payload.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Certification.algorithm`: total rounded certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Certification

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- RHS, iterate, residual, direction and one computed residual-product cell. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 5 :=
  CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0, 1]) domain admitted

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The fixed program writes the zero iterate before any solver input read. -/
def program : Program Standard.Operation CmpTst 2 5 :=
  ⟨.seq (.frame [.var 0] [⟨1, .var 3⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩]
      solve)⟩

/-- The complete wrapper respects the standard local signatures and cell formats. -/
theorem wellTyped_program (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    program.wellTyped (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- The full instrumented instruction count of the fixed zero-start solver. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (Standard.Operation ⊕ Bookkeeping) CmpTst :=
  staticCost program d

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

/-- The actual supplied RHS and four output capacities occupy `4*n+1` abstract cells. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x = 4 * d 0 + 1 := by
  calc
    _ = (List.ofFn fun i : Fin 5 => if i = 0 then d 0 else ![0, d 0, d 0, d 0, 1] i).sum :=
      CG.RawProblem.initialBytes_eq d x
    _ = _ := by simp [List.ofFn_succ]; omega

/-- Raw numerical output and independent full-count, work, span and payload budgets. -/
noncomputable def specification
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (E a a' : (Fin 2 → ℕ) → ℝ) :
    Specification Standard.Operation CmpTst (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch := staticPeak model.resources program
  work d := model.resources.work (staticBudget d)
  span d := model.resources.span (staticBudget d)
  memory d := 4 * d 0 + 1 + staticPeak model.resources program d
  good d x _ _ m := m.pos = 0 ∧
    StableOutput model.decode (model.matrix d x) (decv model.decode (d 0) x.val.1)
      (E d) (a d) (a' d) (d 1) (1, 0) (2, 0) (3, 0) (4, 0) m

/-- Spectral and precision assumptions on the declared inputs imply total rounded execution
and the stored residual-gap, physical-energy and backward-model guarantees. No execution
or initialized iterate is assumed. All resources concern the same canonical execution. -/
noncomputable def algorithm
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (cost : Standard.Costing) (work scratch : List ℕ → ℕ)
    (hresources : model.resources = Standard.resources model.scheme cost work scratch)
    (em E a a' : (Fin 2 → ℕ) → ℝ)
    (hok : ∀ d, domain d → model.scheme.admits (d 0))
    (haccuracy : ∀ d, domain d → Standard.Accuracy (em d)
      (model.scheme.roundoff model.unit) (E d) (model.scheme.errors model.unit) (d 0))
    (hbudget : ∀ d, domain d → ∀ x, model.scheme.roundoff (model.matvecAllowance d x) ≤
      em d * specNorm (model.matrix d x))
    (hAT : ∀ d, domain d → ∀ x, (model.matrix d x)ᵀ = model.matrix d x)
    (ha : ∀ d, domain d → 0 < a d)
    (hspec : ∀ d, domain d → ∀ x, spectrum ℝ (model.matrix d x) ⊆ Set.Icc (a d) (a' d))
    (hprec : ∀ d, domain d → 3 * E d * a' d ≤ a d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (a' d / a d) ^ 2 ≤ 1 / 10 ^ 5) :
    Algorithm model.access (specification model E a a') := by
  refine Algorithm.ofWp program (by
    change program.wellTyped model.resources (fun _ => .cell) = true
    rw [hresources]; exact wellTyped_program ..) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    let μ := (problem (K := K) domain admitted).initial d x
    obtain ⟨hS, _, _, _⟩ := model.laws hI
    have hlen (i : Fin 5) := CG.RawProblem.initial_len d x i
    have hzero := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (1, 0)) hS (by simpa [μ, problem] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hzero.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz
    have hB : ν.store.readBlock 0 0 (d 0) = some x.val.1 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (CG.RawProblem.initial_readBlock d x)
    have hx0 : decv model.decode (d 0) (List.replicate (d 0) (model.machine.lit 0)) = 0 := by
      ext i
      simp [decv, vec, i.isLt, model.scalar.zero]
    have hRun := runs_solve_of_model model hI (cap := d 1) (hok d hd) (hbudget d hd x)
      (hAT d hd x) (ha d hd) (hspec d hd x) (haccuracy d hd) (hprec d hd) (hwindow d hd)
      (τ := τ) (μ := ν) (B := (0, 0)) (X := (1, 0)) (R := (2, 0))
      (S := (3, 0)) (V := (4, 0)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hB hz.2 hx0 (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ, problem] using (hlen 1).ge,
          by simpa [μ, problem] using (hlen 2).ge,
          by simpa [μ, problem] using (hlen 3).ge,
          by simpa [μ, problem] using (hlen 4).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hRun.wp.mono fun m h c _ => by
      simpa [specification, μ, Problem.initial] using And.intro (h.1.trans hz.1) h.2
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Certification
