/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.StoredWords
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Krylov.CG.ZeroStart
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense Hestenes–Stiefel CG

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness and the grade bound on the
prescribed horizon are mathematical admission. All counts, work, span and memory refer to
the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Stored.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Stored

open Ops

/-- Positive definiteness concerns the actual raw matrix. The horizon is no greater than
the initial Krylov grade. -/
def accepts (d : Fin 2 → ℕ) (raw rhs : List ℝ) : Prop :=
  (StoredOperator.denseMatrix (d 0) (d 0) raw).PosDef ∧
    d 1 ≤ krylovGrade (StoredOperator.denseMatrix (d 0) (d 0) raw) (decv id (d 0) rhs)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs)

/-- A declared dense matrix prefix, raw RHS and supplied uninitialized state capacities. -/
abbrev problem : Problem ℝ 2 5 :=
  StoredProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted accepts supply

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 5 :=
  ⟨.seq (.frame [.var 0] [⟨2, .var 4⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨2, .var 4⟩,
        ⟨3, .var 5⟩, ⟨4, .var 6⟩]
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext 1 2
        (ContextLinear.table 1 0)))⟩

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0) := by
  have h := Problem.withContext.initialBytes_eq d x
  refine h.trans ?_
  rw [RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
  omega

/-- Canonical resources and the exact physical CG state at the prescribed horizon. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ HSCG.StoresState id (d 0) (2, 0) (3, 0) (4, 0)
    (cgState (StoredProblem.matrix x) (decv id (d 0) x.val.1.2) 0
      (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine Algorithm.ofWp program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI τ
    obtain ⟨hS, hB, hC⟩ := ExactBlas.laws hI
    let μ := (problem domain admitted supply).initial d x
    have hlen (i : Fin 4) := StoredProblem.initial_len d x i
    have hz := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (2, 0)) hS (by simpa [μ] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hz.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz'
    have hData : ν.store.readBlock 0 0 (d 0 * d 0) = some (x.val.1.1 0) :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (StoredProblem.initial_matrix d x)
    have hRhs : ν.store.readBlock 1 0 (d 0) = some x.val.1.2 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (StoredProblem.initial_rhs d x)
    have hx0 : decv id (d 0) (List.replicate (d 0) (RCLikeBlas.machine.lit 0)) = 0 := by
      ext i
      simp [decv, vec, i.isLt, RCLikeBlas.machine]
    have hw := stored_solve_wp (n := d 0) (cap := d 1) (cutoff := 1) (τ := τ)
      (μ := ν) (B := (1, 0)) (X := (2, 0)) (R := (3, 0)) (P := (4, 0))
      hS hB hC [(0, 0)] 0 (x.val.1.1 0)
      (by simp) (by simp [hfr.length_eq, μ, Problem.initial]) hData (by simp)
      (Problem.withContext.extra_input x).1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hRhs hz'.2 (by
        simpa [hx0] using (Problem.withContext.extra_input x).2) (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ] using (hlen 1).ge,
          by simpa [μ] using (hlen 2).ge, by simpa [μ] using (hlen 3).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hw.mono fun m h _ _ => by
      simpa [specification, StoredProblem.matrix, hx0, μ, Problem.initial] using
        And.intro (h.1.trans hz'.1) h.2
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Stored
