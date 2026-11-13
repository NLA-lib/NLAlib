/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.StoredWords
public import NLAlib.Krylov.CG.HSPCG.StoredProblem
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Krylov.CG.ZeroStart
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense PCG

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness and the preconditioned grade
bound are explicit input admission. All counts, work, span and memory refer to the actual
transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Stored.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Stored

open Ops

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ rawA rawP rhs : List ℝ,
    rawA.length = d 0 * d 0 ∧ rawP.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
      accepts d rawA rawP rhs)

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 7 :=
  ⟨.seq (.frame [.var 0] [⟨3, .var 5⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨3, .var 5⟩,
        ⟨4, .var 6⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩]
      ((solve (Op := Signature) (Tst := CmpTst)).linkContext 2 2
        (StoredContext.table 2 0 1)))⟩

/-- Canonical resources and the exact converged-or-capped physical CG state. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := 2 * d 0 * d 0 + 5 * d 0 + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0)
    (pcgState (matrix x) (preconditioner x) (decv id (d 0) x.val.1.2) 0 (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine Algorithm.ofWp program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI τ
    obtain ⟨hS, hB, _⟩ := ExactBlas.laws hI
    let μ := (problem domain admitted supply).initial d x
    have hlen (i : Fin 5) := initial_len d x i
    have hz := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (3, 0)) hS (by simpa [μ, outputs] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hz.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz'
    have hData : ν.store.readBlock 0 0 (d 0 * d 0) = some (x.val.1.1 0) :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) (initial_matrix d x)
    have hPrec : ν.store.readBlock 1 0 (d 0 * d 0) = some (x.val.1.1 1) :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) (initial_preconditioner d x)
    have hRhs : ν.store.readBlock 2 0 (d 0) = some x.val.1.2 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) (initial_rhs d x)
    have hx0 : decv id (d 0) (List.replicate (d 0) (RCLikeBlas.machine.lit 0)) = 0 := by
      ext i
      simp [decv, vec, i.isLt, RCLikeBlas.machine]
    have hExtra := accepts_input x
    have hw := stored_solve_wp (n := d 0) (cap := d 1) (cutoff := 2) (τ := τ)
      (μ := ν) (B := (2, 0)) (X := (3, 0)) (R := (4, 0)) (Z := (5, 0)) (P := (6, 0))
      hS hB [(0, 0), (1, 0)] 0 1 (x.val.1.1 0) (x.val.1.1 1)
      (by simp) (by simp [hfr.length_eq, μ, Problem.initial]) hData hPrec (by simp)
      hExtra.1 hExtra.2.1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hRhs hz'.2
      (by rw [hx0, Matrix.mulVec_zero, sub_zero]; exact hExtra.2.2) (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ, outputs] using (hlen 1).ge, by simpa [μ, outputs] using (hlen 2).ge,
          by simpa [μ, outputs] using (hlen 3).ge, by simpa [μ, outputs] using (hlen 4).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hw.mono fun m h _ _ => by
      simpa [specification, matrix, preconditioner, hx0, μ, Problem.initial] using
        And.intro (h.1.trans hz'.1) h.2
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSPCG.Stored
