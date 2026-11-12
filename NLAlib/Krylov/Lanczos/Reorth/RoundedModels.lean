/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedSolve
public import NLAlib.Krylov.Lanczos.Reorth.Linked
public import NLAlib.Ops.Profiles.Standard

/-!
# Rounded full reorthogonalization in named standard operation models

One declared-model satisfaction proof supplies every primitive interface. Simple common error
budgets establish the normalization precision condition. The actual two-pass history is
retained without assuming mutual orthogonality or matrix symmetry. The model's declared
primitive workspace is used; scalar-profile diagnostic workspace is not substituted for it.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.runs_solve_standard`: exact, sequential or pairwise
  lowering with the actual two-pass history and transferred primitive/workspace budgets.

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.runs_solve_of_model`: actual output in the
  chosen model.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops
open scoped Matrix

/-- The complete fixed solver matches every declared operation/query signature and uses
only the standard model's cell format, independently of its dimensions or numerical values. -/
theorem wellTyped_program (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    ((solveImpl (Op := Standard.Operation) (Tst := CmpTst)).program 3
      [⟨0, .const 0⟩] [⟨1, .const 0⟩, ⟨2, .const 0⟩]).wellTyped
        (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- A standard model, its admitted size and simple accuracy envelope suffice for the complete
rounded solver. Matvec accuracy is related to the supplied operator's norm explicitly. -/
theorem runs_solve_of_model {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b}
    {sizes : (Fin r → ℕ) → ℕ} (model : Standard.Model P sizes)
    {d : Fin r → ℕ} {input : P.Input d} {I : Interp Standard.Operation CmpTst K}
    (hmodel : model.access.contracts d input I) {cap : ℕ} {em E : ℝ}
    (hok : model.scheme.admits (sizes d))
    (hbudget : model.scheme.roundoff (model.matvecAllowance d input) ≤
      em * specNorm (model.matrix d input))
    (haccuracy : Standard.Accuracy em (model.scheme.roundoff model.unit) E
      (model.scheme.errors model.unit) (sizes d))
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 (sizes d) = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * sizes d, 3 * cap + 2]) :
    ConditionalRuns I model.access.workspace τ solve (Env.frame [sizes d, cap] [B, V, C]) μ
      (solveCount (sizes d) cap) (solvePeak model.access.workspace (sizes d) cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * sizes d) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output model.decode (model.matrix d input) (decv model.decode (sizes d) bs)
          em (model.scheme.roundoff model.unit) E (model.scheme.errors model.unit) cap vs cs) := by
  obtain ⟨hS, hB, hA, hCmp⟩ := model.laws hmodel
  obtain ⟨hu, hd, ha, hc⟩ := model.scheme.errors_nonneg model.unit_nonneg (sizes d)
  have hp := Lanczos.Rounded.Precision.of_budgets haccuracy.nonneg haccuracy.small hu hd ha hc
    haccuracy.matvec haccuracy.scalar haccuracy.dot haccuracy.axpy haccuracy.scal
  exact runs_solve hS model.scalar hB hok (hA.mono hbudget) hCmp hp
    model.access.workspace hBV hBC hVC hl hb hz

/-- Any named standard BLAS profile implements the full solver, with rounded matvec and an
actual rounded two-pass history tied to its packed outputs. Pairwise applicability is explicit. -/
theorem runs_solve_standard {K : Type} [Inhabited K] (scheme : Standard.Scheme)
    {M : Machine K} {dec : K → ℝ} {n cap : ℕ} {em u E : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Standard.Operation CmpTst K}
    (hS : IsScalar M I) (hM : StdModel (scheme.roundoff u) dec M) (hu : 0 ≤ u)
    (hok : scheme.admits n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hprec : Lanczos.Rounded.Precision em (scheme.roundoff u) E (scheme.errors u) n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    ConditionalRuns I scheme.profile.wsLo τ (solve.link scheme.profile.table)
      (Env.frame [n, cap] [B, V, C]) μ
      (Count.push scheme.profile.cost (solveCount n cap)) (solvePeak scheme.profile.ws n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) em (scheme.roundoff u) E (scheme.errors u) cap vs cs) := by
  have hc := scheme.certifies hM hu
  obtain ⟨hS', hB⟩ := hc.meets I hS
  have hA' := Interp.link_meets_kept scheme.table_matvec hA
  have hr := runs_solve hS' hM hB hok hA' hCmp hprec scheme.profile.ws
    (τ := τ) hBV hBC hVC hl hb hz
  exact hc.transfer I τ _ _ _ _ _ _ hr

end NLAlib.Krylov.Lanczos.Reorth.Rounded
