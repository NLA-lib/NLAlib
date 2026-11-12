/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedLinked

/-!
# Lanczos results inside a named standard operation model

One declared-model satisfaction proof supplies every primitive interface. Simple common error
budgets establish the normalization precision condition. The model's actual declared primitive
workspace is used; scalar-profile diagnostic workspace is not substituted for it.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.runs_solve_of_model`: actual solver output in the chosen model.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

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
    (hAT : (model.matrix d input)ᵀ = model.matrix d input)
    (haccuracy : Standard.Accuracy em (model.scheme.roundoff model.unit) E
      (model.scheme.errors model.unit) (sizes d))
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 (sizes d) = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * sizes d, 2 * cap + 2]) :
    ConditionalRuns I model.access.workspace τ solve (Env.frame [sizes d, cap] [B, V, C]) μ
      (solveCount (sizes d) cap) (solvePeak model.access.workspace (sizes d))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * sizes d) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output model.decode (model.matrix d input) (decv model.decode (sizes d) bs)
          E cap vs cs) := by
  obtain ⟨hS, hB, hA, hCmp⟩ := model.laws hmodel
  obtain ⟨hu, hd, ha, hc⟩ := model.scheme.errors_nonneg model.unit_nonneg (sizes d)
  have hp := Precision.of_budgets haccuracy.nonneg haccuracy.small hu hd ha hc
    haccuracy.matvec haccuracy.scalar haccuracy.dot haccuracy.axpy haccuracy.scal
  exact runs_solve hS model.scalar hB hok (hA.mono hbudget) hCmp hAT hp
    model.access.workspace hBV hBC hVC hl hb hz

end NLAlib.Krylov.Lanczos.Rounded
