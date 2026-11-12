/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Stability
public import NLAlib.Ops.Profiles.Standard

/-!
# CG guarantees inside named standard operation models

The declared operation model supplies scalar, BLAS, rounded matvec and exact comparisons.
The same simple common accuracy envelope also supports Lanczos. CG additionally needs its
input spectral interval and accumulated precision window. Its actual stored output retains
the existing physical-energy and backward-model guarantees.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runs_solve_of_model`: complete CG in a standard model.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- The complete fixed CG solver uses only the standard declared signatures and cell format.
The initial guess aliases the solution buffer in this fixed interface. -/
theorem solve_wellTyped (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    ((solveImpl (Op := Standard.Operation) (Tst := CmpTst)).program 5
      [⟨0, .const 0⟩, ⟨1, .const 0⟩]
      [⟨1, .const 0⟩, ⟨2, .const 0⟩, ⟨3, .const 0⟩, ⟨4, .const 0⟩]).wellTyped
        (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- Declared standard-model contracts and input spectral precision imply successful rounded
CG and stability of the actual stored output. The model's declared workspace is retained. -/
theorem runs_solve_of_model {K : Type} [Inhabited K] {r b : ℕ} {P : Problem K r b}
    {sizes : (Fin r → ℕ) → ℕ} (model : Standard.Model P sizes)
    {d : Fin r → ℕ} {input : P.Input d} {I : Interp Standard.Operation CmpTst K}
    (hmodel : model.access.contracts d input I) {cap : ℕ} {em E a a' : ℝ}
    (hok : model.scheme.admits (sizes d))
    (hbudget : model.scheme.roundoff (model.matvecAllowance d input) ≤
      em * specNorm (model.matrix d input))
    (hAT : (model.matrix d input)ᵀ = model.matrix d input)
    (ha : 0 < a) (hspec : spectrum ℝ (model.matrix d input) ⊆ Set.Icc a a')
    (haccuracy : Standard.Accuracy em (model.scheme.roundoff model.unit) E
      (model.scheme.errors model.unit) (sizes d))
    (hprec : 3 * E * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * E * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {τ : Tape K} {μ : Mem K} {B X R S V : ℕ × ℕ} {bs xs : List K}
    (hBX : B.1 ≠ X.1) (hBR : B.1 ≠ R.1) (hBS : B.1 ≠ S.1) (hBV : B.1 ≠ V.1)
    (hXR : X.1 ≠ R.1) (hXS : X.1 ≠ S.1) (hXV : X.1 ≠ V.1)
    (hRS : R.1 ≠ S.1) (hRV : R.1 ≠ V.1) (hSV : S.1 ≠ V.1)
    (hl : μ.Live [B, X, R, S, V]) (hb : μ.store.readBlock B.1 B.2 (sizes d) = some bs)
    (hx : μ.store.readBlock X.1 X.2 (sizes d) = some xs) (hx0 : decv model.decode (sizes d) xs = 0)
    (hz : μ.Room [X, R, S, V] [sizes d, sizes d, sizes d, 1]) :
    ConditionalRuns I model.access.workspace τ solve
      (Env.frame [sizes d, cap] [B, X, X, R, S, V]) μ
      (solveCount (sizes d) cap) (solvePeak model.access.workspace (sizes d))
      (fun μ' => μ'.pos = μ.pos ∧ StableOutput model.decode (model.matrix d input)
        (decv model.decode (sizes d) bs) E a a' cap X R S V μ') := by
  obtain ⟨hS, hB, hA, hCmp⟩ := model.laws hmodel
  obtain ⟨hu, hd, haxpy, _⟩ := model.scheme.errors_nonneg model.unit_nonneg (sizes d)
  have hue : model.scheme.roundoff model.unit ≤ E := by
    linarith [haccuracy.scalar, haccuracy.nonneg]
  have hde : (model.scheme.errors model.unit).dot (sizes d) ≤ E := by
    linarith [haccuracy.dot, haccuracy.nonneg]
  have hr := runs_solve hS model.scalar hB hok (hA.mono hbudget) hCmp hAT ha hspec
    hu hd haxpy haccuracy.matvec hue hde haccuracy.axpy haccuracy.small hprec hwindow
    model.access.workspace (τ := τ) hBX hBR hBS hBV hXR hXS hXV hRS hRV hSV hl hb hx hx0 hz
  exact hr.mono le_rfl le_rfl fun _ h => ⟨h.1, h.2.stable ha hspec hwindow⟩

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
