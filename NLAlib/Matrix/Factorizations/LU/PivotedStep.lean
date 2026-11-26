/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Pivot
public import NLAlib.Matrix.Factorizations.LU.PivotSwaps
public import NLAlib.Matrix.Factorizations.LU.Step
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# One scalar pivoted elimination step

The step consumes both words returned by a fixed selector, moves matching factor rows and
columns, records the two current positions, and executes the common guarded LU step.
Only the two new history cells are reported, so unwritten future history cells need not be
initialized. The two selector scratch words are ordinary unreported output storage.

## Main results

* `NLAlib.LU.pivotedStep_meets`: the actual selection, exchanges, logs and guarded update.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- One actual policy step. History operands are single output cells; selector storage is
unreported scratch supplied by the containing driver. All bounded indices come from words. -/
def pivotedStep (choose : Stmt Op Tst) : Routine Op Tst :=
  routine% [n, k] (R : n * n, L : n * n, U : n * n) →
      (R, L, U, h : 1, q : 1, unreported selected : 2) {
    run (choiceRoutine choose) [n, k] (R, selected);
    let row ← index (Has.inj IdxTst.toNat) (selected) ≤ n - 1;
    let col ← index (Has.inj IdxTst.toNat) (selected[1]) ≤ n - 1;
    run pivotSwaps [n, k, row, col] (R, L, U);
    call (Has.inj IndexOp.lit) [row] () → (h);
    call (Has.inj IndexOp.lit) [col] () → (q);
    run step [n, k] (R, L, U)
  }

variable [Inhabited K]

/-- The reported log words identify the selected active row and column. Their quality refers
to the original residual words. Intermediate exchanged words connect the actual swaps to
factor materialization and elimination, without an assumed successful run. -/
def pivotedStepSpec (M : Machine K) (dec : K → ℝ) (quality : ℝ) (bound : ℕ)
    (fixedColumns : Bool) : Routine.Spec K :=
  spec% [n, k] tape t (rs, ls, us) → (rs', ls', us', [r], [c]) requires
    k < n ∧ n ≤ bound ensures
    ∃ row col : Fin n, k ≤ row.val ∧ k ≤ col.val ∧ dec r = row.val ∧ dec c = col.val ∧
      (fixedColumns = true → col.val = k) ∧
      (∀ i : Fin n, k ≤ i.val →
        quality * |dec (vec rs (col.val * n + i.val))| ≤
          |dec (vec rs (col.val * n + row.val))|) ∧
      ∃ rs₀ ls₀ us₀ : List K,
        (pivotSwapsSpec (K := K)).post [n, k, row.val, col.val] t
          [rs, ls, us] [rs₀, ls₀, us₀] ∧
        (stepSpec M dec).post [n, k] t [rs₀, ls₀, us₀] [rs', ls', us']

/-- All instructions of one policy step succeed from the selector's proved judgment and local
scalar/index contracts. The enclosing concrete drivers instantiate an actual selector tree. -/
theorem pivotedStep_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {quality : ℝ} {bound : ℕ} {fixedColumns : Bool}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hNat : IsExactNatLit dec M bound)
    (hchoice : (choiceRoutine choose).Meets I (choiceSpec dec quality bound fixedColumns)) :
    (pivotedStep choose).Meets I (pivotedStepSpec M dec quality bound fixedColumns) := by
  routine_intro [n, k] (R, L, U, h, q, selected) reads (rs, ls, us)
  obtain ⟨hkn, hnb⟩ := hpre
  call hchoice [n, k] (R, selected) (pre := ⟨hkn, hnb⟩)
    as m₁ hfr₁ hpos₁ (choices) hc
  obtain ⟨rw, cw, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hchoices)
  obtain ⟨row, col, hkr, hkc, hdr, hdc, hfixed, hquality⟩ : ∃ row col : Fin n,
      k ≤ row.val ∧ k ≤ col.val ∧ dec rw = row.val ∧ dec cw = col.val ∧
      (fixedColumns = true → col.val = k) ∧
      ∀ i : Fin n, k ≤ i.val → quality * |dec (vec rs (col.val * n + i.val))| ≤
        |dec (vec rs (col.val * n + row.val))| := hc
  have hrw : m₁.store.get selected.1 selected.2 = some rw := by
    simpa [vec] using Store.get_of_readBlock hchoices (j := 0) (by omega) default
  have hcw : m₁.store.get selected.1 (selected.2 + 1) = some cw := by
    simpa [vec] using Store.get_of_readBlock hchoices (j := 1) (by omega) default
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hrw hdr (by have := row.isLt; omega) ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hcw hdc (by have := col.isLt; omega) ?_
  call (pivotSwaps_meets hI) [n, k, row.val, col.val] (R, L, U)
    (pre := ⟨⟨hkr, row.isLt⟩, hkc, col.isLt⟩)
    as m₂ hfr₂ hpos₂ (rs₀, ls₀, us₀) hswap
  step hlit as m₃ hfr₃ ⟨hpos₃, r, hr, hrword⟩
  have her : M.lit (row.val : ℕ) = r := by simpa [Machine.indexFn] using hrword
  subst r
  simp only [Machine.indexFn, Nat.add_zero] at hpos₃
  step hlit as m₄ hfr₄ ⟨hpos₄, c, hcget, hcword⟩
  have hec : M.lit (col.val : ℕ) = c := by simpa [Machine.indexFn] using hcword
  subst c
  simp only [Machine.indexFn, Nat.add_zero] at hpos₄
  call (step_meets hI hcmp) [n, k] (R, L, U) (pre := hkn)
    as m₅ hfr₅ hpos₅ (rs', ls', us') hstep
  routine_exit
  exact ⟨row, col, hkr, hkc, hNat row.val (by omega), hNat col.val (by omega),
    hfixed, hquality, rs₀, ls₀, us₀, hswap, hstep⟩

end NLAlib.LU
