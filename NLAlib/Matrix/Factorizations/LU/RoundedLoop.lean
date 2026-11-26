/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedLoop
public import NLAlib.Matrix.Factorizations.LU.RoundedPivotedPrefix

/-!
# Actual pivoted LU loop under standard relative rounding

The unchanged policy loop executes on every original matrix, including singular matrices.
Its stored rounded factors carry actual absolute pivot logs and quantitative multiplier bounds.
Only the componentwise numerical backward-error conclusion requires roundoff below one.

## Main results

* `NLAlib.LU.Rounded.pivotedLoop_meets`: actual loop success and rounded factor outputs.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]
  [Has IdxTst Tst] [Inhabited K]

/-- The same actual loop reports rounded factors and histories. Both factor blocks start
with their real literal-zero words, and the dimension stays in the bounded exact index range. -/
def pivotedLoopSpec (M : Machine K) (dec : K → ℝ) (u quality : ℝ)
    (fixedColumns : Bool) (literalBound : ℕ) : Routine.Spec K :=
  spec% [n, columns] tape t (rs, ls, us) → (rs', ls', us', hs, qs) requires
    n ≤ literalBound ∧ columns = (if fixedColumns then 0 else 1) ∧
      ls = List.replicate (n * n) (M.lit 0) ∧ us = List.replicate (n * n) (M.lit 0) ensures
    (factorPivotedSpec dec u quality fixedColumns literalBound).post [n] t [rs] [ls', us', hs, qs]

/-- The actual policy loop derives its rounded reconstruction and committed multiplier
bounds from local scalar/index contracts and the implemented selector. Every input matrix is
admitted within the exact integer range; there is no successful-run or nonzero-pivot premise. -/
theorem pivotedLoop_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {u quality : ℝ} {fixedColumns : Bool} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I) (hQ : IsToNat dec I)
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hNat : IsExactNatLit dec M literalBound)
    (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : (choiceRoutine choose).Meets I (choiceSpec dec quality literalBound fixedColumns)) :
    (LU.pivotedLoop choose).Meets I
      (pivotedLoopSpec M dec u quality fixedColumns literalBound) := by
  routine_intro [n, columns] (R, L, U, H, Q, selected) reads (rs, ls, us)
  obtain ⟨hbound, hcolumns, rfl, rfl⟩ := hpre
  have hzero : dec (M.lit 0) = 0 := by
    have hh := hM.lit 0
    norm_num at hh
    exact hh
  have hstart := IsRoundedPivotedPrefix.initial (quality := quality)
    (fixedColumns := fixedColumns)
    (H := H) (Q := Q) (IsRoundedFactorPrefix.initial (u := u) hzero hrs hls hus)
  loop_inv (fun _ => Fp.blocks [R, L, U, H, Q, selected]
    [n * n, n * n, n * n, n, columns * n + (1 - columns) * (n - (n - 1)), 2])
    (fun k μ => μ.pos = m.pos ∧
      IsRoundedPivotedPrefix dec u (decodeMatrix dec n n rs) quality fixedColumns k
        R L U H Q μ.store)
    with k hk m₁ hfr hP
  case round =>
    obtain ⟨hp, p, q, hpr, hqr, hqfixed, hf, hH, hC, _⟩ := hP
    obtain ⟨rs₁, ls₁, us₁, hr₁, hl₁, hu₁, hnum, hshape, hLfuture, hUfuture, hLbound⟩ := hf
    call (pivotedStep_meets hI hcmp hlit hQ hNat hchoice) [n, k]
      (R, L, U, (H.1, H.2 + k), (Q.1, Q.2 + columns * k), selected)
      (pre := ⟨hk, hbound⟩) as m₂ hfr₂ hpos₂ (rs₂, ls₂, us₂, hs, qs) hstep
    case' hle =>
      change Fp.blocks [R, L, U, (H.1, H.2 + k), (Q.1, Q.2 + columns * k), selected]
        [n * n, n * n, n * n, 1, 1, 2] ≤ Fp.blocks [R, L, U, H, Q, selected]
        [n * n, n * n, n * n, n, columns * n + (1 - columns) * (n - (n - 1)), 2]
      clear * - hk hcolumns
      cases fixedColumns <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hcolumns <;>
        subst columns <;> fp_sub
    case' hroom =>
      change (R.2 + n * n ≤ m₁.store.len R.1) ∧ (L.2 + n * n ≤ m₁.store.len L.1) ∧
        (U.2 + n * n ≤ m₁.store.len U.1) ∧ (H.2 + k + 1 ≤ m₁.store.len H.1) ∧
        (Q.2 + columns * k + 1 ≤ m₁.store.len Q.1) ∧
        (selected.2 + 2 ≤ m₁.store.len selected.1) ∧ True
      simp only [hfr.len_eq]
      refine ⟨hroom.1, hroom.2.1, hroom.2.2.1, by have := hroom.2.2.2.1; omega,
        ?_, hroom.2.2.2.2.2, trivial⟩
      have hcap := hroom.2.2.2.2.1
      clear * - hcap hk hcolumns
      cases fixedColumns <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hcolumns <;>
        subst columns <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.sub_self,
          Nat.zero_add] at * <;> omega
    change Store.EqOff (Fp.blocks
      [R, L, U, (H.1, H.2 + k), (Q.1, Q.2 + columns * k), selected]
      [n * n, n * n, n * n, 1, 1, 2]) m₁.store m₂.store at hfr₂
    obtain ⟨rw, hrw, rfl⟩ := Store.readBlock_one_eq_some.mp hhs
    obtain ⟨cw, hcw, rfl⟩ := Store.readBlock_one_eq_some.mp hqs
    have hone : dec (M.lit 1) = 1 := by
      simpa using hNat 1 (by omega)
    obtain ⟨r, c, hkr, hkc, hdr, hdc, hfixed, hnext⟩ :=
      pivotedStepSpec_rounded hM hu hone hα hα₁ (decodeMatrix dec n n rs) p q ⟨k, hk⟩
        hstep hnum hshape hLfuture hUfuture hLbound hrs₂ hls₂ hus₂
    have hHkeep := hfr₂.keep (Store.readsOnly_indexPrefix_committed dec p k H)
      (by clear * - hRH hLH hUH hHQ hHselected; disjoint) hH
    have hCkeep : fixedColumns = false → ∀ i : Fin n, i.val < k → ∃ w,
        m₂.store.get Q.1 (Q.2 + i.val) = some w ∧ dec w = (q i).val := by
      intro hc
      have hcol : columns = 1 := by
        simpa only [hc, Bool.false_eq_true, ite_false] using hcolumns
      exact hfr₂.keep (Store.readsOnly_indexPrefix_committed dec q k Q)
        (by clear * - hRQ hLQ hUQ hHQ hQselected hcol; subst columns; disjoint) (hC hc)
    have hoff : columns * k = (if fixedColumns then 0 else k) := by
      rw [hcolumns]
      cases fixedColumns <;> simp
    refine ⟨hpos₂.trans hp, ?_⟩
    apply IsRoundedPivotedPrefix.update p q ⟨k, hk⟩ r c hpr hqr hqfixed hkr hkc hfixed
      hnext
      hHkeep hCkeep hrw hdr _ hdc
    simpa only [hoff] using hcw
  case exit =>
    rintro m₁ _ ⟨hp, hstate⟩
    obtain ⟨ls, us, hs, qs, hls, hus, hhs, hqs, hout⟩ :=
      IsRoundedPivotedPrefix.read_outputs hu hstate literalBound (τ.shift m.pos)
    obtain ⟨_, _, _, _, _, hf, _⟩ := hstate
    obtain ⟨rr, _, _, hrr, _⟩ := hf
    exact ⟨hp, [rr, ls, us, hs, qs], Mem.readBlocks_of_cons hrr
      (Mem.readBlocks_of_cons hls (Mem.readBlocks_of_cons hus
        (Mem.readBlocks_of_cons hhs (Mem.readBlocks_of_cons (by
          cases fixedColumns <;> simpa [hcolumns] using hqs) rfl)))), hout⟩

end NLAlib.LU.Rounded
