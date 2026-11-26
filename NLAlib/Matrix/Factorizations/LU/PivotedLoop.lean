/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedStepCorrect

/-!
# The stored pivoted elimination loop

This loop operates on an initialized residual and two zero-filled factors. History cells are
written one at a time and only read as full output blocks after the final step. Fixed-column
policies reuse one column-history word, and independent policies store both full histories.

## Main results

* `NLAlib.LU.pivotedLoop_meets`: the actual scalar loop and its completed canonical factors.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Eliminate an initialized residual. The literal column-storage flag is supplied by the
concrete policy wrapper, and the two selector scratch words are never reported as output. -/
def pivotedLoop (choose : Stmt Op Tst) : Routine Op Tst :=
  routine% [n, columns] (R : n * n, L : n * n, U : n * n) →
      (R, L, U, H : n, Q : columns * n + (1 - columns) * (n - (n - 1)),
        unreported selected : 2) {
    for k < n {
      run (pivotedStep choose) [n, k] (R, L, U, H[k], Q[columns * k], selected)
    }
  }

variable [Inhabited K]

/-- Both factors start as actual zero literals, and the column-storage flag matches the
chosen concrete policy. The completed factors and histories satisfy the common output spec. -/
def pivotedLoopSpec (M : Machine K) (dec : K → ℝ) (quality : ℝ)
    (fixedColumns : Bool) : Routine.Spec K :=
  spec% [n, columns] tape t (rs, ls, us) → (rs', ls', us', hs, qs) requires
    columns = (if fixedColumns then 0 else 1) ∧
      ls = List.replicate (n * n) (M.lit 0) ∧ us = List.replicate (n * n) (M.lit 0) ensures
    (factorPivotedSpec dec quality fixedColumns).post [n] t [rs] [ls', us', hs, qs]

/-- The actual policy loop advances the stored canonical factor and history prefixes. Its
selector hypothesis is instantiated by the concrete partial, complete and quality policies. -/
theorem pivotedLoop_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {quality : ℝ} {fixedColumns : Bool}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : ∀ bound : ℕ,
      (choiceRoutine choose).Meets I (choiceSpec dec quality bound fixedColumns)) :
    (pivotedLoop choose).Meets I (pivotedLoopSpec M dec quality fixedColumns) := by
  routine_intro [n, columns] (R, L, U, H, Q, selected) reads (rs, ls, us)
  obtain ⟨hcolumns, rfl, rfl⟩ := hpre
  have hstart := IsPivotedPrefix.initial (quality := quality) (fixedColumns := fixedColumns)
    (H := H) (Q := Q) (IsFactorPrefix.initial hM hrs hls hus)
  loop_inv (fun _ => Fp.blocks [R, L, U, H, Q, selected]
    [n * n, n * n, n * n, n, columns * n + (1 - columns) * (n - (n - 1)), 2])
    (fun k μ => μ.pos = m.pos ∧
      IsPivotedPrefix dec (decodeMatrix dec n n rs) quality fixedColumns k R L U H Q μ.store)
    with k hk m₁ hfr hP
  case round =>
    obtain ⟨hp, p, q, hpr, hqr, hqfixed, hf, hH, hC, _, hm⟩ := hP
    obtain ⟨rs₁, ls₁, us₁, hr₁, hl₁, hu₁, hres, hlo, hup⟩ := hf.read_blocks
    call (pivotedStep_meets hI hcmp hlit hQ (hM.isExactNatLit n) (hchoice n)) [n, k]
      (R, L, U, (H.1, H.2 + k), (Q.1, Q.2 + columns * k), selected)
      (pre := ⟨hk, le_rfl⟩) as m₂ hfr₂ hpos₂ (rs₂, ls₂, us₂, hs, qs) hstep
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
    obtain ⟨r, c, hkr, hkc, hdr, hdc, hfixed, hnext⟩ :=
      pivotedStepSpec_prefix hM (decodeMatrix dec n n rs) p q ⟨k, hk⟩ hstep hres hlo hup hm
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
    apply IsPivotedPrefix.update p q ⟨k, hk⟩ r c hpr hqr hqfixed hkr hkc hfixed
      (IsFactorPrefix.of_reads hrs₂ hls₂ hus₂ hnext.1 hnext.2.1 hnext.2.2.1)
      hHkeep hCkeep hrw hdr _ hdc hnext.2.2.2
    simpa only [hoff] using hcw
  case exit =>
    rintro m₁ _ ⟨hp, hstate⟩
    obtain ⟨ls, us, hs, qs, hls, hus, hhs, hqs, hout⟩ :=
      IsPivotedPrefix.read_outputs hα hα₁ hstate (τ.shift m.pos)
    obtain ⟨_, _, _, _, _, hf, _⟩ := hstate
    obtain ⟨rr, _, _, hrr, _⟩ := hf.read_blocks
    exact ⟨hp, [rr, ls, us, hs, qs], Mem.readBlocks_of_cons hrr
      (Mem.readBlocks_of_cons hls (Mem.readBlocks_of_cons hus
        (Mem.readBlocks_of_cons hhs (Mem.readBlocks_of_cons (by
          cases fixedColumns <;> simpa [hcolumns] using hqs) rfl)))), hout⟩

end NLAlib.LU
