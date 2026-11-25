/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledChoice
public import NLAlib.Matrix.Factorizations.LU.ScaleSwap
public import NLAlib.Matrix.Factorizations.LU.PivotSwaps
public import NLAlib.Matrix.Factorizations.LU.Step

/-!
# One stored fixed-scale LU step

One packed operand contains the square residual followed by its fixed row scales. The actual
selector consumes both read-only windows, then the same current row exchange acts on the
residual, committed lower rows and scale vector. Common total factor materialization and
Schur elimination follow, and an actual literal records the selected absolute row.

## Main results

* `NLAlib.LU.scaledStep_meets`: actual candidate selection, exchanges and elimination.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Advance one scaled pivot. The packed residual and scales share one operand; factor
buffers remain separate. Selector storage is one unreported scalar supplied by the caller. -/
def scaledStep : Routine Op Tst :=
  routine% [n, k] (R : n * n + n, L : n * n, U : n * n) →
      (R, L, U, h : 1, unreported selected : 1) {
    run scaledChoice [n, k] (R, R[n * n], selected);
    let row ← index (Has.inj IdxTst.toNat) (selected) ≤ n - 1;
    run pivotSwaps [n, k, row, k] (R, L, U);
    run swapScales [n, k, row] (R[n * n]);
    call (Has.inj IndexOp.lit) [row] () → (h);
    run step [n, k] (R, L, U)
  }

variable [Inhabited K]

/-- The reported row comes from the actual weighted scan. The packed output is an actual
new residual followed by exchanged scales; intermediate word contracts relate every phase. -/
def scaledStepSpec (M : Machine K) (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] tape t (packed, ls, us) → (packed', ls', us', [r]) requires
    (scaledChoiceSpec dec bound).pre [n, k] t
      [packed.take (n * n), (packed.drop (n * n)).take n]
  ensures ∃ row : Fin n, k ≤ row.val ∧ dec r = row.val ∧
    (scaledChoiceSpec dec bound).post [n, k] t
      [packed.take (n * n), (packed.drop (n * n)).take n] [[r]] ∧
    ∃ rs₀ ls₀ us₀ ss' rs' : List K,
      rs'.length = n * n ∧ ss'.length = n ∧
      (pivotSwapsSpec (K := K)).post [n, k, row.val, k] t
        [packed.take (n * n), ls, us] [rs₀, ls₀, us₀] ∧
      (swapScalesSpec (K := K)).post [n, k, row.val] t
        [(packed.drop (n * n)).take n] [ss'] ∧
      (stepSpec M dec).post [n, k] t [rs₀, ls₀, us₀] [rs', ls', us'] ∧
      packed' = rs' ++ ss'

/-- The actual scaled step is total under exact arithmetic and exact stored-index queries.
Its premise only requires active compatible scales, including zero original rows. -/
theorem scaledStep_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (scaledStep (Op := Op) (Tst := Tst)).Meets I (scaledStepSpec M dec bound) := by
  routine_intro [n, k] (R, L, U, h, selected) reads (packed, ls, us)
  have hr₀ : m.store.readBlock R.1 R.2 (n * n) = some (packed.take (n * n)) := by
    simpa only [Nat.add_zero, List.drop_zero] using
      Store.readBlock_sub hpacked (o := 0) (n := n * n) (by omega)
  have hs₀ := Store.readBlock_sub hpacked (o := n * n) (n := n) (by omega)
  obtain ⟨⟨hkn, hnb⟩, hcompat⟩ : (k < n ∧ n ≤ bound) ∧
      ∀ i : Fin n, k ≤ i.val →
        0 ≤ dec (vec ((packed.drop (n * n)).take n) i.val) ∧
        (dec (vec ((packed.drop (n * n)).take n) i.val) = 0 →
          dec (vec (packed.take (n * n)) (k * n + i.val)) = 0) := hpre
  call (scaledChoice_meets (bound := bound) hI hcmp hlit hQ hM) [n, k]
    (R, (R.1, R.2 + n * n), selected) (pre := ⟨⟨hkn, hnb⟩, hcompat⟩)
    as m₁ hfr₁ hpos₁ (choices) hc
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hchoices
  obtain ⟨row, hkr, hdr, hquality, hfirst⟩ : ∃ row : Fin n, k ≤ row.val ∧ dec w = row.val ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec (packed.take (n * n)) (k * n + i.val))| /
            dec (vec ((packed.drop (n * n)).take n) i.val) ≤
          |dec (vec (packed.take (n * n)) (k * n + row.val))| /
            dec (vec ((packed.drop (n * n)).take n) row.val)) ∧
      (∀ i : Fin n, k ≤ i.val → i < row →
        |dec (vec (packed.take (n * n)) (k * n + i.val))| /
            dec (vec ((packed.drop (n * n)).take n) i.val) <
          |dec (vec (packed.take (n * n)) (k * n + row.val))| /
            dec (vec ((packed.drop (n * n)).take n) row.val)) := hc
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hdr (by have := row.isLt; omega) ?_
  call (pivotSwaps_meets hI) [n, k, row.val, k] (R, L, U)
    (pre := ⟨⟨hkr, row.isLt⟩, le_rfl, hkn⟩)
    as m₂ hfr₂ hpos₂ (rs₀, ls₀, us₀) hswap
  have hrs : Fp.Disj (Store.inBlock R.1 R.2 (n * n))
      (Store.inBlock R.1 (R.2 + n * n) n) := Fp.disj_inBlock_of_le le_rfl
  have hs₁ : m₁.store.readBlock R.1 (R.2 + n * n) n =
      some ((packed.drop (n * n)).take n) := by keep
  have hs₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs₁
  call (swapScales_meets hI) [n, k, row.val] ((R.1, R.2 + n * n))
    (pre := ⟨hkr, row.isLt⟩) as m₃ hfr₃ hpos₃ (ss') hscale
  have hr₃ : m₃.store.readBlock R.1 R.2 (n * n) = some rs₀ :=
    hfr₃.keep (Store.readsOnly_readBlock _ _ _ _)
      (by simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hrs.symm) hrs₀
  step hlit as m₄ hfr₄ ⟨hpos₄, r, hr, hrword⟩
  have her : M.lit (row.val : ℕ) = r := by simpa [Machine.indexFn] using hrword
  subst r
  simp only [Machine.indexFn, Nat.add_zero] at hpos₄
  call (step_meets hI hcmp) [n, k] (R, L, U) (pre := hkn)
    as m₅ hfr₅ hpos₅ (rs', ls', us') hstep
  have hs₄ : m₄.store.readBlock R.1 (R.2 + n * n) n = some ss' := by keep
  have hs₅ := hfr₅.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint) hs₄
  have hp' := Store.readBlock_add hrs' hs₅
  refine ⟨hpos₅.trans (hpos₄.trans (hpos₃.trans (hpos₂.trans hpos₁))),
    [rs' ++ ss', ls', us', [M.lit (row.val : ℕ)]],
    Mem.readBlocks_of_cons hp' (Mem.readBlocks_of_cons hls'
      (Mem.readBlocks_of_cons hus' (Mem.readBlocks_of_cons
        (Store.readBlock_one_of_get (by keep)) rfl))), ?_⟩
  refine ⟨row, hkr, hM.isExactNatLit n row.val row.isLt.le, ?_,
    rs₀, ls₀, us₀, ss', rs', Store.length_of_readBlock hrs',
    Store.length_of_readBlock hss', hswap, hscale, hstep, rfl⟩
  exact ⟨row, hkr, hM.isExactNatLit n row.val row.isLt.le, hquality, hfirst⟩

end NLAlib.LU
