/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotedAlg
public import NLAlib.Matrix.Factorizations.Cholesky.PivotedChoice
public import NLAlib.Ops.Logic.Allocation

/-!
# Actual diagonal scan and guarded Cholesky advancement

The selected absolute index is read from the executed scan's stored output, through the
bounded conversion instruction in the scalar tree. The resulting step commits that same
index and advances the semidefinite factor prefix. Its scalar selection buffer is scoped.

## Main results

* `NLAlib.Cholesky.pivotedStep_writes`: successful actual selection and prefix advancement.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The actual diagonal scan, stored-index conversion, symmetric exchange and zero-safe
column step succeed from the semidefinite input invariant. No selected pivot or run is assumed. -/
theorem pivotedStep_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) (hcmp : IsCmp dec I) (hQ : IsToNat dec I)
    (hM : ExactModel dec M) {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    {p : Fin N → Fin N} (k : Fin N) {τ : Tape K} {m : Mem K} {R L H : ℕ × ℕ}
    (hlive : m.Live [R, L, H]) (hRL : R.1 ≠ L.1) (hRH : R.1 ≠ H.1) (hLH : L.1 ≠ H.1)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hHroom : H.2 + N ≤ m.store.len H.1)
    (hstate : IsDiagonalPrefix dec (M.lit 0) A p k.val R L H m.store) :
    Writes .total I τ (pivotedStep (Op := Op) (Tst := Tst)) (Env.frame [N, k.val] [R, L, H])
      ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
        Store.inBlock H.1 H.2 N)
      (fun m' => ∃ r : Fin N, m'.pos = m.pos ∧ IsDiagonalPrefix dec (M.lit 0) A
        (Function.update p k r) (k.val + 1) R L H m'.store) m := by
  have hlR : R.1 < m.store.length := hlive R (by simp)
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  unfold pivotedStep
  change Writes .total I τ _ (Env.frame [N, k.val] [R, L, H])
    ((Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N)) ⊔
      Store.inBlock H.1 H.2 N) _ m
  alloc as selected
  have hsEq : selected = m.store.length := by change m.store.length = m.store.length; rfl
  have hslive : selected < s_selected.length := by
    rw [hsEq]
    simp only [List.length_singleton] at hlen_selected
    omega
  have hRs : R.1 ≠ selected := by rw [hsEq]; omega
  have hstart := hbelow_selected.keep (IsDiagonalPrefix.readsOnly dec (M.lit 0) A p k.val R L H)
    (by
      rintro b i ((⟨rfl, _, _⟩ | ⟨rfl, _, _⟩) | ⟨rfl, _, _⟩) <;> assumption) hstate
  obtain ⟨rs, ls, hrs, hls, hres, hfac, hupper⟩ := hstart.1.read_blocks
  call (diagonalChoice_meets hI hcmp hlit hQ hM.toStdModel_zero (hM.isExactNatLit N))
    [N, k.val] (R, (selected, 0)) (pre := ⟨k.isLt, le_rfl⟩)
    as m₁ hfr₁ hpos₁ (ws) hscan
  case' hroom =>
    change (0 + 1 ≤ s_selected.len selected) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hselected.ge, trivial⟩
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  obtain ⟨r, hkr, hd, hchoice⟩ := diagonalChoiceSpec_update hA k hstart.2.2.2 hres hscan
  have hstate₁ := hfr₁.keep (IsDiagonalPrefix.readsOnly dec (M.lit 0) A p k.val R L H) (by
    simp only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq]
    rintro b i hsel ((⟨hb, _, _⟩ | ⟨hb, _, _⟩) | ⟨hb, _, _⟩)
    all_goals have := hsel.1; have := hsEq; omega) hstart
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hd (by have := r.isLt; omega) ?_
  have hlRLH : m₁.Live [R, L, H] := by
    simp only [Mem.live_cons, Mem.live_nil]
    rw [hfr₁.length_eq]
    exact ⟨by have := hlen_selected; simp only [List.length_singleton] at this; omega,
      by have := hlen_selected; simp only [List.length_singleton] at this; omega,
      by have := hlen_selected; simp only [List.length_singleton] at this; omega, trivial⟩
  refine ((pivotedAdvance_writes hI hlit hcmp hM hA k r hchoice hlRLH hRL hRH hLH
    (by rw [hfr₁.len_eq, (hbelow_selected R.1 hlR).1]; exact hRroom)
    (by rw [hfr₁.len_eq, (hbelow_selected L.1 hlL).1]; exact hLroom)
    (by rw [hfr₁.len_eq, (hbelow_selected H.1 hlH).1]; exact hHroom) hstate₁).in_frame
      rfl rfl hlRLH).mono (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hpos₂, hstate₂⟩ s₂ hs₂ hB
  refine ⟨r, hpos₂.trans hpos₁, hB.keep
    (IsDiagonalPrefix.readsOnly dec (M.lit 0) A (Function.update p k r) (k.val + 1) R L H)
    (by
      rintro b i ((⟨rfl, _, _⟩ | ⟨rfl, _, _⟩) | ⟨rfl, _, _⟩) <;> assumption) hstate₂⟩

end NLAlib.Cholesky
