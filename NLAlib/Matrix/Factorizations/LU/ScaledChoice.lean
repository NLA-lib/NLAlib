/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledScan

/-!
# Active-column scaled pivot choice

The selector scans the active residual column and the matching suffix of fixed original row
scales. It consumes the actual relative index with a bounded query and writes its absolute
current row. The residual and scales are read only and may share their packed arena.

## Main results

* `NLAlib.LU.scaledChoice_meets`: actual stable scaled selection and recorded absolute index.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Select an absolute current row from the active residual column and row-scale suffix.
The single reported word is produced by a dimension literal after an actual bounded query. -/
def scaledChoice : Routine Op Tst := routine% [n, k] (R : n * n, scales : n) → (p : 1) {
  let relative ← alloc 1;
  run argmaxScaledAbs [n - k] (R[k * n + k], scales[k], relative);
  let row ← index (Has.inj IdxTst.toNat) (relative) ≤ n - k - 1;
  call (Has.inj IndexOp.lit) [k + row] () → (p)
}

variable [Inhabited K]

/-- The precondition concerns active rows only. The actual decoded row is active, maximizes
its absolute residual-to-fixed-scale ratio, and retains the earliest row at ties. -/
def scaledChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs, ss) → ([r]) requires
    (k < n ∧ n ≤ bound) ∧ ∀ i : Fin n, k ≤ i.val →
      0 ≤ dec (vec ss i.val) ∧
        (dec (vec ss i.val) = 0 → dec (vec rs (k * n + i.val)) = 0)
  ensures ∃ row : Fin n, k ≤ row.val ∧ dec r = row.val ∧
    (∀ i : Fin n, k ≤ i.val →
      |dec (vec rs (k * n + i.val))| / dec (vec ss i.val) ≤
        |dec (vec rs (k * n + row.val))| / dec (vec ss row.val)) ∧
    (∀ i : Fin n, k ≤ i.val → i < row →
      |dec (vec rs (k * n + i.val))| / dec (vec ss i.val) <
        |dec (vec rs (k * n + row.val))| / dec (vec ss row.val))

private theorem scaledChoice_post {M : Machine K} {dec : K → ℝ} {N k bound : ℕ}
    (hM : ExactModel dec M) {rs ss : List K} {τ : Tape K}
    (row : Fin (N - k))
    (hmax : ∀ i : Fin (N - k),
      |dec (vec ((rs.drop (k * N + k)).take (N - k)) i.val)| /
          dec (vec ((ss.drop k).take (N - k)) i.val) ≤
        |dec (vec ((rs.drop (k * N + k)).take (N - k)) row.val)| /
          dec (vec ((ss.drop k).take (N - k)) row.val))
    (hfirst : ∀ i : Fin (N - k), i < row →
      |dec (vec ((rs.drop (k * N + k)).take (N - k)) i.val)| /
          dec (vec ((ss.drop k).take (N - k)) i.val) <
        |dec (vec ((rs.drop (k * N + k)).take (N - k)) row.val)| /
          dec (vec ((ss.drop k).take (N - k)) row.val)) :
    (scaledChoiceSpec dec bound).post [N, k] τ [rs, ss]
      [[M.lit (k + row.val : ℕ)]] := by
  let r : Fin N := ⟨k + row.val, by have := row.isLt; omega⟩
  have hr : k ≤ r.val := by dsimp only [r]; omega
  have hx (i : Fin N) (hi : k ≤ i.val) :
      vec ((rs.drop (k * N + k)).take (N - k)) (i.val - k) =
        vec rs (k * N + i.val) := by
    rw [vec_drop_take (by omega), show k * N + k + (i.val - k) = k * N + i.val by omega]
  have hs (i : Fin N) (hi : k ≤ i.val) :
      vec ((ss.drop k).take (N - k)) (i.val - k) = vec ss i.val := by
    rw [vec_drop_take (by omega), Nat.add_sub_of_le hi]
  have hxr := hx r hr
  have hsr := hs r hr
  simp only [r, Nat.add_sub_cancel_left] at hxr hsr
  refine ⟨r, hr, hM.isExactNatLit N _ (by have := row.isLt; omega), ?_, ?_⟩
  · intro i hi
    simpa only [hx i hi, hs i hi, hxr, hsr] using hmax ⟨i.val - k, by omega⟩
  · intro i hi hir
    have hlt : (⟨i.val - k, by omega⟩ : Fin (N - k)) < row := by
      have hh : i.val < r.val := hir
      dsimp only [r] at hh
      change i.val - k < row.val
      omega
    simpa only [hx i hi, hs i hi, hxr, hsr] using hfirst _ hlt

/-- The active scaled scan consumes its actual relative word and records an absolute index.
All singular compatible columns are admitted; no host-selected pivot or run premise is used. -/
theorem scaledChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (scaledChoice (Op := Op) (Tst := Tst)).Meets I (scaledChoiceSpec dec bound) := by
  routine_intro [n, k] (R, scales, p) reads (rs, ss)
  obtain ⟨⟨hkn, hnb⟩, hcompat⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k] [R, scales, p]) (Fp.blocks [p] [1]) _ m
  alloc as relative
  have hRr : R.1 ≠ relative := by change R.1 ≠ m.store.length + 0; omega
  have hSr : scales.1 ≠ relative := by change scales.1 ≠ m.store.length + 0; omega
  have hpr : p.1 ≠ relative := by change p.1 ≠ m.store.length + 0; omega
  have htail := Store.readBlock_sub hrs (o := k * n + k) (n := n - k)
    (by
      have hh : k + 1 ≤ n := by omega
      have hs : n - k + k = n := Nat.sub_add_cancel hkn.le
      nlinarith)
  have hscale := Store.readBlock_sub hss (o := k) (n := n - k) (by omega)
  call (argmaxScaledAbs_meets (bound := bound) hI hcmp hlit hM) [n - k]
    ((R.1, R.2 + k * n + k), (scales.1, scales.2 + k), (relative, 0))
    as m₁ hfr₁ hpos₁ (js) hscan
  case' hcall => exact [((rs.drop (k * n + k)).take (n - k)), ((ss.drop k).take (n - k))]
  case' hr =>
    refine Mem.readBlocks_of_cons ?_ (Mem.readBlocks_of_cons ?_ rfl)
    · change s_relative.readBlock R.1 (R.2 + k * n + k) (n - k) = _
      simpa only [Nat.add_assoc] using Store.Below.readBlock_of hbelow_relative hl.1 htail
    · exact Store.Below.readBlock_of hbelow_relative hl.2.1 hscale
  case' hpre =>
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro i
    have hr : k + i.val < n := by have := i.isLt; omega
    have hc := hcompat ⟨k + i.val, hr⟩ (Nat.le_add_right k i.val)
    have hx : vec ((rs.drop (k * n + k)).take (n - k)) i.val =
        vec rs (k * n + (k + i.val)) := by
      rw [vec_drop_take i.isLt]
      congr 1
      omega
    simpa only [vec_drop_take i.isLt, hx, Nat.add_assoc] using hc
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_relative.length ∧ scales.1 < s_relative.length ∧
      m.store.length < s_relative.length
    simp only [List.length_singleton] at hlen_relative
    omega
  case' hroom =>
    change 0 + 1 ≤ s_relative.len relative ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hrelative.ge, trivial⟩
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  obtain ⟨row, hrow, hmax, hfirst⟩ : ∃ row : Fin (n - k), dec w = row.val ∧
      (∀ i : Fin (n - k),
        |dec (vec ((rs.drop (k * n + k)).take (n - k)) i.val)| /
            dec (vec ((ss.drop k).take (n - k)) i.val) ≤
          |dec (vec ((rs.drop (k * n + k)).take (n - k)) row.val)| /
            dec (vec ((ss.drop k).take (n - k)) row.val)) ∧
      (∀ i : Fin (n - k), i < row →
        |dec (vec ((rs.drop (k * n + k)).take (n - k)) i.val)| /
            dec (vec ((ss.drop k).take (n - k)) i.val) <
          |dec (vec ((rs.drop (k * n + k)).take (n - k)) row.val)| /
            dec (vec ((ss.drop k).take (n - k)) row.val)) := hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hrow (by have := row.isLt; omega) ?_
  step hlit as m₂ hfr₂ ⟨hpos₂, r, hr, hrword⟩
  have he : M.lit (k + row.val : ℕ) = r := by simpa [Machine.indexFn] using hrword
  subst r
  simp only [Machine.indexFn, Nat.add_zero] at hpos₂
  intro s₂ hs₂ hbelow
  refine ⟨hpos₂.trans hpos₁, [[M.lit (k + row.val : ℕ)]],
    Mem.readBlocks_of_cons (Store.Below.readBlock_of hbelow hl.2.2
      (Store.readBlock_one_of_get hr)) rfl, ?_⟩
  exact scaledChoice_post hM row hmax hfirst

end NLAlib.LU
