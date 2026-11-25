/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PartialPivot

/-!
# Fixed-column threshold pivot selection

The actual scalar selector first finds a stable column maximum. It accepts the diagonal when
its absolute value is at least the specified rational fraction of that maximum, including
equality, and otherwise uses the first maximum. Comparisons use the decoded scalar product;
the exact-model theorem proves that this is the requested rational threshold.

## Main definitions

* `NLAlib.LU.thresholdCandidate`: compare the actual diagonal and a selected column entry.
* `NLAlib.LU.thresholdChoice`: the complete active-column threshold selector.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Compare the diagonal with `threshold` times the magnitude of the supplied selected entry.
Equality accepts the diagonal. The fallback copies the actual selected-index word. -/
def thresholdCandidate (threshold : ℚ) : Routine Op Tst :=
  routine% [n, k, row] (R : n * n, maximal : 1) → (p : 1) {
    let diagonal ← alloc 1;
    let largest ← alloc 1;
    let product ← alloc 1;
    run absolute [] (R[k * n + k], diagonal);
    run absolute [] (R[k * n + row], largest);
    call (Has.inj (ScalarOp.lit threshold)) [] () → (product);
    call (Has.inj ScalarOp.mul) [] (product, largest) → (product);
    if (Has.inj CmpTst.le) [] (product, diagonal) {
      call (Has.inj IndexOp.lit) [k] () → (p)
    } else {
      call (Has.inj ScalarOp.copy) [] (maximal) → (p)
    }
  }

variable [Inhabited K]

/-- The reported word decodes to the diagonal index exactly when the rational threshold test
accepts; otherwise it decodes to the supplied current-position row. -/
def thresholdCandidateSpec (dec : K → ℝ) (threshold : ℚ) : Routine.Spec K :=
  spec% [n, k, row] (rs, [w]) → ([r]) requires
    (k ≤ row ∧ row < n) ∧ dec w = row ensures
    dec r = if (threshold : ℝ) * |dec (vec rs (k * n + row))| ≤
      |dec (vec rs (k * n + k))| then k else row

private theorem thresholdCandidate_return {dec : K → ℝ} {threshold : ℚ}
    {n k row : ℕ} {rs : List K} {w r : K} {τ : Tape K}
    {s s' : Store K} {p : ℕ × ℕ} {length pos initialPos : ℕ}
    (hbelow : Store.Below length s s') (hp : p.1 < length) (hpos : pos = initialPos)
    (hr : s.get p.1 p.2 = some r)
    (hd : dec r = if (threshold : ℝ) * |dec (vec rs (k * n + row))| ≤
      |dec (vec rs (k * n + k))| then k else row) :
    ({store := s', pos := pos} : Mem K).pos = initialPos ∧ ∃ ys,
      ({store := s', pos := pos} : Mem K).readBlocks [p] [1] = some ys ∧
        (thresholdCandidateSpec dec threshold).post [n, k, row] τ [rs, [w]] ys := by
  exact ⟨hpos, [[r]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hp (Store.readBlock_one_of_get hr)) rfl, hd⟩

omit [Has IndexOp Op] in
private theorem thresholdCandidate_absolute_geometry {m : Mem K} {R : ℕ × ℕ}
    {scratch n i j : ℕ} {rs : List K}
    (hR : m.store.readBlock R.1 R.2 (n * n) = some rs) (hi : i < n) (hj : j < n)
    (hcap : 1 ≤ m.store.len scratch) :
    m.store.get R.1 (R.2 + i * n + j) = some (vec rs (i * n + j)) ∧
      m.Live [(R.1, R.2 + i * n + j), (scratch, 0)] ∧
      (absolute (Op := Op) (Tst := Tst)).RoomAt m []
        ((absolute (Op := Op) (Tst := Tst)).operands []
          [(R.1, R.2 + i * n + j), (scratch, 0)]) := by
  have hx : m.store.get R.1 (R.2 + i * n + j) = some (vec rs (i * n + j)) := by
    simpa only [Nat.add_assoc] using Store.get_of_readBlock hR (Idx.add_lt_mul hi hj) default
  refine ⟨hx, ?_, ?_⟩
  · simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hx,
      Store.lt_length_of_lt_len (lt_of_lt_of_le Nat.zero_lt_one hcap)⟩
  · change (0 + 1 ≤ m.store.len scratch) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hcap, trivial⟩

/-- The rational threshold comparison follows from actual scalar multiplication, exact
literal decoding and the exact comparison query. No property of the supplied entry as a
maximum is needed for this local decision. -/
theorem thresholdCandidate_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (threshold : ℚ) (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hM : ExactModel dec M) :
    (thresholdCandidate (Op := Op) (Tst := Tst) threshold).Meets I
      (thresholdCandidateSpec dec threshold) := by
  routine_intro [n, k, row] (R, maximal, p) reads (rs, ws)
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  obtain ⟨⟨hkr, hrn⟩, hwd⟩ := hpre
  have hkn : k < n := hkr.trans_lt hrn
  change Writes .total I τ _ (Env.frame [n, k, row] [R, maximal, p])
    (Fp.blocks [p] [1]) _ m
  alloc as diagonal largest product
  have hRd : R.1 ≠ diagonal := by change R.1 ≠ m.store.length + 0; omega
  have hRl : R.1 ≠ largest := by change R.1 ≠ m.store.length + 1; omega
  have hRp : R.1 ≠ product := by change R.1 ≠ m.store.length + 2; omega
  have hpd : p.1 ≠ diagonal := by change p.1 ≠ m.store.length + 0; omega
  have hpl : p.1 ≠ largest := by change p.1 ≠ m.store.length + 1; omega
  have hpp : p.1 ≠ product := by change p.1 ≠ m.store.length + 2; omega
  have hmd : maximal.1 ≠ diagonal := by change maximal.1 ≠ m.store.length + 0; omega
  have hml : maximal.1 ≠ largest := by change maximal.1 ≠ m.store.length + 1; omega
  have hmp : maximal.1 ≠ product := by change maximal.1 ≠ m.store.length + 2; omega
  have hdl : diagonal ≠ largest := by
    change m.store.length + 0 ≠ m.store.length + 1; omega
  have hdp : diagonal ≠ product := by
    change m.store.length + 0 ≠ m.store.length + 2; omega
  have hlp : largest ≠ product := by
    change m.store.length + 1 ≠ m.store.length + 2; omega
  have hrs₀ := Store.Below.readBlock_of hbelow_diagonal hl.1 hrs
  have hdgeom := thresholdCandidate_absolute_geometry (Op := Op) (Tst := Tst)
    (m := ⟨s_diagonal, m.pos⟩) hrs₀ hkn hkn hdiagonal.ge
  have hdiag := hdgeom.1
  call (absolute_meets hI hcmp) [] ((R.1, R.2 + k * n + k), (diagonal, 0))
    as m₁ hfr₁ hpos₁ (ds) hd
  case' hlive => exact hdgeom.2.1
  case' hroom => exact hdgeom.2.2
  have hrs₁ : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  have hlcap : 1 ≤ m₁.store.len largest := by rw [hfr₁.len_eq]; exact hlargest.ge
  have hlgeom := thresholdCandidate_absolute_geometry (Op := Op) (Tst := Tst)
    hrs₁ hkn hrn hlcap
  have hlargest := hlgeom.1
  call (absolute_meets hI hcmp) [] ((R.1, R.2 + k * n + row), (largest, 0))
    as m₂ hfr₂ hpos₂ (ls) hlargestPost
  obtain ⟨d, hdget, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  obtain ⟨l, hlget, rfl⟩ := Store.readBlock_one_eq_some.mp hls
  have hdd := absoluteSpec_decode hM.toStdModel_zero hd
  have hld := absoluteSpec_decode hM.toStdModel_zero hlargestPost
  step (hI (.lit threshold)) as m₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
  have hlget₃ : m₃.store.get largest 0 = some l := by keep
  step (hI .mul) as m₄ hfr₄ ⟨hpos₄, v, hv, rfl⟩
  have hprod : dec (M.mul (M.lit threshold) l) =
      (threshold : ℝ) * |dec (vec rs (k * n + row))| := by rw [hM.mul, hM.lit, hld]
  have hdget₄ : m₄.store.get diagonal 0 = some d := by keep
  have hdecision : (dec (M.mul (M.lit threshold) l) ≤ dec d) ↔
      (threshold : ℝ) * |dec (vec rs (k * n + row))| ≤
        |dec (vec rs (k * n + k))| := by rw [hprod, hdd]
  refine writes_ite rfl rfl (hcmp.test_le hv hdget₄) ?_
  by_cases hle : dec (M.mul (M.lit threshold) l) ≤ dec d
  · simp only [hle, decide_true, ite_true]
    step hlit as m₅ hfr₅ ⟨hpos₅, v, hv, hword⟩
    have he : M.lit (k : ℕ) = v := by simpa [Machine.indexFn] using hword
    subst v
    simp only [Machine.indexFn, Nat.add_zero] at hpos₅
    intro s₅ hs₅ hbelow
    apply thresholdCandidate_return (τ := τ.shift m.pos) (w := w)
      (pos := m₅.pos) (initialPos := m.pos)
      hbelow hl.2.2 (by omega) hv
    rw [if_pos (hdecision.mp hle)]
    exact hM.isExactNatLit n k hkn.le
  · simp only [hle, decide_false, Bool.false_eq_true, ite_false]
    have hwm : m₄.store.get maximal.1 maximal.2 = some w := by keep
    step (hI .copy) as m₅ hfr₅ ⟨hpos₅, v, hv, rfl⟩
    intro s₅ hs₅ hbelow
    apply thresholdCandidate_return (τ := τ.shift m.pos) (w := w)
      (pos := m₅.pos) (initialPos := m.pos)
      hbelow hl.2.2 (by omega) hv
    simpa only [if_neg (fun h => hle (hdecision.mpr h))] using hwd

section Choice

variable [Has IdxTst Tst]

/-- Find the stable column maximum, then accept the diagonal at the rational threshold or
fall back to that first maximum. The two output words are actual current row and column
indices, and the diagonal/product scratch is allocated after the maximum scan returns. -/
def thresholdChoice (threshold : ℚ) : Routine Op Tst :=
  routine% [n, k] (R : n * n) → (p : 2) {
    let maximal ← alloc 2;
    run partialChoice [n, k] (R, maximal);
    let row ← index (Has.inj IdxTst.toNat) (maximal) ≤ n - 1;
    run (thresholdCandidate threshold) [n, k, row] (R, maximal, p);
    call (Has.inj IndexOp.lit) [k] () → (p[1])
  }

/-- The selector records the threshold decision against a stable active-column maximum.
The diagonal is accepted at equality, including a zero column. Fallback ties retain the
first maximum from the original active column. -/
def thresholdChoiceSpec (dec : K → ℝ) (threshold : ℚ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs) → ([r, c]) requires k < n ∧ n ≤ bound ensures
    ∃ maximal : Fin n, k ≤ maximal.val ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec rs (k * n + i.val))| ≤ |dec (vec rs (k * n + maximal.val))|) ∧
      (∀ i : Fin n, k ≤ i.val → i < maximal →
        |dec (vec rs (k * n + i.val))| < |dec (vec rs (k * n + maximal.val))|) ∧
      dec r = (if (threshold : ℝ) * |dec (vec rs (k * n + maximal.val))| ≤
        |dec (vec rs (k * n + k))| then k else maximal.val) ∧ dec c = k

/-- The full threshold selector consumes the actual bounded maximum index and executes the
specified acceptance test. Exactness of the rational literal is supplied by `ExactModel`;
a bounded natural-literal hypothesis alone would not justify the threshold arithmetic. -/
theorem thresholdChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {bound : ℕ} (threshold : ℚ) (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (thresholdChoice (Op := Op) (Tst := Tst) threshold).Meets I
      (thresholdChoiceSpec dec threshold bound) := by
  routine_intro [n, k] (R, p) reads (rs)
  obtain ⟨hkn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k] [R, p]) (Fp.blocks [p] [2]) _ m
  alloc as maximal
  have hRm : R.1 ≠ maximal := by change R.1 ≠ m.store.length + 0; omega
  have hpm : p.1 ≠ maximal := by change p.1 ≠ m.store.length + 0; omega
  call (partialChoice_meets hI hcmp hlit hQ hM.toStdModel_zero (hM.isExactNatLit bound))
    [n, k] (R, (maximal, 0)) (pre := ⟨hkn, hnb⟩)
    as m₁ hfr₁ hpos₁ (choices) hmaximal
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_maximal.length ∧ m.store.length < s_maximal.length
    simp only [List.length_singleton] at hlen_maximal
    omega
  case' hroom =>
    change 0 + 2 ≤ s_maximal.len maximal ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hmaximal.ge, trivial⟩
  obtain ⟨rw, cw, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hchoices)
  obtain ⟨row, hkr, hdr, _, hmax, hfirst⟩ := hmaximal
  have hw : m₁.store.get maximal 0 = some rw := by
    simpa [vec] using Store.get_of_readBlock hchoices (j := 0) (by omega) default
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hdr (by have := row.isLt; omega) ?_
  have hrs₁ : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (thresholdCandidate_meets threshold hI hcmp hlit hM) [n, k, row.val]
    (R, (maximal, 0), p) (pre := ⟨⟨hkr, row.isLt⟩, hdr⟩)
    as m₂ hfr₂ hpos₂ (rs') hcandidate
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    have hml := Store.lt_length_of_get hw
    have hlen := hfr₁.length_eq
    simp only [List.length_singleton] at hlen_maximal
    exact ⟨by omega, hml, by omega⟩
  obtain ⟨r, hr, rfl⟩ := Store.readBlock_one_eq_some.mp hrs'
  step hlit as m₃ hfr₃ ⟨hpos₃, c, hc, hcword⟩
  have he : M.lit (k : ℕ) = c := by simpa [Machine.indexFn] using hcword
  subst c
  simp only [Machine.indexFn, Nat.add_zero] at hpos₃
  intro s₃ hs₃ hbelow
  have hread : m₃.store.readBlock p.1 p.2 2 = some [r, M.lit (k : ℕ)] :=
    Store.readBlock_succ_of (Store.readBlock_one_of_get (by keep)) hc
  exact ⟨hpos₃.trans (hpos₂.trans hpos₁), _, Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hl.2 hread) rfl,
    row, hkr, hmax, hfirst, hcandidate, hM.isExactNatLit n k hkn.le⟩

private theorem thresholdChoice_quality {dec : K → ℝ} {threshold : ℚ} {bound n k : ℕ}
    {rs : List K} {r c : K} {τ : Tape K} (hkn : k < n)
    (hτ : 0 ≤ (threshold : ℝ)) (hτ₁ : (threshold : ℝ) ≤ 1)
    (h : (thresholdChoiceSpec dec threshold bound).post [n, k] τ [rs] [[r, c]]) :
    (choiceSpec dec (threshold : ℝ) bound true).post [n, k] τ [rs] [[r, c]] := by
  obtain ⟨maximal, hkm, hmax, _, hdr, hdc⟩ := h
  by_cases ha : (threshold : ℝ) * |dec (vec rs (k * n + maximal.val))| ≤
      |dec (vec rs (k * n + k))|
  · refine ⟨⟨k, hkn⟩, ⟨k, hkn⟩, le_rfl, le_rfl, ?_, hdc, fun _ => rfl, ?_⟩
    · simpa only [if_pos ha] using hdr
    · intro i hi
      exact (mul_le_mul_of_nonneg_left (hmax i hi) hτ).trans ha
  · refine ⟨maximal, ⟨k, hkn⟩, hkm, le_rfl, ?_, hdc, fun _ => rfl, ?_⟩
    · simpa only [if_neg ha] using hdr
    · intro i hi
      calc
        (threshold : ℝ) * |dec (vec rs (k * n + i.val))| ≤
            1 * |dec (vec rs (k * n + i.val))| :=
          mul_le_mul_of_nonneg_right hτ₁ (abs_nonneg _)
        _ ≤ |dec (vec rs (k * n + maximal.val))| := by simpa only [one_mul] using hmax i hi

/-- A positive rational threshold at most one supplies its declared column-quality fraction.
The actual selector's stronger diagonal-acceptance and first-fallback tie properties remain
in `thresholdChoiceSpec`; this theorem discharges the common driver policy interface. -/
theorem thresholdChoice_meets_choice {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {bound : ℕ} (threshold : ℚ) (hτ : 0 < threshold) (hτ₁ : threshold ≤ 1)
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (thresholdChoice (Op := Op) (Tst := Tst) threshold).Meets I
      (choiceSpec dec (threshold : ℝ) bound true) := by
  routine_intro [n, k] (R, p) reads (rs)
  have hraw := (thresholdChoice_meets threshold hI hcmp hlit hQ hM)
    [n, k] [R, p] τ m [rs] rfl rfl hlive hsep hr hpre hrooms
  refine hraw.mono le_rfl ?_
  rintro m' hfr ⟨hpos, ys, hys, hpost⟩
  change m'.readBlocks [p] [2] = some ys at hys
  obtain ⟨ws, rest, hws, hrest, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  simp only [Mem.readBlocks_nil, Option.some.injEq] at hrest
  subst rest
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hws)
  refine ⟨hpos, [[r, c]], Mem.readBlocks_of_cons hws rfl, ?_⟩
  have hτR : 0 ≤ (threshold : ℝ) := by exact_mod_cast hτ.le
  have hτR₁ : (threshold : ℝ) ≤ 1 := by exact_mod_cast hτ₁
  exact thresholdChoice_quality hpre.1 hτR hτR₁ hpost

end Choice

end NLAlib.LU
