/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.CompleteColumn

/-!
# Actual complete pivot selection

Each active column is scanned by `completeColumn`. The incumbent changes only on a strict
magnitude improvement. Both selected indices are actual stored words, with ties ordered by
column first and then row. No host-selected pivot or assumed successful scan is used.

## Main results

* `NLAlib.LU.completeChoice_meets` proves actual success and the stated stored-output guarantee.

-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Compare the actual incumbent and candidate scores. A strict improvement copies the
candidate row word and score, and records the current column as an index literal. -/
def improveComplete : Routine Op Tst :=
  routine% [c] (r : 1, a : 1, b : 1, p : 2) → (b, p) {
    if (Has.inj CmpTst.lt) [] (b, a) {
      call (Has.inj ScalarOp.copy) [] (a) → (b);
      call (Has.inj ScalarOp.copy) [] (r) → (p);
      call (Has.inj IndexOp.lit) [c] () → (p[1])
    } else {
      skip
    }
  }

/-- Scan one active column and strictly improve the incumbent stored pair when appropriate.
The candidate row and magnitude words are scoped; the source matrix remains read only. -/
def advanceComplete : Routine Op Tst :=
  routine% [n, k, c] (R : n * n, best : 1, p : 2) → (best, p) {
    let candidateRow ← alloc 1;
    let candidateMagnitude ← alloc 1;
    run completeColumn [n, k, c] (R, candidateRow, candidateMagnitude);
    run improveComplete [c] (candidateRow, candidateMagnitude, best, p)
  }

/-- Scan all active columns, retaining the first column-major maximum. Each candidate row
comes from an actual bounded query of the shared line selector's stored output. -/
def completeChoice : Routine Op Tst := routine% [n, k] (R : n * n) → (p : 2) {
  let best ← alloc 1;
  run completeColumn [n, k, k] (R, p, best);
  call (Has.inj IndexOp.lit) [k] () → (p[1]);
  for j < n - k - 1 {
    run advanceComplete [n, k, k + j + 1] (R, best, p)
  }
}

variable [Inhabited K]

/-- Both actual output words decode to active current-position indices. The selected entry
is a maximum of the whole active square, with strict inequality for all earlier cells in
column-major order. All integer literals lie within the declared matrix-order allowance. -/
def completeChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs) → ([r, c]) requires k < n ∧ n ≤ bound ensures
    ∃ row col : Fin n, k ≤ row.val ∧ k ≤ col.val ∧ dec r = row.val ∧ dec c = col.val ∧
      (∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
        |dec (vec rs (j.val * n + i.val))| ≤ |dec (vec rs (col.val * n + row.val))|) ∧
      (∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
        (j < col ∨ j = col ∧ i < row) →
        |dec (vec rs (j.val * n + i.val))| < |dec (vec rs (col.val * n + row.val))|)

/-- The primitive improvement preserves the old words unless its actual decoded comparison
is strict; in that case it copies the candidate words and records the column literal. -/
def improveCompleteSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [c] ([r], [a], [b], [pr, pc]) → ([b'], [r', c']) ensures
    if dec b < dec a then b' = a ∧ r' = r ∧ c' = M.lit (c : ℕ)
    else b' = b ∧ r' = pr ∧ c' = pc

omit [Has IdxTst Tst] [Inhabited K] in
/-- Each actual comparison, scalar copy and index literal succeeds from the primitive laws. -/
theorem improveComplete_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I) :
    (improveComplete (Op := Op) (Tst := Tst)).Meets I (improveCompleteSpec M dec) := by
  routine_intro [c] (r, a, b, p) reads (rs, ass, bs, ps)
  obtain ⟨r₀, hr₀, rfl⟩ := Store.readBlock_one_eq_some.mp hrs
  obtain ⟨a₀, ha₀, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  obtain ⟨b₀, hb₀, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨pr, pc, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
  refine writes_ite rfl rfl (hcmp.test_lt hb₀ ha₀) ?_
  by_cases hlt : dec b₀ < dec a₀
  · simp only [hlt, decide_true, ite_true]
    step (hI .copy) as m₁ hfr₁ ⟨hpos₁, v, hv, rfl⟩
    step (hI .copy) as m₂ hfr₂ ⟨hpos₂, w, hw, rfl⟩
    step hlit as m₃ hfr₃ ⟨hpos₃, z, hz, hword⟩
    have he : M.lit (c : ℕ) = z := by simpa [Machine.indexFn] using hword
    subst z
    simp only [Machine.indexFn, Nat.add_zero] at hpos₃
    refine ⟨hpos₃.trans (hpos₂.trans hpos₁), [[a₀], [r₀, M.lit (c : ℕ)]],
      Mem.readBlocks_of_cons (Store.readBlock_one_of_get (by keep))
        (Mem.readBlocks_of_cons
          (Store.readBlock_succ_of (Store.readBlock_one_of_get (by keep)) hz) rfl), ?_⟩
    change if dec b₀ < dec a₀ then _ else _
    rw [if_pos hlt]
    exact ⟨rfl, rfl, rfl⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
    apply wp_skip
    refine ⟨Store.EqOff.refl _ _, rfl, [[b₀], [pr, pc]],
      Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hps rfl), ?_⟩
    change if dec b₀ < dec a₀ then _ else _
    rw [if_neg hlt]
    exact ⟨rfl, rfl, rfl⟩

/-- A column advance records the actual candidate row and magnitude and the exact words
produced by its strict-improvement subroutine. The candidate is the first column maximum. -/
def advanceCompleteSpec (M : Machine K) (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k, c] tape t (rs, [b], [pr, pc]) → ([b'], [r', c']) requires
    k < n ∧ c < n ∧ n ≤ bound ensures
    ∃ v a : K,
      (completeColumnSpec dec bound).post [n, k, c] t [rs] [[v], [a]] ∧
      (improveCompleteSpec M dec).post [c] t [[v], [a], [b], [pr, pc]] [[b'], [r', c']]

/-- The column advance executes its actual scan and incumbent update using two scoped
candidate words. Its output specification preserves the original input words. -/
theorem advanceComplete_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (advanceComplete (Op := Op) (Tst := Tst)).Meets I (advanceCompleteSpec M dec bound) := by
  routine_intro [n, k, c] (R, best, p) reads (rs, bs, ps)
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨pr, pc, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
  change Writes .total I τ _ (Env.frame [n, k, c] [R, best, p, best, p])
    (Fp.blocks [best, p] [1, 2]) _ m
  alloc as candidateRow candidateMagnitude
  have hRr : R.1 ≠ candidateRow := by change R.1 ≠ m.store.length + 0; omega
  have hRa : R.1 ≠ candidateMagnitude := by change R.1 ≠ m.store.length + 1; omega
  have hbr : best.1 ≠ candidateRow := by change best.1 ≠ m.store.length + 0; omega
  have hba : best.1 ≠ candidateMagnitude := by change best.1 ≠ m.store.length + 1; omega
  have hpr : p.1 ≠ candidateRow := by change p.1 ≠ m.store.length + 0; omega
  have hpa : p.1 ≠ candidateMagnitude := by change p.1 ≠ m.store.length + 1; omega
  have hra : candidateRow ≠ candidateMagnitude := by
    change m.store.length + 0 ≠ m.store.length + 1; omega
  call (completeColumn_meets hI hcmp hlit hQ hM hNat) [n, k, c]
    (R, (candidateRow, 0), (candidateMagnitude, 0)) (pre := hpre)
    as m₁ hfr₁ hpos₁ (rows, ass) hscan
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_candidateRow.length ∧ m.store.length < s_candidateRow.length ∧
      m.store.length + 1 < s_candidateRow.length
    simp only [List.length_cons, List.length_nil] at hlen_candidateRow
    omega
  case' hroom =>
    change (0 + 1 ≤ s_candidateRow.len candidateRow ∧
      0 + 1 ≤ s_candidateRow.len candidateMagnitude ∧ True)
    rw [hcandidateRow, hcandidateMagnitude]
    exact ⟨by omega, by omega, trivial⟩
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hrows
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  have hb₁ : m₁.store.get best.1 best.2 = some b := by keep
  have hpr₀ : m.store.get p.1 p.2 = some pr := by
    simpa using Store.get_of_readBlock hps (by omega : 0 < 2) default
  have hpr₁ : m₁.store.get p.1 p.2 = some pr := by keep
  have hpc₀ : m.store.get p.1 (p.2 + 1) = some pc := by
    simpa using Store.get_of_readBlock hps (by omega : 1 < 2) default
  have hpc₁ : m₁.store.get p.1 (p.2 + 1) = some pc := by keep
  call (improveComplete_meets hI hcmp hlit) [c]
    ((candidateRow, 0), (candidateMagnitude, 0), best, p)
    as m₂ hfr₂ hpos₂ (bs, ps) hchange
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hv, Store.lt_length_of_get ha,
      Store.lt_length_of_get hb₁, Store.lt_length_of_get hpr₁⟩
  obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨r', c', rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
  intro s₂ hs₂ hbelow
  refine ⟨hpos₂.trans hpos₁, [[b'], [r', c']], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hl.2.1 (Store.readBlock_one_of_get hb'))
    (Mem.readBlocks_of_cons (Store.Below.readBlock_of hbelow hl.2.2 hps) rfl), ?_⟩
  exact ⟨v, a, hscan, hchange⟩

private def IsCompleteMax {N : ℕ} (score : Fin N → Fin N → ℝ)
    (start covered : ℕ) (row col : Fin N) : Prop :=
  start ≤ row.val ∧ start ≤ col.val ∧ col.val < covered ∧
    (∀ i j : Fin N, start ≤ i.val → start ≤ j.val → j.val < covered →
      score i j ≤ score row col) ∧
    (∀ i j : Fin N, start ≤ i.val → start ≤ j.val →
      (j < col ∨ j = col ∧ i < row) → score i j < score row col)

private def IsCompletePrefix (dec : K → ℝ) (xs : List K) (N start covered : ℕ)
    (best index : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ row col : Fin N, ∃ b r c : K,
    s.get best.1 best.2 = some b ∧ s.get index.1 index.2 = some r ∧
    s.get index.1 (index.2 + 1) = some c ∧
    dec b = |dec (vec xs (col.val * N + row.val))| ∧ dec r = row.val ∧ dec c = col.val ∧
    IsCompleteMax (fun i j => |dec (vec xs (j.val * N + i.val))|) start covered row col

private theorem completeMax_initial {N start : ℕ} {score : Fin N → Fin N → ℝ}
    (col row : Fin N) (hc : col.val = start) (hr : start ≤ row.val)
    (hmax : ∀ i : Fin N, start ≤ i.val → score i col ≤ score row col)
    (hfirst : ∀ i : Fin N, start ≤ i.val → i < row → score i col < score row col) :
    IsCompleteMax score start (start + 1) row col := by
  refine ⟨hr, hc.ge, by omega, ?_, ?_⟩
  · intro i j hi hj hjc
    have he : j = col := Fin.ext (by omega)
    subst j
    exact hmax i hi
  · intro i j hi hj he
    rcases he with hlt | ⟨rfl, hir⟩
    · have := (show j.val < col.val from hlt)
      omega
    · exact hfirst i hi hir

private theorem completeMax_improve {N start covered : ℕ} {score : Fin N → Fin N → ℝ}
    {row col q c : Fin N} (h : IsCompleteMax score start covered row col)
    (hc : c.val = covered) (hq : start ≤ q.val)
    (hmax : ∀ i : Fin N, start ≤ i.val → score i c ≤ score q c)
    (hfirst : ∀ i : Fin N, start ≤ i.val → i < q → score i c < score q c)
    (hbetter : score row col < score q c) :
    IsCompleteMax score start (covered + 1) q c := by
  obtain ⟨hr, hl, hu, hm, hf⟩ := h
  refine ⟨hq, by omega, by omega, ?_, ?_⟩
  · intro i j hi hj hjc
    by_cases he : j = c
    · subst j
      exact hmax i hi
    · have hjc' : j.val < covered := by
        have hne : j.val ≠ c.val := fun h => he (Fin.ext h)
        omega
      exact (hm i j hi hj hjc').trans hbetter.le
  · intro i j hi hj he
    rcases he with hlt | ⟨rfl, hir⟩
    · exact (hm i j hi hj (by have hj : j.val < c.val := hlt; omega)).trans_lt hbetter
    · exact hfirst i hi hir

private theorem completeMax_retain {N start covered : ℕ} {score : Fin N → Fin N → ℝ}
    {row col q c : Fin N} (h : IsCompleteMax score start covered row col)
    (hc : c.val = covered)
    (hmax : ∀ i : Fin N, start ≤ i.val → score i c ≤ score q c)
    (hnot : ¬ score row col < score q c) :
    IsCompleteMax score start (covered + 1) row col := by
  obtain ⟨hr, hl, hu, hm, hf⟩ := h
  refine ⟨hr, hl, by omega, ?_, hf⟩
  intro i j hi hj hjc
  by_cases he : j = c
  · subst j
    exact (hmax i hi).trans (le_of_not_gt hnot)
  · exact hm i j hi hj (by have hne : j.val ≠ c.val := fun h => he (Fin.ext h); omega)

private theorem completePrefix_return {dec : K → ℝ} {xs : List K}
    {N start bound : ℕ} {best index : ℕ × ℕ} {s s' : Store K}
    {length pos initialPos : ℕ}
    (h : IsCompletePrefix dec xs N start N best index s)
    (hbelow : Store.Below length s s') (hindex : index.1 < length)
    (hpos : pos = initialPos) (τ : Tape K) :
    ({ store := s', pos := pos } : Mem K).pos = initialPos ∧
      ∃ ys, ({ store := s', pos := pos } : Mem K).readBlocks [index] [2] = some ys ∧
        (completeChoiceSpec dec bound).post [N, start] τ [xs] ys := by
  obtain ⟨row, col, b, r, c, hb, hr, hc, hd, hdr, hdc, hkr, hkc, hcn, hmax, hfirst⟩ := h
  have hread := Store.readBlock_succ_of (Store.readBlock_one_of_get hr) hc
  exact ⟨hpos, [[r, c]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hindex hread) rfl,
    row, col, hkr, hkc, hdr, hdc, fun i j hi hj => hmax i j hi hj j.isLt, hfirst⟩

private theorem completePrefix_changed {M : Machine K} {dec : K → ℝ}
    {xs : List K} {N start covered bound : ℕ} {row col q c : Fin N}
    {best index : ℕ × ℕ} {s : Store K} {b r w a v b' r' c' : K} {τ : Tape K}
    (hNat : IsExactNatLit dec M bound) (hN : N ≤ bound)
    (hprev : IsCompleteMax (fun i j => |dec (vec xs (j.val * N + i.val))|)
      start covered row col)
    (hc : c.val = covered) (hq : start ≤ q.val)
    (hb : dec b = |dec (vec xs (col.val * N + row.val))|)
    (hr : dec r = row.val) (hw : dec w = col.val) (hv : dec v = q.val)
    (ha : dec a = |dec (vec xs (c.val * N + q.val))|)
    (hmax : ∀ i : Fin N, start ≤ i.val →
      |dec (vec xs (c.val * N + i.val))| ≤ |dec (vec xs (c.val * N + q.val))|)
    (hfirst : ∀ i : Fin N, start ≤ i.val → i < q →
      |dec (vec xs (c.val * N + i.val))| < |dec (vec xs (c.val * N + q.val))|)
    (hout : (improveCompleteSpec M dec).post [covered] τ [[v], [a], [b], [r, w]]
      [[b'], [r', c']])
    (hbg : s.get best.1 best.2 = some b') (hrg : s.get index.1 index.2 = some r')
    (hcg : s.get index.1 (index.2 + 1) = some c') :
    IsCompletePrefix dec xs N start (covered + 1) best index s := by
  change (if dec b < dec a then _ else _) at hout
  by_cases hbetter : dec b < dec a
  · rw [if_pos hbetter] at hout
    obtain ⟨heB, heR, heC⟩ := hout
    rw [heB] at hbg
    rw [heR] at hrg
    rw [heC] at hcg
    refine ⟨q, c, a, v, M.lit (covered : ℕ), hbg, hrg, hcg, ha, hv, ?_, ?_⟩
    · simpa only [hc] using hNat covered (by have := c.isLt; omega)
    · exact completeMax_improve hprev hc hq hmax hfirst (by simpa only [hb, ha] using hbetter)
  · rw [if_neg hbetter] at hout
    obtain ⟨heB, heR, heC⟩ := hout
    rw [heB] at hbg
    rw [heR] at hrg
    rw [heC] at hcg
    exact ⟨row, col, b, r, w, hbg, hrg, hcg, hb, hr, hw,
      completeMax_retain hprev hc hmax (by simpa only [hb, ha] using hbetter)⟩

/-- Actual complete pivot selection succeeds from bounded dimensions and local primitive
contracts. It retains the first column-major maximum, including all-zero active squares. -/
theorem completeChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (completeChoice (Op := Op) (Tst := Tst)).Meets I (completeChoiceSpec dec bound) := by
  routine_intro [n, k] (R, p) reads (rs)
  obtain ⟨hkn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k] [R, p]) (Fp.blocks [p] [2]) _ m
  alloc as best
  have hRb : R.1 ≠ best := by change R.1 ≠ m.store.length + 0; omega
  have hpb : p.1 ≠ best := by change p.1 ≠ m.store.length + 0; omega
  call (completeColumn_meets hI hcmp hlit hQ hM hNat) [n, k, k] (R, p, (best, 0))
    (pre := ⟨hkn, hkn, hnb⟩) as m₁ hfr₁ hpos₁ (rows, bs) hscan
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_best.length ∧ p.1 < s_best.length ∧ m.store.length < s_best.length
    simp only [List.length_cons, List.length_nil] at hlen_best
    omega
  case' hroom =>
    change (p.2 + 1 ≤ s_best.len p.1 ∧ 0 + 1 ≤ s_best.len best ∧ True)
    rw [(hbelow_best p.1 hl.2).1, hbest]
    exact ⟨by omega, by omega, trivial⟩
  obtain ⟨wr, hwr, rfl⟩ := Store.readBlock_one_eq_some.mp hrows
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨row, hkr, hdr, hbd, hmax, hfirst⟩ := hscan
  step hlit as m₂ hfr₂ ⟨hpos₂, wc, hwc, hword⟩
  have he : M.lit (k : ℕ) = wc := by simpa [Machine.indexFn] using hword
  subst wc
  simp only [Machine.indexFn, Nat.add_zero] at hpos₂
  have hstart : IsCompletePrefix dec rs n k (k + 1) (best, 0) p m₂.store :=
    ⟨row, ⟨k, hkn⟩, b, wr, M.lit (k : ℕ), by keep, by keep, hwc, hbd, hdr,
      hNat k (by omega), completeMax_initial ⟨k, hkn⟩ row rfl hkr hmax hfirst⟩
  loop_inv (fun _ => Fp.blocks [(best, 0), p] [1, 2])
    (fun j μ => μ.pos = m.pos ∧ IsCompletePrefix dec rs n k (k + j + 1) (best, 0) p μ.store)
    with j hj m₃ hfr hP
  case round =>
    obtain ⟨hp, row, col, b, r, c, hb, hr, hc, hbd, hrd, hcd, hprev⟩ := hP
    have hcn : k + j + 1 < n := by omega
    have hR₃ : m₃.store.readBlock R.1 R.2 (n * n) = some rs := by keep
    have hps₃ : m₃.store.readBlock p.1 p.2 2 = some [r, c] :=
      Store.readBlock_succ_of (Store.readBlock_one_of_get hr) hc
    call (advanceComplete_meets hI hcmp hlit hQ hM hNat) [n, k, k + j + 1]
      (R, (best, 0), p) (pre := ⟨hkn, hcn, hnb⟩)
      as m₄ hfr₄ hpos₄ (bs, ps) hadvance
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      exact ⟨Store.lt_length_of_get (Store.get_of_readBlock hR₃
          (j := 0) (by nlinarith : 0 < n * n) default),
        Store.lt_length_of_get hb, Store.lt_length_of_get hr⟩
    case' hroom =>
      change (0 + 1 ≤ m₃.store.len best ∧ p.2 + 2 ≤ m₃.store.len p.1 ∧ True)
      exact ⟨by simpa using Nat.succ_le_of_lt (Store.lt_len_of_get hb),
        by have := Store.lt_len_of_get hc; omega, trivial⟩
    obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs
    obtain ⟨r', c', rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
    obtain ⟨v, a, hscan, hchange⟩ := hadvance
    obtain ⟨q, hkq, hdv, hda, hmax, hfirst⟩ := hscan
    refine ⟨hpos₄.trans hp, ?_⟩
    have hstep := completePrefix_changed hNat hnb hprev (c := ⟨k + j + 1, hcn⟩) rfl
      hkq hbd hrd hcd hdv hda hmax hfirst hchange hb'
      (by simpa using Store.get_of_readBlock hps (by omega : 0 < 2) default)
      (by simpa using Store.get_of_readBlock hps (by omega : 1 < 2) default)
    convert hstep using 1
    omega
  case initial => exact ⟨hpos₂.trans hpos₁, hstart⟩
  case exit =>
    rintro m₃ _ ⟨hp, hstate⟩ s₃ hs₃ hbelow
    have he : k + (n - k - 1) + 1 = n := by omega
    rw [he] at hstate
    exact completePrefix_return hstate hbelow hl.2 hp _

/-- Complete magnitude dominance supplies unit column quality for the shared all-input
pivoted driver. The policy additionally retains its stronger first-tie square maximum. -/
theorem completeChoiceSpec_choiceSpec {dec : K → ℝ} {bound n k : ℕ}
    {rs : List K} {r c : K} {τ : Tape K}
    (h : (completeChoiceSpec dec bound).post [n, k] τ [rs] [[r, c]]) :
    (choiceSpec dec 1 bound false).post [n, k] τ [rs] [[r, c]] := by
  obtain ⟨row, col, hkr, hkc, hdr, hdc, hmax, hfirst⟩ := h
  exact ⟨row, col, hkr, hkc, hdr, hdc, by simp,
    fun i hi => by simpa only [one_mul] using hmax i col hi hkc⟩

end NLAlib.LU
