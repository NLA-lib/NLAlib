/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Absolute
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.ForMathlib.Order.Fin.Basic
public import NLAlib.Matrix.Factorizations.LU.Pivot

/-!
# Stable absolute-value pivot selection

The selector scans a nonempty stored vector from its first word. It updates the incumbent
only at a strict improvement, so equal scores retain the first index. Magnitudes use exact
sign comparisons and machine negation, and the selected index is written by a dimension
literal. The containing factorization consumes this actual stored index.

## Main definitions

* `NLAlib.LU.argmaxAbs`: the fixed scalar selector.
* `NLAlib.LU.argmaxAbsSpec`: range, maximality and first-index tie behavior.

## Main results

The selector is used by partial pivoting on the active column.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Select the first index with largest decoded absolute value. Two scratch words hold the
incumbent and candidate magnitudes; the caller's output holds the actual selected index. -/
def argmaxAbs : Routine Op Tst := routine% [n] (x : n) → (j : 1) {
  let best ← alloc 1;
  let candidate ← alloc 1;
  run absolute [] (x, best);
  call (Has.inj IndexOp.lit) [0] () → (j);
  for i < n - 1 {
    run absolute [] (x[i + 1], candidate);
    if (Has.inj CmpTst.lt) [] (best, candidate) {
      call (Has.inj ScalarOp.copy) [] (candidate) → (best);
      call (Has.inj IndexOp.lit) [i + 1] () → (j)
    } else {
      skip
    }
  }
}

variable [Inhabited K]

/-- The input length is positive and within the natural-literal allowance. The output is an
exactly decoded index whose magnitude is maximal; every earlier position is strictly smaller. -/
def argmaxAbsSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n] (xs) → ([j]) requires (0 < n ∧ n ≤ bound) ensures
    ∃ i : Fin n, dec j = i.val ∧
      (∀ t : Fin n, |dec (vec xs t)| ≤ |dec (vec xs i)|) ∧
      (∀ t : Fin n, t < i → |dec (vec xs t)| < |dec (vec xs i)|)

private def IsAbsPrefix (dec : K → ℝ) (xs : List K) (N covered : ℕ)
    (best index : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ q : Fin N, ∃ b w : K,
    s.get best.1 best.2 = some b ∧ s.get index.1 index.2 = some w ∧
    dec b = |dec (vec xs q)| ∧ dec w = q.val ∧ q.val < covered ∧
    (∀ t : Fin N, t.val < covered → |dec (vec xs t)| ≤ |dec (vec xs q)|) ∧
    (∀ t : Fin N, t < q → |dec (vec xs t)| < |dec (vec xs q)|)

private theorem absPrefix_initial {dec : K → ℝ} {xs : List K} {N : ℕ} (hN : 0 < N)
    {best index : ℕ × ℕ} {s : Store K} {b w : K}
    (hb : s.get best.1 best.2 = some b) (hw : s.get index.1 index.2 = some w)
    (hbd : dec b = |dec (vec xs 0)|) (hwd : dec w = 0) :
    IsAbsPrefix dec xs N 1 best index s := by
  refine ⟨⟨0, hN⟩, b, w, hb, hw, hbd, by simpa using hwd, Nat.zero_lt_one, ?_, ?_⟩
  · intro t ht
    have he : t.val = 0 := by omega
    simpa only [he] using (le_rfl : |dec (vec xs 0)| ≤ |dec (vec xs 0)|)
  · intro t ht
    exact (Nat.not_lt_zero t.val ht).elim

private theorem absPrefix_output {dec : K → ℝ} {xs : List K} {N bound : ℕ}
    {best index : ℕ × ℕ} {s : Store K} (h : IsAbsPrefix dec xs N N best index s)
    (τ : Tape K) :
    ∃ w : K, s.readBlock index.1 index.2 1 = some [w] ∧
      (argmaxAbsSpec dec bound).post [N] τ [xs] [[w]] := by
  obtain ⟨q, b, w, hb, hw, hbd, hwd, hq, hdom, hfirst⟩ := h
  refine ⟨w, Store.readBlock_one_of_get hw, q, hwd, ?_, hfirst⟩
  intro t
  exact hdom t t.isLt

private theorem absPrefix_return {dec : K → ℝ} {xs : List K} {N bound : ℕ}
    {best index : ℕ × ℕ} {s s' : Store K} {length pos initialPos : ℕ}
    (hN : 0 < N) (h : IsAbsPrefix dec xs N (N - 1 + 1) best index s)
    (hbelow : Store.Below length s s')
    (hindex : index.1 < length) (hpos : pos = initialPos) (τ : Tape K) :
    ({ store := s', pos := pos } : Mem K).pos = initialPos ∧
      ∃ ys, ({ store := s', pos := pos } : Mem K).readBlocks [index] [1] = some ys ∧
        (argmaxAbsSpec dec bound).post [N] τ [xs] ys := by
  have he : N - 1 + 1 = N := by omega
  rw [he] at h
  obtain ⟨w, hw, hpost⟩ := absPrefix_output (bound := bound) h τ
  exact ⟨hpos, [[w]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hindex hw) rfl, hpost⟩

private theorem absPrefix_choose {dec : K → ℝ} {xs : List K} {N covered : ℕ}
    (q t : Fin N) (ht : t.val = covered) (hq : q.val < covered)
    (hdom : ∀ a : Fin N, a.val < covered → |dec (vec xs a)| ≤ |dec (vec xs q)|)
    (hfirst : ∀ a : Fin N, a < q → |dec (vec xs a)| < |dec (vec xs q)|)
    {best index : ℕ × ℕ} {s : Store K} {b w : K}
    (hb : s.get best.1 best.2 = some b) (hw : s.get index.1 index.2 = some w)
    (hbd : dec b = |dec (vec xs (if |dec (vec xs q)| < |dec (vec xs t)| then t else q))|)
    (hwd : dec w = (if |dec (vec xs q)| < |dec (vec xs t)| then t else q).val) :
    IsAbsPrefix dec xs N (covered + 1) best index s := by
  have hh := Fin.max_eq_score_choose_of_prefix
    (fun a : Fin N => |dec (vec xs a)|) q t ht hdom hfirst
  refine ⟨_, b, w, hb, hw, ?_, hwd, ?_, hh.2.1, hh.2.2⟩
  · split_ifs at hbd ⊢ <;> exact hbd
  split_ifs <;> omega

private theorem absPrefix_initial_literal {M : Machine K} {dec : K → ℝ} {u : ℝ}
    {bound N : ℕ} (hM : StdModel u dec M) (hNat : IsExactNatLit dec M bound)
    (hN : 0 < N) {xs : List K} {best index : ℕ × ℕ} {s : Store K} {b w : K}
    {τ : Tape K} (hb : s.get best.1 best.2 = some b)
    (hw : s.get index.1 index.2 = some w)
    (ha : (absoluteSpec M dec).post [] τ [[vec xs 0]] [[b]])
    (hl : M.indexFn.fn [0] [] [] = some [[w]]) :
    IsAbsPrefix dec xs N 1 best index s := by
  have he : M.lit 0 = w := by simpa [Machine.indexFn] using hl
  subst w
  exact absPrefix_initial hN hb hw (absoluteSpec_decode hM ha)
    (by simpa using hNat 0 (Nat.zero_le bound))

private theorem absPrefix_improved_literal {M : Machine K} {dec : K → ℝ}
    {xs : List K} {N covered bound : ℕ} (hNat : IsExactNatLit dec M bound)
    (q t : Fin N) (ht : t.val = covered) (hN : N ≤ bound) (hq : q.val < covered)
    (hdom : ∀ a : Fin N, a.val < covered → |dec (vec xs a)| ≤ |dec (vec xs q)|)
    (hfirst : ∀ a : Fin N, a < q → |dec (vec xs a)| < |dec (vec xs q)|)
    (hbetter : |dec (vec xs q)| < |dec (vec xs t)|)
    {best index : ℕ × ℕ} {s : Store K} {b w : K}
    (hb : s.get best.1 best.2 = some b) (hw : s.get index.1 index.2 = some w)
    (hbd : dec b = |dec (vec xs t)|)
    (hl : M.indexFn.fn [covered] [] [] = some [[w]]) :
    IsAbsPrefix dec xs N (covered + 1) best index s := by
  have he : M.lit (covered : ℚ) = w := by simpa [Machine.indexFn] using hl
  subst w
  apply absPrefix_choose q t ht hq hdom hfirst hb hw
  · simpa only [if_pos hbetter] using hbd
  · rw [if_pos hbetter]
    simpa only [ht] using hNat covered (by omega)

/-- The actual scan returns the first maximum and an exactly decoded natural index. Only
negation is used in the arithmetic model, and every stored index is within `bound`. -/
theorem argmaxAbs_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (argmaxAbs (Op := Op) (Tst := Tst)).Meets I (argmaxAbsSpec dec bound) := by
  routine_intro [n] (x, j) reads (xs)
  obtain ⟨hn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n] [x, j]) (Fp.blocks [j] [1]) _ m
  alloc as best candidate
  have hxb : x.1 ≠ best := by change x.1 ≠ m.store.length + 0; omega
  have hxc : x.1 ≠ candidate := by change x.1 ≠ m.store.length + 1; omega
  have hjb : j.1 ≠ best := by change j.1 ≠ m.store.length + 0; omega
  have hjc : j.1 ≠ candidate := by change j.1 ≠ m.store.length + 1; omega
  have hbc : best ≠ candidate := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hx0 : m.store.get x.1 x.2 = some (vec xs 0) := by
    simpa using Store.get_of_readBlock hxs hn default
  call (absolute_meets hI hcmp) [] (x, (best, 0))
    as m₁ hfr₁ hpos₁ (bs) habs
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change x.1 < s_best.length ∧ m.store.length < s_best.length
    simp only [List.length_cons, List.length_nil] at hlen_best
    omega
  case' hroom =>
    change 0 + 1 ≤ s_best.len best ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hbest.ge, trivial⟩
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  step hlit as m₂ hfr₂ ⟨hpos₂, w, hw, hword⟩
  simp only [Machine.indexFn, Nat.add_zero] at hpos₂
  have hstart : IsAbsPrefix dec xs n 1 (best, 0) j m₂.store :=
    absPrefix_initial_literal hM hNat hn (by keep) hw habs hword
  loop_inv (fun _ => Fp.blocks [(best, 0), (candidate, 0), j] [1, 1, 1])
    (fun i μ => μ.pos = m.pos ∧ IsAbsPrefix dec xs n (i + 1) (best, 0) j μ.store)
    with i hi m₃ hfr hP
  case round =>
    obtain ⟨hp, q, b, w, hb, hw, hbd, hwd, hq, hdom, hfirst⟩ := hP
    have hxs₃ : m₃.store.readBlock x.1 x.2 n = some xs := by keep
    have hit : i + 1 < n := by omega
    have hx : m₃.store.get x.1 (x.2 + (i + 1)) = some (vec xs (i + 1)) :=
      Store.get_of_readBlock hxs₃ hit default
    call (absolute_meets hI hcmp) [] ((x.1, x.2 + (i + 1)), (candidate, 0))
      as m₄ hfr₄ hpos₄ (cs) hc
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      have hxlen := Store.lt_length_of_get hx
      have hclen : candidate < m₃.store.length := by
        change m.store.length + 1 < m₃.store.length
        have hlen := hfr.length_eq.trans (hfr₂.length_eq.trans hfr₁.length_eq)
        simp only [List.length_cons, List.length_nil] at hlen_best
        omega
      exact ⟨hxlen, hclen⟩
    case' hroom =>
      change 0 + 1 ≤ m₃.store.len candidate ∧ True
      have hlen := hfr.len_eq candidate
      have hlen₂ := hfr₂.len_eq candidate
      have hlen₁ := hfr₁.len_eq candidate
      have hc : m₃.store.len candidate = 1 :=
        hlen.trans (hlen₂.trans (hlen₁.trans hcandidate))
      exact ⟨by simpa only [Nat.zero_add] using hc.ge, trivial⟩
    obtain ⟨c, hcget, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
    have hcd := absoluteSpec_decode hM hc
    have hb₄ : m₄.store.get best 0 = some b := by keep
    refine writes_ite rfl rfl (hcmp.test_lt hb₄ hcget) ?_
    have hscore : (dec b < dec c) ↔
        |dec (vec xs q)| < |dec (vec xs (i + 1))| := by rw [hbd, hcd]
    by_cases hlt : dec b < dec c
    · simp only [hlt, decide_true, ite_true]
      step (hI .copy) as m₅ hfr₅ ⟨hpos₅, v, hv, rfl⟩
      step hlit as m₆ hfr₆ ⟨hpos₆, v, hv, hword⟩
      simp only [Machine.indexFn, Nat.add_zero] at hpos₆
      refine ⟨hpos₆.trans (hpos₅.trans (hpos₄.trans hp)), ?_⟩
      exact absPrefix_improved_literal hNat q ⟨i + 1, hit⟩ rfl hnb hq hdom hfirst
        (hscore.mp hlt) (by keep) hv hcd hword
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      apply wp_skip
      refine ⟨Store.EqOff.refl _ _, hpos₄.trans hp, ?_⟩
      apply absPrefix_choose q ⟨i + 1, hit⟩ rfl hq hdom hfirst hb₄ (by keep)
      · simp only [hbd, if_neg (fun h => hlt (hscore.mpr h))]
      · simpa only [hbd, hcd, if_neg (fun h => hlt (hscore.mpr h))] using hwd
  case initial =>
    exact ⟨hpos₂.trans hpos₁, hstart⟩
  case exit =>
    rintro m₃ _ ⟨hp, hstate⟩ s₃ hs₃ hbelow
    exact absPrefix_return hn hstate hbelow hl.2 hp _

section Choice

variable [Has IdxTst Tst]

/-- Select the first largest-magnitude row of the active pivot column. The relative scan
index is read from its actual output word, then both absolute current-position indices are
written as dimension literals. -/
def partialChoice : Routine Op Tst := routine% [n, k] (R : n * n) → (p : 2) {
  let relative ← alloc 1;
  run argmaxAbs [n - k] (R[k * n + k], relative);
  let row ← index (Has.inj IdxTst.toNat) (relative) ≤ n - k - 1;
  call (Has.inj IndexOp.lit) [k + row] () → (p);
  call (Has.inj IndexOp.lit) [k] () → (p[1])
}

/-- The actual row word identifies the first absolute maximum in the active column; the
column word is the current pivot position. Both indices are bounded current positions. -/
def partialChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs) → ([r, c]) requires (k < n ∧ n ≤ bound) ensures
    ∃ row : Fin n, k ≤ row.val ∧ dec r = row.val ∧ dec c = k ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec rs (k * n + i.val))| ≤ |dec (vec rs (k * n + row.val))|) ∧
      (∀ i : Fin n, k ≤ i.val → i < row →
        |dec (vec rs (k * n + i.val))| < |dec (vec rs (k * n + row.val))|)

private theorem partialChoice_post {M : Machine K} {dec : K → ℝ} {N k bound : ℕ}
    {rs : List K} {τ : Tape K} (hN : N ≤ bound)
    (hNat : IsExactNatLit dec M bound) (row : Fin (N - k))
    (hmax : ∀ i : Fin (N - k),
      |dec (vec ((rs.drop (k * N + k)).take (N - k)) i)| ≤
        |dec (vec ((rs.drop (k * N + k)).take (N - k)) row)|)
    (hfirst : ∀ i : Fin (N - k), i < row →
      |dec (vec ((rs.drop (k * N + k)).take (N - k)) i)| <
        |dec (vec ((rs.drop (k * N + k)).take (N - k)) row)|) :
    (partialChoiceSpec dec bound).post [N, k] τ [rs]
      [[M.lit (k + row.val : ℕ), M.lit (k : ℕ)]] := by
  let r : Fin N := ⟨k + row.val, by have := row.isLt; omega⟩
  have hr : k ≤ r.val := by dsimp only [r]; omega
  have hword (i : Fin N) (hi : k ≤ i.val) :
      vec ((rs.drop (k * N + k)).take (N - k)) (i.val - k) = vec rs (k * N + i.val) := by
    rw [vec_drop_take (by omega), show k * N + k + (i.val - k) = k * N + i.val by omega]
  have hrow : vec ((rs.drop (k * N + k)).take (N - k)) row.val =
      vec rs (k * N + r.val) := by
    simpa only [r, Nat.add_sub_cancel_left] using hword r hr
  refine ⟨r, hr, hNat _ (by have := row.isLt; omega),
    hNat k (by have := row.isLt; omega), ?_, ?_⟩
  · intro i hi
    have ht : i.val - k < N - k := by omega
    simpa only [hword i hi, hrow] using hmax ⟨i.val - k, ht⟩
  · intro i hi hir
    have ht : i.val - k < N - k := by omega
    have hlt : (⟨i.val - k, ht⟩ : Fin (N - k)) < row := by
      have hi' : i.val < r.val := hir
      dsimp only [r] at hi'
      change i.val - k < row.val
      omega
    simpa only [hword i hi, hrow] using hfirst ⟨i.val - k, ht⟩ hlt

/-- Partial selection consumes the actual relative scan index through a bounded query and
writes both absolute current-position indices. Singular active columns retain the first row. -/
theorem partialChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (partialChoice (Op := Op) (Tst := Tst)).Meets I (partialChoiceSpec dec bound) := by
  routine_intro [n, k] (R, p) reads (rs)
  obtain ⟨hkn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k] [R, p]) (Fp.blocks [p] [2]) _ m
  alloc as relative
  have hRr : R.1 ≠ relative := by change R.1 ≠ m.store.length + 0; omega
  have hpr : p.1 ≠ relative := by change p.1 ≠ m.store.length + 0; omega
  have htail := Store.readBlock_sub hrs (o := k * n + k) (n := n - k)
    (by
      have hk : k + 1 ≤ n := by omega
      have hs : n - k + k = n := Nat.sub_add_cancel hkn.le
      nlinarith)
  call (argmaxAbs_meets hI hcmp hlit hM hNat) [n - k]
    ((R.1, R.2 + k * n + k), (relative, 0))
    as m₁ hfr₁ hpos₁ (js) hscan
  case' hcall => exact [((rs.drop (k * n + k)).take (n - k))]
  case' hr =>
    refine Mem.readBlocks_of_cons ?_ rfl
    change s_relative.readBlock R.1 (R.2 + k * n + k) (n - k) = _
    simpa only [Nat.add_assoc] using
      (Store.Below.readBlock_of hbelow_relative hl.1 htail)
  case' hpre => exact ⟨by omega, by omega⟩
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_relative.length ∧ m.store.length < s_relative.length
    simp only [List.length_singleton] at hlen_relative
    omega
  case' hroom =>
    change 0 + 1 ≤ s_relative.len relative ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hrelative.ge, trivial⟩
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  obtain ⟨row, hrow, hmax, hfirst⟩ : ∃ row : Fin (n - k), dec w = row.val ∧
      (∀ i : Fin (n - k),
        |dec (vec ((rs.drop (k * n + k)).take (n - k)) i)| ≤
          |dec (vec ((rs.drop (k * n + k)).take (n - k)) row)|) ∧
      (∀ i : Fin (n - k), i < row →
        |dec (vec ((rs.drop (k * n + k)).take (n - k)) i)| <
          |dec (vec ((rs.drop (k * n + k)).take (n - k)) row)|) := hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hrow (by have := row.isLt; omega) ?_
  step hlit as m₂ hfr₂ ⟨hpos₂, r, hr, hrword⟩
  have he : M.lit (k + row.val : ℕ) = r := by simpa [Machine.indexFn] using hrword
  subst r
  simp only [Machine.indexFn, Nat.add_zero] at hpos₂
  step hlit as m₃ hfr₃ ⟨hpos₃, c, hc, hcword⟩
  have he : M.lit (k : ℕ) = c := by simpa [Machine.indexFn] using hcword
  subst c
  simp only [Machine.indexFn, Nat.add_zero] at hpos₃
  intro s₃ hs₃ hbelow
  have hread : m₃.store.readBlock p.1 p.2 2 =
      some [M.lit (k + row.val : ℕ), M.lit (k : ℕ)] :=
    Store.readBlock_succ_of (Store.readBlock_one_of_get (by keep)) hc
  exact ⟨hpos₃.trans (hpos₂.trans hpos₁), _, Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hl.2 hread) rfl, partialChoice_post hnb hNat row hmax hfirst⟩

end Choice

end NLAlib.LU
