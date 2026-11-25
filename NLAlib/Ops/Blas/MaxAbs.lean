/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import NLAlib.Ops.Blas.Absolute
public import NLAlib.Ops.Logic.MatrixView

/-!
# A strided maximum absolute value

The scalar loop starts at literal zero and keeps the largest decoded magnitude. Its only
arithmetic is negation; no index word, multiplication or division is formed. Exact negation
and a zero-decoding zero literal suffice, including for finite models with gradual underflow.
The result is the existing finite Pi supremum norm, with zero for an empty vector.

## Main results

* `NLAlib.Ops.maxAbsValue_meets`: the actual strided scalar loop computes the Pi norm.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute the largest absolute value by actual scalar comparisons. Source and output views
are disjoint and may share a buffer. The scratch consists of one candidate word. -/
def maxAbsValue : Routine Op Tst :=
  routine% [n, stride] (x : n every stride) → (v : 1) by blocks {
    let candidate ← alloc 1;
    call (Has.inj (ScalarOp.lit 0)) [] () → (v);
    for i < n {
      run absolute [] (x[stride * i], candidate);
      if (Has.inj CmpTst.lt) [] (v, candidate) {
        call (Has.inj ScalarOp.copy) [] (candidate) → (v)
      } else {
        skip
      }
    }
  }

variable [Inhabited K]

/-- The reported word is the finite Pi supremum norm of the decoded input vector. Empty
vectors have norm zero, and no bounded natural-literal allowance is needed. -/
def maxAbsValueSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, _stride] (xs) → ([v]) ensures dec v = ‖fun i : Fin n => dec (vec xs i.val)‖

private def IsMaxAbsPrefix (dec : K → ℝ) (xs : List K) (N covered : ℕ)
    (v : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ b : K, s.get v.1 v.2 = some b ∧ 0 ≤ dec b ∧
    (∀ i : Fin N, i.val < covered → |dec (vec xs i.val)| ≤ dec b) ∧
    (dec b = 0 ∨ ∃ i : Fin N, i.val < covered ∧ dec b = |dec (vec xs i.val)|)

private theorem maxAbsPrefix_next {dec : K → ℝ} {xs : List K} {N : ℕ}
    (i : Fin N) {b vword : K} {v : ℕ × ℕ} {s : Store K} (hb : 0 ≤ dec b)
    (hdom : ∀ j : Fin N, j.val < i.val → |dec (vec xs j.val)| ≤ dec b)
    (hatt : dec b = 0 ∨ ∃ j : Fin N, j.val < i.val ∧ dec b = |dec (vec xs j.val)|)
    (hv : s.get v.1 v.2 = some vword)
    (hd : dec vword = max (dec b) |dec (vec xs i.val)|) :
    IsMaxAbsPrefix dec xs N (i.val + 1) v s := by
  refine ⟨vword, hv, hd ▸ hb.trans (le_max_left _ _), ?_, ?_⟩
  · intro j hj
    rw [hd]
    by_cases hji : j.val < i.val
    · exact (hdom j hji).trans (le_max_left _ _)
    · have he : j = i := Fin.ext (by omega)
      subst j
      exact le_max_right _ _
  · by_cases hle : dec b ≤ |dec (vec xs i.val)|
    · exact Or.inr ⟨i, Nat.lt_succ_self _, by simpa only [max_eq_right hle] using hd⟩
    · rw [max_eq_left (le_of_not_ge hle)] at hd
      rcases hatt with hz | ⟨j, hj, he⟩
      · exact Or.inl (hd.trans hz)
      · exact Or.inr ⟨j, by omega, hd.trans he⟩

private theorem maxAbsPrefix_return {dec : K → ℝ} {xs : List K} {N stride : ℕ}
    {v : ℕ × ℕ} {s s' : Store K} {length pos initialPos : ℕ}
    (h : IsMaxAbsPrefix dec xs N N v s) (hbelow : Store.Below length s s')
    (hv : v.1 < length) (hp : pos = initialPos) (τ : Tape K) :
    ({store := s', pos := pos} : Mem K).pos = initialPos ∧ ∃ ys,
      ({store := s', pos := pos} : Mem K).readBlocks [v] [1] = some ys ∧
        (maxAbsValueSpec dec).post [N, stride] τ [xs] ys := by
  obtain ⟨b, hb, hnonneg, hdom, hatt⟩ := h
  refine ⟨hp, [[b]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hv (Store.readBlock_one_of_get hb)) rfl, ?_⟩
  apply le_antisymm
  · rcases hatt with hz | ⟨i, _, hi⟩
    · rw [hz]
      exact norm_nonneg _
    · rw [hi]
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j : Fin N => dec (vec xs j)) i
  · exact (pi_norm_le_iff_of_nonneg hnonneg).mpr fun i => by
      simpa only [Real.norm_eq_abs] using hdom i i.isLt

/-- Exact negation and literal zero suffice for the entire scalar maximum loop. No model of
multiplication, division, rounded literals, or dimension-to-word conversion is assumed. -/
theorem maxAbsValue_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hneg : ∀ a, dec (M.neg a) = -dec a) (hzero : dec (M.lit 0) = 0) :
    (maxAbsValue (Op := Op) (Tst := Tst)).Meets I (maxAbsValueSpec dec) := by
  routine_intro [n, stride] (x, v) reads (xs)
  have hdis : Fp.Disj (Store.inBlock v.1 v.2 1)
      (Fp.inView x.1 x.2 ⟨1, some (n, stride)⟩) := by
    simpa only [Fp.views, Fp.inView_block, sup_bot_eq] using hblocks.2.1
  change Writes .total I τ _ (Env.frame [n, stride] [x, v]) (Fp.blocks [v] [1]) _ m
  alloc as candidate
  have hxc : x.1 ≠ candidate := by change x.1 ≠ m.store.length + 0; omega
  have hvc : v.1 ≠ candidate := by change v.1 ≠ m.store.length + 0; omega
  have hxs₀ := Store.Below.readView_of hbelow_candidate hl.1 hxs
  step (hI (.lit 0)) as m₁ hfr₁ ⟨hpos₁, w, hw, rfl⟩
  have hxs₁ := hfr₁.keep (Store.readsOnly_readView _ _ _ _) hdis hxs₀
  have hstart : IsMaxAbsPrefix dec xs n 0 v m₁.store := by
    refine ⟨M.lit 0, hw, by rw [hzero], fun i hi => (Nat.not_lt_zero i.val hi).elim, Or.inl hzero⟩
  loop_inv (fun _ => Fp.blocks [v, (candidate, 0)] [1, 1])
    (fun i μ => μ.pos = m.pos ∧ IsMaxAbsPrefix dec xs n i v μ.store)
    with i hi m₂ hfr hP
  case round =>
    obtain ⟨hp, b, hb, hb0, hdom, hatt⟩ := hP
    have hdx : Fp.Disj (Fp.blocks [v, (candidate, 0)] [1, 1])
        (Fp.inView x.1 x.2 ⟨1, some (n, stride)⟩) := by
      simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq, Fp.disj_sup_left] using
        And.intro hdis (Fp.disj_inView_inBlock_of_ne hxc).symm
    have hxs₂ := hfr.keep (Store.readsOnly_readView _ _ _ _) hdx hxs₁
    have hx : m₂.store.get x.1 (x.2 + stride * i) = some (vec xs i) := by
      simpa only [View.offset_runs_one] using
        Store.getD_of_readView hxs₂ (by simpa using hi) default
    have hcap : 1 ≤ m₂.store.len candidate := by
      rw [hfr.len_eq, hfr₁.len_eq]
      exact hcandidate.ge
    call (absolute_meets hI hcmp) [] ((x.1, x.2 + stride * i), (candidate, 0))
      as m₃ hfr₃ hpos₃ (cs) hc
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      exact ⟨Store.lt_length_of_get hx,
        Store.lt_length_of_lt_len (lt_of_lt_of_le Nat.zero_lt_one hcap)⟩
    obtain ⟨c, hcget, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
    have hcd := absoluteSpec_decode_of_neg hneg hc
    have hb₃ : m₃.store.get v.1 v.2 = some b := by keep
    refine writes_ite rfl rfl (hcmp.test_lt hb₃ hcget) ?_
    by_cases hlt : dec b < dec c
    · simp only [hlt, decide_true, ite_true]
      step (hI .copy) as m₄ hfr₄ ⟨hpos₄, w, hw, rfl⟩
      refine ⟨hpos₄.trans (hpos₃.trans hp), ?_⟩
      apply maxAbsPrefix_next ⟨i, hi⟩ hb0 hdom hatt hw
      rw [← hcd, max_eq_right hlt.le]
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      apply wp_skip
      refine ⟨Store.EqOff.refl _ _, hpos₃.trans hp, ?_⟩
      apply maxAbsPrefix_next ⟨i, hi⟩ hb0 hdom hatt hb₃
      rw [← hcd, max_eq_left (le_of_not_gt hlt)]
  case exit =>
    rintro m₂ _ ⟨hp, hstate⟩ s₂ hs₂ hbelow
    exact maxAbsPrefix_return (stride := stride) hstate hbelow hl.2 hp (τ.shift m.pos)

end NLAlib.Ops
