/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Catalog.Compare

/-!
# Absolute values by comparison and negation

Pivot scans need absolute values without multiplication or square root rounding. The scalar
routine copies a positive word and negates every other word. Its word specification is
valid for any machine; exact negation gives the decoded absolute value. Partial, complete,
scaled and rook pivot scans use the same routine.

## Main results

* `NLAlib.Ops.absolute_meets`: the actual word selected by the branch.
* `NLAlib.Ops.absoluteSpec_decode`: the decoded absolute value under the standard model.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Copy a positive word, and otherwise negate it. The input and output are separate operands;
the sign test is on the copied output word. -/
def absolute : Routine Op Tst := routine% [] (x : 1) → (y : 1) {
  call (Has.inj ScalarOp.copy) [] (x) → (y);
  if (Has.inj CmpTst.isPos) [] (y) {
    skip
  } else {
    call (Has.inj ScalarOp.neg) [] (y) → (y)
  }
}

/-- The output is the input word when its decoding is positive, and its machine negation
otherwise. Exactness of negation is not assumed in this word specification. -/
def absoluteSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [] ([x]) → ([y]) ensures
    (0 < dec x → y = x) ∧ (¬ 0 < dec x → y = M.neg x)

/-- The scalar comparison-and-negation routine meets its word specification. -/
theorem absolute_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) :
    (absolute (Op := Op) (Tst := Tst)).Meets I (absoluteSpec M dec) := by
  routine_intro [] (x, y) reads (xs)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hxs
  step (hI .copy) as m₁ hfr₁ ⟨hpos₁, v, hv, rfl⟩
  refine writes_ite rfl rfl (hcmp.test_isPos hv) ?_
  by_cases hp : 0 < dec a
  · simp only [hp, decide_true, ite_true]
    change Wp .total I τ .skip _ _ m₁
    apply wp_skip
    refine ⟨Store.EqOff.refl _ _, hpos₁, [[a]],
      Mem.readBlocks_of_cons (Store.readBlock_one_of_get hv) rfl, ?_⟩
    exact ⟨fun _ => rfl, fun h => (h hp).elim⟩
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    step (hI .neg) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
    routine_exit
    exact ⟨fun h => (hp h).elim, fun _ => rfl⟩

/-- Exact negation alone turns the branch's actual word output into a decoded absolute
value. No property of literals or other arithmetic operations is required. -/
theorem absoluteSpec_decode_of_neg {M : Machine K} {dec : K → ℝ}
    (hneg : ∀ a, dec (M.neg a) = -dec a) {x y : K} {τ : Tape K}
    (hpost : (absoluteSpec M dec).post [] τ [[x]] [[y]]) : dec y = |dec x| := by
  have hp : (0 < dec x → y = x) ∧ (¬ 0 < dec x → y = M.neg x) := hpost
  by_cases hx : 0 < dec x
  · rw [hp.1 hx, abs_of_pos hx]
  · rw [hp.2 hx, hneg, abs_of_nonpos (le_of_not_gt hx)]

/-- Exact negation in the standard model turns the word specification into a decoded absolute
value. No positive unit-roundoff premise or condition on the input word is needed. -/
theorem absoluteSpec_decode {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) {x y : K} {τ : Tape K}
    (hpost : (absoluteSpec M dec).post [] τ [[x]] [[y]]) : dec y = |dec x| :=
  absoluteSpec_decode_of_neg hM.neg hpost

end NLAlib.Ops
