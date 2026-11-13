/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Catalog.Compare

/-!
# Scanning stored words against an interval

The scan writes a machine literal zero, tests each actual stored word against two stored
bounds, and writes literal one whenever a test fails. The flag is sticky without reading it.
No exactness or distinguishability of the machine's zero and one literals is assumed.

## Main results

* `NLAlib.Ops.intervalScan`: a scalar/comparison implementation for a vector of words.
* `NLAlib.Ops.writes_intervalScan`: its exact output flag and frame on spatially disjoint inputs.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Write literal zero if all words lie between the stored endpoints and literal one
otherwise. Every comparison is an ordinary counted query on the actual word cells. -/
def intervalScan : Impl Op Tst := opsImpl% [n] (X, lo, hi) → (flag) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (flag);
  for w < n {
    if (Has.inj CmpTst.le) [] (lo, X[w]) {
      if (Has.inj CmpTst.le) [] (X[w], hi) {
        skip
      } else {
        call (Has.inj (ScalarOp.lit 1)) [] () → (flag)
      }
    } else {
      call (Has.inj (ScalarOp.lit 1)) [] () → (flag)
    }
  }
}

/-- The first `n` actual input words decode inside the closed interval. This is a mathematical
predicate on a supplied vector; it performs no hidden reads or preprocessing. -/
def InInterval (dec : K → ℝ) (lo hi : K) (v : ℕ → K) (n : ℕ) : Prop :=
  ∀ i < n, dec lo ≤ dec (v i) ∧ dec (v i) ≤ dec hi

/-- Appending one tested word adds exactly its two endpoint comparisons. -/
theorem inInterval_succ (dec : K → ℝ) (lo hi : K) (v : ℕ → K) (i : ℕ) :
    InInterval dec lo hi v (i + 1) ↔
      InInterval dec lo hi v i ∧ dec lo ≤ dec (v i) ∧ dec (v i) ≤ dec hi := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨h, hcur⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h j hj
    · exact hcur

open Classical in
/-- The scan returns its actual machine literal for the all-words interval predicate. Inputs
are spatially disjoint from the output flag; they may share its buffer at other offsets.
The output cell needs capacity, and no output initialization or scalar literal exactness is
assumed. Every other cell and the tape position are preserved. -/
theorem writes_intervalScan {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K} {m : Mem K}
    {n : ℕ} {x lo hi z : ℕ × ℕ} {a b : K} (v : ℕ → K)
    (hx : m.store.HoldsVec x.1 x.2 n v)
    (hlo : m.store.get lo.1 lo.2 = some a) (hhi : m.store.get hi.1 hi.2 = some b)
    (hz : z.2 < m.store.len z.1)
    (hXz : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 1))
    (hloz : Fp.Disj (Store.inBlock lo.1 lo.2 1) (Store.inBlock z.1 z.2 1))
    (hhiz : Fp.Disj (Store.inBlock hi.1 hi.2 1) (Store.inBlock z.1 z.2 1)) :
    Writes md I τ (intervalScan (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [x, lo, hi, z]) (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 =
        some (M.lit (if InInterval dec a b v n then 0 else 1))) m := by
  classical
  refine (writes_call_const (hS (.lit 0)) rfl trivial hz).seq_le le_rfl
    fun m₀ hfr₀ hp₀ => ?_
  have hX₀ := hfr₀.keep (Store.readsOnly_holdsVec x.1 x.2 n v) hXz.symm hx
  have hlo₀ := hfr₀.keep (Store.readsOnly_get lo.1 lo.2 a) hloz.symm hlo
  have hhi₀ := hfr₀.keep (Store.readsOnly_get hi.1 hi.2 b) hhiz.symm hhi
  refine (writes_loop rfl (fun _ => Store.inBlock z.1 z.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m₀.pos ∧ m'.store.get z.1 z.2 =
      some (M.lit (if InInterval dec a b v i then 0 else 1)))
    ⟨rfl, by simpa [InInterval] using hp₀.2⟩ ?_).mono le_rfl
      (fun _ _ hp => ⟨hp.1.trans hp₀.1, hp.2⟩)
  intro i hi' m' hfr hp
  have hX := hfr.keep (Store.readsOnly_holdsVec x.1 x.2 n v) hXz.symm hX₀
  have ha := hfr.keep (Store.readsOnly_get lo.1 lo.2 a) hloz.symm hlo₀
  have hb := hfr.keep (Store.readsOnly_get hi.1 hi.2 b) hhiz.symm hhi₀
  have hword := hX i hi'
  have hz' : z.2 < m'.store.len z.1 := by rw [hfr.len_eq, hfr₀.len_eq]; exact hz
  refine writes_ite rfl rfl (hC.test_le ha hword) ?_
  by_cases hlow : dec a ≤ dec (v i)
  · simp only [hlow, decide_true, if_true]
    refine writes_ite rfl rfl (hC.test_le hword hb) ?_
    by_cases hhigh : dec (v i) ≤ dec b
    · simp only [hhigh, decide_true, if_true]
      exact Writes.skip ⟨hp.1, by simpa [inInterval_succ, hlow, hhigh] using hp.2⟩
        |>.mono bot_le (fun _ _ h => h)
    · simp only [hhigh, decide_false, Bool.false_eq_true, if_false]
      exact (writes_call_const (hS (.lit 1)) rfl trivial hz').mono le_rfl
        fun _ _ h => ⟨h.1.trans hp.1, by simpa [inInterval_succ, hhigh] using h.2⟩
  · simp only [hlow, decide_false, Bool.false_eq_true, if_false]
    exact (writes_call_const (hS (.lit 1)) rfl trivial hz').mono le_rfl
      fun _ _ h => ⟨h.1.trans hp.1, by simpa [inInterval_succ, hlow] using h.2⟩

end NLAlib.Ops
