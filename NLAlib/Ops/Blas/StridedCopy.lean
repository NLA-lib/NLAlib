/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Catalog.Scalar

/-!
# Scalar copying between strided vectors

The two vectors can have different increments. Each round copies one word, using the scalar
copy operation; the judgment preserves every cell outside the destination view. LU uses this
routine to materialize its upper rows, and rectangular block gathering and scattering use the
same view interface.

## Main results

* `NLAlib.Ops.copyStridedRoutine_meets`: exact word copying between the declared views.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy `n` words from increment `sx` to increment `sy`, between disjoint input and output
views. The views may share a buffer. No operation depends on the values of the words. -/
def copyStridedRoutine : Routine Op Tst :=
  routine% [n, sx, sy] (x : n every sx) → (y : n every sy) by blocks {
    for i < n {
      call (Has.inj ScalarOp.copy) [] (x[sx * i]) → (y[sy * i])
    }
  }

/-- The copied words equal the words read. A nonempty destination has positive increment;
the empty case imposes no increment or handle validity requirement beyond the interface. -/
def copyStridedSpec : Routine.Spec K :=
  spec% [n, _sx, sy] (xs) → (ys) requires (0 < n → 0 < sy) ensures ys = xs

/-- The scalar loop copies the source view exactly, including an empty view. No arithmetic
model or decoding is needed. -/
theorem copyStridedRoutine_meets_of_isFn {I : Interp Op Tst K}
    (hcopy : I.IsFn .total (Has.inj ScalarOp.copy) (.un fun v => some v) AnyOperands) :
    (copyStridedRoutine (Op := Op) (Tst := Tst)).Meets I copyStridedSpec := by
  routine_intro [n, sx, sy] (x, y) reads (xs)
  obtain ⟨hxl, hxg⟩ := Store.readView_eq_some_iff.mp hxs
  have hdis : Fp.Disj (Fp.inView y.1 y.2 ⟨1, some (n, sy)⟩)
      (Fp.inView x.1 x.2 ⟨1, some (n, sx)⟩) := by
    simpa only [Fp.views, sup_bot_eq] using hblocks.2.1
  have hxlen : xs.length = n := by simpa using hxl
  have hg : ∀ k < n, m.store.get x.1 (x.2 + sx * k) = xs[k]? := fun k hk => by
    simpa using hxg k (by simpa using hk)
  change Wp .total I τ _ _ _ m
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Fp.inView y.1 y.2 ⟨1, some (n, sy)⟩) s' ∧
    ∀ k < i, s'.get y.1 (y.2 + sy * k) = xs[k]?)
    ⟨_, rfl, Store.EqOff.refl _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hcells⟩
    have hi' : i < xs.length := hxlen ▸ hi
    have hxi : s'.get x.1 (x.2 + sx * i) = some xs[i] := by
      rw [hfr.get_eq (fun h => hdis _ _ h
        (Fp.inView_apply.mpr ⟨rfl, i, by simpa using hi, by simp⟩))]
      exact (hg i hi).trans (List.getElem?_eq_getElem hi')
    have hyi : y.2 + sy * i < s'.len y.1 := by
      rw [hfr.len_eq]
      simpa only [View.offset_runs_one] using hroom i (by simpa using hi)
    refine wp_call_un hcopy rfl rfl rfl trivial hxi rfl hyi ?_
    refine ⟨_, rfl, hfr.upd (Fp.inView_apply.mpr
      ⟨rfl, i, by simpa using hi, by simp⟩) _, fun k hk => ?_⟩
    by_cases hki : k = i
    · subst hki
      exact (Store.get_upd_self hyi _).trans (List.getElem?_eq_getElem hi').symm
    · have hne : y.2 + sy * k ≠ y.2 + sy * i := fun e =>
        hki (Nat.eq_of_mul_eq_mul_left (hpre (by omega)) (Nat.add_left_cancel e))
      rw [Store.get_upd_of_idx_ne hne]
      exact hcells k (by omega)
  · rintro m' ⟨s', rfl, hfr, hcells⟩
    refine ⟨hfr.mono fun _ _ h => Or.inl h, rfl, [xs],
      Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr
        ⟨by simpa using hxlen, fun k hk => ?_⟩) rfl, rfl⟩
    simpa only [View.offset_runs_one] using hcells k (by simpa using hk)

/-- The strided copy judgment follows from the scalar machine's copy contract alone. -/
theorem copyStridedRoutine_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (copyStridedRoutine (Op := Op) (Tst := Tst)).Meets I copyStridedSpec :=
  copyStridedRoutine_meets_of_isFn (hI .copy)

end NLAlib.Ops
