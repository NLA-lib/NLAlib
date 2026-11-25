/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.StridedCopy

/-!
# Scalar copying between rectangular matrix views

One scalar loop traverses logical entries by columns. Independent source and destination
leading dimensions permit packing or unpacking a submatrix without copying its padding.
Only the actual destination cells change, so disjoint views may share one backing buffer.
Blocked factorizations use this routine to pack operands for the scalar matrix product.

## Main results

* `NLAlib.Ops.copyMatrixRoutine_meets`: exact word copying between rectangular views.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy rectangular views by a scalar traversal of their logical entries. Source and
destination padding is skipped; no allocation or matrix operation is hidden in the routine. -/
def copyMatrixRoutine : Routine Op Tst :=
  routine% [rows, cols, sx, sy] (X : rows × cols every sx) →
      (Y : rows × cols every sy) by blocks {
    for i < cols * rows {
      call (Has.inj ScalarOp.copy) [] (X[(sx * (i / rows) + (i - rows * (i / rows)))]) →
        (Y[(sy * (i / rows) + (i - rows * (i / rows)))])
    }
  }

/-- The destination contains exactly the logical source words. Its nonempty columns must
not overlap. Empty shapes impose no leading-dimension restriction. -/
def copyMatrixSpec : Routine.Spec K :=
  spec% [rows, cols, _sx, sy] (xs) → (ys)
    requires (0 < cols * rows → rows ≤ sy) ensures ys = xs

/-- The scalar loop copies every logical entry and preserves padding and other regions.
The declared views are disjoint; their backing buffer handles may coincide. -/
theorem copyMatrixRoutine_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (copyMatrixRoutine (Op := Op) (Tst := Tst)).Meets I copyMatrixSpec := by
  routine_intro [rows, cols, sx, sy] (X, Y) reads (xs)
  let vx : View := ⟨rows, some (cols, sx)⟩
  let vy : View := ⟨rows, some (cols, sy)⟩
  obtain ⟨hxl, hxg⟩ := Store.readView_eq_some_iff.mp hxs
  have hdis : Fp.Disj (Fp.inView Y.1 Y.2 vy) (Fp.inView X.1 X.2 vx) := by
    simpa only [Fp.views, sup_bot_eq] using hblocks.2.1
  have hxlen : xs.length = cols * rows := hxl
  change Wp .total I τ _ _ _ m
  refine wp_loop (k := cols * rows) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Fp.inView Y.1 Y.2 vy) s' ∧
    ∀ k < i, s'.get Y.1 (Y.2 + vy.offset k) = xs[k]?)
    ⟨_, rfl, Store.EqOff.refl _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hcells⟩
    have hi' : i < xs.length := hxlen ▸ hi
    have hxi : s'.get X.1 (X.2 + vx.offset i) = some xs[i] := by
      rw [hfr.get_eq (fun h => hdis _ _ h (Fp.inView_apply.mpr ⟨rfl, i, hi, rfl⟩))]
      exact (hxg i hi).trans (List.getElem?_eq_getElem hi')
    have hyi : Y.2 + vy.offset i < s'.len Y.1 := by
      rw [hfr.len_eq]
      exact hroom i hi
    simp only [vx, vy, View.offset, Nat.mod_eq_sub_mul_div] at hxi hyi ⊢
    refine wp_call_un (hI .copy) rfl rfl rfl trivial hxi rfl hyi ?_
    refine ⟨_, rfl, ?_, fun k hk => ?_⟩
    · simpa only [vy, View.offset, Nat.mod_eq_sub_mul_div] using
        hfr.upd (Fp.inView_apply.mpr ⟨rfl, i, hi, rfl⟩) xs[i]
    · by_cases hki : k = i
      · subst k
        exact (Store.get_upd_self hyi _).trans (List.getElem?_eq_getElem hi').symm
      · have hne : Y.2 + vy.offset k ≠ Y.2 + vy.offset i := fun e =>
          hki (View.offset_inj (v := vy) (hpre (by omega))
            (show k < vy.cells from by change k < cols * rows; omega) hi
            (Nat.add_left_cancel e))
        simp only [vy, View.offset, Nat.mod_eq_sub_mul_div] at hne
        rw [Store.get_upd_of_idx_ne hne]
        simpa only [vy, View.offset, Nat.mod_eq_sub_mul_div] using hcells k (by omega)
  · rintro m' ⟨s', rfl, hfr, hcells⟩
    refine ⟨hfr.mono fun _ _ h => Or.inl h, rfl, [xs],
      Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr
        ⟨hxlen, fun k hk => hcells k hk⟩) rfl, rfl⟩

end NLAlib.Ops
