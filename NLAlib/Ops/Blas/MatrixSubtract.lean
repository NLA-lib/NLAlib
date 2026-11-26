/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.MatrixCopy
public import NLAlib.Ops.Logic.MatrixView

/-!
# Subtracting a packed correction from a matrix view

One scalar loop subtracts a packed matrix from the corresponding logical entries of a
rectangular destination view. Padding is retained. Blocked elimination uses this routine
after the entire trailing correction has been computed by scalar matrix multiplication.

## Main results

* `NLAlib.Ops.subtractMatrixRoutine_meets`: the actual machine differences and spatial frame.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Subtract a packed correction from a rectangular matrix view by scalar instructions. -/
def subtractMatrixRoutine : Routine Op Tst :=
  routine% [rows, cols, ld] (C : rows * cols, R : rows × cols every ld) → (R) by blocks {
    for i < cols * rows {
      call (Has.inj ScalarOp.sub) []
        (R[(ld * (i / rows) + (i - rows * (i / rows)))], C[i]) →
        (R[(ld * (i / rows) + (i - rows * (i / rows)))])
    }
  }

variable [Inhabited K]

/-- The logical output is the actual machine subtraction of the supplied correction words.
Nonempty destination columns must not overlap. -/
def subtractMatrixSpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, cols, ld] (cs, rs) → (ts)
    requires (0 < cols * rows → rows ≤ ld) ensures
    ts = (List.range (cols * rows)).map fun i => M.sub (vec rs i) (vec cs i)

/-- Every actual matrix-view entry is updated exactly once, with the stated machine word,
and all other cells are retained. The source correction is read only. -/
theorem subtractMatrixRoutine_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (subtractMatrixRoutine (Op := Op) (Tst := Tst)).Meets I (subtractMatrixSpec M) := by
  routine_intro [rows, cols, ld] (C, R) reads (cs, rs)
  let v : View := ⟨rows, some (cols, ld)⟩
  have hdis : Fp.Disj (Fp.inView R.1 R.2 v) (Store.inBlock C.1 C.2 (rows * cols)) := by
    simpa only [Fp.views, sup_bot_eq, Fp.inView_block] using hblocks.2.1
  have hR (i : ℕ) (hi : i < cols * rows) :
      m.store.get R.1 (R.2 + v.offset i) = some (vec rs i) :=
    Store.getD_of_readView hrs hi default
  change Wp .total I τ _ _ _ m
  refine wp_loop (k := cols * rows) rfl (fun i μ => ∃ s', μ = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Fp.inView R.1 R.2 v) s' ∧
    ∀ k < cols * rows, s'.get R.1 (R.2 + v.offset k) =
      some (if k < i then M.sub (vec rs k) (vec cs k) else vec rs k))
    ⟨_, rfl, Store.EqOff.refl _ _, fun k hk => by
      simpa only [Nat.not_lt_zero, if_false] using hR k hk⟩ ?_ ?_
  · rintro i hi μ ⟨s', rfl, hfr, hcells⟩
    have hri : s'.get R.1 (R.2 + v.offset i) = some (vec rs i) := by
      simpa only [if_neg (Nat.lt_irrefl i)] using hcells i hi
    have hci : s'.get C.1 (C.2 + i) = some (vec cs i) := by
      rw [hfr.get_eq (fun h => hdis _ _ h ⟨rfl, by omega, by nlinarith [hi]⟩)]
      exact Store.get_of_readBlock hcs (by nlinarith [hi]) default
    have hroomi := Store.lt_len_of_get hri
    simp only [v, View.offset, Nat.mod_eq_sub_mul_div] at hri hroomi ⊢
    refine wp_call_bin (hI .sub) rfl rfl rfl trivial hri hci rfl hroomi ?_
    refine ⟨_, rfl, ?_, fun k hk => ?_⟩
    · simpa only [v, View.offset, Nat.mod_eq_sub_mul_div] using
        hfr.upd (Fp.inView_apply.mpr ⟨rfl, i, hi, rfl⟩) (M.sub (vec rs i) (vec cs i))
    · by_cases hki : k = i
      · subst k
        rw [Store.get_upd_self hroomi, if_pos (Nat.lt_succ_self i)]
      · have hne : R.2 + v.offset k ≠ R.2 + v.offset i := fun e =>
          hki (View.offset_inj (v := v) (hpre (by omega)) hk hi (Nat.add_left_cancel e))
        simp only [v, View.offset, Nat.mod_eq_sub_mul_div] at hne
        rw [Store.get_upd_of_idx_ne hne]
        have he : (k < i + 1) = (k < i) := propext (by omega)
        simpa only [v, View.offset, Nat.mod_eq_sub_mul_div, he] using hcells k hk
  · rintro μ ⟨s', rfl, hfr, hcells⟩
    refine ⟨hfr.mono fun _ _ h => Or.inl h, rfl,
      [(List.range (cols * rows)).map fun i => M.sub (vec rs i) (vec cs i)],
      Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr ⟨by simp, ?_⟩) rfl, rfl⟩
    intro k hk
    have hk' : k < cols * rows := hk
    simpa [v, hk'] using hcells k hk'

end NLAlib.Ops
