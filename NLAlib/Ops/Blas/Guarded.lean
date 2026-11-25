/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Catalog.GuardedScalar

/-!
# Scalar loops under rejecting arithmetic contracts

The existing copy and normalization trees can run under the guarded scalar interpretation.
Copying needs no numerical range assumption. Normalization requires the denominator to be
nonzero and every exact quotient to be accepted; its actual output remains the same word
recurrence. Numerical factorization bounds must prove these local conditions before calls.

## Main results

* `NLAlib.Ops.copyLoopRoutine_meets_guarded`: the existing copy loop under guarded contracts.
* `NLAlib.Ops.scalLoopRoutine_meets_guarded`: guarded normalization with actual word output.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The actual copy loop is unchanged by arithmetic range rejection. -/
theorem copyLoopRoutine_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (copyLoopRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel copyRel fun _ => True) := by
  routine_intro [n] (x, y) reads (xs)
  have hcopy : I.IsFn .total (Has.inj ScalarOp.copy) (.un fun v => some v) AnyOperands :=
    hI .copy
  refine (unaryMap_writes_of_disj_or_eq hcopy
    (.inl (Fp.disj_inBlock_of_ne hxy)) hxs hroom).mono (by fp_sub) ?_
  rintro m' _ ⟨hp, hr⟩
  rw [List.map_id'] at hr
  exact ⟨hp, [xs], Mem.readBlocks_of_cons hr rfl, rfl⟩

/-- Guarded normalization requires only the actual denominator and exact quotient targets.
Its output is the same functional word list as the ordinary scalar loop. -/
def scalLoopGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) : Routine.Spec K :=
  spec% [n] ([a], xs) → (ys) requires
    (dec a ≠ 0 ∧ ∀ i < n, safe (dec (vec xs i) / dec a)) ensures
    ys = scalF M a (vec xs) n

/-- Every actual division succeeds under its guarded primitive contract and the declared
local quotient conditions. Only the normalized block is written. -/
theorem scalLoopRoutine_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (scalLoopRoutine (Op := Op) (Tst := Tst)).Meets I (scalLoopGuardedSpec M dec safe) := by
  routine_intro [n] (al, x) reads (as, xs)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hxs hk default
  have hF := length_scalF M a (vec xs) n
  refine (Writes.of_wp_updBlock_one (z := x) (ys := scalF M a (vec xs) n)
    (by rw [hF]; exact hroom) ?_).mono
    (by rw [hF]) fun m' _ ⟨hpos, hread⟩ =>
      ⟨hpos, [scalF M a (vec xs) n], by rwa [hF] at hread, rfl⟩
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Store.inBlock x.1 x.2 i) s' ∧
    s'.readBlock x.1 x.2 i = some (scalF M a (vec xs) i))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlt := Store.lt_len_of_get (hgx i hi)
    have hlen := hfr.len_eq x.1
    refine wp_call_bin (hI .div) rfl rfl rfl trivial (a := vec xs i) (b := a)
      (v := M.div (vec xs i) a) ?_ ?_ ?_ ?_ ?_
    · rw [← hgx i hi]
      exact hfr.get_eq (by store_side)
    · rw [← ha]
      exact hfr.get_eq (by store_side)
    · exact if_pos ⟨hpre.1, hpre.2 i hi⟩
    · store_simp
    · refine ⟨_, rfl, (hfr.mono fun b j h => ?_).upd ⟨rfl, by omega, by omega⟩ _, ?_⟩
      · exact ⟨h.1, h.2.1, by have := h.2.2; omega⟩
      · rw [scalF_succ]
        exact Store.readBlock_upd_concat hr (by omega) _
  · rintro m' ⟨s', rfl, hfr, hr⟩
    simp [hfr.eq_updBlock hr, Mem.updBlock]

/-- Acceptance of each exact product and sum performed by the multiply-add loop. -/
def axpyLoopGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) : Routine.Spec K :=
  spec% [n] ([a], xs, ys) → (zs) requires
    ((∀ i < n, safe (dec a * dec (vec xs i))) ∧
      ∀ i < n, safe (dec (vec ys i) + dec (M.mul a (vec xs i)))) ensures
    zs = axpyF M a (vec xs) (vec ys) n

/-- Every actual multiplication and addition succeeds under its guarded contract. The
scratch cell is released and the actual multiply-add word list is returned. -/
theorem axpyLoopRoutine_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (axpyLoopRoutine (Op := Op) (Tst := Tst)).Meets I (axpyLoopGuardedSpec M dec safe) := by
  routine_intro [n] (al, x, y) reads (as, xs, ys)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  obtain ⟨hla, hlx, hly⟩ := hl
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hxs hk default
  have hgy : ∀ k < n, m.store.get y.1 (y.2 + k) = some (vec ys k) :=
    fun k hk => Store.get_of_readBlock hys hk default
  have hF := length_axpyF M a (vec xs) (vec ys) n
  refine (Writes.of_wp_updBlock_one (z := y) (ys := axpyF M a (vec xs) (vec ys) n)
    (by rw [hF]; exact hroom) ?_).mono
    (by rw [hF]) fun m' _ ⟨hpos, hread⟩ =>
      ⟨hpos, [axpyF M a (vec xs) (vec ys) n], by rwa [hF] at hread, rfl⟩
  refine wp_alloc rfl (wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    (m.store.push 1).EqOff (Store.inBlock y.1 y.2 i ⊔ Store.inBuf m.store.length) s' ∧
    s'.readBlock y.1 y.2 i = some (axpyF M a (vec xs) (vec ys) i))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_)
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlt := Store.lt_len_of_get (hgy i hi)
    have hlen : s'.len y.1 = m.store.len y.1 := by rw [hfr.len_eq, Store.len_push_of_lt hly]
    have hlent : s'.len m.store.length = 1 := by rw [hfr.len_eq, Store.len_push_top]
    refine wp_seq (wp_call_bin (hI .mul) rfl rfl rfl trivial (a := a) (b := vec xs i)
      (v := M.mul a (vec xs i)) ?_ ?_ (if_pos (hpre.1 i hi))
      ?_ ?_)
    · rw [← ha, ← Store.get_push_of_lt hla 1]
      exact hfr.get_eq (by store_side)
    · rw [← hgx i hi, ← Store.get_push_of_lt hlx 1]
      exact hfr.get_eq (by store_side)
    · store_simp
    refine wp_call_bin (hI .add) rfl rfl rfl trivial (a := vec ys i)
      (b := M.mul a (vec xs i)) (v := M.add (vec ys i) (M.mul a (vec xs i)))
      ?_ ?_ (if_pos (hpre.2 i hi)) ?_ ?_
    · store_simp
      rw [← hgy i hi, ← Store.get_push_of_lt hly 1]
      exact hfr.get_eq (by store_side)
    · store_simp
    · store_simp
    · refine ⟨_, rfl, ((hfr.mono fun b j h => ?_).upd (Or.inr rfl) _).upd
        (Or.inl ⟨rfl, by omega, by omega⟩) _, ?_⟩
      · exact h.imp (fun h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩) id
      · rw [axpyF_succ]
        exact Store.readBlock_upd_concat (by store_simp) (by store_simp) _
  · rintro m' ⟨s', rfl, hfr, hr⟩
    have : s'.pop = m.store.updBlock y.1 y.2 (axpyF M a (vec xs) (vec ys) n) :=
      hfr.pop.eq_updBlock (by
        rw [Store.readBlock_pop_of_lt (by rw [hfr.length_eq, Store.length_push]; omega), hr])
    simp [this, Mem.updBlock]

end NLAlib.Ops
