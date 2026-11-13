/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1

/-!
# `axpy`, `scal` and `copy` as loops over scalar arithmetic

Three elementwise loops. Each run is stated by an equation: the block is replaced by the list of
the words computed (`NLAlib.Ops.axpyF`, `NLAlib.Ops.scalF`, the input block). The invariant of
each loop is a frame: the cells written so far hold a prefix of the result and the rest of the
store is untouched.

## Main results

* `NLAlib.Ops.wp_axpyLoop`, `NLAlib.Ops.wp_scalLoop`, `NLAlib.Ops.wp_copyLoop`: the runs.
* `NLAlib.Ops.isAxpyErr_axpyF`, `NLAlib.Ops.isScalErr_scalF`: the error bounds, `(1 + u) ^ 2 - 1`
  and `u`.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- The words written by the `axpy` loop. -/
def axpyF (M : Machine K) (a : K) (x y : ℕ → K) (n : ℕ) : List K :=
  (List.range n).map fun i => M.add (y i) (M.mul a (x i))

/-- The words written by the `scal` loop. -/
def scalF (M : Machine K) (a : K) (x : ℕ → K) (n : ℕ) : List K :=
  (List.range n).map fun i => M.div (x i) a

omit [Has ScalarOp Op] in
theorem axpyF_succ (M : Machine K) (a : K) (x y : ℕ → K) (n : ℕ) :
    axpyF M a x y (n + 1) = axpyF M a x y n ++ [M.add (y n) (M.mul a (x n))] := by
  simp [axpyF, List.range_succ]

omit [Has ScalarOp Op] in
theorem scalF_succ (M : Machine K) (a : K) (x : ℕ → K) (n : ℕ) :
    scalF M a x (n + 1) = scalF M a x n ++ [M.div (x n) a] := by
  simp [scalF, List.range_succ]

/-- **`axpy`**: a scratch cell and a loop of `t := α x_i; y_i := y_i + t`. Index variables: `n`,
the offsets of `α`, `x`, `y`, `y`, then the loop variable; buffer variables: `α`, `x`, `y`, `y`,
then the scratch cell. -/
def axpyLoop : Impl Op Tst where
  nd := 1
  nin := 3
  nout := 1
  body := .alloc (.const 1) (.loop (.var 0) (.seq
    (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 1⟩, ⟨1, .var 2 + .var 5⟩] [⟨4, .const 0⟩])
    (.call (Has.inj ScalarOp.add) [] [⟨2, .var 3 + .var 5⟩, ⟨4, .const 0⟩]
      [⟨3, .var 4 + .var 5⟩])))

/-- **`scal`**: a loop of `x_i := x_i / α`. Index variables: `n`, the offsets of `α`, `x`, `x`,
then the loop variable. -/
def scalLoop : Impl Op Tst where
  nd := 1
  nin := 2
  nout := 1
  body := .loop (.var 0) (.call (Has.inj ScalarOp.div) [] [⟨1, .var 2 + .var 4⟩, ⟨0, .var 1⟩]
    [⟨2, .var 3 + .var 4⟩])

/-- **`copy`**: a loop of `y_i := x_i`. Index variables: `n`, the offsets of `x`, `y`, then the
loop variable. -/
def copyLoop : Impl Op Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .loop (.var 0) (.call (Has.inj ScalarOp.copy) [] [⟨0, .var 1 + .var 3⟩]
    [⟨1, .var 2 + .var 3⟩])

variable [Inhabited K]

omit [Has ScalarOp Op] [Inhabited K] in
theorem length_axpyF (M : Machine K) (a : K) (x y : ℕ → K) (n : ℕ) :
    (axpyF M a x y n).length = n := by simp [axpyF]

omit [Has ScalarOp Op] [Inhabited K] in
theorem length_scalF (M : Machine K) (a : K) (x : ℕ → K) (n : ℕ) :
    (scalF M a x n).length = n := by simp [scalF]

omit [Has ScalarOp Op] in
/-- The error of the `axpy` loop: `(1 + u) ^ 2 - 1`, componentwise. -/
theorem isAxpyErr_axpyF {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (a : K) (x y : ℕ → K) (n : ℕ) :
    IsAxpyErr dec ((1 + u) ^ 2 - 1) n a x y (vec (axpyF M a x y n)) := by
  intro i hi
  have : vec (axpyF M a x y n) i = M.add (y i) (M.mul a (x i)) := by
    simp [vec, axpyF, List.getD_eq_getElem?_getD, hi]
  rw [this]
  exact hM.abs_add_mul_sub_le hu _ _ _

omit [Has ScalarOp Op] in
/-- The error of the `scal` loop: `u`, componentwise. -/
theorem isScalErr_scalF {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M) (a : K)
    (x : ℕ → K) (n : ℕ) : IsScalErr dec u n a x (vec (scalF M a x n)) := by
  intro ha i hi
  have : vec (scalF M a x n) i = M.div (x i) a := by
    simp [vec, scalF, List.getD_eq_getElem?_getD, hi]
  rw [this]
  exact hM.div _ _ ha

/-- **The run of the `axpy` loop** replaces the block `y` by `axpyF`. -/
theorem wp_axpyLoop {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {md : Mode}
    {τ : Tape K} {n : ℕ} {al x y : ℕ × ℕ} {m : Mem K} {a : K} {xs ys : List K}
    (hal : al.1 ≠ y.1) (hxy : x.1 ≠ y.1) (hl : m.Live [al, x, y])
    (ha : m.store.get al.1 al.2 = some a) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : m.store.readBlock y.1 y.2 n = some ys) {Q : Mem K → Prop}
    (hQ : Q (m.updBlock y (axpyF M a (vec xs) (vec ys) n))) :
    Wp md I τ (axpyLoop (Op := Op) (Tst := Tst)).body (Env.frame [n] [al, x, y, y]) Q m := by
  obtain ⟨hla, hlx, hly⟩ :
      al.1 < m.store.length ∧ x.1 < m.store.length ∧ y.1 < m.store.length := by simpa using hl
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hx hk default
  have hgy : ∀ k < n, m.store.get y.1 (y.2 + k) = some (vec ys k) :=
    fun k hk => Store.get_of_readBlock hy hk default
  refine wp_alloc rfl (wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    (m.store.push 1).EqOff (Store.inBlock y.1 y.2 i ⊔ Store.inBuf m.store.length) s' ∧
    s'.readBlock y.1 y.2 i = some (axpyF M a (vec xs) (vec ys) i))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_)
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlt := Store.lt_len_of_get (hgy i hi)
    have hlen : s'.len y.1 = m.store.len y.1 := by rw [hfr.len_eq, Store.len_push_of_lt hly]
    have hlent : s'.len m.store.length = 1 := by rw [hfr.len_eq, Store.len_push_top]
    refine wp_seq (wp_call_bin (hI .mul) rfl rfl rfl trivial (a := a) (b := vec xs i) ?_ ?_ rfl
      ?_ ?_)
    · rw [← ha, ← Store.get_push_of_lt hla 1]
      exact hfr.get_eq (by store_side)
    · rw [← hgx i hi, ← Store.get_push_of_lt hlx 1]
      exact hfr.get_eq (by store_side)
    · store_simp
    refine wp_call_bin (hI .add) rfl rfl rfl trivial (a := vec ys i)
      (b := M.mul a (vec xs i)) ?_ ?_ rfl ?_ ?_
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
    simpa [this, Mem.updBlock] using hQ

/-- **The run of the `scal` loop** replaces the block `x` by `scalF`. -/
theorem wp_scalLoop {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {md : Mode}
    {τ : Tape K} {n : ℕ} {al x : ℕ × ℕ} {m : Mem K} {a : K} {xs : List K} (hal : al.1 ≠ x.1)
    (ha : m.store.get al.1 al.2 = some a) (hx : m.store.readBlock x.1 x.2 n = some xs)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock x (scalF M a (vec xs) n))) :
    Wp md I τ (scalLoop (Op := Op) (Tst := Tst)).body (Env.frame [n] [al, x, x]) Q m := by
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hx hk default
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Store.inBlock x.1 x.2 i) s' ∧
    s'.readBlock x.1 x.2 i = some (scalF M a (vec xs) i))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlt := Store.lt_len_of_get (hgx i hi)
    have hlen := hfr.len_eq x.1
    refine wp_call_bin (hI .div) rfl rfl rfl trivial (a := vec xs i) (b := a) ?_ ?_ rfl ?_ ?_
    · rw [← hgx i hi]
      exact hfr.get_eq (by store_side)
    · rw [← ha]
      exact hfr.get_eq (by store_side)
    · store_simp
    · refine ⟨_, rfl, (hfr.mono fun b j h => ?_).upd ⟨rfl, by omega, by omega⟩ _, ?_⟩
      · exact ⟨h.1, h.2.1, by have := h.2.2; omega⟩
      · rw [scalF_succ]
        exact Store.readBlock_upd_concat hr (by omega) _
  · rintro m' ⟨s', rfl, hfr, hr⟩
    simpa [hfr.eq_updBlock hr, Mem.updBlock] using hQ

/-- **The run of the `copy` loop** replaces the block `y` by the block `x`. -/
theorem wp_copyLoop {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {md : Mode}
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K} (hxy : x.1 ≠ y.1)
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hy : y.2 + n ≤ m.store.len y.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock y xs)) :
    Wp md I τ (copyLoop (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, y]) Q m := by
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hx hk default
  have hxl := Store.length_of_readBlock hx
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Store.inBlock y.1 y.2 i) s' ∧ s'.readBlock y.1 y.2 i = some (xs.take i))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlen := hfr.len_eq y.1
    refine wp_call_un (hI .copy) rfl rfl rfl trivial (a := vec xs i) ?_ rfl ?_ ?_
    · rw [← hgx i hi]
      exact hfr.get_eq (by store_side)
    · store_simp
    · refine ⟨_, rfl, (hfr.mono fun b j h => ?_).upd ⟨rfl, by omega, by omega⟩ _, ?_⟩
      · exact ⟨h.1, h.2.1, by have := h.2.2; omega⟩
      · have : xs.take (i + 1) = xs.take i ++ [vec xs i] := by
          rw [List.take_add_one, vec, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)]
          rfl
        rw [this]
        exact Store.readBlock_upd_concat hr (by omega) _
  · rintro m' ⟨s', rfl, hfr, hr⟩
    rw [List.take_of_length_le (by omega)] at hr
    simpa [hfr.eq_updBlock hr, Mem.updBlock] using hQ

/-- **The `axpy` loop meets the contract of `axpy`** with the error `(1 + u) ^ 2 - 1`. -/
theorem axpyLoop_spec {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (axpyLoop (Op := Op) (Tst := Tst)).Triple I .total
      ((axpyRel dec ((1 + u) ^ 2 - 1)).spec (InPlace ok)) := by
  refine Impl.meets_rel fun d ins outs τ m X hnd hadm hl hr _ hz => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨al, x, y, as, xs, ys, rfl, ha, hx, hy, rfl⟩ := Mem.readBlocks_three hr
  obtain ⟨-, hout, hne⟩ := hadm
  obtain rfl : outs = [y] := by simpa using hout
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : m.store.get al.1 al.2 = some a := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one a
  exact ⟨⟨rfl, rfl, rfl⟩, wp_axpyLoop hI (hne al (by simp) y (by simp))
    (hne x (by simp) y (by simp)) (by simpa using hl) ha' hx hy
    ⟨[_], by simp [axpyRel, length_axpyF], isAxpyErr_axpyF hM hu a (vec xs) (vec ys) n, rfl⟩⟩

/-- **The `scal` loop meets the contract of `scal`** with the error `u`. -/
theorem scalLoop_spec {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (ok : ℕ → Prop) :
    (scalLoop (Op := Op) (Tst := Tst)).Triple I .total ((scalRel dec u).spec (InPlace ok)) := by
  refine Impl.meets_rel fun d ins outs τ m X hnd hadm hl hr _ hz => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨al, x, as, xs, rfl, ha, hx, rfl⟩ := Mem.readBlocks_two hr
  obtain ⟨-, hout, hne⟩ := hadm
  obtain rfl : outs = [x] := by simpa using hout
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : m.store.get al.1 al.2 = some a := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one a
  exact ⟨⟨rfl, rfl, rfl⟩, wp_scalLoop hI (hne al (by simp) x (by simp)) ha' hx
    ⟨[_], by simp [scalRel, length_scalF], isScalErr_scalF hM a (vec xs) n, rfl⟩⟩

/-- **The `copy` loop meets the contract of `copy`.** -/
theorem copyLoop_spec {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    (ok : ℕ → Prop) :
    (copyLoop (Op := Op) (Tst := Tst)).Triple I .total (copyRel.spec (OutApart ok)) := by
  refine Impl.meets_rel fun d ins outs τ m X hnd hadm hl hr _ hz => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨z, rfl, hz'⟩ := Mem.room_one hz
  exact ⟨⟨rfl, rfl, rfl⟩, wp_copyLoop hI (hadm.2 x (by simp) z (by simp)) hx hz'
    ⟨[xs], by simp [copyRel, Store.length_of_readBlock hx], rfl, rfl⟩⟩

end NLAlib.Ops
