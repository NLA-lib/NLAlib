/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# `axpy`, `scal` and `copy` as loops over scalar arithmetic

Three elementwise loops, each a routine. The judgment of `axpy` and `scal` states the words the
loop writes for any machine (`NLAlib.Ops.axpyF`, `NLAlib.Ops.scalF`); each error model reads its
bound off those words by weakening the specification. The judgment of `copy` states the copied
block directly. The invariant of each loop is a frame: the cells written so far hold a prefix of
the result and the rest of the store is untouched.

## Main results

* `NLAlib.Ops.axpyLoopRoutine_meets_exact`, `NLAlib.Ops.scalLoopRoutine_meets_exact`: the words
  written, for any machine.
* `NLAlib.Ops.axpyLoopRoutine_meets`, `NLAlib.Ops.scalLoopRoutine_meets`,
  `NLAlib.Ops.copyLoopRoutine_meets`: the judgments under the standard model.
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
def axpyLoop : Stmt Op Tst :=
  .alloc (.const 1) (.loop (.var 0) (.seq
    (.call (Has.inj ScalarOp.mul) [] [⟨0, .var 1⟩, ⟨1, .var 2 + .var 5⟩] [⟨4, .const 0⟩])
    (.call (Has.inj ScalarOp.add) [] [⟨2, .var 3 + .var 5⟩, ⟨4, .const 0⟩]
      [⟨3, .var 4 + .var 5⟩])))

/-- **`scal`**: a loop of `x_i := x_i / α`. Index variables: `n`, the offsets of `α`, `x`, `x`,
then the loop variable. -/
def scalLoop : Stmt Op Tst :=
  .loop (.var 0) (.call (Has.inj ScalarOp.div) [] [⟨1, .var 2 + .var 4⟩, ⟨0, .var 1⟩]
    [⟨2, .var 3 + .var 4⟩])

/-- **`copy`**: a loop of `y_i := x_i`. Index variables: `n`, the offsets of `x`, `y`, then the
loop variable. -/
def copyLoop : Stmt Op Tst :=
  .loop (.var 0) (.call (Has.inj ScalarOp.copy) [] [⟨0, .var 1 + .var 3⟩]
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

/-- The `axpy` loop as a routine: `[n] (α : read 1, x : read n, y : update n)`. The tree has
two buffer variables for `y`. -/
def axpyLoopRoutine : Routine Op Tst :=
  routine% [n] (α : 1, x : n, y : n) → (y) := axpyLoop

/-- The `scal` loop as a routine: `[n] (α : read 1, x : update n)`. The tree has two buffer
variables for `x`. -/
def scalLoopRoutine : Routine Op Tst :=
  routine% [n] (α : 1, x : n) → (x) := scalLoop

/-- The `copy` loop as a routine: `[n] (x : read n) → (y : write n)`. -/
def copyLoopRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (y : n) := copyLoop

/-- What the `axpy` loop writes, for any machine: the words `axpyF`. Each error model reads its
bound off this specification, by applying the exact judgment at its operands. -/
def axpyLoopExactSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] ([a], xs, ys) → (zs) ensures zs = axpyF M a (vec xs) (vec ys) n

/-- What the `scal` loop writes, for any machine: the words `scalF`. -/
def scalLoopExactSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] ([a], xs) → (zs) ensures zs = scalF M a (vec xs) n

/-- The `axpy` loop, for any machine: the block `y` is replaced by `axpyF`. The invariant
is a frame: the cells written so far hold a prefix of the result, the scratch cell is the only
other cell touched, and it is released at the end. -/
theorem axpyLoopRoutine_meets_exact {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (axpyLoopRoutine (Op := Op) (Tst := Tst)).Meets I (axpyLoopExactSpec M) := by
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
    simp [this, Mem.updBlock]

/-- The `scal` loop, for any machine: the block `x` is replaced by `scalF`. -/
theorem scalLoopRoutine_meets_exact {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (scalLoopRoutine (Op := Op) (Tst := Tst)).Meets I (scalLoopExactSpec M) := by
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
    simp [hfr.eq_updBlock hr, Mem.updBlock]

/-- The `axpy` loop meets the specification read off the relation of `axpy`, with the error
`(1 + u) ^ 2 - 1`: the bound of the standard model read off the words it writes. -/
theorem axpyLoopRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (axpyLoopRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (axpyRel dec ((1 + u) ^ 2 - 1)) fun d => ok (d.headD 0)) := by
  routine_intro [n] (al, x, y)
  refine ((axpyLoopRoutine_meets_exact hI) [n] [al, x, y] τ m X rfl rfl hlive hsep hr trivial
    hrooms).mono le_rfl fun m' _ ⟨hpos, zs, hzs, hpost⟩ => ⟨hpos, zs, hzs, ?_⟩
  split_reads hr as (as, xs, ys)
  obtain ⟨a, -, rfl⟩ := Store.readBlock_one_eq_some.mp has
  rcases zs with _ | ⟨z, _ | ⟨_, _⟩⟩
  · exact hpost.elim
  · obtain rfl : z = axpyF M a (vec xs) (vec ys) n := hpost
    exact isAxpyErr_axpyF hM hu a (vec xs) (vec ys) n
  · exact hpost.elim

/-- The `scal` loop meets the specification read off the relation of `scal`, with the error
`u`: the bound of the standard model read off the words it writes. -/
theorem scalLoopRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (ok : ℕ → Prop) :
    (scalLoopRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (scalRel dec u) fun d => ok (d.headD 0)) := by
  routine_intro [n] (al, x)
  refine ((scalLoopRoutine_meets_exact hI) [n] [al, x] τ m X rfl rfl hlive hsep hr trivial
    hrooms).mono le_rfl fun m' _ ⟨hpos, zs, hzs, hpost⟩ => ⟨hpos, zs, hzs, ?_⟩
  split_reads hr as (as, xs)
  obtain ⟨a, -, rfl⟩ := Store.readBlock_one_eq_some.mp has
  rcases zs with _ | ⟨z, _ | ⟨_, _⟩⟩
  · exact hpost.elim
  · obtain rfl : z = scalF M a (vec xs) n := hpost
    exact isScalErr_scalF hM a (vec xs) n
  · exact hpost.elim

/-- The `copy` loop meets the specification read off the relation of `copy`: the block `y`
holds the block `x`. -/
theorem copyLoopRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    (ok : ℕ → Prop) :
    (copyLoopRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel copyRel fun d => ok (d.headD 0)) := by
  routine_intro [n] (x, y) reads (xs)
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hxs hk default
  have hxl := Store.length_of_readBlock hxs
  refine (Writes.of_wp_updBlock_one (z := y) (ys := xs) (by rw [hxl]; exact hroom) ?_).mono
    (by rw [hxl]) fun m' _ ⟨hpos, hread⟩ => ⟨hpos, [xs], by rwa [hxl] at hread, rfl⟩
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
    simp [hfr.eq_updBlock hr, Mem.updBlock]

/-- The routine of the `axpy` loop implements the contract of the operation `axpy`: its operands
are the inputs. -/
theorem axpyLoopRoutine_implements (dec : K → ℝ) (e : ℝ) (ok : ℕ → Prop) :
    (axpyLoopRoutine (Op := Op) (Tst := Tst)).Implements (axpyRel dec e) (InPlace ok)
      (fun ins _ => ins) := by
  implements [n] (al, x, y) → (y) with hadm

/-- The routine of the `scal` loop implements the contract of the operation `scal`: its operands
are the inputs. -/
theorem scalLoopRoutine_implements (dec : K → ℝ) (e : ℝ) (ok : ℕ → Prop) :
    (scalLoopRoutine (Op := Op) (Tst := Tst)).Implements (scalRel dec e) (InPlace ok)
      (fun ins _ => ins) := by
  implements [n] (al, x) → (x) with hadm

omit [Inhabited K] in
/-- The routine of the `copy` loop implements the contract of the operation `copy`. -/
theorem copyLoopRoutine_implements (ok : ℕ → Prop) :
    (copyLoopRoutine (Op := Op) (Tst := Tst)).Implements (copyRel (K := K)) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (y) with hadm

/-- The `axpy` loop satisfies the contract of `axpy` with the error `(1 + u) ^ 2 - 1`: a
consequence of the judgment of its routine. -/
theorem axpyLoop_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (axpyLoopRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((axpyRel dec ((1 + u) ^ 2 - 1)).spec (InPlace ok)) :=
  (axpyLoopRoutine_meets hI hM hu ok).satisfies_ofRel (axpyLoopRoutine_implements dec _ ok)
    fun _ _ _ h => h.2.1.1

/-- The `scal` loop satisfies the contract of `scal` with the error `u`: a consequence of the
judgment of its routine. -/
theorem scalLoop_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (ok : ℕ → Prop) :
    (scalLoopRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total ((scalRel dec u).spec
    (InPlace ok)) :=
  (scalLoopRoutine_meets hI hM ok).satisfies_ofRel (scalLoopRoutine_implements dec _ ok)
    fun _ _ _ h => h.2.1.1

/-- The `copy` loop satisfies the contract of `copy`: a consequence of the judgment of its
routine. -/
theorem copyLoop_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    (ok : ℕ → Prop) :
    (copyLoopRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total (copyRel.spec (OutApart ok))
    :=
  (copyLoopRoutine_meets hI ok).satisfies_ofRel (copyLoopRoutine_implements ok)
    fun _ _ _ h => h.2.1.1

end NLAlib.Ops
