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
# `dot` and `nrm2` over `sum`

`NLAlib.Ops.dotSum`: the products `x_i y_i` in a scratch block, then `sum`. So the summation rule
of `dot` is that of `sum`, whatever implements it; with a `sum` of error `e` the error of `dot`
is `(1 + u) (1 + e) - 1`. `NLAlib.Ops.nrm2Sum`: the squares, `sum`, and a square root.

## Main results

* `NLAlib.Ops.isDotErr_of_isSumErr`: mathematics, from the sum of the rounded products to the dot
  product.
* `NLAlib.Ops.wp_prodLoop`: the loop that fills the scratch block.
* `NLAlib.Ops.dotSumRoutine_meets`, `NLAlib.Ops.nrm2SumRoutine_meets`: the judgments.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-! ### Mathematics -/

/-- **From the sum of the rounded products to the dot product.** -/
theorem isDotErr_of_isSumErr {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    {e : ℝ} (he : 0 ≤ e) {n : ℕ} {a b p : ℕ → K} {v : K}
    (hp : ∀ k < n, p k = M.mul (a k) (b k)) (h : IsSumErr dec e n p v) :
    IsDotErr dec ((1 + u) * (1 + e) - 1) n a b v := by
  unfold IsSumErr at h
  unfold IsDotErr
  have h1 : ∀ k ∈ Finset.range n, |dec (p k) - dec (a k) * dec (b k)| ≤
      u * |dec (a k) * dec (b k)| := fun k hk => by
    rw [hp k (Finset.mem_range.mp hk)]
    exact hM.mul _ _
  have h2 : ∑ k ∈ Finset.range n, |dec (p k)| ≤
      (1 + u) * ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => abs_le_of_abs_sub_le (h1 k hk)
  have h3 : |∑ k ∈ Finset.range n, dec (p k) - ∑ k ∈ Finset.range n, dec (a k) * dec (b k)| ≤
      u * ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h1)
  have h4 := abs_add_le (dec v - ∑ k ∈ Finset.range n, dec (p k))
    (∑ k ∈ Finset.range n, dec (p k) - ∑ k ∈ Finset.range n, dec (a k) * dec (b k))
  rw [sub_add_sub_cancel] at h4
  have hT : 0 ≤ ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 he]

section

variable [Has ScalarOp Op]

/-- The loop `t_i := x_i * y_i` for `i < n`. The operands may depend on the loop variable. -/
def prodLoop (n : IExp) (x y t : Operand) : Stmt Op Tst :=
  .loop n (.call (Has.inj ScalarOp.mul) [] [x, y] [t])

/-- **The product loop** fills the block `t` from offset zero with the rounded products and
writes nothing else. -/
theorem wp_prodLoop {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {md : Mode}
    {τ : Tape K} {ρ : Env} {n : IExp} {x y t : Operand} {N bx by' bt ox oy : ℕ} {S : Store K}
    {p : ℕ} {a b : ℕ → K} (hn : n.eval ρ.idx = some N)
    (hx : ∀ k, x.eval (ρ.pushIdx k) = some (bx, ox + k))
    (hy : ∀ k, y.eval (ρ.pushIdx k) = some (by', oy + k))
    (ht : ∀ k, t.eval (ρ.pushIdx k) = some (bt, k)) (hxt : bx ≠ bt) (hyt : by' ≠ bt)
    (hlen : N ≤ S.len bt) (ha : ∀ k < N, S.get bx (ox + k) = some (a k))
    (hb : ∀ k < N, S.get by' (oy + k) = some (b k)) {Q : Mem K → Prop}
    (hQ : ∀ s', S.EqOff (Store.inBuf bt) s' →
      s'.readBlock bt 0 N = some ((List.range N).map fun k => M.mul (a k) (b k)) → Q ⟨s', p⟩) :
    Wp md I τ (prodLoop (Op := Op) n x y t) ρ Q ⟨S, p⟩ := by
  refine wp_loop hn (fun i m' => ∃ s', m' = ⟨s', p⟩ ∧ S.EqOff (Store.inBuf bt) s' ∧
    s'.readBlock bt 0 i = some ((List.range i).map fun k => M.mul (a k) (b k)))
    ⟨S, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ fun m' ⟨s', h1, h2, h3⟩ => h1 ▸ hQ s' h2 h3
  rintro i hi m' ⟨s', rfl, hfr, hr⟩
  refine wp_call_bin (hI .mul) (x := (bx, ox + i)) (y := (by', oy + i)) (z := (bt, i)) rfl
    (by simp [hx, hy]) (by simp [ht]) trivial (a := a i) (b := b i) ?_ ?_ rfl ?_ ?_
  · rw [← ha i hi]
    exact hfr.get_eq (by simpa [Store.inBuf] using hxt)
  · rw [← hb i hi]
    exact hfr.get_eq (by simpa [Store.inBuf] using hyt)
  · change i < s'.len bt
    rw [hfr.len_eq]
    omega
  · refine ⟨_, rfl, hfr.upd rfl _, ?_⟩
    rw [List.range_succ, List.map_append]
    exact Store.readBlock_upd_concat_zero hr (by rw [hfr.len_eq]; omega) _

variable [Has Blas1Op Op]

/-- **`dot` over `sum`.** Index variables: `n`, the offsets of `x`, `y`, `z`, then the loop
variable; buffer variables: `x`, `y`, `z`, then the scratch block. -/
def dotSum : Stmt Op Tst :=
  .alloc (.var 0)
    (.seq (prodLoop (.var 0) ⟨0, .var 1 + .var 4⟩ ⟨1, .var 2 + .var 4⟩ ⟨3, .var 4⟩)
      (.call (Has.inj Blas1Op.sum) [.var 0] [⟨3, .const 0⟩] [⟨2, .var 3⟩]))

/-- **`nrm2` over `sum`.** Index variables: `n`, the offsets of `x`, `z`, then the loop variable;
buffer variables: `x`, `z`, then the scratch block. -/
def nrm2Sum : Stmt Op Tst :=
  .alloc (.var 0)
    (.seq (prodLoop (.var 0) ⟨0, .var 1 + .var 3⟩ ⟨0, .var 1 + .var 3⟩ ⟨2, .var 3⟩)
      (.seq (.call (Has.inj Blas1Op.sum) [.var 0] [⟨2, .const 0⟩] [⟨1, .var 2⟩])
        (.call (Has.inj ScalarOp.sqrt) [] [⟨1, .var 2⟩] [⟨1, .var 2⟩])))

variable [Inhabited K]

omit [Inhabited K] in
theorem vec_map_range [Inhabited K] (f : ℕ → K) {n k : ℕ} (hk : k < n) :
    vec ((List.range n).map f) k = f k := by
  simp [vec, List.getD_eq_getElem?_getD, hk]

/-- `dotSum` as a routine: `[n] (x : read n, y : read n) → (z : write 1)`. -/
def dotSumRoutine : Routine Op Tst :=
  routine% [n] (x : n, y : n) → (z : 1) := dotSum

/-- `nrm2Sum` as a routine: `[n] (x : read n) → (z : write 1)`. -/
def nrm2SumRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (z : 1) := nrm2Sum

/-- `dotSum` meets the specification read off the relation of `dot`, with the error
`(1 + u) (1 + es n) - 1`, over an interpretation whose `sum` has the error `es`: the products are
formed in a scratch block, summed into the cell, and the scratch block is released. -/
theorem dotSumRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop} (hS : IsSum dec es ok I)
    (hes : ∀ n, 0 ≤ es n) :
    (dotSumRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (dotRel dec fun n => (1 + u) * (1 + es n) - 1)
        fun d => ok (d.headD 0)) := by
  routine_intro [n] (x, y, z) reads (xs, ys)
  obtain ⟨hlx, hly, hlz⟩ := hl
  have hz : z.2 < m.store.len z.1 := by omega
  refine (Writes.of_wp_upd_cell hz ?_).mono le_rfl
    fun m' _ ⟨hpos, v, hv, he⟩ => ⟨hpos, [[v]], hv, he⟩
  refine wp_alloc rfl (wp_seq (wp_prodLoop hI (a := vec xs) (b := vec ys) rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hlx.ne hly.ne (by simp) ?_ ?_ fun s' hfr hr => ?_))
  · exact fun k hk => by store_simp [Store.get_of_readBlock hxs hk default]
  · exact fun k hk => by store_simp [Store.get_of_readBlock hys hk default]
  have hlen : s'.length = m.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlenz : s'.len z.1 = m.store.len z.1 := by rw [hfr.len_eq, Store.len_push_of_lt hlz]
  have hok : ok n := hpre.1
  wp_call hS with v hv
  refine ⟨v, isDotErr_of_isSumErr hM (hes n) (fun k hk => vec_map_range _ hk) hv, ?_⟩
  simp only [Mem.upd]
  rw [Store.pop_upd_of_lt (by omega), hfr.pop_eq]

/-- `nrm2Sum` meets the specification read off the relation of `nrm2`, over an
interpretation whose `sum` has the error `es`: the squares are formed in a scratch block, summed,
and the square root of the sum is taken in place. -/
theorem nrm2SumRoutine_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop} (hS : IsSum dec es ok I)
    (hes : ∀ n, 0 ≤ es n) :
    (nrm2SumRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (nrm2Rel dec (fun n => (1 + u) * (1 + es n) - 1) u)
        fun d => ok (d.headD 0)) := by
  routine_intro [n] (x, z) reads (xs)
  obtain ⟨hlx, hlz⟩ := hl
  have hz : z.2 < m.store.len z.1 := by omega
  refine (Writes.of_wp_upd_cell hz ?_).mono le_rfl
    fun m' _ ⟨hpos, v, hv, he⟩ => ⟨hpos, [[v]], hv, he⟩
  have hg : ∀ k < n, (m.store.push n).get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => by store_simp [Store.get_of_readBlock hxs hk default]
  refine wp_alloc rfl (wp_seq (wp_prodLoop hI (a := vec xs) (b := vec xs) rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hlx.ne hlx.ne (by simp) hg hg fun s' hfr hr => ?_))
  have hlen : s'.length = m.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlenz : s'.len z.1 = m.store.len z.1 := by rw [hfr.len_eq, Store.len_push_of_lt hlz]
  have hok : ok n := hpre.1
  wp_call hS with σ hσ
  wp_call (hI .sqrt)
  refine ⟨M.sqrt σ, ⟨σ, isDotErr_of_isSumErr hM (hes n) (fun k hk => vec_map_range _ hk) hσ,
    hM.sqrt σ⟩, ?_⟩
  simp only [Mem.upd, Store.upd_upd]
  rw [Store.pop_upd_of_lt (by omega), hfr.pop_eq]

/-- The routine `dotSum` implements the contract of the operation `dot`. -/
theorem dotSumRoutine_implements (dec : K → ℝ) (e : ℕ → ℝ) (ok : ℕ → Prop) :
    (dotSumRoutine (Op := Op) (Tst := Tst)).Implements (dotRel dec e) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x, y) → (z) with hadm

/-- The routine `nrm2Sum` implements the contract of the operation `nrm2`. -/
theorem nrm2SumRoutine_implements (dec : K → ℝ) (e : ℕ → ℝ) (u : ℝ) (ok : ℕ → Prop) :
    (nrm2SumRoutine (Op := Op) (Tst := Tst)).Implements (nrm2Rel dec e u) (OutApart ok)
      (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

/-- `dotSum` satisfies the contract of `dot` with the error `(1 + u) (1 + es n) - 1`, over an
interpretation whose `sum` has the error `es`: a consequence of the judgment of its routine. -/
theorem dotSum_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop} (hS : IsSum dec es ok I)
    (hes : ∀ n, 0 ≤ es n) :
    (dotSumRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((dotRel dec fun n => (1 + u) * (1 + es n) - 1).spec (OutApart ok)) :=
  (dotSumRoutine_meets hI hM hS hes).satisfies_ofRel (dotSumRoutine_implements dec _ ok)
    fun _ _ _ h => h.2.1.1

/-- `nrm2Sum` satisfies the contract of `nrm2`, over an interpretation whose `sum` has the error
`es`: a consequence of the judgment of its routine. -/
theorem nrm2Sum_satisfies {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop} (hS : IsSum dec es ok I)
    (hes : ∀ n, 0 ≤ es n) :
    (nrm2SumRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((nrm2Rel dec (fun n => (1 + u) * (1 + es n) - 1) u).spec (OutApart ok)) :=
  (nrm2SumRoutine_meets hI hM hS hes).satisfies_ofRel (nrm2SumRoutine_implements dec _ u ok)
    fun _ _ _ h => h.2.1.1

end

end NLAlib.Ops
