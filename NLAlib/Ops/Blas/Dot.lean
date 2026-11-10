/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1

/-!
# `dot` and `nrm2` over `sum`

`NLAlib.Ops.dotSum`: the products `x_i y_i` in a scratch block, then `sum`. So the summation rule
of `dot` is that of `sum`, whatever implements it; with a `sum` of error `e` the error of `dot`
is `(1 + u) (1 + e) - 1`. `NLAlib.Ops.nrm2Sum`: the squares, `sum`, and a square root.

## Main results

* `NLAlib.Ops.isDotErr_of_isSumErr`: mathematics, from the sum of the rounded products to the dot
  product.
* `NLAlib.Ops.wp_prodLoop`: the loop that fills the scratch block.
* `NLAlib.Ops.wp_dotSum`, `NLAlib.Ops.wp_nrm2Sum`: the runs.
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
    {τ : ℕ → K} {ρ : Env} {n : IExp} {x y t : Operand} {N bx by' bt ox oy : ℕ} {S : Store K}
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
def dotSum : Impl Op Tst where
  nd := 1
  nin := 2
  nout := 1
  body := .alloc (.var 0)
    (.seq (prodLoop (.var 0) ⟨0, .var 1 + .var 4⟩ ⟨1, .var 2 + .var 4⟩ ⟨3, .var 4⟩)
      (.call (Has.inj Blas1Op.sum) [.var 0] [⟨3, .const 0⟩] [⟨2, .var 3⟩]))

/-- **`nrm2` over `sum`.** Index variables: `n`, the offsets of `x`, `z`, then the loop variable;
buffer variables: `x`, `z`, then the scratch block. -/
def nrm2Sum : Impl Op Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .alloc (.var 0)
    (.seq (prodLoop (.var 0) ⟨0, .var 1 + .var 3⟩ ⟨0, .var 1 + .var 3⟩ ⟨2, .var 3⟩)
      (.seq (.call (Has.inj Blas1Op.sum) [.var 0] [⟨2, .const 0⟩] [⟨1, .var 2⟩])
        (.call (Has.inj ScalarOp.sqrt) [] [⟨1, .var 2⟩] [⟨1, .var 2⟩])))

variable [Inhabited K]

omit [Inhabited K] in
theorem vec_map_range [Inhabited K] (f : ℕ → K) {n k : ℕ} (hk : k < n) :
    vec ((List.range n).map f) k = f k := by
  simp [vec, List.getD_eq_getElem?_getD, hk]

/-- **The run of `dotSum`**, over an interpretation whose `sum` has the error `es`. -/
theorem wp_dotSum {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop}
    (hS : IsSum dec es ok I) {τ : ℕ → K} {n : ℕ} {x y z : ℕ × ℕ} {m : Mem K} {xs ys : List K}
    (hes : 0 ≤ es n) (hok : ok n) (hl : m.Live [x, y, z])
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hy : m.store.readBlock y.1 y.2 n = some ys)
    (hz : z.2 < m.store.len z.1) :
    Wp .total I τ (dotSum (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, y, z])
      (fun m' => ∃ v, IsDotErr dec ((1 + u) * (1 + es n) - 1) n (vec xs) (vec ys) v ∧
        m' = m.upd z v) m := by
  obtain ⟨hlx, hly, hlz⟩ :
      x.1 < m.store.length ∧ y.1 < m.store.length ∧ z.1 < m.store.length := by simpa using hl
  refine wp_alloc rfl (wp_seq (wp_prodLoop hI (a := vec xs) (b := vec ys) rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hlx.ne hly.ne (by simp) ?_ ?_ fun s' hfr hr => ?_))
  · exact fun k hk => by store_simp [Store.get_of_readBlock hx hk default]
  · exact fun k hk => by store_simp [Store.get_of_readBlock hy hk default]
  have hlen : s'.length = m.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlenz : s'.len z.1 = m.store.len z.1 := by rw [hfr.len_eq, Store.len_push_of_lt hlz]
  refine wp_call_rel_cell hS rfl rfl rfl rfl rfl ⟨hok, by simp; omega⟩ ?_
    (xs := [(List.range n).map fun k => M.mul (vec xs k) (vec ys k)]) ?_ ?_ fun v hv => ?_
  · store_simp
  · store_simp
  · store_simp
  refine ⟨v, isDotErr_of_isSumErr hM hes (fun k hk => vec_map_range _ hk) hv, ?_⟩
  simp only [Mem.upd]
  rw [Store.pop_upd_of_lt (by omega), hfr.pop_eq]

/-- **The run of `nrm2Sum`**, over an interpretation whose `sum` has the error `es`. -/
theorem wp_nrm2Sum {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {es : ℕ → ℝ} {ok : ℕ → Prop}
    (hS : IsSum dec es ok I) {τ : ℕ → K} {n : ℕ} {x z : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hes : 0 ≤ es n) (hok : ok n) (hl : m.Live [x, z])
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hz : z.2 < m.store.len z.1) :
    Wp .total I τ (nrm2Sum (Op := Op) (Tst := Tst)).body (Env.frame [n] [x, z])
      (fun m' => ∃ ν, IsNrm2Err dec ((1 + u) * (1 + es n) - 1) u n (vec xs) ν ∧
        m' = m.upd z ν) m := by
  obtain ⟨hlx, hlz⟩ : x.1 < m.store.length ∧ z.1 < m.store.length := by simpa using hl
  have hg : ∀ k < n, (m.store.push n).get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => by store_simp [Store.get_of_readBlock hx hk default]
  refine wp_alloc rfl (wp_seq (wp_prodLoop hI (a := vec xs) (b := vec xs) rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) hlx.ne hlx.ne (by simp) hg hg fun s' hfr hr => ?_))
  have hlen : s'.length = m.store.length + 1 := by rw [hfr.length_eq, Store.length_push]
  have hlenz : s'.len z.1 = m.store.len z.1 := by rw [hfr.len_eq, Store.len_push_of_lt hlz]
  refine wp_seq (wp_call_rel_cell hS rfl rfl rfl rfl rfl ⟨hok, by simp; omega⟩ ?_
    (xs := [(List.range n).map fun k => M.mul (vec xs k) (vec xs k)]) ?_ ?_ fun σ hσ => ?_)
  · store_simp
  · store_simp
  · store_simp
  refine wp_call_un (hI .sqrt) rfl rfl rfl trivial (a := σ) ?_ rfl ?_ ?_
  · store_simp
  · store_simp
  refine ⟨M.sqrt σ, ⟨σ, isDotErr_of_isSumErr hM hes (fun k hk => vec_map_range _ hk) hσ,
    hM.sqrt σ⟩, ?_⟩
  simp only [Mem.upd, Store.upd_upd]
  rw [Store.pop_upd_of_lt (by omega), hfr.pop_eq]

end

end NLAlib.Ops
