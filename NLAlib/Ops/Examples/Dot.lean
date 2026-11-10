/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar

/-!
# Example: the dot product over scalar arithmetic

## Main results

* Mathematics (`NLAlib.Ops.Examples.abs_dec_dotF_sub_le`): the recursive summation of rounded
  products,
  as a function `NLAlib.Ops.Examples.dotF` of a machine, has the error `(1 + u) ^ (2 n) - 1`
  relative to the sum of the absolute values of the products. No program.
* Program logic (`NLAlib.Ops.Examples.wp_dotLoop`): the accumulation loop
  `NLAlib.Ops.Examples.dotLoop` computes `dotF` in the cell `z`, with a scratch cell on top of the
  store. It is stated for arbitrary operands whose offsets may depend on the loop variable, so
  that the matrix product reuses it.
* The exact certificate (`NLAlib.Ops.Examples.dot_cert`): the run of the implementation
  `NLAlib.Ops.Examples.dotImpl` is the block function `NLAlib.Ops.Examples.dotFn`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type}

/-- The functional contract of scalar arithmetic, for a signature that is the scalar group. -/
abbrev IsArith (M : Machine K) (I : Interp ScalarOp Empty K) : Prop :=
  ∀ o, I.IsFn .total o (M.fn o) AnyOperands

/-- The recursive summation of the rounded products `a k * b k`, `k < n`, by a machine. -/
def dotF (M : Machine K) (a b : ℕ → K) (n : ℕ) : K :=
  (List.range n).foldl (fun acc k => M.add acc (M.mul (a k) (b k))) (M.lit 0)

theorem dotF_succ (M : Machine K) (a b : ℕ → K) (n : ℕ) :
    dotF M a b (n + 1) = M.add (dotF M a b n) (M.mul (a n) (b n)) := by
  simp [dotF, List.range_succ]

/-! ### Mathematics -/

/-- **The error of the rounded dot product**, on decoded values. -/
theorem abs_dec_dotF_sub_le {u : ℝ} {dec : K → ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : 0 ≤ u) (a b : ℕ → K) (n : ℕ) :
    |dec (dotF M a b n) - ∑ k ∈ Finset.range n, dec (a k) * dec (b k)| ≤
      ((1 + u) ^ (2 * n) - 1) * ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| := by
  induction n with
  | zero => simp [dotF, hM.zero]
  | succ n ih =>
    rw [dotF_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hST := Finset.abs_sum_le_sum_abs (fun k => dec (a k) * dec (b k)) (Finset.range n)
    have hT : 0 ≤ ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hc : 0 ≤ (1 + u) ^ (2 * n) - 1 := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + u by linarith) (n := 2 * n)
      linarith
    have hc' : (1 + u) ^ (2 * (n + 1)) - 1 = (1 + u) ^ 2 * ((1 + u) ^ (2 * n) - 1 + 1) - 1 := by
      ring
    rw [hc']
    generalize (1 + u) ^ (2 * n) - 1 = c at ih hc
    generalize ∑ k ∈ Finset.range n, dec (a k) * dec (b k) = S at ih hST
    generalize ∑ k ∈ Finset.range n, |dec (a k) * dec (b k)| = T at ih hST hT
    have h1 := hM.mul (a n) (b n)
    have h2 := hM.add (dotF M a b n) (M.mul (a n) (b n))
    generalize dec (M.add (dotF M a b n) (M.mul (a n) (b n))) = s' at h2
    generalize dec (M.mul (a n) (b n)) = p at h1 h2
    generalize dec (dotF M a b n) = s at ih h2
    generalize dec (a n) * dec (b n) = x at h1
    have hx := abs_nonneg x
    have hs : |s| ≤ T + c * T := by
      have := abs_add_le S (s - S)
      rw [add_sub_cancel] at this
      linarith
    have hp : |p| ≤ |x| + u * |x| := by
      have := abs_add_le x (p - x)
      rw [add_sub_cancel] at this
      linarith
    have hsp : |s + p| ≤ T + c * T + (|x| + u * |x|) := (abs_add_le s p).trans (by linarith)
    have hA : |s' - (s + p)| ≤ u * (T + c * T + (|x| + u * |x|)) :=
      h2.trans (mul_le_mul_of_nonneg_left hsp hu)
    have h3 : |s' - (S + x)| ≤ |s' - (s + p)| + |s - S| + |p - x| := by
      have := abs_add_three (s' - (s + p)) (s - S) (p - x)
      rwa [show s' - (s + p) + (s - S) + (p - x) = s' - (S + x) by ring] at this
    nlinarith [mul_nonneg hu hT, mul_nonneg (mul_nonneg hu hu) hT, mul_nonneg hc hT,
      mul_nonneg hu (mul_nonneg hc hT), mul_nonneg (mul_nonneg hu hu) (mul_nonneg hc hT),
      mul_nonneg hc hx, mul_nonneg hu (mul_nonneg hc hx),
      mul_nonneg (mul_nonneg hu hu) (mul_nonneg hc hx), mul_nonneg hu hx]

/-! ### Program logic -/

/-- The accumulation loop: `z := 0; for k < n: t := x * y; z := z + t`. The operands `x`, `y` may
depend on the loop variable. -/
def dotLoop (n : IExp) (x y z t : Operand) : Stmt ScalarOp Empty :=
  .seq (.call (.lit 0) [] [] [z])
    (.loop n (.seq (.call .mul [] [x, y] [t]) (.call .add [] [z, t] [z])))

/-- **The accumulation loop computes `dotF`** in the cell `z`, for a store with one scratch cell
on top (the operand `t`), input cells in other buffers than `z`. -/
theorem wp_dotLoop {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) {md : Mode}
    {τ : ℕ → K}
    {ρ : Env} {n : IExp} {x y z t : Operand} {N bx by' bz oz : ℕ} {fx fy : ℕ → ℕ} {s : Store K}
    {tb : Buf K} {p : ℕ} {a b : ℕ → K} (hn : n.eval ρ.idx = some N)
    (hz0 : z.eval ρ = some (bz, oz)) (hx : ∀ k, x.eval (ρ.pushIdx k) = some (bx, fx k))
    (hy : ∀ k, y.eval (ρ.pushIdx k) = some (by', fy k))
    (hz : ∀ k, z.eval (ρ.pushIdx k) = some (bz, oz))
    (ht : ∀ k, t.eval (ρ.pushIdx k) = some (s.length, 0)) (htb : tb.length = 1) (hxz : bx ≠ bz)
    (hyz : by' ≠ bz) (hzl : oz < s.len bz) (ha : ∀ k < N, s.get bx (fx k) = some (a k))
    (hb : ∀ k < N, s.get by' (fy k) = some (b k)) {Q : Mem K → Prop}
    (hQ : ∀ tb' : Buf K, tb'.length = 1 → Q ⟨s.upd bz oz (dotF M a b N) ++ [tb'], p⟩) :
    Wp md I τ (dotLoop n x y z t) ρ Q ⟨s ++ [tb], p⟩ := by
  have hbz : bz < s.length := Store.lt_length_of_lt_len hzl
  refine wp_seq (wp_call_const (hI (.lit 0)) (z := (bz, oz)) rfl rfl (by simp [hz0]) trivial
    ?_ ?_)
  · change oz < (s ++ [tb]).len bz
    rwa [Store.len_append_of_lt hbz]
  have e0 : Mem.upd ⟨s ++ [tb], p⟩ (bz, oz) (M.lit 0) =
      ⟨s.upd bz oz (dotF M a b 0) ++ [tb], p⟩ := by
    simp only [Mem.upd, Store.upd_append_of_lt hbz]
    rfl
  rw [e0]
  refine wp_loop hn
    (fun i m => ∃ tb' : Buf K, tb'.length = 1 ∧ m = ⟨s.upd bz oz (dotF M a b i) ++ [tb'], p⟩)
    ⟨tb, htb, rfl⟩ ?_ (fun m ⟨tb', h1, h2⟩ => h2 ▸ hQ tb' h1)
  rintro i hi m ⟨tb', htb', rfl⟩
  have hlen : (s.upd bz oz (dotF M a b i)).length = s.length := Store.length_upd _ _ _ _
  have hbx : bx < (s.upd bz oz (dotF M a b i)).length := hlen ▸ Store.lt_length_of_get (ha i hi)
  have hby : by' < (s.upd bz oz (dotF M a b i)).length := hlen ▸ Store.lt_length_of_get (hb i hi)
  refine wp_seq (wp_call_bin (hI .mul) (x := (bx, fx i)) (y := (by', fy i)) (z := (s.length, 0))
    rfl (by simp [hx, hy]) (by simp [ht]) trivial (a := a i) (b := b i) ?_ ?_ rfl ?_ ?_)
  · change (s.upd bz oz (dotF M a b i) ++ [tb']).get bx (fx i) = some (a i)
    rw [Store.get_append_of_lt hbx, Store.get_upd_of_ne (Or.inl hxz), ha i hi]
  · change (s.upd bz oz (dotF M a b i) ++ [tb']).get by' (fy i) = some (b i)
    rw [Store.get_append_of_lt hby, Store.get_upd_of_ne (Or.inl hyz), hb i hi]
  · change 0 < (s.upd bz oz (dotF M a b i) ++ [tb']).len s.length
    rw [Store.len_top hlen.symm, htb']
    exact Nat.one_pos
  have e1 : Mem.upd ⟨s.upd bz oz (dotF M a b i) ++ [tb'], p⟩ (s.length, 0)
      (M.mul (a i) (b i)) =
      ⟨s.upd bz oz (dotF M a b i) ++ [tb'.set 0 (some (M.mul (a i) (b i)))], p⟩ := by
    simp only [Mem.upd]
    rw [Store.upd_top hlen.symm]
  rw [e1]
  refine wp_call_bin (hI .add) (x := (bz, oz)) (y := (s.length, 0)) (z := (bz, oz)) rfl
    (by simp [hz, ht]) (by simp [hz]) trivial (a := dotF M a b i) (b := M.mul (a i) (b i))
    ?_ ?_ rfl ?_ ?_
  · change (s.upd bz oz (dotF M a b i) ++ [_]).get bz oz = some _
    rw [Store.get_append_of_lt (hlen ▸ hbz), Store.get_upd_self hzl]
  · change (s.upd bz oz (dotF M a b i) ++ [_]).get s.length 0 = some _
    rw [Store.get_top hlen.symm]
    simp [htb']
  · change oz < (s.upd bz oz (dotF M a b i) ++ [_]).len bz
    rwa [Store.len_append_of_lt (hlen ▸ hbz), Store.len_upd]
  · refine ⟨tb'.set 0 (some (M.mul (a i) (b i))), by simpa using htb', ?_⟩
    simp only [Mem.upd]
    rw [Store.upd_append_of_lt (hlen ▸ hbz), Store.upd_upd, dotF_succ]

/-! ### The implementation and its exact certificate -/

variable [Inhabited K]

/-- The block function of `dot` at the dimension `[n]`: two blocks of length `n` to one cell. -/
def dotFn (M : Machine K) : BlockFn K where
  inLens d := match d with
    | [n] => [n, n]
    | _ => []
  fn d _ xs := match d, xs with
    | [n], [xs, ys] => some [dotF M (fun k => xs.getD k default) (fun k => ys.getD k default) n]
    | _, _ => none

/-- What a successful call of the block function of `dot` is. -/
theorem dotFn_apply {M : Machine K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K}
    {m m' : Mem K} (h : (dotFn M).apply d ins z τ m = some m') :
    ∃ n x y xs ys, d = [n] ∧ ins = [x, y] ∧ m.store.readBlock x.1 x.2 n = some xs ∧
      m.store.readBlock y.1 y.2 n = some ys ∧ z.2 < m.store.len z.1 ∧
      m' = m.upd z (dotF M (fun k => xs.getD k default) (fun k => ys.getD k default) n) := by
  obtain ⟨hlive, X, v, hread, hfn, hlen, rfl⟩ := BlockFn.apply_eq_some_iff.mp h
  rcases d with _ | ⟨n, _ | ⟨n', d⟩⟩
  · simp [dotFn] at hfn
  · obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
    simp only [dotFn, Option.some.injEq] at hfn
    subst hfn
    exact ⟨n, x, y, xs, ys, rfl, rfl, hx, hy, by simpa using hlen, rfl⟩
  · simp [dotFn] at hfn

/-- Operands in other buffers than the output. -/
def DisjointBufs : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop := fun _ ins z => ∀ a ∈ ins, a.1 ≠ z.1

/-- **The implementation of `dot`** over scalar arithmetic: a scratch cell and the accumulation
loop. Index variables: `n`, the offsets of `x`, `y`, `z`, then the loop variable. -/
def dotImpl : Impl ScalarOp Empty where
  nd := 1
  nin := 2
  nout := 1
  body := .alloc (.const 1)
    (dotLoop (.var 0) ⟨0, .var 1 + .var 4⟩ ⟨1, .var 2 + .var 4⟩ ⟨2, .var 3⟩ ⟨3, .const 0⟩)

/-- **The exact certificate of `dotImpl`**: where the block function of `dot` succeeds on
operands in other buffers than the output, the run of the implementation is the block function.
A statement about words, with no error analysis. -/
theorem dot_cert {M : Machine K} {I : Interp ScalarOp Empty K} (hI : IsArith M I) {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} (hadm : DisjointBufs d ins z)
    (h : (dotFn M).apply d ins z τ m = some m') :
    dotImpl.Fits d.length ins.length 1 ∧
      run I τ dotImpl.body (Env.frame d (ins ++ [z])) m = some m' := by
  obtain ⟨n, x, y, xs, ys, rfl, rfl, hx, hy, hz, rfl⟩ := dotFn_apply h
  refine ⟨⟨rfl, rfl, rfl⟩, run_of_wp (wp_alloc rfl ?_)⟩
  exact wp_dotLoop hI (s := m.store) (tb := List.replicate 1 none) (fx := fun k => x.2 + k)
    (fy := fun k => y.2 + k) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rfl (hadm x (by simp)) (hadm y (by simp)) hz
    (fun k hk => Store.get_of_readBlock hx hk default)
    (fun k hk => Store.get_of_readBlock hy hk default) (fun tb' _ => by simp [Mem.upd])

end NLAlib.Ops.Examples
