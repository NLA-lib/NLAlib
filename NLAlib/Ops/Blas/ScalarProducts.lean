/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.RCLikeBlas
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Tactic

/-!
# Streamed scalar products with explicit strides

Each product is computed in a single caller-owned temporary and added to the output
accumulator. Explicit strides permit both contiguous dot products and rows of a matrix
stored by columns. Only scalar multiplication, addition and literal zero are used.

## Main results

* `NLAlib.Ops.ScalarProducts.step` adds one product to an accumulator.
* `NLAlib.Ops.ScalarProducts.sum` sums products with explicit word strides.
* `NLAlib.Ops.ScalarProducts.writes_sum_word` returns the actual machine accumulation.
* `NLAlib.Ops.ScalarProducts.writes_sum` specializes it to the exact stored sum.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarProducts

variable {Op Tst : Type} [Has ScalarOp Op]

/-- One scalar multiplication followed by one accumulation. -/
def step : Impl Op Tst := opsImpl% [] (X, Y, t, out) → () {
  call (Has.inj ScalarOp.mul) [] (X, Y) → (t);
  call (Has.inj ScalarOp.add) [] (out, t) → (out)
}

/-- Stream products from two strided word views, using one caller-owned temporary. -/
def sum : Impl Op Tst := opsImpl% [n, sx, sy] (X, Y, t, out) → () {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for j < n { run step.body [] (X[sx * j], Y[sy * j], t, out) }
}

/-- The actual streamed accumulator: literal zero followed by one multiplication and one
addition per input pair, including the first pair. -/
def sumWord {K : Type} (M : Machine K) (xs ys : ℕ → K) : ℕ → K
  | 0 => M.lit 0
  | n + 1 => M.add (sumWord M xs ys n) (M.mul (xs n) (ys n))

variable {K : Type} {M : Machine K}
  {I : Interp Op Tst K} {tape : Tape K} {m : Mem K}

/-- A streamed scalar step performs multiplication and addition, preserving the input
accumulator through the disjoint temporary cell. -/
theorem writes_step_word (hS : IsScalar M I)
    {x y t out : ℕ × ℕ} (a b acc : K) (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 1 = some [a])
    (hY : m.store.readBlock y.1 y.2 1 = some [b])
    (hA : m.store.readBlock out.1 out.2 1 = some [acc])
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape step.body (Env.frame [] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [M.add acc (M.mul a b)]) m := by
  unfold step
  dsimp only
  refine Writes.seq_le (writes_call_fn1 (hS .mul) (xs := [[a], [b]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl x (by simp), hl y (by simp), trivial⟩, hl t (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hX, hY]) rfl rfl ht) le_sup_left ?_
  intro m₁ hf ⟨hp, hProd⟩
  change m₁.store.readBlock t.1 t.2 1 = some [M.mul a b] at hProd
  have hA₁ := hf.keep (Store.readsOnly_readBlock _ _ _ [acc]) hTO hA
  have hl₁ := hl.congr hf.length_eq
  refine (writes_call_fn1 (hS .add) (xs := [[acc], [M.mul a b]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl₁ out (by simp), hl₁ t (by simp), trivial⟩, hl₁ out (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hA₁, hProd]) rfl rfl
    (by simpa only [hf.len_eq] using ho)).mono le_sup_right ?_
  exact fun _ _ h => ⟨h.1.trans hp, h.2⟩

/-- The streamed loop returns the actual machine sum, using only the declared accumulator and
temporary. Inputs can share a buffer or repeat words; their accessed cells stay outside
the two-cell write footprint. Empty products return literal zero. -/
theorem writes_sum_word (hS : IsScalar M I)
    {n sx sy : ℕ} {x y t out : ℕ × ℕ} (xs ys : ℕ → K)
    (hl : m.Live [x, y, t, out])
    (hX : ∀ j < n, m.store.readBlock x.1 (x.2 + sx * j) 1 = some [xs j])
    (hY : ∀ j < n, m.store.readBlock y.1 (y.2 + sy * j) 1 = some [ys j])
    (hDX : ∀ j < n, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock x.1 (x.2 + sx * j) 1))
    (hDY : ∀ j < n, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock y.1 (y.2 + sy * j) 1))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape sum.body (Env.frame [n, sx, sy] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [sumWord M xs ys n]) m := by
  unfold sum
  dsimp only
  refine Writes.seq_le (writes_call_fn1 (hS (.lit 0)) (xs := [])
    rfl rfl rfl rfl rfl trivial (by simpa [Mem.Live] using hl out (by simp))
    rfl rfl rfl ho) le_sup_right ?_
  intro m₁ hf₁ ⟨hp₁, hzero⟩
  refine writes_loop rfl (fun _ => Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
    (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
      some [sumWord M xs ys i])
    ⟨hp₁, by simpa only [sumWord] using hzero⟩ ?_
  intro i hi m' hf ⟨hp, hAcc⟩
  have hWhole := (hf₁.mono (show Store.inBlock out.1 out.2 1 ≤
    Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1 from le_sup_right)).trans hf
  have hX' := hWhole.keep (Store.readsOnly_readBlock _ _ _ [xs i]) (hDX i hi) (hX i hi)
  have hY' := hWhole.keep (Store.readsOnly_readBlock _ _ _ [ys i]) (hDY i hi) (hY i hi)
  have hl' : m'.Live [(x.1, x.2 + sx * i), (y.1, y.2 + sy * i), t, out] := by
    simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hWhole.length_eq
  refine ((writes_step_word hS (xs i) (ys i) (sumWord M xs ys i)
    hl' hX' hY' hAcc hTO (by simpa only [hWhole.len_eq] using ht)
    (by simpa only [hWhole.len_eq] using ho)).in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' _ h
  exact ⟨h.1.trans hp, by simpa only [sumWord] using h.2⟩

section Exact

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp Op Tst 𝕜} {tape : Tape 𝕜} {m : Mem 𝕜}

/-- Exact scalar arithmetic turns the same word recurrence into the usual finite sum. -/
theorem sumWord_exact (xs ys : ℕ → 𝕜) (n : ℕ) :
    sumWord RCLikeBlas.machine xs ys n = ∑ j ∈ Finset.range n, xs j * ys j := by
  induction n with
  | zero => simp [sumWord, RCLikeBlas.machine]
  | succ n ih =>
    rw [sumWord, Finset.sum_range_succ]
    change sumWord RCLikeBlas.machine xs ys n + xs n * ys n = _
    rw [ih]

/-- A streamed scalar step adds the exact product, preserving the input accumulator
through the disjoint temporary cell. -/
theorem writes_step (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {x y t out : ℕ × ℕ} (a b acc : 𝕜) (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 1 = some [a])
    (hY : m.store.readBlock y.1 y.2 1 = some [b])
    (hA : m.store.readBlock out.1 out.2 1 = some [acc])
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape step.body (Env.frame [] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 = some [acc + a * b]) m := by
  simpa only [RCLikeBlas.machine] using
    writes_step_word hS a b acc hl hX hY hA hTO ht ho

/-- The streamed loop returns the exact sum, using only the declared accumulator and
temporary. Inputs can share a buffer or repeat words; their accessed cells stay outside
the two-cell write footprint. Empty products return literal zero. -/
theorem writes_sum (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n sx sy : ℕ} {x y t out : ℕ × ℕ} (xs ys : ℕ → 𝕜)
    (hl : m.Live [x, y, t, out])
    (hX : ∀ j < n, m.store.readBlock x.1 (x.2 + sx * j) 1 = some [xs j])
    (hY : ∀ j < n, m.store.readBlock y.1 (y.2 + sy * j) 1 = some [ys j])
    (hDX : ∀ j < n, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock x.1 (x.2 + sx * j) 1))
    (hDY : ∀ j < n, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock y.1 (y.2 + sy * j) 1))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape sum.body (Env.frame [n, sx, sy] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [∑ j ∈ Finset.range n, xs j * ys j]) m := by
  simpa only [sumWord_exact] using
    writes_sum_word hS xs ys hl hX hY hDX hDY hTO ht ho

end Exact

end NLAlib.Ops.ScalarProducts
