/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.RCLikeBlas
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Logic.Loop

/-!
# Sums of corresponding Hermitian column products

The implementation uses local dot products and visible scalar additions. The temporary
coefficient is caller-owned and disjoint from the accumulator. This contraction is useful
for compressed traces and residual estimators over real or complex words.

## Main definitions

* `NLAlib.Ops.ColumnProducts.sum` adds the inner products of corresponding columns.
-/

@[expose] public section

namespace NLAlib.Ops.ColumnProducts

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- Add one Hermitian product to an existing scalar accumulator, using one temporary cell. -/
def step : Impl Op Tst := opsImpl% [n] (X, Y, t, out) → () {
  call (Has.inj Blas1Op.dot) [n] (X, Y) → (t);
  call (Has.inj ScalarOp.add) [] (out, t) → (out)
}

/-- Sum corresponding column inner products, reading column-major matrices.
The accumulator is initialized to zero, including an empty collection of columns. -/
def sum : Impl Op Tst := opsImpl% [n, k] (X, Y, t) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for j < k {
    run step.body [n] (X[n * j], Y[n * j], t, out)
  }
}

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- A local contraction step writes the old accumulator plus the exact Hermitian product.
The input vectors may overlap; the temporary cell must preserve the accumulator. -/
theorem writes_step (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n : ℕ} {x y t out : ℕ × ℕ} (xs ys : List 𝕜) (a : 𝕜)
    (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hA : m.store.readBlock out.1 out.2 1 = some [a])
    (hTX : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock x.1 x.2 n))
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 n))
    (hdis : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ step.body (Env.frame [n] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [a + RCLikeBlas.dot n xs ys]) m := by
  unfold step
  dsimp only
  refine Writes.seq_le (RCLikeBlas.writes_dot hB rfl rfl rfl
    (by simp only [Mem.live_cons, Mem.live_nil];
        exact ⟨hl x (by simp), hl y (by simp), hl t (by simp), trivial⟩)
    hX hY hTX hTY ht) le_sup_left ?_
  intro m₁ hfr ⟨hp, hd⟩
  have hA₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ [a]) hdis hA
  have hl₁ := hl.congr hfr.length_eq
  refine (writes_call_fn1 (hS .add) (xs := [[a], [RCLikeBlas.dot n xs ys]])
    rfl rfl rfl rfl rfl trivial
    (by simp only [Mem.live_append, Mem.live_cons, Mem.live_nil];
        exact ⟨⟨hl₁ out (by simp), hl₁ t (by simp), trivial⟩, hl₁ out (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hA₁, hd]) rfl rfl
    (by simpa only [hfr.len_eq] using ho)).mono le_sup_right ?_
  intro m₂ _ ⟨hp₂, ha⟩
  exact ⟨hp₂.trans hp, ha⟩

/-- Sum the actual column inner products with one caller-owned temporary cell.
Readable inputs are retained through the two-cell output footprint, including shared buffers. -/
theorem writes_sum (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n k : ℕ} {x y t out : ℕ × ℕ}
    (xs ys : ℕ → List 𝕜) (hl : m.Live [x, y, t, out])
    (hX : ∀ j < k, m.store.readBlock x.1 (x.2 + n * j) n = some (xs j))
    (hY : ∀ j < k, m.store.readBlock y.1 (y.2 + n * j) n = some (ys j))
    (hDX : ∀ j < k, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock x.1 (x.2 + n * j) n))
    (hDY : ∀ j < k, Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock y.1 (y.2 + n * j) n))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ sum.body (Env.frame [n, k] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [∑ j ∈ Finset.range k, RCLikeBlas.dot n (xs j) (ys j)]) m := by
  unfold sum
  dsimp only
  refine Writes.seq_le (writes_call_const (hS (.lit 0)) rfl trivial
    (by change out.2 < m.store.len out.1; omega)) le_sup_right ?_
  intro m₁ hfr₁ ⟨hp₁, hzero⟩
  have hzero' : m₁.store.get out.1 out.2 = some 0 := by
    simpa [RCLikeBlas.machine] using hzero
  refine writes_loop rfl (fun _ => Store.inBlock t.1 t.2 1 ⊔
    Store.inBlock out.1 out.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
      some [∑ j ∈ Finset.range i, RCLikeBlas.dot n (xs j) (ys j)])
    ⟨hp₁, by simp [Store.readBlock, hzero']⟩ ?_
  intro i hi m' hfr ⟨hp, hacc⟩
  have hOutSub : Store.inBlock out.1 out.2 1 ≤
      Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1 := le_sup_right
  have hWhole := (hfr₁.mono hOutSub).trans hfr
  have hX' := hWhole.keep (Store.readsOnly_readBlock _ _ _ (xs i)) (hDX i hi) (hX i hi)
  have hY' := hWhole.keep (Store.readsOnly_readBlock _ _ _ (ys i)) (hDY i hi) (hY i hi)
  have hl' : m'.Live [(x.1, x.2 + n * i), (y.1, y.2 + n * i), t, out] := by
    simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hWhole.length_eq
  refine ((writes_step hS hB (xs i) (ys i)
    (∑ j ∈ Finset.range i, RCLikeBlas.dot n (xs j) (ys j)) hl' hX' hY' hacc
    ((hDX i hi).mono le_sup_left le_rfl) ((hDY i hi).mono le_sup_left le_rfl) hTO
    (by simpa only [hWhole.len_eq] using ht)
    (by simpa only [hWhole.len_eq] using ho)).in_frame rfl rfl hl').mono le_rfl ?_
  intro m'' _ ⟨hp', hout⟩
  exact ⟨hp'.trans hp, by simpa only [Finset.sum_range_succ] using hout⟩

end NLAlib.Ops.ColumnProducts
