/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Combine

/-!
# Accumulating the Hutch++ trace estimate

Two instances of the shared column-product contraction compute the low-rank trace and
residual sum. Actual dimension-literal arithmetic then combines the stored scalars.

## Main results

* `NLAlib.HutchPlusPlus.writes_accumulate` returns the exact two trace sums.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op] [Has IndexOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- The explicit accumulation returns the low-rank sum plus the mean residual sum.
Input blocks are read from actual columns and retained through disjoint scalar writes. -/
theorem writes_accumulate (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I)
    {n k ell : ℕ} {b c t out : ℕ × ℕ} (xs ys : ℕ → List 𝕜)
    (hl : m.Live [b, c, t, out])
    (hX : ∀ j < k + ell, m.store.readBlock b.1 (b.2 + n * j) n = some (xs j))
    (hY : ∀ j < k + ell, m.store.readBlock c.1 (c.2 + n * j) n = some (ys j))
    (hDX : ∀ j < k + ell, Fp.Disj (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock b.1 (b.2 + n * j) n))
    (hDY : ∀ j < k + ell, Fp.Disj (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock c.1 (c.2 + n * j) n))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 2 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ accumulate.body (Env.frame [n, k, ell] [b, c, t, out])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 = some
        [(∑ j ∈ Finset.range k, RCLikeBlas.dot n (xs j) (ys j)) +
          (∑ j ∈ Finset.range ell, RCLikeBlas.dot n (xs (k + j)) (ys (k + j))) / (ell : 𝕜)])
      m := by
  have ht₀ : Store.inBlock t.1 t.2 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have ht₁ : Store.inBlock t.1 (t.2 + 1) 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hF₀ : Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1 ≤
      Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1 := sup_le_sup ht₀ le_rfl
  have hF₁ : Store.inBlock t.1 t.2 1 ⊔ Store.inBlock t.1 (t.2 + 1) 1 ≤
      Store.inBlock t.1 t.2 2 := sup_le ht₀ ht₁
  unfold accumulate
  dsimp only
  refine Writes.seq_le ((ColumnProducts.writes_sum hS hB xs ys hl
    (fun j hj => hX j (by omega)) (fun j hj => hY j (by omega))
    (fun j hj => (hDX j (by omega)).mono hF₀ le_rfl)
    (fun j hj => (hDY j (by omega)).mono hF₀ le_rfl)
    (hTO.mono ht₀ le_rfl) (by omega) ho).in_frame rfl rfl hl) hF₀ ?_
  intro m₁ hfr₁ ⟨hp₁, hlo⟩
  have hX₁ : ∀ j < k + ell, m₁.store.readBlock b.1 (b.2 + n * j) n = some (xs j) := by
    intro j hj
    exact hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) ((hDX j hj).mono hF₀ le_rfl) (hX j hj)
  have hY₁ : ∀ j < k + ell, m₁.store.readBlock c.1 (c.2 + n * j) n = some (ys j) := by
    intro j hj
    exact hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) ((hDY j hj).mono hF₀ le_rfl) (hY j hj)
  have hl₁ : m₁.Live [(b.1, b.2 + n * k), (c.1, c.2 + n * k), t, (t.1, t.2 + 1)] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨(hl.congr hfr₁.length_eq) b (by simp), (hl.congr hfr₁.length_eq) c (by simp),
      (hl.congr hfr₁.length_eq) t (by simp), (hl.congr hfr₁.length_eq) t (by simp), trivial⟩
  refine Writes.seq_le ((ColumnProducts.writes_sum hS hB (fun j => xs (k + j))
    (fun j => ys (k + j)) hl₁
    (fun j hj => by simpa [Nat.mul_add, Nat.add_assoc] using hX₁ (k + j) (by omega))
    (fun j hj => by simpa [Nat.mul_add, Nat.add_assoc] using hY₁ (k + j) (by omega))
    (fun j hj => by simpa [Nat.mul_add, Nat.add_assoc] using
      (hDX (k + j) (by omega)).mono (hF₁.trans le_sup_left) le_rfl)
    (fun j hj => by simpa [Nat.mul_add, Nat.add_assoc] using
      (hDY (k + j) (by omega)).mono (hF₁.trans le_sup_left) le_rfl)
    (Fp.disj_inBlock_of_le (by omega))
    (by rw [hfr₁.len_eq]; omega)
    (by change t.2 + 1 + 1 ≤ m₁.store.len t.1; rw [hfr₁.len_eq]; omega)).in_frame
      rfl rfl hl₁) (hF₁.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hhi⟩
  have hlo₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
    (hTO.mono hF₁ le_rfl) hlo
  have hl₂ : m₂.Live [t, out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨(hl.congr (hfr₂.length_eq.trans hfr₁.length_eq)) t (by simp),
      (hl.congr (hfr₂.length_eq.trans hfr₁.length_eq)) out (by simp), trivial⟩
  refine ((writes_combineTrace hS hLit _ _ hl₂ hlo₂ hhi hTO
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using ht)
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using ho)).in_frame
      rfl rfl hl₂).mono le_rfl ?_
  intro m₃ _ ⟨hp₃, hv⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hv⟩

end NLAlib.HutchPlusPlus
