/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Alg
public import NLAlib.Matrix.Factorizations.MGS.Math
public import NLAlib.Ops.Logic.RCLikeBlas
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.Tactic

/-!
# One exact modified Gram–Schmidt reduction

Local functional contracts compute the coefficient and update the current residual.
The two vector inputs may alias; the coefficient cell is disjoint from both vectors.

## Main results

* `NLAlib.MGS.writes_reduce` executes one exact Hermitian projection subtraction.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- A reduction writes the projection subtraction and its negated coefficient, preserving
all other cells. Input/output vector overlap is allowed by the local block contracts. -/
theorem writes_reduce (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n : ℕ} {q v r : ℕ × ℕ} (qs vs : List 𝕜)
    (hl : m.Live [q, v, r])
    (hq : m.store.readBlock q.1 q.2 n = some qs)
    (hv : m.store.readBlock v.1 v.2 n = some vs)
    (hrq : Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock q.1 q.2 n))
    (hrv : Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock v.1 v.2 n))
    (hqv : Fp.Disj (Store.inBlock q.1 q.2 n) (Store.inBlock v.1 v.2 n) ∨ q = v)
    (hroom : r.2 + 1 ≤ m.store.len r.1) (hvroom : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ reduce.body (Env.frame [n] [q, v, r])
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn fun i : Fin n =>
          vs.getD i 0 - RCLikeBlas.dot n qs vs * qs.getD i 0)) m := by
  unfold reduce
  dsimp only
  refine Writes.seq_le (RCLikeBlas.writes_dot hB rfl rfl rfl hl hq hv hrq hrv hroom)
    le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hr₁⟩
  have hq₁ := hfr₁.keep (Store.readsOnly_readBlock q.1 q.2 n qs) hrq hq
  have hv₁ := hfr₁.keep (Store.readsOnly_readBlock v.1 v.2 n vs) hrv hv
  have hl₁ : m₁.Live [q, v, r] := by
    simpa only [Mem.Live, hfr₁.length_eq] using hl
  refine Writes.seq_le (writes_call_fn1 (hS .neg) (xs := [[RCLikeBlas.dot n qs vs]])
    rfl rfl rfl rfl rfl trivial
    (by simp only [Mem.live_append, Mem.live_cons, Mem.live_nil];
        exact ⟨⟨hl₁ r (by simp), trivial⟩, hl₁ r (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hr₁]) rfl rfl
    (by simpa only [hfr₁.len_eq] using hroom))
    le_sup_left ?_
  intro m₂ hfr₂ ⟨hp₂, hr₂⟩
  have hq₂ := hfr₂.keep (Store.readsOnly_readBlock q.1 q.2 n qs) hrq hq₁
  have hv₂ := hfr₂.keep (Store.readsOnly_readBlock v.1 v.2 n vs) hrv hv₁
  have hl₂ : m₂.Live [q, v, r] := by
    simpa only [Mem.Live, hfr₂.length_eq] using hl₁
  refine (RCLikeBlas.writes_axpy hB rfl rfl rfl
    (by simp only [Mem.live_cons, Mem.live_nil];
        exact ⟨hl₂ r (by simp), hl₂ q (by simp), hl₂ v (by simp),
          hl₂ v (by simp), trivial⟩) hr₂ hq₂ hv₂ hrv hqv (Or.inr rfl)
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using hvroom)).mono le_sup_right ?_
  intro m₃ _ ⟨hp₃, hv₃⟩
  refine ⟨hp₃.trans (hp₂.trans hp₁), ?_⟩
  simpa [RCLikeBlas.machine, sub_eq_add_neg, neg_mul] using hv₃

end NLAlib.MGS
