/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Reduce
public import NLAlib.Ops.Logic.Loop

/-!
# Total execution of a modified Gram–Schmidt sweep

The loop follows the existing mathematical recurrence. Its read-only columns may be
subviews of the same buffer as the residual, provided their actual spans are disjoint.

## Main results

* `NLAlib.MGS.writes_sweep` computes the full `mgsSweep` recurrence.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- The sweep is total on readable columns and a writable residual. Its mathematical
recurrence has no orthogonality or rank assumption. -/
theorem writes_sweep (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n k : ℕ} {q v r : ℕ × ℕ}
    (Q : ℕ → Fin n → 𝕜) (w : Fin n → 𝕜) (hl : m.Live [q, v, r])
    (hQ : ∀ i < k, m.store.readBlock q.1 (q.2 + n * i) n = some (List.ofFn (Q i)))
    (hv : m.store.readBlock v.1 v.2 n = some (List.ofFn w))
    (hdis : ∀ i < k, Fp.Disj
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (Store.inBlock q.1 (q.2 + n * i) n))
    (hrv : Fp.Disj (Store.inBlock r.1 r.2 1) (Store.inBlock v.1 v.2 n))
    (hr : r.2 + 1 ≤ m.store.len r.1) (hz : v.2 + n ≤ m.store.len v.1) :
    Writes .total I τ sweep.body (Env.frame [n, k] [q, v, r])
      (Store.inBlock r.1 r.2 1 ⊔ Store.inBlock v.1 v.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
        some (List.ofFn (mgsSweep Q w k))) m := by
  unfold sweep
  dsimp only
  refine writes_loop rfl (fun _ => Store.inBlock r.1 r.2 1 ⊔
    Store.inBlock v.1 v.2 n) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock v.1 v.2 n =
      some (List.ofFn (mgsSweep Q w i))) ⟨rfl, hv⟩ ?_
  intro i hi m' hfr ⟨hp, hvec⟩
  have hcol := hfr.keep (Store.readsOnly_readBlock q.1 (q.2 + n * i) n
    (List.ofFn (Q i))) (hdis i hi) (hQ i hi)
  have hl' : m'.Live [(q.1, q.2 + n * i), v, r] := by
    simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hfr.length_eq
  refine writes_frame rfl rfl hl' ?_
  refine (writes_reduce hS hB (List.ofFn (Q i)) (List.ofFn (mgsSweep Q w i))
    hl' hcol hvec ((hdis i hi).mono le_sup_left le_rfl) hrv
    (Or.inl (((hdis i hi).mono le_sup_right le_rfl).symm))
    (by simpa only [hfr.len_eq] using hr)
    (by simpa only [hfr.len_eq] using hz)).mono le_rfl ?_
  intro m'' _ ⟨hp', hv'⟩
  refine ⟨hp'.trans hp, ?_⟩
  change m''.store.readBlock v.1 v.2 n = some (List.ofFn fun a : Fin n =>
    mgsSweep Q w i a - (star (Q i) ⬝ᵥ mgsSweep Q w i) * Q i a)
  simpa [RCLikeBlas.dot_ofFn, List.getD_eq_getElem?_getD, dotProduct] using hv'

end NLAlib.MGS
