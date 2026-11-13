/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Alg
public import NLAlib.Matrix.Factorizations.MGS.Sweep
public import NLAlib.Ops.Logic.IndependentLoop
public import NLAlib.Ops.Logic.EntryColumn

/-!
# In-place probe reduction against a retained basis

The independent-column loop retains each future original probe and each completed
reduced probe while reusing its scalar coefficient cell. No rank assumption is needed.

## Main results

* `NLAlib.HutchPlusPlus.writes_projectProbes` computes the sweep of every actual probe.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- A batch of probes is reduced in place against the retained prefix. The exact footprint
contains only the probe tail and scalar workspace, so the basis remains readable. -/
theorem writes_projectProbes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n k ell : ℕ} {b t : ℕ × ℕ}
    (Q G : ℕ → Fin n → 𝕜) (hl : m.Live [b, t])
    (hQ : ∀ i < k, m.store.readBlock b.1 (b.2 + n * i) n = some (List.ofFn (Q i)))
    (hG : ∀ j < ell, m.store.readBlock b.1 (b.2 + n * (k + j)) n =
      some (List.ofFn (G j)))
    (hTB : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock b.1 b.2 ((k + ell) * n)))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hb : b.2 + (k + ell) * n ≤ m.store.len b.1) :
    Writes .total I τ projectProbes.body (Env.frame [n, k, ell] [b, t])
      (Store.inBlock b.1 (b.2 + n * k) (ell * n) ⊔ Store.inBlock t.1 t.2 2)
      (fun m' => m'.pos = m.pos ∧ ∀ j < ell,
        m'.store.readBlock b.1 (b.2 + n * (k + j)) n =
          some (List.ofFn (mgsSweep Q (G j) k))) m := by
  let col : ℕ → Fp := fun j => Store.inBlock b.1 (b.2 + n * j) n
  let region : ℕ → Fp := fun j => col (k + j)
  have hcol : ∀ j < k + ell, col j ≤ Store.inBlock b.1 b.2 ((k + ell) * n) := by
    intro j hj
    have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ, Nat.mul_comm n (k + ell)] at hm
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  have hcd : ∀ i j, i ≠ j → Fp.Disj (col i) (col j) := by
    intro i j hij
    simpa [col, EntryCodec.scalar, Nat.mul_comm] using
      (EntryCodec.scalar 𝕜).disj_columns (L := ⟨b.1, b.2, n, k + ell, n⟩) le_rfl hij
  have hprotect : ∀ j < ell, Fp.Disj (Store.inBlock t.1 t.2 2) (region j) := by
    intro j hj
    exact hTB.mono le_rfl (hcol (k + j) (by omega))
  unfold projectProbes
  dsimp only
  refine writes_loop_disjoint_prefix_scratch region
    (fun j s => s.readBlock b.1 (b.2 + n * (k + j)) n =
      some (List.ofFn (mgsSweep Q (G j) k))) rfl ?_ le_sup_right
    (fun i hi j hj hij => hcd _ _ (by omega)) hprotect
    (fun j _ => Store.readsOnly_readBlock _ _ _ _) ?_
  · intro j hj
    apply le_trans _ le_sup_left
    have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ, Nat.mul_comm n ell] at hm
    apply Fp.inBlock_le_inBlock <;> rw [Nat.mul_add] <;> omega
  · intro j hj m' hfr
    have hQ' : ∀ i < k, m'.store.readBlock b.1 (b.2 + n * i) n = some (List.ofFn (Q i)) := by
      intro i hi
      exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr
        ⟨fun _ _ ⟨a, ha, hx⟩ hy => hcd (k + a) i (by omega) _ _ hx hy,
          hTB.mono le_rfl (hcol i (by omega))⟩) (hQ i hi)
    have hG' := hfr.keep (Store.readsOnly_readBlock _ _ _ (List.ofFn (G j)))
      (Fp.disj_sup_left.mpr ⟨fun _ _ ⟨a, ha, hx⟩ hy =>
        hcd (k + a) (k + j) (by omega) _ _ hx hy, hprotect j hj⟩) (hG j hj)
    have hl' : m'.Live [b, (b.1, b.2 + n * (k + j)), t] := by
      simp only [Mem.live_cons, Mem.live_nil]
      exact ⟨(hl.congr hfr.length_eq) b (by simp), (hl.congr hfr.length_eq) b (by simp),
        (hl.congr hfr.length_eq) t (by simp), trivial⟩
    have ht₀ : Store.inBlock t.1 t.2 1 ≤ Store.inBlock t.1 t.2 2 :=
      Fp.inBlock_le_inBlock le_rfl (by omega)
    refine ((MGS.writes_sweep hS hB Q (G j) hl' hQ' hG' ?_
      ((hprotect j hj).mono ht₀ le_rfl) (by rw [hfr.len_eq]; omega)
      (by have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt (show k + j < k + ell by omega))
          rw [Nat.mul_succ, Nat.mul_comm n (k + ell)] at hm
          change b.2 + n * (k + j) + n ≤ m'.store.len b.1
          rw [hfr.len_eq]; omega)).in_frame rfl rfl hl').mono
        (sup_le (ht₀.trans le_sup_right) le_sup_left) (fun _ _ h => h)
    intro i hi
    exact Fp.disj_sup_left.mpr ⟨hTB.mono ht₀ (hcol i (by omega)), hcd _ _ (by omega)⟩

end NLAlib.HutchPlusPlus
