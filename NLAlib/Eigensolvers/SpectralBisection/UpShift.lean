/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Stored upward reconstruction of a one-child node

The child basis is copied and its eigenvalues receive the actual stored signed shift. This
is the one-child assembly of the pure bisection recursion, using explicit scalar additions.

## Main results

* `NLAlib.SpectralBisection.writes_upShiftResult`: both actual reconstructed output blocks.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The actual child basis and pointwise shifted eigenvalues are returned together. Spatial
separation allows input and output regions to share an arena buffer. -/
theorem writes_upShiftResult {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K}
    {m : Mem K} {k : ℕ} {uc ec sigma u e : ℕ × ℕ}
    (U : Matrix (Fin k) (Fin k) (K × K)) (values : List K) (s : K)
    (hl : m.Live [uc, ec, sigma, u, e])
    (hU : m.store.readBlock uc.1 uc.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix U))
    (hE : m.store.readBlock ec.1 ec.2 k = some values)
    (hs : m.store.get sigma.1 sigma.2 = some s)
    (hu : u.2 + 2 * (k * k) ≤ m.store.len u.1) (he : e.2 + k ≤ m.store.len e.1)
    (hap : Fp.Apart [u, e, uc, ec, sigma] [2 * (k * k), k, 2 * (k * k), k, 1]) :
    Writes .total I τ (upShiftResultImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [k] [uc, ec, sigma, u, e])
      (Fp.blocks [u, e] [2 * (k * k), k])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [u, e] [2 * (k * k), k] =
        some [(EntryCodec.pair K).packFinMatrix U, values.map fun v => M.add v s]) m := by
  have hd (i j : Fin 5) (hne : i ≠ j) := hap.disj_getD (i := i) (j := j)
    (by simp) (by simp) (Fin.val_ne_of_ne hne)
  have hUE : Fp.Disj (Store.inBlock u.1 u.2 (2 * (k * k)))
      (Fp.blocks [e] [k]) := by simpa using hd 0 1 (by simp)
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  refine (writes_frame rfl rfl (by room) (PairMatrix.writes_copy hS (by room)
    (Or.inl (by simpa using hd 2 0 (by simp))) hU hu)).seq_readBlock hUE ?_
  intro m₁ hfr _ _
  have hE₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by
    simpa using hd 0 3 (by simp)) hE
  have hs₁ := hfr.keep (Store.readsOnly_get _ _ _) (by
    simpa using hd 0 4 (by simp)) hs
  exact (writes_frame rfl rfl (by room)
    (writes_scalarBroadcast_readBlock (hS .add) hE₁ hs₁ (by rw [hfr.len_eq]; exact he)
      (Or.inl (by simpa using hd 3 1 (by simp)))
      (by simpa using hd 4 1 (by simp)))).readBlocks_singleton

end NLAlib.SpectralBisection
