/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Eigensolvers.SpectralBisection.Result
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Ops.Blas.MapCorrect

/-!
# Copy the reconstructed root result

The two final copies expose the actual packed matrix and eigenvalue vector. Both copies are
ordinary scalar operations; their mathematical output requires no numerical assumptions.

## Main results

* `NLAlib.SpectralBisection.writes_rootResultCopy`: total copying of the stored root pair.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The final copies write both supplied result blocks and consume no random words. -/
theorem writes_rootResultCopy {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {μ : Mem K} {n : ℕ} {ua ea u dv : ℕ × ℕ}
    (result : Matrix (Fin n) (Fin n) (K × K) × (Fin n → K))
    (hl : μ.Live [ua, ea, u, dv])
    (hAP : Fp.Apart [ua, ea, u, dv] [2 * (n * n), n, 2 * (n * n), n])
    (hread : StoresResult n 0 0 ua ea result μ.store)
    (hroom : μ.Room [u, dv] [2 * (n * n), n]) :
    Writes .total I τ (rootResultCopy (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [ua, ea, u, dv]) (Fp.blocks [u, dv] [2 * (n * n), n])
      (fun μ' => μ'.pos = μ.pos ∧ μ'.readBlocks [u, dv] [2 * (n * n), n] =
        some [(EntryCodec.pair K).packFinMatrix result.1, List.ofFn result.2]) μ := by
  have hu := hl ua (by simp)
  have he := hl ea (by simp)
  have ho := hl u (by simp)
  have hd := hl dv (by simp)
  have hU : μ.store.readBlock ua.1 ua.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix result.1) := by simpa using hread.matrix_read
  have hE : μ.store.readBlock ea.1 ea.2 n = some (List.ofFn result.2) := by
    simpa using hread.values_read
  have hUU : Fp.Disj (Store.inBlock ua.1 ua.2 (2 * (n * n)))
      (Store.inBlock u.1 u.2 (2 * (n * n))) := by
    simpa using hAP.disj_getD (i := 0) (j := 2) (by simp) (by simp) (by simp)
  have hUE : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n)))
      (Store.inBlock ea.1 ea.2 n) := by
    simpa using hAP.disj_getD (i := 2) (j := 1) (by simp) (by simp) (by simp)
  have hUD : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n)))
      (Fp.blocks [dv] [n]) := hAP.2.2.1
  have hED : Fp.Disj (Store.inBlock ea.1 ea.2 n) (Store.inBlock dv.1 dv.2 n) := by
    simpa using hAP.disj_getD (i := 1) (j := 3) (by simp) (by simp) (by simp)
  have hc := PairMatrix.writes_copy (md := .total) (rows := n) (cols := n) (τ := τ)
    hS (by room) (Or.inl hUU) hU hroom.1
  refine (hc.in_frame rfl rfl (by room)).seq_readBlock hUD ?_
  intro μ₁ hfr₁ _ _
  have hE₁ := hfr₁.keep (Store.readsOnly_readBlock ea.1 ea.2 n _) hUE hE
  have hv := writes_unaryMap_of_disj_or_eq (md := .total) (f := id) (τ := τ) (hS .copy)
    (Or.inl hED) hE₁ (by rw [hfr₁.len_eq]; exact hroom.2.1)
  simp only [List.map_id] at hv
  exact (hv.in_frame rfl rfl (by room)).readBlocks_singleton

end NLAlib.SpectralBisection
