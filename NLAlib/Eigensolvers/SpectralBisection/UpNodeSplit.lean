/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNode
public import NLAlib.Eigensolvers.SpectralBisection.UpPacked

/-!
# Typed upward reconstruction of a split node

The stored mathematical split and represented child outputs determine the actual parent
basis and shifted eigenvalues. The common arena separation invariant supplies all local
operand assumptions, and the finite sum packing bridge returns one mathematical result pair.

## Main results

* `NLAlib.SpectralBisection.writes_upNode_splitResult`: total mathematical split assembly.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A stored split returns its two projected child bases and shifted eigenvalues in the
pure recursion's finite sum order. Actual metadata decoding, child reads, parent capacities
and the common arena separation invariant suffice for total execution. -/
theorem writes_upNode_splitResult {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (mm : MatMulMap (K × K)) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    {τ : Tape K} {m : Mem K} {n d lo k r : ℕ} {R sigma : K} {hr : r ≤ k}
    {ma ua qa ea sz kd kp t : ℕ × ℕ}
    {Qp : Matrix (Fin k) (Fin r) (K × K)} {Qm : Matrix (Fin k) (Fin (k - r)) (K × K)}
    {Ap : Matrix (Fin r) (Fin r) (K × K)}
    {Am : Matrix (Fin (k - r)) (Fin (k - r)) (K × K)}
    (cp : Matrix (Fin r) (Fin r) (K × K) × (Fin r → K))
    (cm : Matrix (Fin (k - r)) (Fin (k - r)) (K × K) × (Fin (k - r) → K))
    (hStep : StoresStep M R n d lo ma ua qa ea sz kd kp (.split r hr Qp Qm Ap Am sigma) m)
    (hChildP : StoresResult n (d + 1) lo ua ea cp m.store)
    (hChildM : StoresResult n (d + 1) (lo + r) ua ea cm m.store)
    (hLit : IsExactNatLit dec M (max n 4)) (hk : k ≤ n)
    (hl : m.Live [ua, qa, ea, kd, kp, t])
    (ht : m.store.get t.1 t.2 = some (M.div R (M.lit 2)))
    (hroom : m.Room (resultOperands n d lo ua ea) (resultLengths k))
    (hap : Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n k)) :
    let index : Fin k ≃ Fin r ⊕ Fin (k - r) :=
      (finCongr (Nat.add_sub_of_le hr).symm).trans finSumFinEquiv.symm
    Writes .total I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t])
      (Fp.blocks (resultOperands n d lo ua ea) (resultLengths k))
      (fun m' => m'.pos = m.pos ∧ StoresResult n d lo ua ea
        ((Matrix.fromCols (mm Qp cp.1) (mm Qm cm.1)).submatrix id index,
          fun i => Sum.elim (fun j => M.add (cp.2 j) sigma)
            (fun j => M.sub (cm.2 j) sigma) (index i)) m'.store) m := by
  have hs : m.store.get t.1 t.2 = some sigma := by rw [hStep.1]; exact ht
  have hreads := readBlocks_upSplit_sources cp cm hStep hChildP hChildM hs
  have hAll := apart_upSplit hk hr (by
    simpa only [upNodeRegions, upNodeRegionLengths, resultOperands, List.cons_append,
      List.nil_append] using hap)
  have hparts := hAll.take_drop rfl 4
  have hdec4 : dec (M.lit 4) = (4 : ℕ) := hLit 4 (by omega)
  have hdecr := hLit r ((hr.trans hk).trans (Nat.le_max_left n 4))
  have hev := eval_upNode_split (τ := τ) hQ hStep.kind_read hdec4
    hStep.split_size_read hdecr hr hl
  have hLive : m.Live [(qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
      (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * r)),
      (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (ua.1, ua.2 + 2 * (n * n) * (d + 1) + 2 * n * (lo + r)),
      (ea.1, ea.2 + n * (d + 1) + lo), (ea.1, ea.2 + n * (d + 1) + lo + r), t,
      (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo), (ea.1, ea.2 + n * d + lo)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.2.1, hl.2.1, hl.1, hl.1, hl.2.2.1, hl.2.2.1,
      hl.2.2.2.2.2, hl.1, hl.2.2.1⟩
  simp only [resultOperands, resultLengths, Mem.room_cons, Mem.room_nil, and_true] at hroom
  have hRoom := room_upSplit (m := m)
    (u := (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo))
    (e := (ea.1, ea.2 + n * d + lo)) hr hroom.1 hroom.2
  have hRun := writes_upSplitResult (τ := τ) hS mm hMM Qp Qm cp.1 cm.1
    (List.ofFn cp.2) (List.ofFn cm.2) sigma hLive hreads hRoom
    (by simpa using hparts.1) (by simpa [Nat.mul_add, Nat.add_assoc] using hparts.2.2)
  unfold Writes Wp
  rw [hev]
  change Writes .total I τ upSplitResultImpl.body _ _ _ m
  refine hRun.mono (le_of_eq ?_) ?_
  · simpa only [resultOperands, resultLengths] using fp_upSplit_eq hr
      (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo) (ea.1, ea.2 + n * d + lo)
  · intro m' _ ⟨hp, hr'⟩
    refine ⟨hp, storesResult_iff_readBlocks.mpr ?_⟩
    simpa only [resultOperands, resultLengths] using
      readBlocks_upSplit hr (mm Qp cp.1) (mm Qm cm.1) cp.2 cm.2 sigma hr'

end NLAlib.SpectralBisection
