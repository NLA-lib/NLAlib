/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Matrix.FinitePrecision.OpsHermitian
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.BlockSequence
public import NLAlib.Ops.Logic.Step

/-!
# Total stored-output refinement of a single bisection child

A child writes its shifted matrix in the next level, records its size, and marks the parent
branch. All three stored outputs are collected in one block-read contract. The source and
next-level matrix may share an arena buffer when their actual occupied intervals are disjoint.

## Main results

* `NLAlib.SpectralBisection.writes_child`: exact shifted matrix and metadata on actual words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The single-child branch writes the shifted next-level matrix and both metadata words,
without a successful-run or numerical-accuracy assumption. The literal values are the actual
machine words; exact natural decoding is a separate numerical-model obligation. -/
theorem writes_child {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    {M : Machine K} (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {τ : Tape K} {μ : Mem K}
    {n d lo k branch : ℕ} {ma sz kd sigma : ℕ × ℕ} :
    let x := (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo)
    let y := (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo)
    let z := (sz.1, sz.2 + n * (d + 1) + lo)
    let w := (kd.1, kd.2 + n * d + lo)
    ∀ (A : Matrix (Fin k) (Fin k) (K × K)) (s : K),
    μ.Live [ma, sz, kd, sigma] →
    μ.store.readBlock x.1 x.2 (2 * (k * k)) = some ((EntryCodec.pair K).packFinMatrix A) →
    μ.store.get sigma.1 sigma.2 = some s →
    y.2 + 2 * (k * k) ≤ μ.store.len y.1 →
    z.2 < μ.store.len z.1 → w.2 < μ.store.len w.1 →
    Fp.Disj (Store.inBlock x.1 x.2 (2 * (k * k)))
      (Store.inBlock y.1 y.2 (2 * (k * k))) →
    Fp.Disj (Store.inBlock sigma.1 sigma.2 1) (Store.inBlock y.1 y.2 (2 * (k * k))) →
    Fp.Apart [y, z, w] [2 * (k * k), 1, 1] →
    Writes .total I τ (child (Op := Op) (Tst := Tst))
      (Env.frame [n, d, lo, k, branch] [ma, sz, kd, sigma])
      (Fp.blocks [y, z, w] [2 * (k * k), 1, 1])
      (fun μ' => μ'.pos = μ.pos ∧ μ'.readBlocks [y, z, w] [2 * (k * k), 1, 1] =
        some [(EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).hermShift A s),
          [M.lit (k : ℚ)], [M.lit (branch : ℚ)]]) μ := by
  dsimp only
  intro A s hl hA hs hy hz hw hxy hsy hap
  have hma := hl ma (by simp)
  have hsz := hl sz (by simp)
  have hkd := hl kd (by simp)
  have hsigma := hl sigma (by simp)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
    Fp.disj_bot_right, and_true] at hap
  obtain ⟨⟨hYZ, hYW⟩, hZW⟩ := hap
  refine (writes_frame rfl rfl (by room) (Hermitian.writes_shift_packed
    (dec := dec) (mm := mm) (qr := qr) (unif := unif) (normal := normal)
    hS A s (x := (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo))
    hxy hsy hA hs hy (by room))).seq_readBlock ?_ ?_
  · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq, Fp.disj_sup_right] using ⟨hYZ, hYW⟩
  intro μ₁ hfr₁ hp₁ hB
  refine (writes_indexLit hL rfl rfl (by room)).readBlock_of_get.seq_readBlock ?_ ?_
  · simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hZW
  intro μ₂ hfr₂ hp₂ hsize
  exact (writes_indexLit hL rfl rfl (by room)).readBlock_of_get.readBlocks_singleton

end NLAlib.SpectralBisection
