/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Leaf
public import NLAlib.Matrix.FinitePrecision.OpsMachine
public import NLAlib.Matrix.FinitePrecision.EntrywiseRounding
public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Packed mathematical outputs of the actual leaf program

The scalar identity and eigenvalue guarantees expose the same finite matrices and vectors as
the mathematical bisection leaf. The adapter uses actual input words and no numerical accuracy
or successful-execution hypothesis.

## Main results

* `NLAlib.SpectralBisection.writes_leaf_packed`: actual identity, eigenvalues and leaf metadata.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Actual leaf outputs as the finite mathematical identity and diagonal or zero vector. -/
theorem writes_leaf_packed {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] {M : Machine K} {dec : K → ℝ} {mm : MatMulMap (K × K)}
    {qr : QRMap (K × K)} {unif : K → Su → K} {normal : Sg → K × K}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (diagonal : Bool) {τ : Tape K} {m : Mem K} {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (K × K)) {a u e kind : ℕ × ℕ}
    (hl : m.Live [a, u, e, kind])
    (hA : m.store.readBlock a.1 a.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hu : u.2 + 2 * (k * k) ≤ m.store.len u.1) (he : e.2 + k ≤ m.store.len e.1)
    (hk : kind.2 < m.store.len kind.1)
    (hAP : Fp.Apart [u, e, kind, a] [2 * (k * k), k, 1, 2 * (k * k)]) :
    Writes .total I τ (leaf diagonal) (Env.frame [k] [a, u, e, kind])
      (Fp.blocks [u, e, kind] [2 * (k * k), k, 1])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [u, e, kind] [2 * (k * k), k, 1] =
        some [(EntryCodec.pair K).packFinMatrix
          ((M.toFloatMachine dec mm qr unif normal).identityMat k),
          List.ofFn (fun i => if diagonal then (A i i).1 else M.lit 0), [M.lit 1]]) m := by
  refine (writes_leaf hS hL diagonal hl (Store.holdsVec_of_readBlock hA) hu he hk hAP).mono
    (by fp_sub) ?_
  rintro μ _ ⟨hU, hE, hKind, hpos⟩
  have hUread := (PairMatrix.holdsEntries_of_holdsVec hU).readBlock_packFinMatrix rfl
  have hU' : μ.store.readBlock u.1 u.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix
        ((M.toFloatMachine dec mm qr unif normal).identityMat k)) := by
    have hId : (Matrix.of fun (i j : Fin k) =>
        (if i = j then M.lit 1 else M.lit 0, M.lit 0)) =
        (M.toFloatMachine dec mm qr unif normal).identityMat k := by
      apply Matrix.ext
      intro i j
      by_cases hij : i = j <;> simp [FloatMachine.identityMat, Machine.toFloatMachine, hij]
    simpa only [Nat.mul_comm, EntryCodec.pair, Fin.val_inj, hId] using hUread
  have hE' : μ.store.readBlock e.1 e.2 k =
      some (List.ofFn (fun i => if diagonal then (A i i).1 else M.lit 0)) := by
    refine Store.readBlock_eq_some_iff.mpr ⟨by simp, ?_⟩
    intro j hj
    have hd := (EntryCodec.pair K).vec_packFinMatrix A ⟨j, hj⟩ ⟨j, hj⟩ 0
    have hd' : vec ((EntryCodec.pair K).packFinMatrix A) (2 * (j * k + j)) =
        (A ⟨j, hj⟩ ⟨j, hj⟩).1 := by
      simpa [Nat.mul_comm, EntryCodec.pair] using hd
    have hEj := hE j hj
    cases diagonal with
    | false => simpa [hj] using hEj
    | true =>
      change μ.store.get e.1 (e.2 + j) =
        some (vec ((EntryCodec.pair K).packFinMatrix A) (2 * (j * k + j))) at hEj
      rw [hd'] at hEj
      simpa [hj] using hEj
  refine ⟨hpos, ?_⟩
  simp [Mem.readBlocks, hU', hE', Store.readBlock, hKind]

end NLAlib.SpectralBisection
