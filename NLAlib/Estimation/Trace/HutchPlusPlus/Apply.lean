/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Alg
public import NLAlib.Ops.Logic.StoredOperator
public import NLAlib.Ops.Logic.EntryColumn
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Batched explicit-data operator application

Each column is obtained from the actual packed input matrix and the declared data
operand. The shared independent-loop rule retains the computed output columns.

## Main results

* `NLAlib.HutchPlusPlus.writes_applyColumns` computes the packed matrix product.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has StoredOperatorOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies the raw word padding convention in this module. -/
local instance instInhabitedApply : Inhabited 𝕜 := ⟨0⟩

/-- A batch of local matrix-vector applications computes a matrix product. Read-only
operator data and input columns may share a buffer when their spans satisfy the contract. -/
theorem writes_applyColumns {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List 𝕜 → Matrix (Fin m) (Fin n) 𝕜}
    (hI : StoredOperator.IsExact dataLength matrix I) {n k : ℕ} {data x y : ℕ × ℕ}
    (as : List 𝕜) (X : Matrix (Fin n) (Fin k) 𝕜) (hl : m.Live [data, x, y])
    (hA : m.store.readBlock data.1 data.2 (dataLength n n) = some as)
    (hX : m.store.readBlock x.1 x.2 (k * n) = some ((EntryCodec.scalar 𝕜).packFinMatrix X))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 (k * n)) (Store.inBlock x.1 x.2 (k * n)))
    (hYA : Fp.Disj (Store.inBlock y.1 y.2 (k * n))
      (Store.inBlock data.1 data.2 (dataLength n n)))
    (hy : y.2 + k * n ≤ m.store.len y.1) :
    Writes .total I τ applyColumns.body (Env.frame [n, k] [data, x, y])
      (Store.inBlock y.1 y.2 (k * n))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 (k * n) =
        some ((EntryCodec.scalar 𝕜).packFinMatrix (matrix n n as * X))) m := by
  let B := matrix n n as * X
  let region : ℕ → Fp := fun j => Store.inBlock y.1 (y.2 + n * j) n
  let col : ℕ → Fin n → 𝕜 := fun j r => if hj : j < k then B r ⟨j, hj⟩ else 0
  have hsub : ∀ j < k, region j ≤ Store.inBlock y.1 y.2 (k * n) := by
    intro j hj
    have hb := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ, Nat.mul_comm n k] at hb
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  unfold applyColumns
  dsimp only
  refine (writes_loop_disjoint region
    (fun j s => s.readBlock y.1 (y.2 + n * j) n = some (List.ofFn (col j)))
    rfl hsub ?_ (fun j _ => Store.readsOnly_readBlock _ _ _ _) ?_).mono le_rfl ?_
  · intro i hi j hj hne
    simpa [region, EntryCodec.scalar, Nat.mul_comm] using
      (EntryCodec.scalar 𝕜).disj_columns (L := ⟨y.1, y.2, n, k, n⟩) le_rfl hne
  · intro j hj m' hfr
    have hA' := hfr.keep (Store.readsOnly_readBlock _ _ _ as) hYA hA
    have hX' := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hYX hX
    have hc := Store.readBlock_scalar_matrix_column hX' ⟨j, hj⟩
    have hl' : m'.Live [data, (x.1, x.2 + n * j), (y.1, y.2 + n * j)] := by
      simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hfr.length_eq
    refine (StoredOperator.writes_matvec hI rfl rfl rfl hl' hA'
      (by simpa only [Nat.mul_comm] using hc)
      (hYA.mono (hsub j hj) le_rfl)
      (hYX.mono (hsub j hj) (by
        have hb := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
        rw [Nat.mul_succ, Nat.mul_comm n k] at hb
        exact Fp.inBlock_le_inBlock (by omega) (by omega))) ?_).mono le_rfl ?_
    · have hb := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ, Nat.mul_comm n k] at hb
      change y.2 + n * j + n ≤ m'.store.len y.1
      rw [hfr.len_eq]
      omega
    · intro m'' _ ⟨hp, ho⟩
      refine ⟨hp, ?_⟩
      simp only [col, dif_pos hj, B, Matrix.mul_apply]
      simpa [List.getD_eq_getElem?_getD, Matrix.col, Matrix.transpose, Matrix.of_apply] using ho
  · intro m' _ ⟨hp, hcols⟩
    let A : ℕ → ℕ → 𝕜 := fun i j => if hi : i < n then col j ⟨i, hi⟩ else 0
    have hs : m'.store.HoldsEntries (EntryCodec.scalar 𝕜) ⟨y.1, y.2, n, k, n⟩ A := by
      apply Store.holdsEntries_of_readBlock_columns
      intro j hj
      simpa [EntryCodec.scalar_pack, EntryCodec.scalar, A, Nat.mul_comm] using hcols j hj
    refine ⟨hp, ?_⟩
    have hout := hs.readBlock_packFinMatrix rfl
    have he : (Matrix.of fun (i : Fin n) (j : Fin k) => A i j) = B := by
      ext i j
      simp [A, col]
    simpa only [EntryCodec.scalar, Nat.mul_one, he] using hout

end NLAlib.HutchPlusPlus
