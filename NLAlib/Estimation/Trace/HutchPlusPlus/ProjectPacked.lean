/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Project
public import NLAlib.Estimation.Trace.HutchPlusPlus.Math

/-!
# Packed matrix refinement of probe reduction

The stored basis prefix remains unchanged while the probe tail is swept. The result is
one ordinary packed matrix, ready for the next batch of matrix-vector applications.

## Main results

* `NLAlib.HutchPlusPlus.writes_projectProbes_packed` returns `projectedBasis`.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies the raw word padding convention in this module. -/
local instance instInhabitedProjectPacked : Inhabited 𝕜 := ⟨0⟩

/-- Project the actual stored probes and retain the basis, with an exact matrix result.
The computation is valid for every basis, including zero and dependent columns. -/
theorem writes_projectProbes_packed (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hB : RCLikeBlas.IsExact I) {n k ell : ℕ} {b t : ℕ × ℕ}
    (Q : Matrix (Fin n) (Fin k) 𝕜) (G : Matrix (Fin n) (Fin ell) 𝕜)
    (hl : m.Live [b, t])
    (hInput : m.store.readBlock b.1 b.2 ((k + ell) * n) =
      some ((EntryCodec.scalar 𝕜).packFinMatrix (basisProbes Q G)))
    (hTB : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock b.1 b.2 ((k + ell) * n)))
    (ht : t.2 + 2 ≤ m.store.len t.1) (hb : b.2 + (k + ell) * n ≤ m.store.len b.1) :
    Writes .total I τ projectProbes.body (Env.frame [n, k, ell] [b, t])
      (Store.inBlock b.1 (b.2 + n * k) (ell * n) ⊔ Store.inBlock t.1 t.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock b.1 b.2 ((k + ell) * n) =
        some ((EntryCodec.scalar 𝕜).packFinMatrix (projectedBasis Q G))) m := by
  have hQ : ∀ i < k, m.store.readBlock b.1 (b.2 + n * i) n =
      some (List.ofFn (column Q i)) := by
    intro i hi
    have h := Store.readBlock_scalar_matrix_column hInput ⟨i, by omega⟩
    change m.store.readBlock b.1 (b.2 + i * n) n =
      some (List.ofFn fun a : Fin n => basisProbes Q G a ⟨i, by omega⟩) at h
    rw [column_eq Q i hi]
    simpa [basisProbes, hi, Nat.mul_comm] using h
  have hG : ∀ j < ell, m.store.readBlock b.1 (b.2 + n * (k + j)) n =
      some (List.ofFn (column G j)) := by
    intro j hj
    have h := Store.readBlock_scalar_matrix_column hInput ⟨k + j, by omega⟩
    change m.store.readBlock b.1 (b.2 + (k + j) * n) n =
      some (List.ofFn fun a : Fin n => basisProbes Q G a ⟨k + j, by omega⟩) at h
    rw [column_eq G j hj]
    simpa [basisProbes, show ¬ k + j < k by omega, Nat.mul_comm] using h
  refine (writes_projectProbes hS hB (column Q) (column G) hl hQ hG hTB ht hb).mono
    le_rfl ?_
  intro m' hfr ⟨hp, hProbe⟩
  refine ⟨hp, Store.readBlock_scalar_matrix_of_columns _ fun j => ?_⟩
  by_cases hj : (j : ℕ) < k
  · have hcol : Store.inBlock b.1 (b.2 + n * j) n ≤
        Store.inBlock b.1 b.2 ((k + ell) * n) := by
      have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt j.isLt)
      rw [Nat.mul_succ, Nat.mul_comm n (k + ell)] at hm
      exact Fp.inBlock_le_inBlock (by omega) (by omega)
    have hdis : Fp.Disj (Store.inBlock b.1 (b.2 + n * k) (ell * n))
        (Store.inBlock b.1 (b.2 + n * j) n) := by
      have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at hm
      exact (Fp.disj_inBlock_of_le (by omega)).symm
    have h := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨hdis, hTB.mono le_rfl hcol⟩) (hQ j hj)
    change _ = some (List.ofFn fun a : Fin n => projectedBasis Q G a j)
    rw [column_eq Q j hj] at h
    simpa [projectedBasis, hj, Nat.mul_comm] using h
  · have hc : (j : ℕ) - k < ell := by omega
    have h := hProbe (j - k) hc
    have he : k + ((j : ℕ) - k) = j := by omega
    rw [he] at h
    change _ = some (List.ofFn fun a : Fin n => projectedBasis Q G a j)
    simpa only [projectedBasis, Matrix.of_apply, dif_neg hj, Nat.mul_comm n j] using h

end NLAlib.HutchPlusPlus
