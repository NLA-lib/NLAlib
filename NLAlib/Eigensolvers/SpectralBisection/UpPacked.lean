/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpSplit
public import NLAlib.Ops.Logic.EntryAppend
public import NLAlib.ForMathlib.Data.List.OfFn

/-!
# Mathematical packing of reconstructed split outputs

The two computed matrix blocks are columns of the parent basis. The two shifted eigenvalue
blocks concatenate in the same finite sum order as the pure recursive algorithm.

## Main results

* `NLAlib.SpectralBisection.readBlocks_upSplit`: four adjacent child blocks give the two parent
  output blocks in the mathematical assembly order.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Joining the actual adjacent output blocks gives the mathematical split assembly. Empty
children are included; the split-size inequality justifies the total finite dimension. -/
theorem readBlocks_upSplit {K : Type} {M : Machine K} {m : Mem K} {k kp : ℕ}
    (hp : kp ≤ k) {u e : ℕ × ℕ}
    (A : Matrix (Fin k) (Fin kp) (K × K)) (B : Matrix (Fin k) (Fin (k - kp)) (K × K))
    (dp : Fin kp → K) (dm : Fin (k - kp) → K) (s : K)
    (h : m.readBlocks [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
      [kp * k * 2, (k - kp) * k * 2, kp, k - kp] =
      some [(EntryCodec.pair K).packFinMatrix A, (EntryCodec.pair K).packFinMatrix B,
        (List.ofFn dp).map (fun v => M.add v s), (List.ofFn dm).map (fun v => M.sub v s)]) :
    let index : Fin k ≃ Fin kp ⊕ Fin (k - kp) :=
      (finCongr (Nat.add_sub_of_le hp).symm).trans finSumFinEquiv.symm
    m.readBlocks [u, e] [2 * (k * k), k] =
      some [(EntryCodec.pair K).packFinMatrix ((Matrix.fromCols A B).submatrix id index),
        List.ofFn (fun i => Sum.elim (fun j => M.add (dp j) s)
          (fun j => M.sub (dm j) s) (index i))] := by
  have hA := Mem.readBlocks_getD h (i := 0) (by simp)
  have hB := Mem.readBlocks_getD h (i := 1) (by simp)
  have hdp := Mem.readBlocks_getD h (i := 2) (by simp)
  have hdm := Mem.readBlocks_getD h (i := 3) (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hA hB hdp hdm
  have hB' : m.store.readBlock u.1 (u.2 + kp * k * 2) ((k - kp) * k * 2) =
      some ((EntryCodec.pair K).packFinMatrix B) := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hB
  have hmat := Store.readBlock_add hA hB'
  have hlen : kp * k * 2 + (k - kp) * k * 2 = 2 * (k * k) := by
    have := Nat.sub_add_cancel hp
    nlinarith
  rw [hlen, ← (EntryCodec.pair K).packFinMatrix_fromCols_cast
    (Nat.add_sub_of_le hp).symm A B] at hmat
  have hvec := Store.readBlock_add hdp hdm
  rw [Nat.add_sub_of_le hp] at hvec
  simp only [List.map_ofFn] at hvec
  rw [← List.ofFn_sumElim_cast (Nat.add_sub_of_le hp).symm] at hvec
  simp only [Mem.readBlocks, hmat, hvec, Option.bind_some, Option.map_some,
    Function.comp_def]

end NLAlib.SpectralBisection
