/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SemidefiniteCholesky

/-!
# Exact semidefinite Cholesky routine certificates

The positive-diagonal `IsCholesky` and `IsCholeskyErr` predicates exclude singular factors.
This exact certificate instead records a lower triangular factor with nonnegative diagonal
and its Gram identity, together with the actual successful output write. No positive-diagonal
predicate is weakened and no rounded semidefinite accuracy theorem is asserted.

## Main definitions

* `NLAlib.Computation.IsSemidefiniteCholeskyRoutine`: the exact one-output PSD contract.

## Main results

* `NLAlib.Computation.IsSemidefiniteCholeskyRoutine.toBlockRoutine`: its output footprint.
* `NLAlib.Computation.isSemidefiniteCholeskyRoutine_semidefiniteCholesky`: the actual instance.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- An exact semidefinite factor routine succeeds, writes one full factor block, and its
decoded lower triangular factor has nonnegative diagonal and the original matrix as Gram
product. Zero diagonal entries are permitted. Scratch remains outside the net store footprint. -/
structure IsSemidefiniteCholeskyRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (pre : Store P K → Prop)
    (Lb : ℕ) (lo : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The routine composes with the following computation. -/
  composable : ExecutionComposable I routine
  /-- Actual execution, the original output write, and the exact decoded Gram factor. -/
  run : ∀ st : St P K C, pre st.store → Writable st.store tag Lb lo.eval (N * N) →
    ∃ (out : St P K C) (W : Array K), W.size = N * N ∧
      exec I routine.run st = some out ∧
      st.store.writeBlock tag Lb lo.eval W = some out.store ∧
      (unflatten N N (W.map (dec tag))).IsLowerTriangular ∧
      (∀ i, 0 ≤ unflatten N N (W.map (dec tag)) i i) ∧
      A = unflatten N N (W.map (dec tag)) * (unflatten N N (W.map (dec tag)))ᴴ

/-- The exact semidefinite certificate projects to its one-block output footprint. -/
theorem IsSemidefiniteCholeskyRoutine.toBlockRoutine {I : Interp P ι K C}
    {dec : P → K → ℝ} {tag : P} {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {pre : Store P K → Prop} {Lb : ℕ} {lo : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}
    (h : IsSemidefiniteCholeskyRoutine I dec tag A pre Lb lo routine) :
    IsBlockRoutine I tag pre [(Lb, lo.eval, N * N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, W, hsize, hr, hs, -⟩ := h.run st hp (hw _ List.mem_cons_self)
    exact ⟨out, [W], hr, Store.writeBlocks_singleton_eq_some_iff.mpr ⟨hsize, hs⟩⟩

/-- The actual zero-safe stored factorization supplies the exact PSD certificate. Input and
output may overlap; empty matrices require no valid handles. -/
theorem isSemidefiniteCholeskyRoutine_semidefiniteCholesky {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) (Ab Lb : ℕ) (ao lo : IExp ℕ) :
    IsSemidefiniteCholeskyRoutine I (fun _ x => x) tag A
      (fun s => Holds s tag Ab ao.eval A) Lb lo
      (semidefiniteCholesky tag (.const N) Ab ao Lb lo) where
  composable := executionComposable_semidefiniteCholesky I tag (.const N) Ab ao Lb lo
  run st hp hw := by
    obtain ⟨out, hr, hs, -, ht, hd, he⟩ :=
      exec_semidefiniteCholesky I hI hc tag st (.const N) Ab Lb ao lo A hA hp hw
    refine ⟨out, flatten (choleskyLower A), by simp only [size_flatten], hr, hs, ?_⟩
    rw [Array.map_id', unflatten_flatten]
    exact ⟨ht, hd, he⟩

end NLAlib.Computation
