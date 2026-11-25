/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.CholeskyFactorization
public import NLAlib.Matrix.Perturbation.CholeskyErr

/-!
# Cholesky routines: execution and decoded factorization

A Cholesky routine succeeds, writes exactly its factor block and meets a decoded absolute
spectral backward-error guarantee. Arithmetic and input admissibility are established by
implementation instances, rather than assumed by the certificate's definition.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main results

* `NLAlib.Computation.IsCholeskyRoutine.mono`: larger error allowances.
* `NLAlib.Computation.IsCholeskyRoutine.toBlockRoutine`: the factor footprint.
* `NLAlib.Computation.isCholeskyRoutine_cholesky`: the exact stored factorization instance.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A certified Cholesky routine for a fixed decoded real matrix: a state meeting `pre`
and writable factor capacity imply successful execution, one net factor block write and
absolute spectral backward error at most $\varepsilon$. Matrix words are column-major;
the existing decoding function determines the output matrix. Scratch is scoped. -/
structure IsCholeskyRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (pre : Store P K → Prop)
    (Lb : ℕ) (lo : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- Execution composes with the following routine. -/
  composable : ExecutionComposable I routine
  /-- Successful execution, the exact output write and the decoded mathematical guarantee. -/
  run : ∀ st : St P K C, pre st.store → Writable st.store tag Lb lo.eval (N * N) →
    ∃ (out : St P K C) (W : Array K), W.size = N * N ∧
      exec I routine.run st = some out ∧
      st.store.writeBlock tag Lb lo.eval W = some out.store ∧
      IsCholeskyErr ε A (unflatten N N (W.map (dec tag)))

variable {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {ε ε' : ℝ} {pre : Store P K → Prop}
    {Lb : ℕ} {lo : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}

/-- Increasing the absolute spectral error allowance preserves a certified Cholesky routine. -/
theorem IsCholeskyRoutine.mono
    (h : IsCholeskyRoutine I dec tag A ε pre Lb lo routine) (hε : ε ≤ ε') :
    IsCholeskyRoutine I dec tag A ε' pre Lb lo routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, W, hsize, hr, hs, he⟩ := h.run st hp hw
    exact ⟨out, W, hsize, hr, hs, he.mono hε⟩

/-- The footprint of a Cholesky certificate is its one full column-major factor block. -/
theorem IsCholeskyRoutine.toBlockRoutine
    (h : IsCholeskyRoutine I dec tag A ε pre Lb lo routine) :
    IsBlockRoutine I tag pre [(Lb, lo.eval, N * N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, W, hsize, hr, hs, -⟩ := h.run st hp (hw _ List.mem_cons_self)
    exact ⟨out, [W], hr, Store.writeBlocks_singleton_eq_some_iff.mpr ⟨hsize, hs⟩⟩

/-- The stored full Cholesky factorization supplies a zero-error routine certificate under
exact real semantics and standard instruction charges, for every positive definite input.
Input and output storage may overlap; the routine copies its input before writing its factor.
[GolubVanLoan2013, §4.2]. -/
theorem isCholeskyRoutine_cholesky {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (Ab Lb : ℕ) (ao lo : IExp ℕ) :
    IsCholeskyRoutine I (fun _ x => x) tag A 0
      (fun s => Holds s tag Ab ao.eval A) Lb lo
      (cholesky tag (.const N) Ab ao Lb lo) where
  composable := executionComposable_cholesky I tag (.const N) Ab ao Lb lo
  run st hp hw := by
    obtain ⟨out, hr, hs, -, he⟩ :=
      exec_cholesky I hI hc tag st (.const N) Ab Lb ao lo A hA hp hw
    refine ⟨out, flatten (choleskyLower A), by simp only [size_flatten], hr, hs, ?_⟩
    rw [Array.map_id', unflatten_flatten]
    exact he.isCholeskyErr

end NLAlib.Computation
