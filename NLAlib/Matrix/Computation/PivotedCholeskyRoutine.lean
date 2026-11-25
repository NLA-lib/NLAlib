/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotedCholesky
public import NLAlib.Computation.RoutineFrames

/-!
# Exact pivoted semidefinite Cholesky routine certificates

The actual output log determines the simultaneous row and column permutation of the input.
The decoded factor is lower triangular, has nonnegative diagonal and reproduces that permuted
input as its Gram matrix. This exact semidefinite certificate permits zero diagonal entries;
the existing positive-definite Cholesky and error predicates retain their strict convention.

## Main definitions

* `NLAlib.Computation.IsPivotedCholeskyRoutine`: execution, two writes and the exact factorization.

## Main results

* `NLAlib.Computation.IsPivotedCholeskyRoutine.toBlockRoutine`: the factor/log footprint.
* `NLAlib.Computation.isPivotedCholeskyRoutine_pivotedCholesky`: the actual stored driver instance.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- An exact pivoted semidefinite Cholesky routine succeeds, writes a factor and its absolute
current-position pivot log, and gives the jointly permuted input's Gram factorization. The
factor is lower triangular with nonnegative diagonal. Zero pivots are permitted. Arithmetic
and source admissibility belong to implementation instances. [GolubVanLoan2013, §4.2]. -/
structure IsPivotedCholeskyRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (pre : Store P K → Prop)
    (Lb Hb : ℕ) (lo ho : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The scoped execution composes with its continuation. -/
  composable : ExecutionComposable I routine
  /-- Actual successful execution, both net writes and the decoded log/factor guarantees. -/
  run : ∀ st : St P K C, pre st.store →
    WritableBlocks st.store tag [(Lb, lo.eval, N * N), (Hb, ho.eval, N)] →
    blockDisjoint (Lb, lo.eval, N * N) (Hb, ho.eval, N) = true →
    ∃ (out : St P K C) (Lw Hw : Array K) (p : Fin N → Fin N),
      Lw.size = N * N ∧ Hw.size = N ∧ exec I routine.run st = some out ∧
      st.store.writeBlocks tag [(Lb, lo.eval, N * N), (Hb, ho.eval, N)] [Lw, Hw] =
        some out.store ∧
      ReadsDecoded out.store dec tag Hb ho.eval (fun i => (p i : ℕ)) ∧
      (∀ i, i ≤ p i) ∧
      let D := unflatten N N (Lw.map (dec tag))
      D.IsLowerTriangular ∧ (∀ i, 0 ≤ D i i) ∧
        A.submatrix (luPivotPermutation p N) (luPivotPermutation p N) = D * Dᴴ

/-- The footprint of an exact pivoted Cholesky routine consists of the full factor and pivot
log. The disjoint windows preserve each other's decoded output. -/
theorem IsPivotedCholeskyRoutine.toBlockRoutine
    {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {pre : Store P K → Prop} {Lb Hb : ℕ}
    {lo ho : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}
    (h : IsPivotedCholeskyRoutine I dec tag A pre Lb Hb lo ho routine)
    (hLH : blockDisjoint (Lb, lo.eval, N * N) (Hb, ho.eval, N) = true) :
    IsBlockRoutine I tag pre [(Lb, lo.eval, N * N), (Hb, ho.eval, N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, Lw, Hw, _, _, _, he, hs, _⟩ := h.run st hp hw hLH
    exact ⟨out, [Lw, Hw], he, hs⟩

/-- The actual diagonal-pivoted driver supplies the exact semidefinite routine certificate
under exact real arithmetic and standard charges. Source storage may overlap either distinct
output buffer. Singular inputs are allowed. [GolubVanLoan2013, §4.2]. -/
theorem isPivotedCholeskyRoutine_pivotedCholesky {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) (Ab : ℕ) (ao : IExp ℕ)
    (Lb : ℕ) (lo : IExp ℕ) (Hb : ℕ) (ho : IExp ℕ) (hLH : Lb ≠ Hb) :
    IsPivotedCholeskyRoutine I (fun _ x => x) tag A (fun s => Holds s tag Ab ao.eval A)
      Lb Hb lo ho (pivotedCholesky tag (.const N) Ab ao Lb lo Hb ho) where
  composable := executionComposable_pivotedCholesky I tag (.const N) Ab ao Lb lo Hb ho
  run st hp hw _ := by
    obtain ⟨out, p, he, hs, hrange, _, hlog, hlow, hdiag, hgram⟩ :=
      exec_pivotedCholesky I hI hc tag st (.const N) Ab ao Lb lo Hb ho A hA hp
        (hw _ List.mem_cons_self) (hw (Hb, ho.eval, N) (by simp)) hLH
    change Fin N → Fin N at p
    simp only [IExp.eval] at hs hrange hlog hlow hdiag hgram
    refine ⟨out, _, _, p, size_flatten _, Array.size_ofFn, he, hs, ?_, hrange, ?_⟩
    · intro i
      exact ⟨_, hlog i, rfl⟩
    · dsimp only
      rw [Array.map_id', unflatten_flatten]
      exact ⟨hlow, hdiag, hgram⟩

end NLAlib.Computation
