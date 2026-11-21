/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.ZeroStart
public import NLAlib.Ops.Profiles.ContextLinearRoundedGuarded
public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stability
public import NLAlib.Ops.Certification
public import NLAlib.Matrix.FinitePrecision.StoredDense
public import NLAlib.Ops.RoutineData

/-!
# Rounded capped conjugate gradient on a stored dense matrix

`NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.storedRoutine` reads a matrix stored as `n * n`
words and a right-hand side, and writes the iterate, the residual, the direction and the cell of
the carried residual product: it fills the iterate with literal zeros and runs the rounded capped
solver on the stored matrix. The solver is the matrix-free one on stored data
(`NLAlib.Ops.Routine.withData`): the matrix is an isolated operand, forwarded to every product.

## Main definitions

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.linkedSolveRoutine`: the solver on a stored
  matrix.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.storedRoutine`,
  `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.storedSpec`: the routine and its specification.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.linkedSolveRoutine_meets`: the solver on a
  stored matrix meets the specification of the matrix-free solver at the decoded matrix.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.storedRoutine_meets`: the routine meets its
  specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored

open Ops

variable {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ} {u em E a₀ a₁ : ℝ}

/-- The rounded capped solver on a stored matrix: the matrix-free rounded solver with the matrix
words, `n * n` of them, a new isolated leading operand forwarded to every product. -/
def linkedSolveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (Rounded.solveRoutine (Op := Standard.Operation) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0] (ContextLinear.table 1 0)

/-- Zero the iterate, then solve on the stored matrix. Index variables: `n`, `cap`, then the
offsets of `A`, `b`, `x`, `r`, `p`, `v`. -/
def zeroStart : Stmt RCLikeBlas.Operation CmpTst := ops% [n, cap] (A, B) → (X, R, P, RHO) {
  run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n] (X);
  run linkedSolveRoutine [n, cap] (A, B, X, R, P, RHO)
}

/-- The specification of the rounded solver on a stored matrix of order `n`: for a symmetric
matrix decoded from the stored words with spectrum in the window `[a₀, a₁]`, that of the
matrix-free rounded solver at that matrix. -/
noncomputable def linkedSolveSpec (n : ℕ) (E a₀ a₁ : ℝ) : Routine.Spec ℝ :=
  .onData 1
    (fun d raws => d.headD 0 = n ∧
      (StoredOperator.denseMatrix n n (raws.headD []))ᵀ =
        StoredOperator.denseMatrix n n (raws.headD []) ∧
      spectrum ℝ (StoredOperator.denseMatrix n n (raws.headD [])) ⊆ Set.Icc a₀ a₁)
    (fun _ raws => Rounded.solveSpec id (StoredOperator.denseMatrix n n (raws.headD [])) E a₀ a₁)

/-- The normwise error of the product with a stored matrix, from the bound on the accumulated
roundoff of a row. -/
theorem matvec_error (hM : StdModel u id M) (hu : 0 ≤ u) {n : ℕ}
    (hMatvec : ScalarProducts.roundoff u n * Real.sqrt n ≤ em) (raw ys : List ℝ) :
    ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n ys -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw ys)))‖ ≤
      (em * specNorm (StoredOperator.denseMatrix n n raw)) *
        ‖WithLp.toLp 2 (decv id n ys)‖ :=
  (hM.norm_mulVec_sub_rowWord_le hu n n raw ys).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMatvec (specNorm_nonneg _))
      (norm_nonneg _))

/-- The rounded solver on a stored matrix meets its specification: it is the matrix-free rounded
solver on stored data, and under the interpretation in which a product reads the stored words
that solver meets its own specification at the decoded matrix
(`NLAlib.Ops.Routine.Meets.withData`). -/
theorem linkedSolveRoutine_meets (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u)
    (hB : IsBlas1 id (Blas.seq.err u) (fun _ => True) I) (hCmp : IsCmp id I) {n : ℕ}
    (hMatvec : ScalarProducts.roundoff u n * Real.sqrt n ≤ em)
    (hAccuracy : Standard.Accuracy em u E (Blas.seq.err u) n)
    (ha₀ : 0 < a₀) (hprec : 3 * E * a₁ ≤ a₀) :
    linkedSolveRoutine.Meets I (linkedSolveSpec n E a₀ a₁) := by
  have hem : 0 ≤ em := le_trans (mul_nonneg (ScalarProducts.roundoff_nonneg hu n)
    (Real.sqrt_nonneg _)) hMatvec
  obtain ⟨_, hd, haa, _⟩ := Standard.Scheme.sequential.errors_nonneg hu n
  have hue : u ≤ E := by linarith [hAccuracy.scalar, hAccuracy.nonneg]
  have hde : (Blas.seq.err u).dot n ≤ E := by linarith [hAccuracy.dot, hAccuracy.nonneg]
  refine Routine.Meets.withData _ _
    (fun _ raws => ContextLinearRounded.relation M (Blas.seq.err u)
      (StoredOperator.denseMatrix n n (raws.headD []))
      (em * specNorm (StoredOperator.denseMatrix n n (raws.headD []))))
    (fun _ => ContextLinearRounded.admissible (fun _ => True) n)
    (fun _ raws => ContextLinearRounded.fallback I
      (StoredOperator.denseMatrix n n (raws.headD [])))
    rfl rfl ?_ ?_
  · intro d ctx m raws hc hr hP
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
    split_reads hr as (raw)
    have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
      rw [← hP.1]
      exact hraw
    exact ContextLinearRounded.satisfies_guarded hS hB [a] ⟨0, by simp⟩ m.store raw
      (mul_nonneg hem (specNorm_nonneg _)) (matvec_error hM hu hMatvec raw)
      (fun z hz => List.mem_map_of_mem hz) hraw'
  · intro d ctx m raws hc hr hP
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hc
    split_reads hr as (raw)
    have hraw' : m.store.readBlock a.1 a.2 (n * n) = some raw := by
      rw [← hP.1]
      exact hraw
    obtain ⟨hs, hb', hA, hc⟩ := ContextLinearRounded.guarded_laws hS hB hCmp [a] ⟨0, by simp⟩
      m.store raw (mul_nonneg hem (specNorm_nonneg _)) (matvec_error hM hu hMatvec raw)
      (fun z hz => List.mem_map_of_mem hz) hraw'
    exact Rounded.solveRoutine_meets hs hM hb' trivial hA hc hP.2.1 ha₀ hP.2.2 hu hd haa
      hAccuracy.matvec hue hde hAccuracy.axpy hAccuracy.small hprec

/-- Rounded capped conjugate gradient with a carried residual product on a stored dense matrix
from the zero iterate: the matrix words are isolated, the right-hand side is read, and the
iterate, the residual, the direction and the cell of the carried residual product are written. -/
def storedRoutine : Routine RCLikeBlas.Operation CmpTst :=
  routine% [n, k] (isolated A : n * n, b : n) → (x : n, r : n, p : n, v : 1) := zeroStart

/-- For a symmetric matrix decoded from the stored words with spectrum in the window
`[a₀, a₁]`, and a cap within the precision window, the four written blocks satisfy the stable
output claim for the right-hand side read. -/
noncomputable def storedSpec (n : ℕ) (E a₀ a₁ : ℝ) : Routine.Spec ℝ :=
  spec% [m, cap] (raw, bs) → (xs, rs, ps, vs)
    requires m = n ∧
      (StoredOperator.denseMatrix n n raw)ᵀ = StoredOperator.denseMatrix n n raw ∧
      spectrum ℝ (StoredOperator.denseMatrix n n raw) ⊆ Set.Icc a₀ a₁ ∧
      (cap : ℝ) ^ 2 * Real.sqrt cap * E * (a₁ / a₀) ^ 2 ≤ 1 / 10 ^ 5
    ensures StableValues id (StoredOperator.denseMatrix n n raw) (decv id n bs) E a₀ a₁ cap
      [xs, rs, ps, vs]

/-- Rounded capped conjugate gradient on a stored matrix meets its specification under the
standard model of scalar arithmetic and the sequential rounded vector contracts: the iterate is
zeroed by its routine, then the stored rounded solver runs, each used by its judgment, and its
claim gives the stable output claim. -/
theorem storedRoutine_meets (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u)
    (hB : IsBlas1 id (Blas.seq.err u) (fun _ => True) I) (hCmp : IsCmp id I) {n : ℕ}
    (hMatvec : ScalarProducts.roundoff u n * Real.sqrt n ≤ em)
    (hAccuracy : Standard.Accuracy em u E (Blas.seq.err u) n)
    (ha₀ : 0 < a₀) (hprec : 3 * E * a₁ ≤ a₀) :
    storedRoutine.Meets I (storedSpec n E a₀ a₁) := by
  routine_intro [n', cap] (a, b, x, r, p, v) reads (raw, bs)
  obtain ⟨hn, hAT, hspec, hwindow⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hx0 : decv id n (List.replicate n (M.lit 0)) = (0 : Fin n → ℝ) := by
    have hzero' : M.lit 0 = 0 := hM.zero
    ext i
    simp [decv, vec, i.isLt, hzero']
  call (fillRoutine_meets (Tst := CmpTst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (M.lit 0) := hzero
  call (linkedSolveRoutine_meets hS hM hu hB hCmp hMatvec hAccuracy ha₀ hprec)
    [n, cap] (a, b, x, r, p, v) (pre := ⟨⟨rfl, hAT, hspec⟩, rfl, hx0, hwindow⟩)
    as m₂ hfr₂ hpos₂ (xs', rs, ps, vs) hpost
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  routine_exit
  exact stableValues_of_solve ha₀ hspec hwindow hpost

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored
