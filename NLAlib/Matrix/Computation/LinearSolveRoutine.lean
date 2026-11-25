/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Triangular
public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Perturbation.LinearSolveErr

/-!
# Linear solve routines: the execution certificate

`NLAlib.Computation.IsLinearSolveRoutine` records successful execution of an in-place linear
solve, its exact output block write and the decoded backward error `NLAlib.IsLinearSolveErr`.
The scalar-loop lower triangular solve is an instance. Its certificate uses the standard
relative-error model with every real value in range; no finite-range claim follows.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.IsLinearSolveRoutine`: the execution certificate of a linear solve.

## Main results

* `NLAlib.Computation.IsLinearSolveRoutine.mono`: larger backward error allowances.
* `NLAlib.Computation.IsLinearSolveRoutine.toBlockRoutine`: the certified footprint.
* `NLAlib.Computation.IsRelErrSem.isLinearSolveRoutine_trsvLower`: the actual lower solve.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A certified linear solve for a real matrix $\mathbf{T}$ with componentwise backward
allowance $\eta$: from any state satisfying `pre` whose block at (`xb`, `xo`) holds
$\mathbf{b}$ and is writable, the routine succeeds, writes only that block, and its decoded
solution meets `NLAlib.IsLinearSolveErr`. Scratch storage is scoped; counts, tape positions
and peak memory are not constrained by this certificate. -/
structure IsLinearSolveRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (η : ℝ) (pre : Store P K → Prop)
    (xb : ℕ) (xo : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The routine composes with its continuation. -/
  composable : ExecutionComposable I routine
  /-- Readable inputs and writable outputs imply execution, its frame and backward error. -/
  run : ∀ (st : St P K C) (b : Fin N → ℝ), pre st.store →
    ReadsDecoded st.store dec tag xb xo.eval b → Writable st.store tag xb xo.eval N →
    ∃ (out : St P K C) (W : Fin N → K), exec I routine.run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store ∧
      IsLinearSolveErr η T b (fun i => dec tag (W i))

variable {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {T : Matrix (Fin N) (Fin N) ℝ} {η η' : ℝ} {pre : Store P K → Prop}
    {xb : ℕ} {xo : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}

/-- A certified linear solve remains certified when its componentwise backward allowance
increases from $\eta$ to $\eta'$. -/
theorem IsLinearSolveRoutine.mono
    (h : IsLinearSolveRoutine I dec tag T η pre xb xo routine) (hη : η ≤ η') :
    IsLinearSolveRoutine I dec tag T η' pre xb xo routine where
  composable := h.composable
  run st b hp hb hw := by
    obtain ⟨out, W, hr, hs, he⟩ := h.run st b hp hb hw
    exact ⟨out, W, hr, hs, he.mono hη⟩

/-- The footprint of a certified linear solve: a readable right-hand side and the backend
precondition imply a successful run whose only net store effect is one output block write. -/
theorem IsLinearSolveRoutine.toBlockRoutine
    (h : IsLinearSolveRoutine I dec tag T η pre xb xo routine) :
    IsBlockRoutine I tag
      (fun s => pre s ∧ ∃ b : Fin N → ℝ, ReadsDecoded s dec tag xb xo.eval b)
      [(xb, xo.eval, N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨hp, b, hb⟩ := hp
    obtain ⟨out, W, hr, hs, -⟩ := h.run st b hp hb (hw _ List.mem_cons_self)
    exact ⟨out, [Array.ofFn W], hr, Store.writeBlocks_singleton_eq_some_iff.mpr ⟨by simp, hs⟩⟩

/-- The actual lower triangular solve is a certified linear solve. For a real lower triangular
$N\times N$ matrix $\mathbf{T}$ with nonzero diagonal stored column-major in a block disjoint
from the right-hand side, the standard relative-error model with all values in range and
$u_p<1$ gives successful execution and componentwise backward allowance
$(1-u_p)^{-N}-1$. The source matrix block is retained, including when it shares a buffer with
the disjoint right-hand side block. [Higham2002, Theorem 8.5]. -/
theorem IsRelErrSem.isLinearSolveRoutine_trsvLower
    {u : P → ℝ} (I : Interp P ι K C) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (tOff xo : IExp ℕ) (hu : u tag < 1)
    (hdis : blockDisjoint (matrix, tOff.eval, N * N) (xb, xo.eval, N) = true) :
    IsLinearSolveRoutine I dec tag T (roundingFactor N (u tag))
      (fun store => HoldsDecoded store dec tag matrix tOff.eval T) xb xo
      (trsvLower tag (.const N) matrix tOff xb xo) where
  composable := executionComposable_single I (fun _ => rfl)
  run st b hp hb _ := by
    have hxT : xb = matrix → xo.eval + N ≤ tOff.eval ∨
        tOff.eval + N * N ≤ xo.eval := by
      intro heq
      have hd := blockDisjoint_iff.mp hdis
      by_cases hN : N = 0
      · simpa only [hN, Nat.zero_mul, Nat.add_zero] using le_total xo.eval tOff.eval
      · subst xb
        rcases hd with hd | hd | hd | hd | hd
        · exact (hd rfl).elim
        · exact (Nat.mul_ne_zero hN hN hd).elim
        · exact (hN hd).elim
        · exact Or.inr hd
        · exact Or.inl hd
    obtain ⟨out, W, hr, hs, ΔT, hΔ, heq⟩ :=
      h.exec_trsvLower_add_mulVec_eq I tag st (.const N) matrix tOff xb xo T hT hd b hu
        (fun i j _ => hp i j) hb hxT
    refine ⟨out, fun i => W i, hr, ?_,
      ⟨ΔT, by simpa only [Real.norm_eq_abs, IExp.eval_const] using hΔ, heq⟩⟩
    convert hs using 1
    congr 1
    apply Array.ext (by simp)
    intro i hi hj
    simp

end NLAlib.Computation
