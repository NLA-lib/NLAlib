/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.Solve
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Rounded preconditioned conjugate gradient from the zero iterate

`NLAlib.Krylov.CG.HSPCG.Rounded.zeroStartRoutine` reads the right-hand side and writes the
iterate, the residual, the preconditioned residual and the direction: it fills the iterate with
literal zeros and runs the capped rounded solver
(`NLAlib.Krylov.CG.HSPCG.Rounded.solveRoutine`). Its specification states, on the written
blocks, that they are a prefix of a rounded preconditioned run
(`NLAlib.Krylov.CG.HSPCG.Rounded.PrefixValues`).

## Main definitions

* `NLAlib.Krylov.CG.HSPCG.Rounded.zeroStartRoutine`,
  `NLAlib.Krylov.CG.HSPCG.Rounded.zeroStartSpec`: the routine and its specification.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.zeroStartRoutine_meets`: the routine meets its
  specification.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op] [Has CmpTst Tst]

/-- Rounded preconditioned conjugate gradient from the zero iterate: the right-hand side is read,
and the iterate, the residual, the preconditioned residual and the direction are written. The tree
fills the iterate and then runs the solver on it. -/
def zeroStartRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n) → (x : n, r : n, z : n, p : n) := zeroStart

/-- For the order `n` and a cap within the precision window, the written blocks are a prefix of
the rounded preconditioned run for the right-hand side read. -/
noncomputable def zeroStartSpec {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (O : MatvecOracle P)
    (e a a' p p' : ℝ) : Routine.Spec ℝ :=
  spec% [m, cap] (bs) → (xs, rs, zs, ps)
    requires m = n ∧ e * (1024 * (a' / a) * (p' / p)) ^ (cap + 1) ≤ 1 / 2
    ensures PrefixValues A P O (decv id n bs) e cap [xs, rs, zs, ps]

/-- Rounded preconditioned conjugate gradient from the zero iterate meets its specification:
literal-zero initialization and raw spectral precision give the capped rounded prefix. The
right-hand side may be zero; no successful execution or computed-trajectory assumption is
required. -/
theorem zeroStartRoutine_meets {F : Machine ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hS : IsScalar F I) (hF : StdModel u id F) (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    (hCmp : IsCmp id I) (hAT : Aᵀ = A) (hPT : Pᵀ = P) {a a' p p' : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hAs : spectrum ℝ A ⊆ Set.Icc a a') (hPs : spectrum ℝ P ⊆ Set.Icc p p')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e)
    (he : e ≤ 1 / 100) (hOe : O.ε ≤ e)
    (hAp : 6 * e * a' ≤ a) (hPp : 6 * e * p' ≤ p) :
    (zeroStartRoutine (Op := Op) (Tst := Tst)).Meets I (zeroStartSpec A P O e a a' p p') := by
  routine_intro [n', cap] (b, x, r, z, v) reads (bs)
  obtain ⟨hn, hwindow⟩ := hpre
  obtain rfl : n = n' := hn.symm
  call (fillRoutine_meets (Tst := Tst) (hS (.lit 0))) [n] (x) as ν hfr hpos (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (F.lit 0) := hzero
  have hx0 : decv id n (List.replicate n (F.lit 0)) = 0 := by
    have hz0 : F.lit 0 = 0 := hF.zero
    ext i
    simp [decv, vec, i.isLt, hz0]
  call (solveRoutine_meets (Tst := Tst) hS hF hB hok hA hP hD hCmp hAT hPT ha hp hAs hPs
    hu hd haa hem hue hde hae he hOe hAp hPp) [n, cap] (b, x, r, z, v)
    (pre := ⟨rfl, hx0, hwindow⟩) as ν₂ hfr₂ hpos₂ (xs, rs, zs, ps) hpost
  routine_exit
  exact hpost

end NLAlib.Krylov.CG.HSPCG.Rounded
