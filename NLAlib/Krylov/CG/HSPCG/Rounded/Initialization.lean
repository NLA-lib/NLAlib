/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Initialization

/-!
# Rounded zero-start preconditioned CG initialization

The residual is copied from the raw right-hand side. The direction is copied from the
actual rounded preconditioner output. The supplied decoded zero iterate is retained.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.initializeRoutine_meets` gives the total local numerical bridge.
* `NLAlib.Krylov.CG.HSPCG.Rounded.staticCost_initialize` counts its primitive calls.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has Blas1Op Op] [Has (Tagged Preconditioner OperatorOp) Op]

/-- The applied inverse preconditioner satisfies the shared rounded matvec contract at its
own operation name, with an absolute operator allowance. -/
def IsPreconditioner (dec : K → ℝ) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ) (I : Interp Op Tst K) : Prop :=
  I.Satisfies .total (Tagged.inj Preconditioner OperatorOp.matvec)
    ((matvecErrorRel dec P delta).spec (MatvecOperands n n))

omit [Has Blas1Op Op] in
/-- The exact tagged operator contract realizes every nonnegative rounded allowance.
This is the existing matvec inclusion through the preconditioner's operation tag. -/
theorem IsPreconditioner.of_exact
    {dec : K → ℝ} {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} {delta : ℝ}
    {I : Interp Op Tst K} (h : IsExactPreconditioner dec P I) (hd : 0 ≤ delta) :
    IsPreconditioner dec P delta I := by
  let : Has OperatorOp Op := Tagged.has Preconditioner
  exact IsExactMatvec.isMatvec (show IsExactMatvec dec P I from h) hd

/-- Retain a supplied zero iterate, copy the right-hand side, and initialize the two
preconditioned vectors from one actual operator application. [Saad2003, Algorithm 9.1]. -/
def initializeState : Stmt Op Tst := ops% [n] (B, X) → (X, R, Z, P) {
  call (Has.inj Blas1Op.copy) [n] (B) → (R);
  call (Tagged.inj Preconditioner OperatorOp.matvec) [n, n] (R) → (Z);
  call (Has.inj Blas1Op.copy) [n] (Z) → (P)
}

/-- Initialization as a routine: the right-hand side is read, the iterate is kept in place, the
residual, the preconditioned residual and the direction are written. -/
def initializeRoutine : Routine Op Tst :=
  routine% [n] (b : n, x : n) → (x, r : n, z : n, p : n) := initializeState

/-- At the dimension of the preconditioner, from a zero iterate, the written state has an exact
residual and direction copy and a preconditioned residual within the declared error. -/
noncomputable def initializeSpec (dec : K → ℝ) {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (delta : ℝ) : Routine.Spec K :=
  spec% [m] (bs, xs) → (xs', rs, zs, ps)
    requires m = n ∧ decv dec n xs = 0
    ensures decv dec n xs' = 0 ∧ decv dec n rs = decv dec n bs ∧
      decv dec n ps = decv dec n zs ∧
      ‖WithLp.toLp 2 (P *ᵥ decv dec n rs - decv dec n zs)‖ ≤
        delta * ‖WithLp.toLp 2 (decv dec n rs)‖

/-- Initialization meets its specification under rounded BLAS and preconditioner contracts: the
run is total, including zero right-hand sides, singular preconditioners and empty dimensions. -/
theorem initializeRoutine_meets {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {delta : ℝ} {I : Interp Op Tst K}
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hP : IsPreconditioner dec P delta I) :
    (initializeRoutine (Op := Op) (Tst := Tst)).Meets I (initializeSpec dec P delta) := by
  routine_intro [n'] (b, x, r, z, p) reads (bs, xs)
  obtain ⟨hn, hdom⟩ := hpre
  obtain rfl : n = n' := hn.symm
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs, hrs, hcopy₁⟩
  subst rs
  step hP as m₂ hfr₂ ⟨hpos₂, zs, hzs, herr⟩
  step hB.copy as m₃ hfr₃ ⟨hpos₃, ps, hps, hcopy₂⟩
  subst ps
  routine_exit
  exact ⟨hdom, rfl, rfl, herr⟩

/-- Exactly two vector copies and one tagged preconditioner application are executed. -/
noncomputable def initializeCount (n : ℕ) : Count Op Tst :=
  2 • Count.one (Has.inj Blas1Op.copy) [n] +
    Count.one (Tagged.inj Preconditioner OperatorOp.matvec) [n, n]

/-- The static evaluator counts the initializer's three calls without scalar arithmetic. -/
theorem staticCost_initialize (n b x x' r z p : ℕ) :
    stmtCost (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, z, p] =
      initializeCount n := by
  simp [initializeState, initializeCount, stmtCost, useCost, IExp.evalList, IExp.eval]
  module

/-- No allocation occurs in initialization; only the declared primitive workspaces contribute. -/
theorem staticPeak_initialize (W : Op → List ℕ → ℕ) (n b x x' r z p : ℕ) :
    stmtPeak W (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, z, p] =
      max (W (Has.inj Blas1Op.copy) [n])
        (W (Tagged.inj Preconditioner OperatorOp.matvec) [n, n]) := by
  simp [initializeState, stmtPeak, max_comm]

end NLAlib.Krylov.CG.HSPCG.Rounded
