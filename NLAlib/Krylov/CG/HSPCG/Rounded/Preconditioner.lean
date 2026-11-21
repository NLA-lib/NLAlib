/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.Initialization
public import NLAlib.Matrix.Basic.MatvecOracle

/-!
# Functional rounded preconditioners for PCG

A fixed approximate action is not assumed linear. Its functional primitive semantics ensure
that repeated identical residuals produce the same preconditioned vector, as required by the
existing mathematical PCG run model. Its reference matrix carries any SPD assumption later.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.satisfies_preconditioner_oracle` transfers a local word kernel.
* `NLAlib.Krylov.CG.HSPCG.Rounded.initializeRoutine_meets_oracle` identifies the actual initial
  action.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops

variable {Op Tst : Type} [Has (Tagged Preconditioner OperatorOp) Op]

/-- The real-word output is the specified approximate preconditioner action, which may be
nonlinear; its normwise accuracy is supplied by the existing oracle structure. -/
@[simps (attr := storeNF)]
def oracleRel {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (O : MatvecOracle P) : BlockRel ℝ where
  nd := 2
  inLens d := [d.getD 1 0]
  outLens d := [d.headD 0]
  rel _ X _ Y := match X, Y with
    | [xs], [ys] => decv id n ys = O.mulVec (decv id n xs)
    | _, _ => False

/-- A primitive implemented by the actual fixed oracle function satisfies its local output
contract. This premise specifies only one tagged matrix-vector call, not a solver run. -/
theorem satisfies_preconditioner_oracle {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (h : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) :
    I.Satisfies .total (Tagged.inj Preconditioner OperatorOp.matvec)
      ((oracleRel O).spec (MatvecOperands n n)) := by
  refine h.satisfies_rel (fun _ _ _ h => h) rfl rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_
  intro d w X μ ins outs hnd hw hadm hr hdom
  obtain ⟨rfl, -⟩ := hadm
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  exact ⟨[List.ofFn (O.mulVec (decv id n xs))], by simp [matvecFn, BlockFn.of1]; rfl,
    by simp [oracleRel], decv_ofFn _⟩

/-- The same functional tagged primitive satisfies the rounded normwise preconditioner
contract with the oracle's relative tolerance and reference matrix norm. -/
theorem isPreconditioner_of_oracle {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (h : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) :
    IsPreconditioner id P (O.ε * specNorm P) I :=
  h.satisfies_matvec_error_of_admission (fun _ _ _ h => h) O.norm_sub_mulVec_le

variable [Has Blas1Op Op]

/-- At the dimension of the preconditioner, from a zero iterate, the written state is the
zero-start state of the fixed approximate action: the computed preconditioner result, not the
reference matrix product. The routine is `NLAlib.Krylov.CG.HSPCG.Rounded.initializeRoutine`. -/
def initializeOracleSpec {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (O : MatvecOracle P) :
    Routine.Spec ℝ :=
  spec% [m] (bs, xs) → (xs', rs, zs, ps)
    requires m = n ∧ decv id n xs = 0
    ensures decodedState id n xs' rs zs ps =
      ⟨0, decv id n bs, O.mulVec (decv id n bs), O.mulVec (decv id n bs)⟩

/-- Initialization meets the specification of the fixed approximate action: functional
preconditioner semantics and rounded BLAS contracts establish all initial vector identities
required by the mathematical PCG run, without a successful-run premise. -/
theorem initializeRoutine_meets_oracle {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n)) :
    (initializeRoutine (Op := Op) (Tst := Tst)).Meets I (initializeOracleSpec O) := by
  routine_intro [n'] (b, x, r, z, p) reads (bs, xs)
  obtain ⟨hn, hdom⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hO := satisfies_preconditioner_oracle hP
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs, hrs, hcopy₁⟩
  subst rs
  step hO as m₂ hfr₂ ⟨hpos₂, zs, hzs, heq⟩
  step hB.copy as m₃ hfr₃ ⟨hpos₃, ps, hps, hcopy₂⟩
  subst ps
  routine_exit
  change decodedState id n xs bs zs zs =
    ⟨0, decv id n bs, O.mulVec (decv id n bs), O.mulVec (decv id n bs)⟩
  simp only [decodedState, hdom, heq]

end NLAlib.Krylov.CG.HSPCG.Rounded
