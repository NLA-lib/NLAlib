/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Initialization
public import NLAlib.Matrix.Basic.MatvecOracle

/-!
# Functional rounded preconditioners for PCG

A fixed approximate action is not assumed linear. Its functional primitive semantics ensure
that repeated identical residuals produce the same preconditioned vector, as required by the
existing mathematical PCG run model. Its reference matrix carries any SPD assumption later.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.meets_preconditioner_oracle` transfers a local word kernel.
* `NLAlib.Krylov.CG.HSPCG.Rounded.initialize_oracle_spec` identifies the actual initial action.
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
theorem meets_preconditioner_oracle {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (h : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) AnyOperands) :
    I.Meets .total (Tagged.inj Preconditioner OperatorOp.matvec)
      ((oracleRel O).spec (MatvecOperands n n)) := by
  refine h.meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
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
      (matvecFn O.mulVec) AnyOperands) :
    IsPreconditioner id P (O.ε * specNorm P) I :=
  h.meets_matvec_error O.norm_sub_mulVec_le

variable [Has Blas1Op Op]

/-- The output vectors are exactly the zero-start vectors of the fixed approximate action.
The equality retains the computed preconditioner result, rather than replacing it by the
reference matrix product. -/
@[simps (attr := storeNF)]
def initializeOracleRel {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (O : MatvecOracle P) : BlockRel ℝ where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom _ X _ := match X with
    | [_, xs] => decv id n xs = 0
    | _ => False
  rel _ X _ Y := match X, Y with
    | [bs, _], [xs, rs, zs, ps] =>
        decodedState id n xs rs zs ps =
          ⟨0, decv id n bs, O.mulVec (decv id n bs), O.mulVec (decv id n bs)⟩
    | _, _ => False

/-- Functional preconditioner semantics and rounded BLAS contracts establish all initial
vector identities required by the mathematical PCG run, without a successful-run premise. -/
theorem initialize_oracle_spec {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) AnyOperands) :
    (initializeImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((initializeOracleRel O).spec (InitializeOperands n)) := by
  have hO := meets_preconditioner_oracle hP
  cert_intro [m] (b, x) → (x', r, z, p) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x'
  change decv id n xs = 0 at hdom
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs, hrs, hcopy₁⟩
  subst rs
  step hO as m₂ hfr₂ ⟨hpos₂, zs, hzs, heq⟩
  step hB.copy as m₃ hfr₃ ⟨hpos₃, ps, hps, hcopy₂⟩
  subst ps
  refine ⟨by simp [initializeOracleRel, hpos₃, hpos₂, hpos₁],
    [xs, bs, zs, zs], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · simp only [initializeOracleRel, decodedState, hdom, heq]

end NLAlib.Krylov.CG.HSPCG.Rounded
