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
      (matvecFn O.mulVec) (MatvecOperands n n)) :
    I.Meets .total (Tagged.inj Preconditioner OperatorOp.matvec)
      ((oracleRel O).spec (MatvecOperands n n)) := by
  refine h.meets_rel (fun _ _ _ h => h) rfl rfl (fun _ => rfl)
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
  h.meets_matvec_error_of_admission (fun _ _ _ h => h) O.norm_sub_mulVec_le

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
      (matvecFn O.mulVec) (MatvecOperands n n)) :
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

/-- The zero-start initializer stores the exact initial four-vector state of the fixed
approximate oracle action. Its raw input buffers are the right-hand side and zero iterate;
no computed preconditioner output or execution-success premise is supplied by the caller. -/
theorem initialize_oracle_writes {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    {τ : Tape ℝ} {μ : Mem ℝ} {b x r z p : ℕ × ℕ} {bs xs : List ℝ}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv id n xs = 0)
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ initializeState (Env.frame [n] [b, x, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState id n x r z p
        ⟨0, decv id n bs, O.mulVec (decv id n bs), O.mulVec (decv id n bs)⟩ μ') μ := by
  have hl' : μ.Live ([b, x] ++ [x, r, z, p]) := by
    change μ.Live [b, x, x, r, z, p]
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine ((initialize_oracle_spec hB hok hP).writes_blocks rfl
    ⟨rfl, b, x, r, z, p, rfl, rfl, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩
    hl' (Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hxs rfl)) hx0
    hz (by disjoint)).mono le_rfl ?_
  rintro μ' _ ⟨hpos, ys, hread, hrel⟩
  obtain ⟨xs', rs, zs, ps, rfl⟩ := List.length_eq_four.mp
    (by simpa [initializeOracleRel] using
      congrArg List.length (Mem.map_length_of_readBlocks hread))
  exact ⟨by simpa [initializeOracleRel] using hpos, xs', rs, zs, ps, hread, hrel⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
