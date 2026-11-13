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

* `NLAlib.Krylov.CG.HSPCG.Rounded.initialize_spec` gives the total local numerical bridge.
* `NLAlib.Krylov.CG.HSPCG.Rounded.initialize_writes` exposes the actual stored state.
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
  I.Meets .total (Tagged.inj Preconditioner OperatorOp.matvec)
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

/-- Initialization reads two blocks and outputs the four PCG state blocks. -/
def initializeImpl : Impl Op Tst := ⟨1, 2, 4, initializeState⟩

/-- The actual four-state output has an exact initial residual and direction copy, while
its preconditioned residual retains the declared primitive error. -/
@[simps (attr := storeNF)]
noncomputable def initializeRel (dec : K → ℝ) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom _ X _ := match X with
    | [_, xs] => decv dec n xs = 0
    | _ => False
  rel _ X _ Y := match X, Y with
    | [bs, _], [xs, rs, zs, ps] =>
        decv dec n xs = 0 ∧ decv dec n rs = decv dec n bs ∧
        decv dec n ps = decv dec n zs ∧
        ‖WithLp.toLp 2 (P *ᵥ decv dec n rs - decv dec n zs)‖ ≤
          delta * ‖WithLp.toLp 2 (decv dec n rs)‖
    | _, _ => False

/-- Rounded BLAS and preconditioner contracts initialize PCG totally, including zero
right-hand sides, singular preconditioners and empty dimensions. -/
theorem initialize_spec {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {delta : ℝ} {I : Interp Op Tst K}
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hP : IsPreconditioner dec P delta I) :
    (initializeImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((initializeRel dec P delta).spec (InitializeOperands n)) := by
  cert_intro [m] (b, x) → (x', r, z, p) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x'
  change decv dec n xs = 0 at hdom
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs, hrs, hcopy₁⟩
  subst rs
  step hP as m₂ hfr₂ ⟨hpos₂, zs, hzs, herr⟩
  step hB.copy as m₃ hfr₃ ⟨hpos₃, ps, hps, hcopy₂⟩
  subst ps
  refine ⟨by simp [initializeRel, hpos₃, hpos₂, hpos₁], [xs, bs, zs, zs], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · exact ⟨hdom, rfl, rfl, herr⟩

/-- Initialization establishes the actual stored four-vector state and its preconditioner
error. No execution-success hypothesis or computed answer is supplied by the caller. -/
theorem initialize_writes {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {delta : ℝ} {I : Interp Op Tst K}
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hP : IsPreconditioner dec P delta I)
    {τ : Tape K} {μ : Mem K} {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ initializeState (Env.frame [n] [b, x, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ zs, StoresState dec n x r z p
        ⟨0, decv dec n bs, zs, zs⟩ μ' ∧
        ‖WithLp.toLp 2 (P *ᵥ decv dec n bs - zs)‖ ≤
          delta * ‖WithLp.toLp 2 (decv dec n bs)‖) μ := by
  have hread : μ.readBlocks [b, x] [n, n] = some [bs, xs] :=
    Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hxs rfl)
  have hl' : μ.Live ([b, x] ++ [x, r, z, p]) := by
    change μ.Live [b, x, x, r, z, p]
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  have hpre : (((initializeRel dec P delta).spec (InitializeOperands n)).on .total [n]
      [b, x] [x, r, z, p] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, b, x, r, z, p, rfl, rfl, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩,
      fun _ => ⟨hl', ⟨[bs, xs], hread, hx0⟩, hz⟩⟩
  refine ((initialize_spec hB hok hP).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, ys, hlen, hrel, rfl⟩
  obtain rfl : X = [bs, xs] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨xs', rs, zs, ps, rfl⟩ := List.length_eq_four.mp
    (show ys.length = 4 by simpa using congrArg List.length hlen)
  have hap : Fp.Apart [x, r, z, p] [n, n, n, n] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (ys := [xs', rs, zs, ps])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  change decv dec n xs' = 0 ∧ decv dec n rs = decv dec n bs ∧
    decv dec n ps = decv dec n zs ∧ _ at hrel
  refine ⟨by simp [initializeRel], decv dec n zs,
    ⟨xs', rs, zs, ps, by simpa [initializeRel] using hout, ?_⟩, ?_⟩
  · simp only [decodedState, hrel.1, hrel.2.1, hrel.2.2.1]
  · simpa only [hrel.2.1] using hrel.2.2.2


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

/-- The same total initialization run has exactly three abstract primitive calls and the
stated scratch bound. The postcondition concerns its actual output memory. -/
theorem runs_initialize {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {delta : ℝ} {I : Interp Op Tst K}
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hP : IsPreconditioner dec P delta I)
    (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    ConditionalRuns I W τ initializeState (Env.frame [n] [b, x, x, r, z, p]) μ
      (initializeCount n)
      (max (W (Has.inj Blas1Op.copy) [n])
        (W (Tagged.inj Preconditioner OperatorOp.matvec) [n, n]))
      ((initializeRel dec P delta).Post [n] [bs, xs] [x, r, z, p] [] μ) := by
  have hl' : μ.Live ([b, x] ++ [x, r, z, p]) := by
    change μ.Live [b, x, x, r, z, p]
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine ((initialize_spec hB hok hP).runs_rel W (d := [n]) (ins := [b, x])
    (outs := [x, r, z, p]) rfl
    ⟨rfl, b, x, r, z, p, rfl, rfl, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩
    hl' (Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hxs rfl)) hx0 hz).mono
      (le_of_eq (staticCost_initialize ..)) (le_of_eq (staticPeak_initialize ..)) ?_
  intro μ' h
  exact h

end NLAlib.Krylov.CG.HSPCG.Rounded
