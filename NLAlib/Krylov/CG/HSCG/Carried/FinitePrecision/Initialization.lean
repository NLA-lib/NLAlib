/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Bounds

/-!
# Zero-start initialization for rounded conjugate gradient

The caller supplies a decoded zero iterate. Exact vector copies establish the residual and
search direction, and a rounded self-dot supplies the retained residual product. No rounded
addition to the right-hand side intervenes, so the existing zero-start CG run model applies.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.initialize_spec` certifies the three initialization calls.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has Blas1Op Op]

/-- A zero iterate is retained while exact copies initialize the two other vectors and a
rounded self-dot initializes the scalar cache. [HestenesStiefel1952, (3:1)]. -/
def initializeState : Stmt Op Tst := ops% [n] (B, X) → (X, R, P, rho) {
  call (Has.inj Blas1Op.copy) [n] (B) → (R);
  call (Has.inj Blas1Op.copy) [n] (B) → (P);
  call (Has.inj Blas1Op.dot) [n] (R, R) → (rho)
}

/-- The initializer reads two blocks and outputs the four carried state blocks. -/
def initializeImpl : Impl Op Tst := ⟨1, 2, 4, initializeState⟩

/-- The initial vectors are exactly the zero-start mathematical state; the retained scalar
satisfies the same rounded dot-product contract as later rounds. -/
@[simps (attr := storeNF)]
noncomputable def initializeRel (dec : K → ℝ) (ed : ℝ) (n : ℕ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  dom _ X _ := match X with
    | [_, xs] => decv dec n xs = 0
    | _ => False
  rel _ X _ Y := match X, Y with
    | [bs, _], [xs, rs, ps, [rr]] =>
        decodedState dec n xs rs ps = ⟨0, decv dec n bs, decv dec n bs⟩ ∧
        IsDotErr dec ed n (vec rs) (vec rs) rr
    | _, _ => False

/-- Rounded BLAS contracts establish exact initial vectors and the computed residual-cache
error; this total certificate includes zero right-hand sides and empty dimensions. -/
theorem initialize_spec {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {I : Interp Op Tst K} (hB : IsBlas1 dec ε ok I) (hok : ok n) :
    (initializeImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((initializeRel dec (ε.dot n) n).spec (Carried.SolveOperands n)) := by
  cert_intro [m] (b, x) → (x', r, p, v) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbp, hbv, hxr, hxp, hxv, hrp, hrv, hpv⟩ := hadm
  subst m x'
  change decv dec n xs = 0 at hdom
  step hB.copy as m₁ hfr₁ ⟨hpos₁, rs, hrs, hcopy₁⟩
  subst rs
  step hB.copy as m₂ hfr₂ ⟨hpos₂, ps, hps, hcopy₂⟩
  subst ps
  step hB.dot as m₃ hfr₃ ⟨hpos₃, rr, hrr, herr⟩
  refine ⟨by simp [initializeRel, hpos₃, hpos₂, hpos₁], [xs, bs, bs, [rr]], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · exact ⟨by simp only [decodedState, hdom], herr⟩

/-- The initializer's abstract operation count is two copies and one dot product. -/
noncomputable def initializeCount (n : ℕ) : Count Op Tst :=
  2 • Count.one (Has.inj Blas1Op.copy) [n] + Count.one (Has.inj Blas1Op.dot) [n]

/-- Initialization performs no allocations beyond those of its operation implementations. -/
def initializePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (W (Has.inj Blas1Op.copy) [n]) (W (Has.inj Blas1Op.dot) [n])

/-- Static evaluation computes exactly the three initialization calls. -/
theorem staticCost_initialize (n b x x' r p v : ℕ) :
    stmtCost (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, p, v] =
      initializeCount n := by
  simp [initializeState, initializeCount, stmtCost, useCost, IExp.evalList, IExp.eval]
  module

/-- The caller's four state buffers require no initialization scratch allocation. -/
theorem staticPeak_initialize_le (W : Op → List ℕ → ℕ) (n b x x' r p v : ℕ) :
    stmtPeak W (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, p, v] ≤
      initializePeak W n := by
  simp [initializeState, stmtPeak, initializePeak]

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
