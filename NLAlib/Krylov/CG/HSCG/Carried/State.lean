/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Exact
public import NLAlib.Krylov.CG.Math.Recurrence

/-!
# Stored state for exact CG with a retained residual product

The four-block invariant supports composition of certified rounds and the early-exit loop.
It records readable state blocks, their exact mathematical state and the retained self-product.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.StoresState` is the state invariant.
* `NLAlib.Krylov.CG.HSCG.Carried.step_writes` advances it through the certified round.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The readable state blocks decode to the given CG state and retain its residual product. -/
def StoresState (dec : K → ℝ) (n : ℕ) (x r p v : ℕ × ℕ)
    (s : CGState ℝ (Fin n)) (μ : Mem K) : Prop :=
  ∃ xs rs ps rr, μ.readBlocks [x, r, p, v] [n, n, n, 1] = some [xs, rs, ps, [rr]] ∧
    decodedState dec n xs rs ps = s ∧ dec rr = decv dec n rs ⬝ᵥ decv dec n rs

/-- A certified active round advances the state and its retained residual product, with no
unfolding of the round implementation. -/
theorem step_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    {τ : Tape K} {μ : Mem K} {x r p v : ℕ × ℕ} {s : CGState ℝ (Fin n)}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v]) (hs : StoresState dec n x r p v s μ)
    (hnb : Nonbreakdown A s) (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ step (Env.frame [n] [x, r, p, v, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p v (cgStep A s) μ') μ := by
  obtain ⟨xs, rs, ps, rr, hread, he, hv⟩ := hs
  have hl' := (μ.live_append _ _).mpr (And.intro hl hl)
  have hpre : (((stepRel dec A).spec (StepOperands n)).on .total [n]
      [x, r, p, v] [x, r, p, v] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, x, r, p, v, rfl, rfl, hxr, hxp, hxv, hrp, hrv, hpv⟩,
      fun _ => ⟨hl', ⟨[xs, rs, ps, [rr]], hread,
        by simpa only [stepRel_dom, he] using And.intro hnb hv⟩, hz⟩⟩
  refine ((step_spec hS hM hB hA).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, ys, hlen, hrel, rfl⟩
  obtain rfl : X = [xs, rs, ps, [rr]] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨xs', rs', ps', vs, rfl⟩ := List.length_eq_four.mp
    (show ys.length = 4 by simpa using congrArg List.length hlen)
  obtain ⟨rr', rfl⟩ := List.length_eq_one_iff.mp
    (show vs.length = 1 by simpa using congrArg (fun ns => ns.getD 3 0) hlen)
  have hap : Fp.Apart [x, r, p, v] [n, n, n, 1] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (ys := [xs', rs', ps', [rr']])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  refine ⟨by simp [stepRel], xs', rs', ps', rr', by simpa [stepRel] using hout, ?_⟩
  simpa only [stepRel_rel, he] using hrel

end NLAlib.Krylov.CG.HSCG.Carried
