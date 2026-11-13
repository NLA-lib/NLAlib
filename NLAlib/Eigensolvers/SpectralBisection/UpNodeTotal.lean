/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNodeSplit

/-!
# Total upward assembly of an arbitrary mathematical node outcome

The actual stored node constructor chooses the reconstruction. Only occupied child results
are needed. The returned ordinary matrix/eigenvalue pair is exactly the assembly used by the
existing pure recursive bisection algorithm.

## Main results

* `NLAlib.SpectralBisection.writes_upNode`: actual execution returns mathematical assembly.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Any stored node outcome reconstructs its mathematical result from the occupied child
results. Explicit metadata exactness, capacities, arena separation and actual scalar/matrix
operation contracts suffice for total execution; no successful-run or numerical-quality
premise is assumed. -/
theorem writes_upNode {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {m : Mem K}
    {n d lo k : ℕ} {R : K} {ma ua qa ea sz kd kp t : ℕ × ℕ} (step : EighStep K k)
    (children : (b : Bool) →
      Matrix (Fin (step.childSize b)) (Fin (step.childSize b)) (K × K) ×
        (Fin (step.childSize b) → K))
    (hStep : StoresStep M R n d lo ma ua qa ea sz kd kp step m)
    (hChildren : ∀ b, step.HasChild b →
      StoresResult n (d + 1) (step.childSlot lo b) ua ea (children b) m.store)
    (hLit : IsExactNatLit dec M (max n 4)) (hk : k ≤ n)
    (hl : m.Live [ua, qa, ea, kd, kp, t])
    (ht : m.store.get t.1 t.2 = some (M.div R (M.lit 2)) ∧
      m.store.get t.1 (t.2 + 1) = some (M.neg (M.div R (M.lit 2))))
    (hroom : m.Room (resultOperands n d lo ua ea) (resultLengths k))
    (hap : Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n k)) :
    Writes .total I τ (upNodeImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d, lo, k] [ua, qa, ea, kd, kp, t])
      (Fp.blocks (resultOperands n d lo ua ea) (resultLengths k))
      (fun m' => m'.pos = m.pos ∧ StoresResult n d lo ua ea
        (step.assemble (M.toFloatMachine dec mm qr unif normal) children) m'.store) m := by
  cases step with
  | leaf U values =>
    simpa only [EighStep.assemble] using writes_upNode_leaf hQ U values
      (by simpa using hLit 1 (by omega)) hStep
  | shift side A sigma =>
    simpa only [EighStep.assemble, EighStep.childSize, Machine.toFloatMachine] using
      writes_upNode_shiftResult (k := k) hS hQ (children side) hStep
        (by simpa only [EighStep.childSlot, EighStep.childSize] using hChildren side rfl)
        hLit hk hl ht hroom hap
  | split r hr Qp Qm Ap Am sigma =>
    simpa only [EighStep.assemble, EighStep.childSize, Machine.toFloatMachine] using
      writes_upNode_splitResult (r := r) hS hQ mm hMM (children true) (children false) hStep
        (by simpa only [EighStep.childSlot, EighStep.childSize] using hChildren true trivial)
        (by simpa only [EighStep.childSlot, EighStep.childSize] using hChildren false trivial)
        hLit hk hl ht.1 hroom hap

end NLAlib.SpectralBisection
