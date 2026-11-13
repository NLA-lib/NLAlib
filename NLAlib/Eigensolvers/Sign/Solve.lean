/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Initialized
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Step

/-!
# Total stored-output refinement of the matrix sign program

The allocated program returns the mathematical capped Newton–Schulz result on the supplied
word matrix and parameters. Scratch separation and cleanup use shared footprint and allocation
rules. Convergence and numerical accuracy are separate mathematical results about that output.

## Main results

* `NLAlib.Sign.writes_program`: total execution with the actual stored capped sign result.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

/-- Readable matrix and parameter blocks, writable disjoint output, and the functional
operation contracts suffice for total capped execution. The returned matrix is the existing
mathematical sign algorithm on those exact words, including early stopping and cap exhaustion.
No numerical convergence or successful-run premise is assumed. -/
theorem writes_program {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IndexOp Op] [Has CmpTst Tst]
    {M : Machine K} (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hIndex : IsIndexLit M I)
    {τ : Tape K} {m : Mem K} {n cap : ℕ} {a par x : ℕ × ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) (eps b : K)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) (hl : m.Live [a, par, x])
    (hAP : Fp.Apart [a, par, x] [2 * (n * n), 2, 2 * (n * n)])
    (hA : m.store.readBlock a.1 a.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : m.store.readBlock par.1 par.2 2 = some [eps, b])
    (hx : x.2 + 2 * (n * n) ≤ m.store.len x.1) :
    Writes .total I τ (program (Has.inj MatrixOp.mul)).body
      (Env.frame [n, cap] [a, par, x]) (Store.inBlock x.1 x.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock x.1 x.2 (2 * (n * n)) =
        some ((EntryCodec.pair K).packFinMatrix
          (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal) eps b cap A))) m := by
  apply writes_allocs_readBlock
    (lens := [.const 5, .const 2 * (.var 0 * .var 0), .const 2 * (.var 0 * .var 0)])
    (ns := [5, 2 * (n * n), 2 * (n * n)]) rfl (hl x (by simp))
  intro store hlength hlens hBelow
  have ha : a.1 < m.store.length := hl a (by simp)
  have hp : par.1 < m.store.length := hl par (by simp)
  have ho : x.1 < m.store.length := hl x (by simp)
  have ht : store.len m.store.length = 5 := by simpa using hlens 0 (by simp)
  have hw : store.len (m.store.length + 1) = 2 * (n * n) := by
    simpa using hlens 1 (by simp)
  have hv : store.len (m.store.length + 2) = 2 * (n * n) := by
    simpa using hlens 2 (by simp)
  have hApart : Fp.Apart
      [a, par, x, (m.store.length + 1, 0), (m.store.length + 2, 0), (m.store.length, 0)]
      [2 * (n * n), 2, 2 * (n * n), 2 * (n * n), 2 * (n * n), 5] :=
    hAP.append (by disjoint) rfl (by disjoint)
  refine (writes_frame rfl rfl ?_ (writes_initialized (dec := dec) (mm := mm) (qr := qr)
    (unif := unif) (normal := normal) hS hC hMM hIndex A eps b h01
    (by room) hApart (by kept) (by kept) (by room) (by room) (by room) (by room))).mono
    (by fp_sub) (fun _ _ h => h)
  room

end NLAlib.Sign
