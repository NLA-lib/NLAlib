/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Matrix
public import NLAlib.Ops.Logic.Functional

/-!
# Matrix kernel calls in mathematical form

Routines operate on matrices decoded from the actual stored input blocks. The shared
functional call rule writes the exact packed results and frames all other cells. Clients do
not unfold execution or recover identical outputs from graph-relation witnesses.

## Main results

* `NLAlib.Ops.writes_matrixMul` executes rectangular multiplication, permitting input/output alias.
* `NLAlib.Ops.writes_matrixQR` executes full QR with disjoint output blocks.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K E Op Tst : Type} [Inhabited K] [Has MatrixOp Op]
  {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {μ : Mem K}

/-- A multiplication call writes its word-level routine's exact packed result. Both inputs
are read before the output is written, so input/output overlap is allowed. -/
theorem writes_matrixMul {C : EntryCodec K E}
    {mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E} (hI : IsMatrixMul C mm I)
    {ds : List IExp} {ins outs : List Operand} {l m n : ℕ} {a b c : ℕ × ℕ} {as bs : List K}
    (hd : IExp.evalList ρ.idx ds = some [l, m, n])
    (ha : Operand.evalList ρ ins = some [a, b]) (hb : Operand.evalList ρ outs = some [c])
    (hl : μ.Live [a, b, c])
    (hA : μ.store.readBlock a.1 a.2 (m * l * C.width) = some as)
    (hB : μ.store.readBlock b.1 b.2 (n * m * C.width) = some bs)
    (hC : c.2 + n * l * C.width ≤ μ.store.len c.1) :
    Writes .total I τ (.call (Has.inj MatrixOp.mul) ds ins outs) ρ
      (Store.inBlock c.1 c.2 (n * l * C.width))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock c.1 c.2 (n * l * C.width) =
        some (C.packFinMatrix (mm (C.matrix l m as) (C.matrix m n bs)))) μ := by
  exact writes_call_fn1 hI (xs := [as, bs]) hd ha hb rfl rfl trivial hl
    (by simp [Mem.readBlocks, matrixMulFn, hA, hB]) rfl (by simp) hC

/-- A full QR call writes both factors of the same routine on its actual stored matrix.
Only the two output blocks must be disjoint; either may overlap the input. -/
theorem writes_matrixQR {C : EntryCodec K E}
    {qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E} (hI : IsMatrixQR C qr I)
    {ds : List IExp} {ins outs : List Operand} {m n : ℕ} {a q r : ℕ × ℕ} {as : List K}
    (hd : IExp.evalList ρ.idx ds = some [m, n])
    (ha : Operand.evalList ρ ins = some [a]) (hb : Operand.evalList ρ outs = some [q, r])
    (hl : μ.Live [a, q, r])
    (hA : μ.store.readBlock a.1 a.2 (n * m * C.width) = some as)
    (hQR : Fp.Disj (Store.inBlock q.1 q.2 (m * m * C.width))
      (Store.inBlock r.1 r.2 (n * m * C.width)))
    (hQ : q.2 + m * m * C.width ≤ μ.store.len q.1)
    (hR : r.2 + n * m * C.width ≤ μ.store.len r.1) :
    Writes .total I τ (.call (Has.inj MatrixOp.qr) ds ins outs) ρ
      (Store.inBlock q.1 q.2 (m * m * C.width) ⊔ Store.inBlock r.1 r.2 (n * m * C.width))
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.store.readBlock q.1 q.2 (m * m * C.width) =
          some (C.packFinMatrix (qr (C.matrix m n as)).1) ∧
        μ'.store.readBlock r.1 r.2 (n * m * C.width) =
          some (C.packFinMatrix (qr (C.matrix m n as)).2)) μ := by
  exact writes_call_fn2 hI (xs := [as]) hd ha hb rfl rfl trivial hQR hl
    (by simp [Mem.readBlocks, matrixQRFn, hA]) rfl (by simp) (by simp) hQ hR

end NLAlib.Ops
