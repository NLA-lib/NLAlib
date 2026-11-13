/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Matrix

/-!
# Matrix kernel calls on actual stored matrices

A matrix multiplication or QR call is one mathematical routine application. The generic
functional call rules recover its packed outputs, frame and tape position; callers need only
their actual input reads, live handles and output capacity. No numerical accuracy of the
routine is assumed by these functional execution statements.

## Main results

* `NLAlib.Ops.writes_matrixMul_packFinMatrix`: packed product of the actual stored input matrices.
* `NLAlib.Ops.writes_matrixQR_packFinMatrix`: packed factors of the actual stored input matrix.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The leading columns of a packed column-major matrix form a contiguous readable block.
This is a storage consequence, requiring no arithmetic or matrix primitive contract. -/
theorem Store.readBlock_packFinMatrix_columns {K E : Type} (C : EntryCodec K E)
    {s : Store K} {b off rows cols count : ℕ} {A : Matrix (Fin rows) (Fin cols) E}
    (h : s.readBlock b off (cols * rows * C.width) = some (C.packFinMatrix A))
    (hc : count ≤ cols) :
    s.readBlock b off (count * rows * C.width) =
      some (C.packFinMatrix (A.submatrix id (Fin.castLE hc))) := by
  have hs := Store.readBlock_sub h (o := 0) (n := count * rows * C.width)
    (by simpa using Nat.mul_le_mul_right C.width (Nat.mul_le_mul_right rows hc))
  simpa only [Nat.add_zero, List.drop_zero, C.take_packFinMatrix A hc] using hs

variable {K E Op Tst : Type} [Inhabited K] [Has MatrixOp Op]
  {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-- A matrix multiplication call writes the supplied routine's result on the actual stored
matrices and preserves every other cell. Complete input blocks are read before writing, so
input/output buffers may alias; live handles and sufficient output capacity are explicit. -/
theorem writes_matrixMul_packFinMatrix (C : EntryCodec K E)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E →
      Matrix (Fin l) (Fin n) E) (hI : IsMatrixMul C mm I)
    {l k n : ℕ} (A : Matrix (Fin l) (Fin k) E) (B : Matrix (Fin k) (Fin n) E)
    {ds : List IExp} {ins outs : List Operand} {x y z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some [l, k, n])
    (ha : Operand.evalList ρ ins = some [x, y])
    (hb : Operand.evalList ρ outs = some [z]) (hl : m.Live [x, y, z])
    (hA : m.store.readBlock x.1 x.2 (k * l * C.width) = some (C.packFinMatrix A))
    (hB : m.store.readBlock y.1 y.2 (n * k * C.width) = some (C.packFinMatrix B))
    (hz : z.2 + n * l * C.width ≤ m.store.len z.1) :
    Writes md I τ (.call (Has.inj MatrixOp.mul) ds ins outs) ρ
      (Store.inBlock z.1 z.2 (n * l * C.width))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 (n * l * C.width) =
        some (C.packFinMatrix (mm A B))) m := by
  simpa only [EntryCodec.matrix_packFinMatrix] using
    (writes_matrixMul hI hd ha hb hl hA hB hz).of_total (md := md)

/-- A QR call writes both factors of the supplied routine on its actual stored matrix and
preserves every other cell. The two output blocks are disjoint; either may alias the input
because the complete input is read before the outputs are written. -/
theorem writes_matrixQR_packFinMatrix (C : EntryCodec K E)
    (qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E →
      Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E) (hI : IsMatrixQR C qr I)
    {r c : ℕ} (A : Matrix (Fin r) (Fin c) E)
    {ds : List IExp} {ins outs : List Operand} {x q z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some [r, c]) (ha : Operand.evalList ρ ins = some [x])
    (hb : Operand.evalList ρ outs = some [q, z]) (hl : m.Live [x, q, z])
    (hA : m.store.readBlock x.1 x.2 (c * r * C.width) = some (C.packFinMatrix A))
    (hap : Fp.Disj (Store.inBlock q.1 q.2 (r * r * C.width))
      (Store.inBlock z.1 z.2 (c * r * C.width)))
    (hq : q.2 + r * r * C.width ≤ m.store.len q.1)
    (hz : z.2 + c * r * C.width ≤ m.store.len z.1) :
    Writes md I τ (.call (Has.inj MatrixOp.qr) ds ins outs) ρ
      (Store.inBlock q.1 q.2 (r * r * C.width) ⊔ Store.inBlock z.1 z.2 (c * r * C.width))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock q.1 q.2 (r * r * C.width) = some (C.packFinMatrix (qr A).1) ∧
        m'.store.readBlock z.1 z.2 (c * r * C.width) = some (C.packFinMatrix (qr A).2)) m := by
  simpa only [EntryCodec.matrix_packFinMatrix] using
    (writes_matrixQR hI hd ha hb hl hA hap hq hz).of_total (md := md)

end NLAlib.Ops
