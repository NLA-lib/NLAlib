/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.Logic.Functional

/-!
# Stored-output rule for explicit-data matrix-vector application

The local operation consumes its declared representation and vector blocks, then writes
the exact mathematical product into a disjoint output span. It can neither read hidden
buffers nor assume a whole-algorithm postcondition.

## Main results

* `NLAlib.Ops.StoredOperator.writes_matvec` supplies the exact packed output and frame.
-/

@[expose] public section

namespace NLAlib.Ops.StoredOperator

variable {K Op Tst : Type} [Semiring K] [Has StoredOperatorOp Op]
  {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-- Explicit-data matrix-vector application writes its mathematical vector after reading
both inputs. Output separation is the explicit local operation-model admission. -/
theorem writes_matvec {dataLength : ℕ → ℕ → ℕ}
    {matrix : (m n : ℕ) → List K → Matrix (Fin m) (Fin n) K}
    (hI : IsExact dataLength matrix I)
    {ds : List IExp} {ins outs : List Operand} {rows cols : ℕ}
    {data x y : ℕ × ℕ} {as xs : List K}
    (hd : IExp.evalList ρ.idx ds = some [rows, cols])
    (ha : Operand.evalList ρ ins = some [data, x])
    (hb : Operand.evalList ρ outs = some [y]) (hl : m.Live [data, x, y])
    (hA : m.store.readBlock data.1 data.2 (dataLength rows cols) = some as)
    (hX : m.store.readBlock x.1 x.2 cols = some xs)
    (hYA : Fp.Disj (Store.inBlock y.1 y.2 rows)
      (Store.inBlock data.1 data.2 (dataLength rows cols)))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 rows) (Store.inBlock x.1 x.2 cols))
    (hY : y.2 + rows ≤ m.store.len y.1) :
    Writes .total I τ (.call (Has.inj StoredOperatorOp.matvec) ds ins outs) ρ
      (Store.inBlock y.1 y.2 rows)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 rows =
        some (List.ofFn fun i : Fin rows =>
          ∑ j : Fin cols, matrix rows cols as i j * xs.getD j 0)) m := by
  exact writes_call_fn1 hI (xs := [as, xs]) hd ha hb rfl rfl
    (by simpa [OutApart, Fp.blocks] using Fp.disj_sup_right.mpr ⟨hYA, hYX⟩) hl
    (by simp [functions, Mem.readBlocks, hA, hX]) rfl (List.length_ofFn ..) hY

end NLAlib.Ops.StoredOperator
