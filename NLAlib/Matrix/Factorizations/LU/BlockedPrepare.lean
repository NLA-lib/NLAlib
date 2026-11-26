/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotSaved
public import NLAlib.Ops.Blas.Dot

/-!
# Saved pivot operands for panel elimination

The ordinary saved-pivot copy runs before either panel rectangle is written. Two scalar
instructions then form the negative reciprocal coefficient. The word specification states
the actual machine result; numerical nonzero-pivot reasoning belongs to its consumer.

## Main results

* `NLAlib.LU.preparePanelPivot_meets`: the exact saved words and machine coefficient.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Save both complete pivot vectors and form the scalar rank-one coefficient. -/
def preparePanelPivot : Routine Op Tst :=
  routine% [n, k] (R : n * n) → (c : n, r : n, a : 1) {
    run pivotSaved [n, k] (R, c, r);
    call (Has.inj (ScalarOp.lit (-1))) [] () → (a);
    call (Has.inj ScalarOp.div) [] (a, R[k * n + k]) → (a)
  }

variable [Inhabited K]

/-- The outputs are the original pivot words and the actual machine negative reciprocal. -/
def preparePanelPivotSpec (M : Machine K) : Routine.Spec K :=
  spec% [n, k] (As) → (cs, rs, as) requires k < n ensures
    cs = pivotColumnWords As n k ∧ rs = pivotRowWords As n k ∧
      as = [M.div (M.lit (-1)) (vec As (k * n + k))]

/-- The saved operands and coefficient come from actual copies and scalar instructions.
No exact arithmetic, nonzero decoded pivot, or successful-execution premise is used. -/
theorem preparePanelPivot_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (preparePanelPivot (Op := Op) (Tst := Tst)).Meets I (preparePanelPivotSpec M) := by
  routine_intro [n, k] (R, c, r, a) reads (As)
  call (pivotSaved_meets hI) [n, k] (R, c, r) (pre := hpre)
    as m₁ hfr₁ hpos₁ (cs, rs) hsaved
  obtain ⟨rfl, rfl⟩ := hsaved
  have hAs₁ : m₁.store.readBlock R.1 R.2 (n * n) = some As := by keep
  step (hI (.lit (-1))) as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
  have hcs₂ : m₂.store.readBlock c.1 c.2 n = some (pivotColumnWords As n k) := by keep
  have hrs₂ : m₂.store.readBlock r.1 r.2 n = some (pivotRowWords As n k) := by keep
  have hAs₂ : m₂.store.readBlock R.1 R.2 (n * n) = some As := by keep
  have hpivot := Store.get_of_readBlock hAs₂ (Idx.add_lt_mul hpre hpre) default
  have hpivot' : m₂.store.get R.1 (R.2 + k * n + k) = some (vec As (k * n + k)) := by
    simpa only [Nat.add_assoc] using hpivot
  step (hI .div) as m₃ hfr₃ ⟨hpos₃, q, hq, rfl⟩
  have hcs₃ : m₃.store.readBlock c.1 c.2 n = some (pivotColumnWords As n k) := by keep
  have hrs₃ : m₃.store.readBlock r.1 r.2 n = some (pivotRowWords As n k) := by keep
  refine ⟨by omega, [pivotColumnWords As n k, pivotRowWords As n k,
    [M.div (M.lit (-1)) (vec As (k * n + k))]], ?_, rfl, rfl, rfl⟩
  exact Mem.readBlocks_of_cons hcs₃ (Mem.readBlocks_of_cons hrs₃
    (Mem.readBlocks_of_cons (Store.readBlock_one_of_get hq) rfl))

end NLAlib.LU
