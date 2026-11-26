/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.LineChoice

/-!
# A stored active-column candidate and its magnitude

Complete pivoting repeatedly consumes the actual first-maximum row word and the magnitude
of its original matrix entry. This routine shares the same gather/scan and bounded readback
for the initial column and all subsequent columns.

## Main results

* `NLAlib.LU.completeColumn_meets` proves actual success and the stated stored-output guarantee.

-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Select the first maximal active row in column `c`, then read that actual row word and
compute the magnitude of the selected original stored entry. -/
def completeColumn : Routine Op Tst := routine% [n, k, c] (R : n * n) → (r : 1, b : 1) {
  run lineChoice [n, k, c * n + k, 1] (R, r);
  let row ← index (Has.inj IdxTst.toNat) (r) ≤ n - 1;
  run absolute [] (R[c * n + row], b)
}

variable [Inhabited K]

/-- The row is bounded and exactly decoded. The stored magnitude equals the largest active
column magnitude, and every earlier eligible row has strictly smaller magnitude. -/
def completeColumnSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k, c] (rs) → ([r], [b]) requires
    k < n ∧ c < n ∧ n ≤ bound ensures
    ∃ row : Fin n, k ≤ row.val ∧ dec r = row.val ∧
      dec b = |dec (vec rs (c * n + row.val))| ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec rs (c * n + i.val))| ≤ |dec (vec rs (c * n + row.val))|) ∧
      (∀ i : Fin n, k ≤ i.val → i < row →
        |dec (vec rs (c * n + i.val))| < |dec (vec rs (c * n + row.val))|)

/-- The candidate comes from the actual line scan, bounded index query and scalar magnitude
instruction. Every source address is bounded by the declared full matrix block. -/
theorem completeColumn_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (completeColumn (Op := Op) (Tst := Tst)).Meets I (completeColumnSpec dec bound) := by
  routine_intro [n, k, c] (R, r, b) reads (rs)
  obtain ⟨hkn, hcn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k, c] [R, r, b])
    (Fp.blocks [r, b] [1, 1]) _ m
  call (lineChoice_meets hI hcmp hlit hQ hM hNat) [n, k, c * n + k, 1]
    (R, r) as m₁ hfr₁ hpos₁ (rows) hscan
  case' hpre =>
    refine ⟨hkn, hnb, ?_⟩
    intro i hi
    have ht : k + i < n := by omega
    have hcell := Idx.add_lt_mul hcn ht
    simpa only [Nat.one_mul, Nat.add_assoc] using hcell
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hrows
  obtain ⟨row, hkr, hd, hmax, hfirst⟩ :=
    lineChoiceSpec_column (k := ⟨k, hkn⟩) (c := ⟨c, hcn⟩) hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hd (by have := row.isLt; omega) ?_
  have hR : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  have hx : m₁.store.get R.1 (R.2 + c * n + row.val) =
      some (vec rs (c * n + row.val)) :=
    by simpa only [Nat.add_assoc] using
      Store.get_of_readBlock hR (Idx.add_lt_mul hcn row.isLt) default
  call (absolute_meets hI hcmp) [] ((R.1, R.2 + c * n + row.val), b)
    as m₂ hfr₂ hpos₂ (bs) habs
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  refine ⟨hpos₂.trans hpos₁, [[w], [v]], Mem.readBlocks_of_cons ?_
    (Mem.readBlocks_of_cons ?_ rfl), row, hkr, hd, absoluteSpec_decode hM habs, hmax, hfirst⟩
  · exact Store.readBlock_one_of_get (by keep)
  · exact Store.readBlock_one_of_get hv

end NLAlib.LU
