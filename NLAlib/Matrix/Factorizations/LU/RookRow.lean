/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.LineChoice

/-!
# A stored active-row candidate and its magnitude

Rook pivoting repeatedly consumes the actual first-maximum column word and the magnitude
of its original matrix entry. This routine shares the same gather/scan and bounded readback
for every alternating row scan in the bounded search.

## Main results

* `NLAlib.LU.rookRow_meets` proves actual success and the stated stored-output guarantee.

-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Select the first maximal active column in row `r`, then read that actual column word and
compute the magnitude of the selected original stored entry. -/
def rookRow : Routine Op Tst := routine% [n, k, r] (R : n * n) → (c : 1, b : 1) {
  run lineChoice [n, k, k * n + r, n] (R, c);
  let col ← index (Has.inj IdxTst.toNat) (c) ≤ n - 1;
  run absolute [] (R[col * n + r], b)
}

variable [Inhabited K]

/-- The column is bounded and exactly decoded. The stored magnitude equals the largest active
row magnitude, and every earlier eligible column has strictly smaller magnitude. -/
def rookRowSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k, r] (rs) → ([c], [b]) requires
    k < n ∧ r < n ∧ n ≤ bound ensures
    ∃ col : Fin n, k ≤ col.val ∧ dec c = col.val ∧
      dec b = |dec (vec rs (col.val * n + r))| ∧
      (∀ j : Fin n, k ≤ j.val →
        |dec (vec rs (j.val * n + r))| ≤ |dec (vec rs (col.val * n + r))|) ∧
      (∀ j : Fin n, k ≤ j.val → j < col →
        |dec (vec rs (j.val * n + r))| < |dec (vec rs (col.val * n + r))|)

/-- The candidate comes from the actual line scan, bounded index query and scalar magnitude
instruction. Every source address is bounded by the declared full matrix block. -/
theorem rookRow_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookRow (Op := Op) (Tst := Tst)).Meets I (rookRowSpec dec bound) := by
  routine_intro [n, k, r] (R, c, b) reads (rs)
  obtain ⟨hkn, hrn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k, r] [R, c, b])
    (Fp.blocks [c, b] [1, 1]) _ m
  call (lineChoice_meets hI hcmp hlit hQ hM hNat) [n, k, k * n + r, n]
    (R, c) as m₁ hfr₁ hpos₁ (cols) hscan
  case' hpre =>
    refine ⟨hkn, hnb, ?_⟩
    intro i hi
    have haddr : k * n + r + n * i = (k + i) * n + r := by
      rw [Nat.add_mul, Nat.mul_comm i n]
      omega
    rw [haddr]
    exact Idx.add_lt_mul (by omega) hrn
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hcols
  obtain ⟨col, hkc, hd, hmax, hfirst⟩ :=
    lineChoiceSpec_row (k := ⟨k, hkn⟩) (i := ⟨r, hrn⟩) hscan
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hd (by have := col.isLt; omega) ?_
  have hR : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  have hx : m₁.store.get R.1 (R.2 + col.val * n + r) =
      some (vec rs (col.val * n + r)) := by
    simpa only [Nat.add_assoc] using
      Store.get_of_readBlock hR (Idx.add_lt_mul col.isLt hrn) default
  call (absolute_meets hI hcmp) [] ((R.1, R.2 + col.val * n + r), b)
    as m₂ hfr₂ hpos₂ (bs) habs
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  refine ⟨hpos₂.trans hpos₁, [[w], [v]], Mem.readBlocks_of_cons ?_
    (Mem.readBlocks_of_cons ?_ rfl), col, hkc, hd, absoluteSpec_decode hM habs, hmax, hfirst⟩
  · exact Store.readBlock_one_of_get (by keep)
  · exact Store.readBlock_one_of_get hv

end NLAlib.LU
