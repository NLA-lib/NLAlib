/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Compare

/-!
# Integer literals supplied by dimensions

An evaluated size can be written into a word by an ordinary counted operation. This operation
uses the same literal function as scalar arithmetic; exactness is a separate model assumption.
Reading the word back uses the existing index query and its explicit bound.

## Main results

* `NLAlib.Ops.IsIndexLit` specifies the dimension-to-word operation.
* `NLAlib.Ops.IsExactNatLit` states exactness of bounded natural literals.
* `NLAlib.Ops.IsToNat.index_eq_of_decode_nat` reads an exactly decoded natural word.
* `NLAlib.Ops.indexScalarInterp` jointly realizes scalar operations, dimension literals and
  index queries on one machine.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Operations that write an evaluated natural dimension to a scalar word. -/
inductive IndexOp where
  /-- `lit [n] [] [z]` writes the machine's rounded rational literal of `n` into cell `z`. -/
  | lit
  deriving DecidableEq

variable {K Op Tst : Type}

/-- The dimension literal uses exactly the same literal function as scalar arithmetic. -/
def Machine.indexFn (M : Machine K) : BlockFn K where
  nd := 1
  inLens _ := []
  outLens _ := [1]
  fn d _ _ := some [[M.lit (d.headD 0)]]

/-- Functional contract of dimension literals, with no numerical exactness assumed. -/
def IsIndexLit [Has IndexOp Op] (M : Machine K) (I : Interp Op Tst K) : Prop :=
  I.IsFn .total (Has.inj IndexOp.lit) M.indexFn AnyOperands

/-- The natural literals up to `bound` decode exactly. This is additional to the standard
rounding model; a finite format need only satisfy it within its exact integer range. -/
def IsExactNatLit (dec : K → ℝ) (M : Machine K) (bound : ℕ) : Prop :=
  ∀ n ≤ bound, dec (M.lit (n : ℚ)) = n

/-- Exactness on an integer range restricts to every smaller range. -/
theorem IsExactNatLit.mono {dec : K → ℝ} {M : Machine K} {a b : ℕ}
    (h : IsExactNatLit dec M b) (hab : a ≤ b) : IsExactNatLit dec M a :=
  fun n hn => h n (hn.trans hab)

/-- An exact arithmetic machine has exact natural literals at every bound. -/
theorem ExactModel.isExactNatLit {dec : K → ℝ} {M : Machine K} (h : ExactModel dec M)
    (bound : ℕ) : IsExactNatLit dec M bound := by
  intro n _
  simpa using h.lit (n : ℚ)

/-- A readable exactly decoded natural converts to that same index. -/
theorem IsToNat.index_eq_of_decode_nat [Has IdxTst Tst] {dec : K → ℝ}
    {I : Interp Op Tst K} (h : IsToNat dec I) {x : ℕ × ℕ} {m : Mem K} {w : K} {n : ℕ}
    (hx : m.store.get x.1 x.2 = some w) (hw : dec w = n) :
    I.index (Has.inj IdxTst.toNat) [x] m = some n := by
  rw [h.index_eq hx (hw ▸ Nat.cast_nonneg n), hw, Nat.floor_natCast]

/-- Scalar arithmetic, dimension literals and index queries on the same machine and decoding.
The index query rejects negative values. No conversion is hidden in a comparison. -/
noncomputable def indexScalarInterp (M : Machine K) (dec : K → ℝ) :
    Interp (ScalarOp ⊕ IndexOp) IdxTst K where
  call o := (Interp.ofFns (fun o : ScalarOp ⊕ IndexOp =>
    o.elim M.fn (fun _ => M.indexFn)) : Interp _ IdxTst K).call o
  test _ _ _ _ := none
  index _ a m := (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten

/-- The joint interpretation realizes the scalar contract on its given machine. -/
theorem isScalar_indexScalarInterp (M : Machine K) (dec : K → ℝ) :
    IsScalar M (indexScalarInterp M dec) := by
  intro o
  exact Interp.ofFns_isFn (Tst := IdxTst) (fun o : ScalarOp ⊕ IndexOp =>
    o.elim M.fn (fun _ => M.indexFn)) .total (.inl o) AnyOperands

/-- The joint interpretation realizes dimension literals using that same machine. -/
theorem isIndexLit_indexScalarInterp (M : Machine K) (dec : K → ℝ) :
    IsIndexLit M (indexScalarInterp M dec) :=
  Interp.ofFns_isFn (Tst := IdxTst) (fun o : ScalarOp ⊕ IndexOp =>
    o.elim M.fn (fun _ => M.indexFn)) .total (.inr .lit) AnyOperands

/-- The joint interpretation realizes the specified floor query. -/
theorem isToNat_indexScalarInterp (M : Machine K) (dec : K → ℝ) :
    IsToNat dec (indexScalarInterp M dec) := by
  intro a m xs h
  change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten) = _
  rw [h]
  rfl

/-- A single exact real interpretation witnesses all three functional interfaces and bounded
integer exactness at every bound, including zero. -/
theorem exists_isScalar_isIndexLit_isToNat (bound : ℕ) :
    ∃ (I : Interp (ScalarOp ⊕ IndexOp) IdxTst ℝ),
      IsScalar exactMachine I ∧ IsIndexLit exactMachine I ∧ IsToNat id I ∧
        IsExactNatLit id exactMachine bound :=
  ⟨indexScalarInterp exactMachine id, isScalar_indexScalarInterp _ _,
    isIndexLit_indexScalarInterp _ _, isToNat_indexScalarInterp _ _,
    exactModel_exactMachine.isExactNatLit bound⟩

end NLAlib.Ops
