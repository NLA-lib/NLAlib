/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Sum
public import NLAlib.Ops.Catalog.Tagged

/-!
# Fixture: two precisions in one program

`NLAlib.Ops.Examples.mulAddMixed` computes `z := x y + w` with the product in the precision
`Lo`, a cast, and the sum in the precision `Hi`. The signature contains scalar arithmetic at two
tags and a cast between them.

## Main results

* `NLAlib.Ops.Examples.runs_mulAddMixed`: for every interpretation meeting the contracts of the
  two tags (two machines, two unit roundoffs) and of an exact cast,
  `|ẑ - (x y + w)| ≤ u_hi |x y + w| + (1 + u_hi) u_lo |x y|`, with **one multiplication counted
  at `Lo`, one addition at `Hi` and one cast**.
* `NLAlib.Ops.Examples.sumSeq_spec_at`: sequential summation at a tag is the same implementation
  with the same certificate; nothing is rewritten for a tag.
* `NLAlib.Ops.Examples.exists_isMixed`: the contracts of the two tags and of the cast can be met
  together.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} {Lo Hi : Type} [Has (Tagged Lo ScalarOp) Op]
  [Has (Tagged Hi ScalarOp) Op] [Has (CastOp Lo Hi) Op]

/-- **`z := x y + w`, the product in the precision `Lo` and the sum in the precision `Hi`.**
Index variables: the offsets of `x`, `y`, `w`, `z`; buffer variables: `x`, `y`, `w`, `z`, then
a scratch cell. -/
def mulAddMixed (Lo Hi : Type) [Has (Tagged Lo ScalarOp) Op] [Has (Tagged Hi ScalarOp) Op]
    [Has (CastOp Lo Hi) Op] : Stmt Op Tst :=
  .alloc (.const 1)
    (.seq (.call (Tagged.inj Lo ScalarOp.mul) [] [⟨0, .var 0⟩, ⟨1, .var 1⟩] [⟨4, .const 0⟩])
      (.seq (.call (Has.inj (CastOp.cast : CastOp Lo Hi)) [] [⟨4, .const 0⟩] [⟨4, .const 0⟩])
        (.call (Tagged.inj Hi ScalarOp.add) [] [⟨4, .const 0⟩, ⟨2, .var 2⟩] [⟨3, .var 3⟩])))

/-- The counts of `mulAddMixed`, per tag. -/
noncomputable def mulAddMixedCount (Lo Hi : Type) [Has (Tagged Lo ScalarOp) Op]
    [Has (Tagged Hi ScalarOp) Op] [Has (CastOp Lo Hi) Op] : Count Op Tst :=
  Count.one (Tagged.inj Lo ScalarOp.mul) [] +
    (Count.one (Has.inj (CastOp.cast : CastOp Lo Hi)) [] +
      Count.one (Tagged.inj Hi ScalarOp.add) [])

/-- **A rounded product in one precision added in another**: the two unit roundoffs enter
separately. -/
theorem abs_mixed_le {ul uh A B C p v : ℝ} (hh : 0 ≤ uh) (hp : |p - A * B| ≤ ul * |A * B|)
    (hv : |v - (p + C)| ≤ uh * |p + C|) :
    |v - (A * B + C)| ≤ uh * |A * B + C| + (1 + uh) * ul * |A * B| := by
  have h1 : |v - (A * B + C)| ≤ |v - (p + C)| + |p - A * B| := by
    have := abs_add_le (v - (p + C)) (p - A * B)
    rwa [show v - (p + C) + (p - A * B) = v - (A * B + C) by ring] at this
  have h2 : |p + C| ≤ |A * B + C| + |p - A * B| := by
    have := abs_add_le (A * B + C) (p - A * B)
    rwa [show A * B + C + (p - A * B) = p + C by ring] at this
  nlinarith [mul_le_mul_of_nonneg_left h2 hh, mul_le_mul_of_nonneg_left hp hh]

/-- **The mixed-precision theorem**: one machine and one standard model per tag, an exact cast.
The counts are per tag: one multiplication at `Lo`, one addition at `Hi`, one cast. -/
theorem runs_mulAddMixed {Ml Mh : Machine K} {c : K → K} {ul uh : ℝ} {dec : K → ℝ}
    {I : Interp Op Tst K} (hLo : IsScalarAt Lo Ml I) (hHi : IsScalarAt Hi Mh I)
    (hC : IsCast Lo Hi c I) (hMl : StdModel ul dec Ml) (hMh : StdModel uh dec Mh)
    (hc : CastModel 0 dec c) (huh : 0 ≤ uh) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {x y w z : ℕ × ℕ} {m : Mem K} {a b e : K} (hx : m.store.get x.1 x.2 = some a)
    (hy : m.store.get y.1 y.2 = some b) (hw : m.store.get w.1 w.2 = some e)
    (hz : z.2 < m.store.len z.1) :
    Runs I W τ (mulAddMixed Lo Hi) ⟨[x.2, y.2, w.2, z.2], [x.1, y.1, w.1, z.1]⟩ m
      (mulAddMixedCount Lo Hi)
      (1 + max (W (Tagged.inj Lo ScalarOp.mul) []) (max (W (Has.inj (CastOp.cast : CastOp Lo Hi))
        []) (W (Tagged.inj Hi ScalarOp.add) [])))
      fun m' => ∃ v, m' = m.upd z v ∧ |dec v - (dec a * dec b + dec e)| ≤
        uh * |dec a * dec b + dec e| + (1 + uh) * ul * |dec a * dec b| := by
  have hlx := Store.lt_length_of_get hx
  have hly := Store.lt_length_of_get hy
  have hlw := Store.lt_length_of_get hw
  have hlz := Store.lt_length_of_lt_len hz
  have hwp : Wp .total I τ (mulAddMixed Lo Hi) ⟨[x.2, y.2, w.2, z.2], [x.1, y.1, w.1, z.1]⟩
      (fun m' => ∃ v, m' = m.upd z v ∧ |dec v - (dec a * dec b + dec e)| ≤
        uh * |dec a * dec b + dec e| + (1 + uh) * ul * |dec a * dec b|) m := by
    refine wp_alloc rfl ?_
    wp_call (hLo .mul)
    wp_call hC
    wp_call (hHi .add)
    refine ⟨Mh.add (c (Ml.mul a b)) e, by store_simp; rfl, ?_⟩
    have h1 := hMl.mul a b
    have h2 := hMh.add (c (Ml.mul a b)) e
    rw [hc.eq_of_zero] at h2
    exact abs_mixed_le huh h1 h2
  obtain ⟨m', hrun, hpost⟩ := hwp
  exact (Runs.of_run hrun hpost W).mono
    (by simp [mulAddMixed, mulAddMixedCount, staticCost, useCost])
    (by simp [mulAddMixed, staticPeak]) fun _ h => h

/-! ### An implementation at a tag: nothing is rewritten -/

section AtTag

variable {π : Type} [Has (Tagged π ScalarOp) Op] [Inhabited K]

/-- Sequential summation at the tag `π`: the same tree, with the instance of the tag. -/
def sumSeqAt (π : Type) [Has (Tagged π ScalarOp) Op] : Impl Op Tst :=
  @sumSeq Op Tst (Tagged.has π)

/-- **The certificate of sequential summation at a tag** is the certificate of sequential
summation: the unit roundoff is that of the machine of the tag. -/
theorem sumSeq_spec_at {M : Machine K} {I : Interp Op Tst K} (hI : IsScalarAt π M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) (ok : ℕ → Prop) :
    (sumSeqAt (Op := Op) (Tst := Tst) π).Meets I .total
      ((sumRel dec fun n => (1 + u) ^ (n - 1) - 1).spec (OutApart ok)) :=
  @sumSeq_spec K Op Tst (Tagged.has π) _ M I hI.isScalar u dec hM hu ok

end AtTag

/-! ### Witness -/

/-- The tag of the low precision in the witness. -/
inductive LoTag
/-- The tag of the high precision in the witness. -/
inductive HiTag

/-- A signature with scalar arithmetic at two tags and a cast between them. -/
inductive MixOp where
  /-- Scalar arithmetic at the low precision. -/
  | lo (a : ScalarOp)
  /-- Scalar arithmetic at the high precision. -/
  | hi (a : ScalarOp)
  /-- The cast from the low to the high precision. -/
  | cast
  deriving DecidableEq

instance : Has (Tagged LoTag ScalarOp) MixOp where
  inj t := .lo t.op
  proj
    | .lo a => some ⟨a⟩
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by
    cases o with
    | lo a => cases h; rfl
    | hi a => cases h
    | cast => cases h

instance : Has (Tagged HiTag ScalarOp) MixOp where
  inj t := .hi t.op
  proj
    | .hi a => some ⟨a⟩
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by
    cases o with
    | lo a => cases h
    | hi a => cases h; rfl
    | cast => cases h

instance : Has (CastOp LoTag HiTag) MixOp where
  inj _ := .cast
  proj
    | .cast => some .cast
    | _ => none
  proj_inj c := by cases c; rfl
  inj_of_proj o g h := by
    cases o with
    | lo a => cases h
    | hi a => cases h
    | cast => rfl

/-- **Witness**: the contracts of two tags and of an exact cast can be met together, with two
different unit roundoffs: the low precision by the machine that inflates by `1 + ul`, the high
precision by exact arithmetic. -/
theorem exists_isMixed {ul uh : ℝ} (hl : 0 ≤ ul) (hh : 0 ≤ uh) :
    ∃ (Ml Mh : Machine ℝ) (I : Interp MixOp Empty ℝ), StdModel ul id Ml ∧ StdModel uh id Mh ∧
      CastModel 0 id (id : ℝ → ℝ) ∧ IsScalarAt LoTag Ml I ∧ IsScalarAt HiTag Mh I ∧
      IsCast LoTag HiTag id I := by
  let F : MixOp → BlockFn ℝ
    | .lo a => (inflMachine ul).fn a
    | .hi a => exactMachine.fn a
    | .cast => .un fun a => some a
  exact ⟨inflMachine ul, exactMachine, Interp.ofFns F, stdModel_infl hl, stdModel_exact hh,
    fun a => by simp, fun a => Interp.ofFns_isFn F _ (.lo a) _,
    fun a => Interp.ofFns_isFn F _ (.hi a) _, Interp.ofFns_isFn F _ .cast _⟩

end NLAlib.Ops.Examples
