/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Logic.Footprint

/-!
# Exact real or complex level-one operations

The existing level-one operation names have functional contracts on an `RCLike` word
carrier. Dot products conjugate their first argument. Scaling divides by the supplied
scalar, as in the level-one catalog. Comparisons observe real parts; algorithms use them
on real norm squares. The scalar and block functions are jointly realized by one
interpretation, without using either algorithm or an execution premise in a contract.

## Main results

* `NLAlib.Ops.RCLikeBlas.machine` supplies exact field arithmetic and real square roots.
* `NLAlib.Ops.RCLikeBlas.functions` specifies each level-one operation on input blocks.
* `NLAlib.Ops.RCLikeBlas.IsExact` is the functional level-one contract set.
* `NLAlib.Ops.RCLikeBlas.interp_contracts` jointly realizes all three contract groups.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeBlas

variable {𝕜 : Type} [RCLike 𝕜]

/-- Exact field arithmetic; square roots embed the square root of the real part. On
nonnegative real inputs this is the usual nonnegative scalar square root. -/
noncomputable def machine : Machine 𝕜 where
  lit q := q
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := Neg.neg
  sqrt x := RCLike.ofReal (Real.sqrt (RCLike.re x))

/-- Over real words the exact real-or-complex machine is the standard exact scalar model. -/
theorem exactModel_real : ExactModel id (machine : Machine ℝ) := by
  simpa [machine, exactMachine] using exactModel_exactMachine

/-- The exact Hermitian product of the first `n` entries of two word blocks. The zero
padding only totalizes this mathematical function; the primitive checks actual lengths. -/
def dot (n : ℕ) (xs ys : List 𝕜) : 𝕜 :=
  ∑ i : Fin n, star (xs.getD i 0) * ys.getD i 0

/-- Packing finite vectors leaves their exact Hermitian product unchanged. -/
theorem dot_ofFn {n : ℕ} (x y : Fin n → 𝕜) :
    dot n (List.ofFn x) (List.ofFn y) = ∑ i, star (x i) * y i := by
  simp [dot, List.getD_eq_getElem?_getD]

/-- Exact local block functions for the existing level-one operation names. Their input
and output lengths are checked by the common block-function interpreter. -/
noncomputable def functions : Blas1Op → BlockFn 𝕜
  | .sum => {
      nd := 1
      inLens d := [d.headD 0]
      outLens _ := [1]
      fn d _ xs := match xs with
        | [x] => some [[∑ i : Fin (d.headD 0), x.getD i 0]]
        | _ => none }
  | .dot => {
      nd := 1
      inLens d := [d.headD 0, d.headD 0]
      outLens _ := [1]
      fn d _ xs := match xs with
        | [x, y] => some [[dot (d.headD 0) x y]]
        | _ => none }
  | .axpy => {
      nd := 1
      inLens d := [1, d.headD 0, d.headD 0]
      outLens d := [d.headD 0]
      fn d _ xs := match xs with
        | [[a], x, y] => some [List.ofFn fun i : Fin (d.headD 0) =>
            y.getD i 0 + a * x.getD i 0]
        | _ => none }
  | .nrm2 => {
      nd := 1
      inLens d := [d.headD 0]
      outLens _ := [1]
      fn d _ xs := match xs with
        | [x] => some [[RCLike.ofReal (Real.sqrt (RCLike.re (dot (d.headD 0) x x)))]]
        | _ => none }
  | .scal => {
      nd := 1
      inLens d := [1, d.headD 0]
      outLens d := [d.headD 0]
      fn d _ xs := match xs with
        | [[a], x] => some [List.ofFn fun i : Fin (d.headD 0) => x.getD i 0 / a]
        | _ => none }
  | .copy => {
      nd := 1
      inLens d := [d.headD 0]
      outLens d := [d.headD 0]
      fn _ _ xs := match xs with
        | [x] => some [x]
        | _ => none }

/-- Spatial admission for exact scalar lowerings. Dot products and reductions write apart
from their inputs. Vector maps admit exact alias or disjoint views; broadcast scalars remain
apart from output. Partial shifted aliases are not admitted. No numerical condition is used. -/
@[admNF] def admissible (o : Blas1Op) (d : List ℕ)
    (ins outs : List (ℕ × ℕ)) : Prop :=
  let n := d.headD 0
  match o, ins, outs with
  | .sum, [x], [z] | .nrm2, [x], [z] =>
      Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock x.1 x.2 n)
  | .dot, [x, y], [z] =>
      Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock x.1 x.2 n) ∧
        Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock y.1 y.2 n)
  | .axpy, [a, x, y], [z] =>
      Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
        (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z) ∧
        (Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z)
  | .scal, [a, x], [z] =>
      Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
        (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
  | .copy, [x], [z] =>
      Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z
  | _, _, _ => False

/-- Every level-one primitive has exactly the declared Hermitian block function. This is
an exact functional model, independently of the real decoded relative-error model. -/
def IsExact {Op Tst : Type} [Has Blas1Op Op] (I : Interp Op Tst 𝕜) : Prop :=
  ∀ o : Blas1Op, I.IsFn .total (Has.inj o) (functions o) (admissible o)

/-- One signature containing the scalar and level-one operation groups. -/
abbrev Operation := ScalarOp ⊕ Blas1Op

/-- Local scalar and vector functions for the combined signature. -/
noncomputable def operationFunctions : Operation → BlockFn 𝕜
  | .inl o => machine.fn o
  | .inr o => functions o

/-- A jointly realizing interpretation of exact scalar and level-one arithmetic with
comparison of real parts. It contains no algorithm-specific operation. -/
noncomputable def interp : Interp Operation CmpTst 𝕜 where
  call := (Interp.ofFns (Tst := CmpTst) (operationFunctions (𝕜 := 𝕜))).call
  test c _ a m := (m.readBlocks a c.lens).map (c.fn RCLike.re)
  index _ _ _ := none

/-- All exact field, Hermitian vector and real-part comparison contracts hold for the
same interpretation. Realizability requires no rank or execution hypothesis. -/
theorem interp_contracts :
    IsScalar (machine : Machine 𝕜) interp ∧ IsExact (interp (𝕜 := 𝕜)) ∧
      IsCmp RCLike.re (interp (𝕜 := 𝕜)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro o
    exact Interp.ofFns_isFn (Tst := CmpTst) (operationFunctions (𝕜 := 𝕜))
      .total (.inl o) AnyOperands
  · intro o
    exact Interp.ofFns_isFn (Tst := CmpTst) (operationFunctions (𝕜 := 𝕜))
      .total (.inr o) (admissible o)
  · intro c d a m xs h
    change (m.readBlocks a c.lens).map (c.fn RCLike.re) = _
    rw [h]
    rfl

end NLAlib.Ops.RCLikeBlas
