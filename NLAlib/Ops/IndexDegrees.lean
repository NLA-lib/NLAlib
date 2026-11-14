/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Syntax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Nat.Log

/-!
# Polynomial degrees for individual index slots

Each initial natural index has its own exponent relative to a common base. Expression
analysis retains these exponents separately: multiplication adds degrees, addition takes the
larger degree plus one, and truncated subtraction or division retains the numerator degree.
Literal degrees use the binary ceiling logarithm; zero and one have degree zero. Successful
evaluation preserves the exact alignment between dimension values and their computed degrees.

## Main results

* `NLAlib.Ops.IExp.degreeAt`: a computable expression degree relative to its index slots.
* `NLAlib.Ops.IExp.eval_le_pow_degreeAt`: evaluation respects the individual slot degrees.
* `NLAlib.Ops.IExp.evalList_le_pow_degreeAt`: dimension lists retain aligned degree bounds.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A context-sensitive degree for a natural index expression. Unbound slots default to zero;
the evaluation theorem requires successful evaluation, which excludes reading such a slot. -/
def IExp.degreeAt (degrees : List ℕ) : IExp → ℕ
  | .var i => degrees.getD i 0
  | .const n => Nat.clog 2 n
  | .add a c => max (a.degreeAt degrees) (c.degreeAt degrees) + 1
  | .mul a c => a.degreeAt degrees + c.degreeAt degrees
  | .sub a _ | .div a _ => a.degreeAt degrees

/-- The maximum individual degree of a dimension list, with zero for an empty list. -/
def IExp.listDegreeAt (degrees : List ℕ) (es : List IExp) : ℕ :=
  (es.map (degreeAt degrees)).foldr max 0

private theorem slot_le_pow {base : ℕ} {idx degrees : List ℕ}
    (h : List.Forall₂ (fun v d => v ≤ base ^ d) idx degrees) :
    ∀ {i v : ℕ}, idx[i]? = some v → v ≤ base ^ degrees.getD i 0 := by
  induction h with
  | nil => intro i v hv; simp at hv
  | @cons v d idx degrees hv _ ih =>
    intro i w hw
    cases i with
    | zero => cases hw; exact hv
    | succ i => exact ih hw

/-- If each initial index is bounded by its corresponding power of a base at least two, a
successfully evaluated expression is bounded by the power of its computed slot-sensitive degree. -/
theorem IExp.eval_le_pow_degreeAt {base : ℕ} (hb : 2 ≤ base) {idx degrees : List ℕ}
    (hi : List.Forall₂ (fun v d => v ≤ base ^ d) idx degrees)
    (e : IExp) {v : ℕ} (hv : e.eval idx = some v) : v ≤ base ^ e.degreeAt degrees := by
  induction e generalizing v with
  | var i => exact slot_le_pow hi hv
  | const n =>
    have he : n = v := Option.some.inj hv
    subst v
    exact (Nat.le_pow_clog (by omega : 1 < 2) n).trans (pow_le_pow_left' hb _)
  | add a c iha ihc =>
    cases ha : a.eval idx <;> cases hc : c.eval idx <;>
      simp only [eval, ha, hc, reduceCtorEq] at hv
    rename_i av cv
    cases hv
    have hA := (iha ha).trans (pow_le_pow_right' (by omega)
      (Nat.le_max_left (a.degreeAt degrees) (c.degreeAt degrees)))
    have hC := (ihc hc).trans (pow_le_pow_right' (by omega)
      (Nat.le_max_right (a.degreeAt degrees) (c.degreeAt degrees)))
    change av + cv ≤ base ^ (max (a.degreeAt degrees) (c.degreeAt degrees) + 1)
    calc
      av + cv ≤ base ^ max (a.degreeAt degrees) (c.degreeAt degrees) +
          base ^ max (a.degreeAt degrees) (c.degreeAt degrees) := Nat.add_le_add hA hC
      _ ≤ base ^ max (a.degreeAt degrees) (c.degreeAt degrees) * base := by
        simpa only [Nat.mul_two] using
          Nat.mul_le_mul_left (base ^ max (a.degreeAt degrees) (c.degreeAt degrees)) hb
      _ = _ := (pow_succ _ _).symm
  | mul a c iha ihc =>
    cases ha : a.eval idx <;> cases hc : c.eval idx <;>
      simp only [eval, ha, hc, reduceCtorEq] at hv
    rename_i av cv
    cases hv
    simpa only [degreeAt, pow_add] using Nat.mul_le_mul (iha ha) (ihc hc)
  | sub a c iha _ | div a c iha _ =>
    cases ha : a.eval idx <;> cases hc : c.eval idx <;>
      simp only [eval, ha, hc, reduceCtorEq] at hv
    all_goals rename_i av cv
    all_goals cases hv
    all_goals change _ ≤ base ^ a.degreeAt degrees
    all_goals first
      | exact (Nat.sub_le av cv).trans (iha ha)
      | exact (Nat.div_le_self av cv).trans (iha ha)

/-- A successfully evaluated dimension list has exactly one bound for each corresponding
expression, retaining the individual degrees rather than raising every slot to a common maximum. -/
theorem IExp.evalList_le_pow_degreeAt {base : ℕ} (hb : 2 ≤ base) {idx degrees : List ℕ}
    (hi : List.Forall₂ (fun v d => v ≤ base ^ d) idx degrees)
    {es : List IExp} {vs : List ℕ} (hv : evalList idx es = some vs) :
    List.Forall₂ (fun v d => v ≤ base ^ d) vs (es.map (degreeAt degrees)) := by
  induction es generalizing vs with
  | nil => cases hv; exact .nil
  | cons e es ih =>
    cases he : e.eval idx <;> cases ht : evalList idx es <;>
      simp only [evalList, he, ht, reduceCtorEq] at hv
    rename_i v tail
    cases hv
    exact .cons (e.eval_le_pow_degreeAt hb hi he) (ih ht)

private theorem forall₂_pow_le_foldr_max {base : ℕ} (hb : 2 ≤ base)
    {vs ds : List ℕ} (h : List.Forall₂ (fun v d => v ≤ base ^ d) vs ds) :
    ∀ v ∈ vs, v ≤ base ^ ds.foldr max 0 := by
  induction h with
  | nil => simp
  | @cons v d vs ds hv _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv.trans (pow_le_pow_right' (by omega) (Nat.le_max_left _ _))
    · exact (ih x hx).trans (pow_le_pow_right' (by omega) (Nat.le_max_right _ _))

/-- Every successfully evaluated dimension is bounded by the power of the maximum individual
expression degree. This retains exact slot alignment until the final common ceiling. -/
theorem IExp.evalList_le_pow_listDegreeAt {base : ℕ} (hb : 2 ≤ base)
    {idx degrees : List ℕ} (hi : List.Forall₂ (fun v d => v ≤ base ^ d) idx degrees)
    {es : List IExp} {vs : List ℕ} (hv : evalList idx es = some vs) :
    ∀ v ∈ vs, v ≤ base ^ listDegreeAt degrees es :=
  forall₂_pow_le_foldr_max hb (evalList_le_pow_degreeAt hb hi hv)

end NLAlib.Ops
