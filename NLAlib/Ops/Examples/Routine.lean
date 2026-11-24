/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Blas.Sum
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Example: two routines, composed

`NLAlib.Ops.Examples.Routines.sum` is rounded sequential summation as a routine
`[n] (x : read n) → (z : write 1)`. `NLAlib.Ops.Examples.Routines.sum2` is
`[n] (x : read n, y : read n) → (z : write 1, w : write 1)`: it calls `sum` on `x` and on `y` and
adds the two results. Its accuracy is proved from the specification of `sum`, never from its
tree.

## Main definitions

* `NLAlib.Ops.Examples.Routines.sum`, `NLAlib.Ops.Examples.Routines.sumSpec`.
* `NLAlib.Ops.Examples.Routines.sum2`, `NLAlib.Ops.Examples.Routines.sum2Spec`.
* `NLAlib.Ops.Examples.Routines.double`: one operand updated in place by a tree with two
  buffer variables.

## Main results

* `NLAlib.Ops.Examples.Routines.sum_meets`: summation meets its specification.
* `NLAlib.Ops.Examples.Routines.sum2_meets`: the composite meets its specification.
* `NLAlib.Ops.Examples.Routines.double_meets`: the in-place routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Routines

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]

/-- Sequential summation: `[n] (x : read n) → (z : write 1)`, the routine of the library. -/
abbrev sum : Routine Op Tst := sumSeqRoutine

/-- The written cell is the sum of the entries read, with relative error
$(1 + u)^{n - 1} - 1$ in the sum of their absolute values. -/
abbrev sumSpec (dec : K → ℝ) (u : ℝ) : Routine.Spec K := sumSeqSpec dec u

/-- Sequential summation meets its specification under the standard model of arithmetic. -/
theorem sum_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) :
    (sum (Op := Op) (Tst := Tst)).Meets I (sumSpec dec u) :=
  sumSeqRoutine_meets hI hM hu

/-- Sum two vectors by two calls of `sum` and one addition. The cell `w` is scratch for the second
partial sum: it is written, and its final contents are not reported. -/
def sum2 : Routine Op Tst := noted% routine% [n] (x : n, y : n) → (z : 1, unreported w : 1) {
  run (sum (Op := Op) (Tst := Tst)) [n] (x, z);
  run (sum (Op := Op) (Tst := Tst)) [n] (y, w);
  call (Has.inj ScalarOp.add) [] (z, w) → (z)
}

/-- The first written cell is the sum of all entries of both vectors, with relative error
$(1 + u)^{n} - 1$ in the sum of their absolute values. -/
def sum2Spec (dec : K → ℝ) (u : ℝ) : Routine.Spec K :=
  spec% [n] (xs, ys) → ([v]) ensures
    |dec v - (∑ k ∈ Finset.range n, dec (vec xs k) + ∑ k ∈ Finset.range n, dec (vec ys k))| ≤
      ((1 + u) * (1 + u) ^ (n - 1) - 1) *
        (∑ k ∈ Finset.range n, |dec (vec xs k)| + ∑ k ∈ Finset.range n, |dec (vec ys k)|)

/-- Two accurate partial sums and one rounded addition give an accurate total: relative errors
$(1 + u)^{n - 1} - 1$ compose with one more factor $1 + u$. -/
theorem sum2_error {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u)
    {n : ℕ} {xs ys : List K} {v₁ v₂ : K}
    (h₁ : IsSumErr dec ((1 + u) ^ (n - 1) - 1) n (vec xs) v₁)
    (h₂ : IsSumErr dec ((1 + u) ^ (n - 1) - 1) n (vec ys) v₂) :
    |dec (M.add v₁ v₂) - (∑ k ∈ Finset.range n, dec (vec xs k) +
      ∑ k ∈ Finset.range n, dec (vec ys k))| ≤
      ((1 + u) * (1 + u) ^ (n - 1) - 1) *
        (∑ k ∈ Finset.range n, |dec (vec xs k)| + ∑ k ∈ Finset.range n, |dec (vec ys k)|) := by
  have habs (zs : List K) : |∑ k ∈ Finset.range n, dec (vec zs k)| ≤
      ∑ k ∈ Finset.range n, |dec (vec zs k)| := Finset.abs_sum_le_sum_abs _ _
  have h := hM.abs_add_sub_le hu h₁ h₂ (habs xs) (habs ys)
  have he : (1 + u) * (1 + ((1 + u) ^ (n - 1) - 1)) - 1 = (1 + u) * (1 + u) ^ (n - 1) - 1 := by
    ring
  rw [he] at h
  exact h

/-- The composite meets its specification, from the specification of `sum` and the
standard model of the one addition. The tree of `sum` is not inspected: each call uses its
judgment, and returns the cell it wrote with its postcondition. -/
theorem sum2_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) (hu : 0 ≤ u) :
    (sum2 (Op := Op) (Tst := Tst)).Meets I (sum2Spec dec u) := by
  routine_intro [n] (x, y, z, w) reads (xs, ys)
  have hsum := sum_meets (Op := Op) (Tst := Tst) hI hM hu
  call hsum [n] (x, z) as ν hfr hpos (zs) hpost
  obtain ⟨v₁, hv₁, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  call hsum [n] (y, w) as ν₂ hfr₂ hpos₂ (ws) hpost₂
  obtain ⟨v₂, hv₂, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  step (hI .add) as ν₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
  routine_exit
  exact sum2_error hM hu hpost hpost₂

/-! ### An operand updated in place by a tree with two buffer variables -/

/-- Double a cell in place: `[] (x : update 1)`. The tree is `x := x + x` with two buffer
variables, an input and an output; naming `x` on both sides of the header binds both to the one
operand. -/
def double : Routine Op Tst := routine% [] (x : 1) → (x) {
  call (Has.inj ScalarOp.add) [] (x, x) → (x)
}

/-- What `routine%` generates for `double`: one operand, and the layout
(`NLAlib.Ops.Routine.binds`) that sends both buffer variables of the tree to it. -/
example : (double : Routine Op Tst).ports.length = 1 ∧
    (double : Routine Op Tst).binds = some [0, 0] := ⟨rfl, rfl⟩

/-- The cell holds the machine sum of its initial value with itself. -/
def doubleSpec (M : Machine K) : Routine.Spec K :=
  spec% [] ([x]) → ([v]) ensures v = M.add x x

omit [Inhabited K] in
/-- Doubling in place meets its specification: the layout sends both buffer variables of the
tree to the one operand of the interface. -/
theorem double_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (double (Op := Op) (Tst := Tst)).Meets I (doubleSpec M) := by
  routine_intro [] (x) reads (xs)
  obtain ⟨u, hu, rfl⟩ := Store.readBlock_one_eq_some.mp hxs
  step (hI .add) as ν hfr ⟨hpos, v, hv, rfl⟩
  routine_exit
  exact rfl

/-- The operand marks of `routine%` reach the interface: an isolated operand and an unreported
one. -/
example : (routine% [n] (isolated A : n, x : n) → (y : n, unreported w : n) := .skip :
    Routine Empty Empty).ports.map (fun p => (p.access, p.cont, p.reported)) =
    [(.isolated, false, true), (.read, false, true), (.write, false, true),
      (.write, false, false)] := rfl

/-- With `one variable` the operands of a block are one buffer variable each, in the order of the
interface: an updated operand is not numbered twice, and there is no layout. -/
example : (routine% [n] (x : n, y : n) → (x) one variable {
      run (Stmt.skip : Stmt Empty Empty) [n] (y, x)
    } : Routine Empty Empty).body = .frame [.var 0] [⟨1, .var 2⟩, ⟨0, .var 1⟩] .skip := rfl

end NLAlib.Ops.Examples.Routines
