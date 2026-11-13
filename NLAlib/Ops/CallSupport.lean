/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Static

/-!
# Composing properties of static primitive-call support

The predicate concerns primitive calls in the existing count, not successful executions.
Query counts do not impose primitive-call properties.

## Main results

* `NLAlib.Ops.Count.CallsSatisfy`: a property of every supported primitive call.
* `NLAlib.Ops.Stmt.allOps`: a shape-independent syntactic operation checker.
* `NLAlib.Ops.Stmt.allOps_callsSatisfy`: soundness on the existing static call support.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

/-- Every primitive call in a count's support satisfies the supplied operation/shape property. -/
def Count.CallsSatisfy (c : Count Op Tst) (P : Op → List ℕ → Prop) : Prop :=
  ∀ o ds, c (.inl o, ds) ≠ 0 → P o ds

/-- A support property restricts to any smaller count. -/
theorem Count.CallsSatisfy.mono {c c' : Count Op Tst} {P : Op → List ℕ → Prop}
    (h : c'.CallsSatisfy P) (hc : c ≤ c') : c.CallsSatisfy P := by
  intro o ds hn
  apply h o ds
  intro hz
  exact hn (Nat.eq_zero_of_le_zero (hz ▸ hc (.inl o, ds)))

@[simp] theorem Count.callsSatisfy_zero (P : Op → List ℕ → Prop) :
    (0 : Count Op Tst).CallsSatisfy P := by
  intro o ds h
  exact (h rfl).elim

@[simp] theorem Count.callsSatisfy_add (c d : Count Op Tst) (P : Op → List ℕ → Prop) :
    (c + d).CallsSatisfy P ↔ c.CallsSatisfy P ∧ d.CallsSatisfy P := by
  constructor
  · intro h
    exact ⟨h.mono le_self_add, h.mono le_add_self⟩
  · rintro ⟨hc, hd⟩ o ds hn
    by_cases hz : c (.inl o, ds) = 0
    · apply hd o ds
      simpa [Finsupp.add_apply, hz] using hn
    · exact hc o ds hz

@[simp] theorem Count.callsSatisfy_sup (c d : Count Op Tst) (P : Op → List ℕ → Prop) :
    (c ⊔ d).CallsSatisfy P ↔ c.CallsSatisfy P ∧ d.CallsSatisfy P := by
  constructor
  · intro h
    exact ⟨h.mono le_sup_left, h.mono le_sup_right⟩
  · rintro ⟨hc, hd⟩ o ds hn
    by_cases hz : c (.inl o, ds) = 0
    · apply hd o ds
      simpa [Finsupp.sup_apply, hz] using hn
    · exact hc o ds hz

@[simp] theorem Count.callsSatisfy_sum {α : Type} (s : Finset α)
    (f : α → Count Op Tst) (P : Op → List ℕ → Prop) :
    (∑ i ∈ s, f i).CallsSatisfy P ↔ ∀ i ∈ s, (f i).CallsSatisfy P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

@[simp] theorem Count.callsSatisfy_finset_sup {α : Type} (s : Finset α)
    (f : α → Count Op Tst) (P : Op → List ℕ → Prop) :
    (s.sup f).CallsSatisfy P ↔ ∀ i ∈ s, (f i).CallsSatisfy P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro _ i hi
      simp at hi
    · intro _ o ds hn
      exact (hn (by simp [bot_eq_zero])).elim
  | @insert a s ha ih => simp [Finset.sup_insert, ih]

@[simp] theorem Count.callsSatisfy_one (o : Op) (ds : List ℕ)
    (P : Op → List ℕ → Prop) :
    (Count.one o ds : Count Op Tst).CallsSatisfy P ↔ P o ds := by
  classical
  constructor
  · exact fun h => h o ds (by simp [Count.one])
  · intro h o' ds' hn
    by_cases ho : o' = o
    · subst o'
      by_cases hd : ds' = ds
      · subst ds'; exact h
      · simp [Count.one, hd] at hn
    · simp [Count.one, ho] at hn

@[simp] theorem Count.callsSatisfy_test (q : Tst) (ds : List ℕ)
    (P : Op → List ℕ → Prop) :
    (Count.test q ds : Count Op Tst).CallsSatisfy P := by
  intro o d hn
  simp [Count.test] at hn

/-- Framing preserves a support property when it holds for the evaluated dimensions and
all operand offsets. Invalid index evaluation contributes no call support. -/
theorem callsSatisfy_stmtCost_frame {ds : List IExp} {args : List Operand}
    {s : Stmt Op Tst} {idx d : List ℕ} {P : Op → List ℕ → Prop}
    (hd : IExp.evalList idx ds = some d)
    (h : ∀ os, (stmtCost s (d ++ os)).CallsSatisfy P) :
    (stmtCost (.frame ds args s) idx).CallsSatisfy P := by
  simp only [stmtCost, hd]
  cases IExp.evalList idx (args.map Operand.off) with
  | none => exact Count.callsSatisfy_zero P
  | some os => exact h os

/-- A frame has as many evaluated offsets as declared operands. -/
theorem callsSatisfy_stmtCost_frame_of_length {ds : List IExp} {args : List Operand}
    {s : Stmt Op Tst} {idx d : List ℕ} {P : Op → List ℕ → Prop}
    (hd : IExp.evalList idx ds = some d)
    (h : ∀ os, os.length = args.length → (stmtCost s (d ++ os)).CallsSatisfy P) :
    (stmtCost (.frame ds args s) idx).CallsSatisfy P := by
  simp only [stmtCost, hd]
  cases ho : IExp.evalList idx (args.map Operand.off) with
  | none => exact Count.callsSatisfy_zero P
  | some os => exact h os (by simpa using IExp.length_of_evalList ho)

/-- Every primitive in the statement tree passes a shape-independent Boolean check.
Dimensions, queries and operand addresses do not affect this syntactic operation check. -/
def Stmt.allOps (p : Op → Bool) : Stmt Op Tst → Bool
  | .skip | .abort => true
  | .call o _ _ _ => p o
  | .seq s t | .ite _ _ _ s t | .whileFuel _ _ _ _ s t => s.allOps p && t.allOps p
  | .bindIdx _ _ _ s | .allocAs _ _ s | .loop _ s | .frame _ _ s => s.allOps p

/-- Queries never introduce primitive calls, including when their dimensions do not evaluate. -/
@[simp] theorem callsSatisfy_testCost (q : Tst) (ds : List IExp) (idx : List ℕ)
    (P : Op → List ℕ → Prop) : (testCost q ds idx).CallsSatisfy P := by
  unfold testCost
  cases IExp.evalList idx ds <;> simp

/-- The operation checker implies properties of every supported static primitive call.
It applies to all bounded-index choices, not merely choices reached in a successful run. -/
theorem Stmt.allOps_callsSatisfy (p : Op → Bool) (P : Op → List ℕ → Prop)
    (hP : ∀ o, p o = true → ∀ ds, P o ds) (s : Stmt Op Tst)
    (hs : s.allOps p = true) (idx : List ℕ) : (stmtCost s idx).CallsSatisfy P := by
  induction s generalizing idx with
  | skip | abort => exact Count.callsSatisfy_zero P
  | call o ds ins outs =>
    unfold stmtCost useCost
    cases IExp.evalList idx ds <;> simp [hP o hs]
  | seq s t ihs iht =>
    exact Count.callsSatisfy_add _ _ _ |>.mpr
      ⟨ihs (Bool.and_eq_true_iff.mp hs).1 idx, iht (Bool.and_eq_true_iff.mp hs).2 idx⟩
  | ite q ds args s t ihs iht =>
    simp only [stmtCost, Count.callsSatisfy_add, callsSatisfy_testCost,
      Count.callsSatisfy_sup, true_and]
    exact ⟨ihs (Bool.and_eq_true_iff.mp hs).1 idx, iht (Bool.and_eq_true_iff.mp hs).2 idx⟩
  | whileFuel fuel q ds args s t ihs iht =>
    simp only [stmtCost, Count.callsSatisfy_add, Count.callsSatisfy_sum,
      callsSatisfy_testCost, true_and, Count.callsSatisfy_finset_sup]
    exact ⟨fun i _ => ihs (Bool.and_eq_true_iff.mp hs).1 _,
      fun i _ => iht (Bool.and_eq_true_iff.mp hs).2 _⟩
  | bindIdx q args bound s ih =>
    simp only [stmtCost, Count.callsSatisfy_add, Count.callsSatisfy_test, true_and,
      Count.callsSatisfy_finset_sup]
    exact fun i _ => ih hs _
  | allocAs fmt len s ih => exact ih hs idx
  | loop n s ih =>
    simp only [stmtCost, Count.callsSatisfy_sum]
    exact fun i _ => ih hs _
  | frame ds args s ih =>
    simp only [stmtCost]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      first | exact Count.callsSatisfy_zero P | exact ih hs _

end NLAlib.Ops
