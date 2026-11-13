/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Exec

/-!
# Invariant-sensitive congruence for bounded iteration

An implementation change need only agree on states reachable under a preserved invariant.
The rules below compare the actual bounded iterators, including early termination and failure.
They support environment/context transformations without imposing a global interpreter law
on memories that cannot arise in the program.

## Main results

* `NLAlib.Ops.iter_congr_of_invariant`: fixed-count iteration.
* `NLAlib.Ops.whileIter_congr_of_invariant`: iteration with a stopping test.
-/

@[expose] public section

namespace NLAlib.Ops

variable {α : Type}

/-- Successful fixed-count iterations retain every step invariant. -/
theorem iter_preserves {f : ℕ → α → Option α} {P : α → Prop}
    (hstep : ∀ i a b, P a → f i a = some b → P b) {n : ℕ} {a b : α}
    (ha : P a) (hr : iter f n a = some b) : P b := by
  induction n generalizing b with
  | zero => cases hr; exact ha
  | succ n ih =>
    obtain ⟨v, hv, hb⟩ := Option.bind_eq_some_iff.mp hr
    exact hstep n v b (ih hv) hb

/-- Agreement on reachable states suffices to preserve the whole fixed-count result. -/
theorem iter_congr_of_invariant (P : α → Prop) (f g : ℕ → α → Option α)
    (hagree : ∀ i a, P a → f i a = g i a)
    (hkeep : ∀ i a b, P a → g i a = some b → P b) (n : ℕ) (a : α) (ha : P a) :
    iter f n a = iter g n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter, ih]
    cases hr : iter g n a with
    | none => rfl
    | some b => exact hagree n b (iter_preserves hkeep ha hr)

/-- Tests and bodies that preserve an invariant also preserve it upon early termination. -/
theorem whileIter_preserves {test : ℕ → α → Option (Bool × α)}
    {body : ℕ → α → Option α} {P : α → Prop}
    (htest : ∀ i a b, P a → test i a = some b → P b.2)
    (hbody : ∀ i a b, P a → body i a = some b → P b) {fuel i : ℕ} {a : α} {b : ℕ × α}
    (ha : P a) (hr : whileIter test body fuel i a = some b) : P b.2 := by
  induction fuel generalizing i a b with
  | zero => cases hr; exact ha
  | succ fuel ih =>
    obtain ⟨⟨flag, v⟩, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hp := htest i a (flag, v) ha hv
    cases flag with
    | false => cases hr; exact hp
    | true =>
      obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
      exact ih (hbody i v w hp hw) hr

/-- Agreement of tests and bodies on reachable states preserves every early-exit result. -/
theorem whileIter_congr_of_invariant (P : α → Prop)
    (test test' : ℕ → α → Option (Bool × α)) (body body' : ℕ → α → Option α)
    (htest : ∀ i a, P a → test i a = test' i a)
    (hbody : ∀ i a, P a → body i a = body' i a)
    (hkeepTest : ∀ i a b, P a → test' i a = some b → P b.2)
    (hkeepBody : ∀ i a b, P a → body' i a = some b → P b)
    (fuel i : ℕ) (a : α) (ha : P a) :
    whileIter test body fuel i a = whileIter test' body' fuel i a := by
  induction fuel generalizing i a with
  | zero => rfl
  | succ fuel ih =>
    simp only [whileIter, htest i a ha]
    cases hr : test' i a with
    | none => rfl
    | some result =>
      obtain ⟨flag, v⟩ := result
      have hv := hkeepTest i a (flag, v) ha hr
      cases flag with
      | false => rfl
      | true =>
        simp only [Option.bind_some, ↓reduceIte, hbody i v hv]
        cases hb : body' i v with
        | none => rfl
        | some w => exact ih (i + 1) w (hkeepBody i v w hv hb)

/-- A successful source iteration transfers through every invariant-preserving local step. -/
theorem iter_sim_of_invariant (P : α → Prop) (target source : ℕ → α → Option α)
    (hstep : ∀ i a b, P a → source i a = some b → target i a = some b ∧ P b)
    {n : ℕ} {a b : α} (ha : P a) (hr : iter source n a = some b) :
    iter target n a = some b ∧ P b := by
  induction n generalizing b with
  | zero => cases hr; exact ⟨rfl, ha⟩
  | succ n ih =>
    obtain ⟨v, hv, hb⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hvt, hpv⟩ := ih hv
    obtain ⟨hbt, hpb⟩ := hstep n v b hpv hb
    exact ⟨by simp only [iter, hvt, Option.bind_some, hbt], hpb⟩

/-- Successful early-exit iteration transfers when both tests and bodies preserve the
same invariant. The target contains no extra tests introduced by this proof rule. -/
theorem whileIter_sim_of_invariant (P : α → Prop)
    (testTarget testSource : ℕ → α → Option (Bool × α))
    (bodyTarget bodySource : ℕ → α → Option α)
    (htest : ∀ i a b, P a → testSource i a = some b → testTarget i a = some b ∧ P b.2)
    (hbody : ∀ i a b, P a → bodySource i a = some b → bodyTarget i a = some b ∧ P b)
    {fuel i : ℕ} {a : α} {b : ℕ × α} (ha : P a)
    (hr : whileIter testSource bodySource fuel i a = some b) :
    whileIter testTarget bodyTarget fuel i a = some b ∧ P b.2 := by
  induction fuel generalizing i a b with
  | zero => cases hr; exact ⟨rfl, ha⟩
  | succ fuel ih =>
    obtain ⟨⟨flag, v⟩, hv, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hvt, hpv⟩ := htest i a (flag, v) ha hv
    cases flag with
    | false => cases hr; exact ⟨by simp [whileIter, hvt], hpv⟩
    | true =>
      obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨hwt, hpw⟩ := hbody i v w hpv hw
      obtain ⟨hrt, hpb⟩ := ih hpw hr
      exact ⟨by simp only [whileIter, hvt, Option.bind_some, ↓reduceIte, hwt, hrt], hpb⟩

end NLAlib.Ops
