/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.TapeLaw

/-!
# Measurability with respect to the past of the tape, for `fun_prop`

A law-level proof needs `Measurable[Tape.past ξ q] X` for a random variable `X` built from the
entries of the tape before `q` (the window lemma, `integral_window`). `fun_prop` cannot prove it
in that form: the σ-algebra on `Ω` is not an instance, so the composition lemmas of Mathlib, which
take the measurable space of the domain as an instance, do not unify with it.

The fix is a type synonym: `NLAlib.Ops.Tape.PastAt ξ q` is `Ω` with the instance `past ξ q`.
Measurability with respect to the past is measurability on the synonym
(`NLAlib.Ops.Tape.measurable_past_iff`, by `Iff.rfl`), and the entries and windows of the tape
before `q` are registered with `fun_prop` on the synonym, with the position condition as a side
goal (discharged by `omega`). So `fun_prop (disch := omega)` proves the measurability of any
measurable function of the entries before `q`.

**Phase A**: statements only (`sorry`).

## Main results

* `NLAlib.Ops.Tape.PastAt`, `NLAlib.Ops.Tape.measurable_past_iff`.
* `NLAlib.Ops.Tape.measurable_pastEntry`, `NLAlib.Ops.Tape.measurable_pastWindow`: the
  `fun_prop` leaves.
-/

@[expose] public section

namespace NLAlib.Ops.Tape

variable {K Ω β : Type} [MeasurableSpace K] [MeasurableSpace β]

/-- `Ω` with the σ-algebra of the past of the position `q` of the tape `ξ`, as an instance. -/
def PastAt (_ξ : Ω → Tape K) (_q : ℕ) : Type := Ω

instance (ξ : Ω → Tape K) (q : ℕ) : MeasurableSpace (PastAt ξ q) := past ξ q

/-- Measurability with respect to the past is measurability on the synonym. -/
theorem measurable_past_iff {ξ : Ω → Tape K} {q : ℕ} {f : Ω → β} :
    @Measurable Ω β (past ξ q) inferInstance f ↔ @Measurable (PastAt ξ q) β _ _ f := Iff.rfl

/-- The entry `(i, s)` of the tape, as a function on the synonym: the leaf that `fun_prop` sees.
A random variable `fun ω => g (ξ ω i s) …` is written `fun ω => g (pastEntry ξ q i s ω) …`,
which is the same term up to `rfl`. -/
def pastEntry (ξ : Ω → Tape K) (q i s : ℕ) : PastAt ξ q → K := fun ω => ξ ω i s

/-- The window of `k` entries of the stream `s` from `p`, as a function on the synonym. -/
def pastWindow (ξ : Ω → Tape K) (q s p k : ℕ) : PastAt ξ q → Fin k → K :=
  fun ω => windowFn (ξ ω) s p k

/-- An entry before `q` is measurable with respect to the past of `q`. -/
@[fun_prop] theorem measurable_pastEntry {ξ : Ω → Tape K} {q i : ℕ} (s : ℕ) (h : i < q) :
    Measurable (pastEntry ξ q i s) := by sorry

/-- A window that ends at or before `q` is measurable with respect to the past of `q`. -/
@[fun_prop] theorem measurable_pastWindow {ξ : Ω → Tape K} {q p k : ℕ} (s : ℕ) (h : p + k ≤ q) :
    Measurable (pastWindow ξ q s p k) := by sorry

end NLAlib.Ops.Tape
