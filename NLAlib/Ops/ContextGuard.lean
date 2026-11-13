/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Contract

/-!
# Contract-guarded interpretations for context refinement

This proof-side interpretation delegates calls only while a context invariant holds,
ordinary outputs avoid the protected buffer prefix, and the source primitive precondition
holds. Outside the context regime a jointly valid reference interpretation supplies the
source contracts. These guards are proof devices, never instructions inserted into the
executed target tree or charges omitted from its resource accounting.

## Main results

* `NLAlib.Ops.Interp.guardContext`: the guarded source interpretation.
* `NLAlib.Ops.Interp.meets_guardContext`: global source laws from local primitive contracts.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- Guard delegation by the source primitive precondition and the protected-context regime.
Queries retain the active interpretation and receive no additional context operands. -/
noncomputable def Interp.guardContext (active : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (cutoff : ℕ)
    (fallback : Interp Op Tst K) : Interp Op Tst K := by
  classical
  exact {
    call := fun o d ins outs τ m =>
      if good m ∧ ∀ z ∈ outs, cutoff ≤ z.1 then
        if ((contracts o).on .total d ins outs τ m).pre m then
          active.call o d ins outs τ m
        else none
      else fallback.call o d ins outs τ m
    test := active.test
    index := active.index }

open scoped Classical in
/-- The ordinary core liveness and shape checks commute with the proof-side guard. -/
theorem Interp.callS_guardContext (active fallback : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (cutoff : ℕ)
    (o : Op) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) :
    (active.guardContext contracts good cutoff fallback).callS o d ins outs τ m =
      if good m ∧ ∀ z ∈ outs, cutoff ≤ z.1 then
        if ((contracts o).on .total d ins outs τ m).pre m then
          active.callS o d ins outs τ m
        else none
      else fallback.callS o d ins outs τ m := by
  classical
  by_cases hg : good m ∧ ∀ z ∈ outs, cutoff ≤ z.1
  · by_cases hp : ((contracts o).on .total d ins outs τ m).pre m
    · simp only [Interp.callS, Interp.guardContext, if_pos hg, if_pos hp]
    · simp only [Interp.callS, Interp.guardContext, if_pos hg, if_neg hp, Option.bind_none]
      split_ifs <;> rfl
  · simp only [Interp.callS, Interp.guardContext, if_neg hg]

/-- Local correctness of delegated primitive calls and a valid fallback give a globally
valid source contract. No algorithm execution is included in either premise. -/
theorem Interp.meets_guardContext (active fallback : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (cutoff : ℕ) (o : Op)
    (hFallback : fallback.Meets .total o (contracts o))
    (hActive : ∀ d ins outs τ m, good m → (∀ z ∈ outs, cutoff ≤ z.1) →
      ((contracts o).on .total d ins outs τ m).pre m →
      Mode.total.Holds (active.callS o d ins outs τ m)
        (((contracts o).on .total d ins outs τ m).post m)) :
    (active.guardContext contracts good cutoff fallback).Meets .total o (contracts o) := by
  classical
  intro d ins outs τ m hp
  rw [Interp.callS_guardContext]
  by_cases hg : good m ∧ ∀ z ∈ outs, cutoff ≤ z.1
  · rw [if_pos hg, if_pos hp]
    exact hActive d ins outs τ m hg.1 hg.2 hp
  · rw [if_neg hg]
    exact hFallback d ins outs τ m hp

/-- A successful guarded call within the protected regime uses the actual delegated call
and satisfies the source primitive precondition. -/
theorem Interp.callS_guardContext_of_good {active fallback : Interp Op Tst K}
    {contracts : Op → Contract K} {good : Mem K → Prop} {cutoff : ℕ}
    {o : Op} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K}
    (hg : good m) (ho : ∀ z ∈ outs, cutoff ≤ z.1)
    (hr : (active.guardContext contracts good cutoff fallback).callS o d ins outs τ m = some m') :
    ((contracts o).on .total d ins outs τ m).pre m ∧
      active.callS o d ins outs τ m = some m' := by
  classical
  rw [Interp.callS_guardContext, if_pos ⟨hg, ho⟩] at hr
  split_ifs at hr with hp
  exact ⟨hp, hr⟩

end NLAlib.Ops
