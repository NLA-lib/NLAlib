/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Exec

/-!
# Contracts

A contract is a precondition and a postcondition for a call, on the memory
(`NLAlib.Ops.OpSpec`, `NLAlib.Ops.Contract`). An interpretation meets it in a mode
(`NLAlib.Ops.Interp.Meets`): in total mode the call succeeds and the postcondition holds, in
liberal mode the postcondition holds if the call succeeds. A contract receives the mode, so that
one statement serves both: what is needed only for success is put under `NLAlib.Ops.Mode.Needs`.

A contract does not receive the tape. It declares a stream and the length of a window, and it is
given the entries of that window at the position of the call, and nothing else of the tape.

Every contract of the library is written in **operand form**, `NLAlib.Ops.BlockRel` (file
`NLAlib.Ops.BlockRel`): functional, relational and with a window are one structure.

A contract says nothing of counts, workspaces or the tape positions an operation may read: those
are fixed by the evaluator and the access model (`NLAlib.Ops.exec`, `NLAlib.Ops.Interp.TapeLocal`).

The exactness of tests and index conversions is imposed by the access model
(`NLAlib.Ops.Interp.IsTest`, `NLAlib.Ops.Interp.IsIndex`); a conversion may fail.

## Main results

* `NLAlib.Ops.Interp.Meets`: an operation meets a contract.
* `NLAlib.Ops.Interp.Meets.mono`: weakening.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- The two modes of a specification. -/
inductive Mode where
  /-- Total correctness: the run succeeds and the postcondition holds. -/
  | total
  /-- Partial correctness: if the run succeeds, the postcondition holds. -/
  | liberal
  deriving DecidableEq

namespace Mode

/-- A hypothesis needed only for success. -/
def Needs (md : Mode) (p : Prop) : Prop := md = .total → p

/-- The result `x` of a run satisfies `Q`, in the mode `md`. -/
def Holds (md : Mode) {α : Type} (x : Option α) (Q : α → Prop) : Prop :=
  match md with
  | .total => ∃ a, x = some a ∧ Q a
  | .liberal => ∀ a, x = some a → Q a

@[simp] theorem needs_total (p : Prop) : total.Needs p ↔ p := by simp [Needs]
@[simp] theorem needs_liberal (p : Prop) : liberal.Needs p ↔ True := by simp [Needs]

theorem holds_total {α : Type} {x : Option α} {Q : α → Prop} :
    total.Holds x Q ↔ ∃ a, x = some a ∧ Q a := Iff.rfl

theorem holds_liberal {α : Type} {x : Option α} {Q : α → Prop} :
    liberal.Holds x Q ↔ ∀ a, x = some a → Q a := Iff.rfl

theorem holds_some {md : Mode} {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    md.Holds (some a) Q := by
  cases md
  · exact ⟨a, rfl, h⟩
  · rintro b ⟨⟩
    exact h

theorem Holds.mono {md : Mode} {α : Type} {x : Option α} {Q Q' : α → Prop} (h : md.Holds x Q)
    (hQ : ∀ a, Q a → Q' a) : md.Holds x Q' := by
  cases md
  · obtain ⟨a, ha, hq⟩ := h
    exact ⟨a, ha, hQ a hq⟩
  · exact fun a ha => hQ a (h a ha)

/-- A total statement holds in every mode. -/
theorem Holds.of_total {md : Mode} {α : Type} {x : Option α} {Q : α → Prop}
    (h : total.Holds x Q) : md.Holds x Q := by
  cases md
  · exact h
  · obtain ⟨a, ha, hq⟩ := h
    intro b hb
    rw [ha] at hb
    cases hb
    exact hq

theorem holds_bind {md : Mode} {α β : Type} {x : Option α} {f : α → Option β} {Q : β → Prop}
    (h : md.Holds x fun a => md.Holds (f a) Q) : md.Holds (x.bind f) Q := by
  cases md
  · obtain ⟨a, rfl, b, hb, hq⟩ := h
    exact ⟨b, hb, hq⟩
  · intro b hb
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
    exact h a ha b hb

theorem holds_map {md : Mode} {α β : Type} {x : Option α} {g : α → β} {Q : β → Prop}
    (h : md.Holds x fun a => Q (g a)) : md.Holds (x.map g) Q := by
  cases md
  · obtain ⟨a, rfl, hq⟩ := h
    exact ⟨g a, rfl, hq⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact h a ha

end Mode

/-- A precondition and a postcondition for a call, on the memory before and after. -/
structure OpSpec (K : Type) where
  /-- The precondition. -/
  pre : Mem K → Prop
  /-- The postcondition, of the memory before and the memory after. -/
  post : Mem K → Mem K → Prop

/-- **A contract** for an operation: the stream and the length of the tape window it may
mention, and a specification for each mode, list of dimensions, input and output operands, and
list of the entries of the window. The contract is never given the tape itself. -/
structure Contract (K : Type) where
  /-- The stream of the tape that the window is read from. -/
  stream : ℕ := 0
  /-- The length of the window at the dimensions. -/
  win : List ℕ → ℕ := fun _ => 0
  /-- The specification, given the entries of the window. -/
  spec : Mode → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List K → OpSpec K

/-- The specification of a contract for a call from the memory `m` under the tape `τ`: the
contract is given the window at the position of `m`. -/
def Contract.on (C : Contract K) (md : Mode) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K)
    (m : Mem K) : OpSpec K :=
  C.spec md d ins outs (τ.window C.stream m.pos (C.win d))

/-- **The operation `o` of `I` meets the contract `C`** in the mode `md`. -/
def Interp.Meets (I : Interp Op Tst K) (md : Mode) (o : Op) (C : Contract K) : Prop :=
  ∀ d ins outs τ m, (C.on md d ins outs τ m).pre m →
    md.Holds (I.callS o d ins outs τ m) ((C.on md d ins outs τ m).post m)

/-- Weakening: a contract with a stronger precondition and a weaker postcondition is met. -/
theorem Interp.Meets.mono {I : Interp Op Tst K} {md : Mode} {o : Op} {C C' : Contract K}
    (h : I.Meets md o C) (hpre : ∀ d ins outs τ m, (C'.on md d ins outs τ m).pre m →
      (C.on md d ins outs τ m).pre m)
    (hpost : ∀ d ins outs τ m m', (C'.on md d ins outs τ m).pre m →
      (C.on md d ins outs τ m).post m m' → (C'.on md d ins outs τ m).post m m') :
    I.Meets md o C' :=
  fun d ins outs τ m hp => (h d ins outs τ m (hpre d ins outs τ m hp)).mono
    fun m' => hpost d ins outs τ m m' hp

/-- The exactness of a test, imposed by the access model: the Boolean is the function `f` of the
input blocks. -/
def Interp.IsTest (I : Interp Op Tst K) (o : Tst) (lens : List ℕ → List ℕ)
    (f : List ℕ → List (List K) → Bool) : Prop :=
  ∀ d a m xs, m.readBlocks a (lens d) = some xs → I.test o d a m = some (f d xs)

/-- The exactness of an index conversion, imposed by the access model: the number is the function
`f` of the input cells, and **the conversion fails exactly where `f` does** (a negative or
non-integral value, a value that is not a number): no clamping. -/
def Interp.IsIndex (I : Interp Op Tst K) (o : Tst) (f : List K → Option ℕ) : Prop :=
  ∀ a m xs, m.readBlocks a (a.map fun _ => 1) = some xs → I.index o a m = f xs.flatten

end NLAlib.Ops
