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

Two forms.

* **Relational**: the outputs satisfy a bound. Any `Contract`.
* **Functional**: the result is a function of the input blocks (and of the entries of the tape
  window, for an operation that draws). `NLAlib.Ops.BlockFn` is such a function,
  `NLAlib.Ops.BlockFn.apply` its effect on the memory, `NLAlib.Ops.BlockFn.spec` the contract
  "the call is `apply`", and `NLAlib.Ops.Interp.IsFn` says an operation meets it. Under `IsFn` a
  call is an equation (`NLAlib.Ops.Interp.IsFn.callS_eq`).

A contract says nothing of counts, workspaces or the tape positions an operation may read: those
are fixed by the evaluator and the access model (`NLAlib.Ops.exec`, `NLAlib.Ops.Interp.TapeLocal`).
## Main results

* `NLAlib.Ops.Interp.IsFn.callS_eq`: under a functional contract a call is an equation.
* `NLAlib.Ops.Interp.ofFns_isFn`: an interpretation given by block functions meets their
  functional contracts.
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

/-- **A contract** for an operation: a specification for each mode, list of dimensions, input and
output operands, and tape. -/
abbrev Contract (K : Type) := Mode → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → (ℕ → K) → OpSpec K

/-- **The operation `o` of `I` meets the contract `C`** in the mode `md`. -/
def Interp.Meets (I : Interp Op Tst K) (md : Mode) (o : Op) (C : Contract K) : Prop :=
  ∀ d ins outs τ m, (C md d ins outs τ).pre m →
    md.Holds (I.callS o d ins outs τ m) ((C md d ins outs τ).post m)

/-- Weakening: a contract with a stronger precondition and a weaker postcondition is met. -/
theorem Interp.Meets.mono {I : Interp Op Tst K} {md : Mode} {o : Op} {C C' : Contract K}
    (h : I.Meets md o C) (hpre : ∀ d ins outs τ m, (C' md d ins outs τ).pre m →
      (C md d ins outs τ).pre m)
    (hpost : ∀ d ins outs τ m m', (C' md d ins outs τ).pre m → (C md d ins outs τ).post m m' →
      (C' md d ins outs τ).post m m') : I.Meets md o C' :=
  fun d ins outs τ m hp => (h d ins outs τ m (hpre d ins outs τ m hp)).mono
    fun m' => hpost d ins outs τ m m' hp

/-- **A block function**: the output block as a function of the dimensions, the entries of the
tape window and the input blocks. `win` is the length of the window (zero for an operation that
does not draw), `inLens` the lengths of the input blocks. -/
structure BlockFn (K : Type) where
  /-- The length of the tape window read at the dimensions. -/
  win : List ℕ → ℕ := fun _ => 0
  /-- The lengths of the input blocks at the dimensions. -/
  inLens : List ℕ → List ℕ
  /-- The output block. -/
  fn : List ℕ → List K → List (List K) → Option (List K)

namespace BlockFn

/-- The effect of a block function on the memory: read the input blocks and the tape window,
apply the function, write the output block at `z`, advance the tape. It fails if an operand
handle is not a buffer of the store. -/
def apply (f : BlockFn K) (d : List ℕ) (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : ℕ → K) (m : Mem K) :
    Option (Mem K) :=
  if m.Live (ins ++ [z]) then
    (m.readBlocks ins (f.inLens d)).bind fun xs =>
      (f.fn d ((List.range (f.win d)).map fun j => τ (m.pos + j)) xs).bind fun ys =>
        (m.write z ys).map fun m' => m'.advance (f.win d)
  else none

/-- **The functional contract** of a block function, on the admitted operands `adm`: the call is
`apply`. Success of `apply` is needed only for success of the call. -/
def spec (f : BlockFn K) (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Contract K :=
  fun md d ins outs τ =>
    { pre := fun m => ∃ z, outs = [z] ∧ adm d ins z ∧ md.Needs (f.apply d ins z τ m).isSome
      post := fun m m' => ∃ z, outs = [z] ∧ f.apply d ins z τ m = some m' }

theorem shape_of_apply {f : BlockFn K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K}
    {m m' : Mem K} (h : f.apply d ins z τ m = some m') : m'.store.shape = m.store.shape := by
  unfold apply at h
  split_ifs at h
  obtain ⟨xs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (Mem.shape_of_write h₁).1

/-- The effect of a block function, unfolded. -/
theorem apply_eq_some_iff {f : BlockFn K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {τ : ℕ → K} {m m' : Mem K} :
    f.apply d ins z τ m = some m' ↔ m.Live (ins ++ [z]) ∧
      ∃ xs ys, m.readBlocks ins (f.inLens d) = some xs ∧
      f.fn d ((List.range (f.win d)).map fun j => τ (m.pos + j)) xs = some ys ∧
      z.2 + ys.length ≤ m.store.len z.1 ∧ m' = (m.updBlock z ys).advance (f.win d) := by
  unfold apply
  by_cases hl : m.Live (ins ++ [z])
  · simp only [hl, if_true, true_and, Option.bind_eq_some_iff, Option.map_eq_some_iff, Mem.write]
    constructor
    · rintro ⟨xs, hxs, ys, hys, m₁, hw, rfl⟩
      split_ifs at hw with hlen
      cases hw
      exact ⟨xs, ys, hxs, hys, hlen, rfl⟩
    · rintro ⟨xs, ys, hxs, hys, hlen, rfl⟩
      exact ⟨xs, hxs, ys, hys, _, if_pos hlen, rfl⟩
  · simp [hl]

end BlockFn

/-- **The operation `o` of `I` is the block function `f`** on the admitted operands, in the mode
`md`: it meets the functional contract of `f`. -/
def Interp.IsFn (I : Interp Op Tst K) (md : Mode) (o : Op) (f : BlockFn K)
    (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Prop :=
  I.Meets md o (f.spec adm)

/-- **A call of a functional operation is an equation.** -/
theorem Interp.IsFn.callS_eq {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : I.IsFn .total o f adm) {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} (hadm : adm d ins z)
    (ha : f.apply d ins z τ m = some m') : I.callS o d ins [z] τ m = some m' := by
  obtain ⟨m₁, h₁, z', hz, h₂⟩ := h d ins [z] τ m ⟨z, rfl, hadm, by simp [ha]⟩
  cases hz
  rw [h₁, ← h₂, ha]

/-- In liberal mode: a successful call of a functional operation is `apply`. -/
theorem Interp.IsFn.apply_of_callS {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : I.IsFn .liberal o f adm) {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} (hadm : adm d ins z)
    (hc : I.callS o d ins [z] τ m = some m') : f.apply d ins z τ m = some m' := by
  obtain ⟨z', hz, h₂⟩ := h d ins [z] τ m ⟨z, rfl, hadm, by simp⟩ m' hc
  cases hz
  exact h₂

/-- **The interpretation whose operations are given block functions** (model primitives, concrete
formats, witnesses): a call with one output operand is `apply`; nothing is a test or an index. -/
def Interp.ofFns (F : Op → BlockFn K) : Interp Op Tst K where
  call o d ins outs τ m :=
    match outs with
    | [z] => (F o).apply d ins z τ m
    | _ => none
  test _ _ _ _ := none
  index _ _ _ := none

theorem Interp.ofFns_callS (F : Op → BlockFn K) (o : Op) (d : List ℕ) (ins : List (ℕ × ℕ))
    (z : ℕ × ℕ) (τ : ℕ → K) (m : Mem K) :
    (Interp.ofFns F : Interp Op Tst K).callS o d ins [z] τ m = (F o).apply d ins z τ m := by
  by_cases hl : m.Live (ins ++ [z])
  · simp only [Interp.callS, Interp.ofFns, hl, if_true]
    cases h : (F o).apply d ins z τ m with
    | none => rfl
    | some m' => simp [BlockFn.shape_of_apply h]
  · simp [Interp.callS, BlockFn.apply, hl]

/-- An interpretation given by block functions meets their functional contracts, in both modes
and on all operands. -/
theorem Interp.ofFns_isFn (F : Op → BlockFn K) (md : Mode) (o : Op)
    (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) :
    (Interp.ofFns F : Interp Op Tst K).IsFn md o (F o) adm := by
  rintro d ins outs τ m ⟨z, rfl, -, hn⟩
  rw [Interp.ofFns_callS]
  cases md with
  | total =>
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp (hn rfl)
    exact ⟨m', hm', z, rfl, hm'⟩
  | liberal => exact fun m' hm' => ⟨z, rfl, hm'⟩

/-- The exactness of a test, imposed by the access model: the Boolean is the function `f` of the
input blocks. -/
def Interp.IsTest (I : Interp Op Tst K) (o : Tst) (lens : List ℕ → List ℕ)
    (f : List ℕ → List (List K) → Bool) : Prop :=
  ∀ d a m xs, m.readBlocks a (lens d) = some xs → I.test o d a m = some (f d xs)

/-- The exactness of an index conversion, imposed by the access model: the number is the function
`f` of the input cells. -/
def Interp.IsIndex (I : Interp Op Tst K) (o : Tst) (f : List K → ℕ) : Prop :=
  ∀ a m xs, m.readBlocks a (a.map fun _ => 1) = some xs → I.index o a m = some (f xs.flatten)

end NLAlib.Ops
