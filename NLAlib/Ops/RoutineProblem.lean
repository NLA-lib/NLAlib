/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Confined
public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Logic.Step
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.StoredOperator

/-!
# The problem of a routine

A certificate is about a problem: the sizes admitted, the inputs admitted at each size, and the
buffers supplied for them. This file builds that problem from the interface of a routine, so
that its author states mathematics only.

A `NLAlib.Ops.Codec` says what an operand holds: a scalar, a vector, a matrix, a tuple of
these, or raw words. Encoding and decoding are mutually inverse at the length of the operand.

A `NLAlib.Ops.Routine.Domain` of a routine gives the admitted sizes (`valid`), the type of the
inputs at each size (`In`), the admitted inputs (`accepts`), and for every operand a
`NLAlib.Ops.Slot`:

* `stored c get`: the buffer holds the encoding by `c` of the component `get` of the inputs;
* `derived len f`: the buffer holds the words `f` of the inputs, a quantity computed from them
  (a threshold, say). This is the only way a buffer may depend on the inputs otherwise than by
  holding one of them, and `NLAlib.Ops.Routine.Domain.derived` lists these operands;
* `blank len`: the buffer is `len` uninitialised cells.

The slots agree with the interface (`fits`): an operand that is read is `stored` or `derived`, an
operand that is only written is `blank`, and the lengths are those of the ports. The inputs are
determined by the stored buffers and the declared unstored part (`faithful`): no other
input is in no buffer. `NLAlib.Ops.Routine.Domain.Oracles` declares the operations of a model
through which unstored data is reached.

`NLAlib.Ops.Routine.Domain.problem` is the problem: the supplied buffers are exactly those of the
slots, and nothing else is admitted. So an input of the problem is an admitted tuple of inputs
and conversely (`NLAlib.Ops.Routine.Domain.inputEquiv`): the certificate covers every input that
satisfies `accepts`.

## Main definitions

* `NLAlib.Ops.Codec`: what an operand holds.
* `NLAlib.Ops.Slot`: the buffer supplied for an operand.
* `NLAlib.Ops.Routine.Domain`, `NLAlib.Ops.Routine.Domain.problem`: the admitted inputs of a
  routine and its problem.
* `NLAlib.Ops.Routine.Domain.algorithm`: the certificate of a routine on its problem.

## Main results

* `NLAlib.Ops.Routine.Domain.inputEquiv`, `NLAlib.Ops.Routine.Domain.covers`: the inputs of the
  problem are the admitted inputs.
* `NLAlib.Ops.Routine.Domain.readBlocks_initial`, `NLAlib.Ops.Routine.Domain.room_initial`: the
  initial memory holds the blocks read and has room for the blocks written.
* `NLAlib.Ops.Routine.Domain.checked`: what a certificate states, for the admitted inputs.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-! ### What an operand holds -/

/-- **What an operand holds**: values of type `α` as blocks of `len` words. Encoding and decoding
are mutually inverse on blocks of that length, so a block is a value and a value is a block. -/
structure Codec (K α : Type) where
  /-- The number of words of a value. -/
  len : ℕ
  /-- The words of a value. -/
  encode : α → List K
  /-- The value of a block. -/
  decode : List K → α
  /-- A value has `len` words. -/
  length_encode : ∀ a, (encode a).length = len
  /-- Decoding recovers the value. -/
  decode_encode : ∀ a, decode (encode a) = a
  /-- Every block of the length is the encoding of its value. -/
  encode_decode : ∀ ws : List K, ws.length = len → encode (decode ws) = ws

namespace Codec

attribute [simp] length_encode decode_encode

/-- Encoding is injective. -/
theorem encode_injective {α : Type} (c : Codec K α) : Function.Injective c.encode :=
  fun a b h => by rw [← c.decode_encode a, h, c.decode_encode]

/-- One word. -/
def scalar [Inhabited K] : Codec K K where
  len := 1
  encode a := [a]
  decode ws := ws.headD default
  length_encode _ := rfl
  decode_encode _ := rfl
  encode_decode ws h := by
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
    rfl

/-- A vector of `n` words. -/
def vector [Inhabited K] (n : ℕ) : Codec K (Fin n → K) where
  len := n
  encode v := List.ofFn v
  decode ws := fun i => ws.getD i default
  length_encode _ := List.length_ofFn
  decode_encode v := by
    funext i
    simp
  encode_decode ws h := by
    subst h
    exact List.ext_getElem (by simp) fun i h₁ h₂ => by simp

/-- Raw words: a block of `n` words, as it is. The honest type of an operand whose
specification is stated on words. -/
def words [Inhabited K] (n : ℕ) : Codec K { ws : List K // ws.length = n } where
  len := n
  encode ws := ws.val
  decode ws := if h : ws.length = n then ⟨ws, h⟩ else ⟨List.replicate n default, by simp⟩
  length_encode ws := ws.property
  decode_encode ws := by simp [ws.property]
  encode_decode ws h := by simp [h]

/-- A matrix, column by column, each entry in the words of the entry codec. -/
def matrix [Inhabited K] {E : Type} (C : EntryCodec K E) (rows cols : ℕ) :
    Codec K (Matrix (Fin rows) (Fin cols) E) where
  len := cols * rows * C.width
  encode A := C.packFinMatrix A
  decode ws := C.matrix rows cols ws
  length_encode A := C.length_packFinMatrix A
  decode_encode A := C.matrix_packFinMatrix A
  encode_decode ws h := C.packFinMatrix_matrix rows cols ws h

/-- A pair of values, one after the other: a tuple of parameters is an iterated pair. -/
def prod {α β : Type} (c₁ : Codec K α) (c₂ : Codec K β) : Codec K (α × β) where
  len := c₁.len + c₂.len
  encode p := c₁.encode p.1 ++ c₂.encode p.2
  decode ws := (c₁.decode (ws.take c₁.len), c₂.decode (ws.drop c₁.len))
  length_encode p := by simp
  decode_encode p := by
    rw [List.take_left' (c₁.length_encode p.1), List.drop_left' (c₁.length_encode p.1)]
    simp
  encode_decode ws h := by
    rw [c₁.encode_decode _ (by simp only [List.length_take]; omega),
      c₂.encode_decode _ (by simp only [List.length_drop]; omega), List.take_append_drop]

/-- The same blocks read as values of an equivalent type. -/
def map {α β : Type} (c : Codec K α) (e : α ≃ β) : Codec K β where
  len := c.len
  encode b := c.encode (e.symm b)
  decode ws := e (c.decode ws)
  length_encode _ := c.length_encode _
  decode_encode b := by simp
  encode_decode ws h := by simp [c.encode_decode ws h]

end Codec

/-! ### The buffer supplied for an operand -/

/-- **The buffer supplied for an operand**, as a function of the inputs `In`. -/
inductive Slot (K In : Type) : Type 1 where
  /-- The buffer holds the encoding of a component of the inputs. -/
  | stored {α : Type} (c : Codec K α) (get : In → α)
  /-- The buffer holds `len` words computed from the inputs. -/
  | derived (len : ℕ) (f : In → List K) (hf : ∀ x, (f x).length = len)
  /-- The buffer is `len` uninitialised cells. -/
  | blank (len : ℕ)

namespace Slot

variable {In : Type}

/-- The number of cells of the buffer. -/
def len : Slot K In → ℕ
  | stored c _ => c.len
  | derived n _ _ => n
  | blank n => n

/-- The buffer holds words: it is not blank. -/
def held : Slot K In → Bool
  | blank _ => false
  | _ => true

/-- The buffer holds words computed from the inputs, not one of the inputs. -/
def isDerived : Slot K In → Bool
  | derived _ _ _ => true
  | _ => false

/-- The words the buffer holds at the inputs `x`; none for a blank buffer. -/
def words : Slot K In → In → List K
  | stored c get, x => c.encode (get x)
  | derived _ f _, x => f x
  | blank _, _ => []

/-- The words of an input held by the buffer; `none` unless the slot is `stored`. -/
def input : Slot K In → In → Option (List K)
  | stored c get, x => some (c.encode (get x))
  | _, _ => none

/-- The supplied buffer at the inputs `x`. -/
def buffer : Slot K In → In → Buf K
  | blank n, _ => List.replicate n none
  | s, x => (s.words x).map some

@[simp] theorem length_buffer (s : Slot K In) (x : In) : (s.buffer x).length = s.len := by
  cases s <;> simp [buffer, words, len, *]

theorem length_words_of_held {s : Slot K In} (h : s.held = true) (x : In) :
    (s.words x).length = s.len := by
  cases s with
  | stored c get => exact c.length_encode _
  | derived n f hf => exact hf x
  | blank n => exact absurd h (by simp [held])

theorem buffer_of_held {s : Slot K In} (h : s.held = true) (x : In) :
    s.buffer x = (s.words x).map some := by
  cases s <;> first | rfl | exact absurd h (by simp [held])

/-- A derived slot of `len` cells for the words `f` of the inputs, when it is the admission and
not the type of the inputs that equates the number of words with `len` (a dimension): the words
are cut or padded to `len`, and are `f x` at every input with `(f x).length = len`
(`NLAlib.Ops.Slot.words_derivedOfLength`). -/
def derivedOfLength [Inhabited K] (len : ℕ) (f : In → List K) : Slot K In :=
  .derived len (fun x => (f x).take len ++ List.replicate (len - (f x).length) default)
    (fun x => by simp only [List.length_append, List.length_take, List.length_replicate]; omega)

/-- At an input whose words have the length of the slot, the slot holds those words. -/
theorem words_derivedOfLength [Inhabited K] {len : ℕ} {f : In → List K} {x : In}
    (h : (f x).length = len) : (derivedOfLength len f).words x = f x := by
  simp [derivedOfLength, words, ← h]

/-- At an input whose words have the length of the slot, the buffer holds those words. -/
theorem buffer_derivedOfLength [Inhabited K] {len : ℕ} {f : In → List K} {x : In}
    (h : (f x).length = len) : (derivedOfLength len f).buffer x = (f x).map some := by
  rw [show (derivedOfLength len f).buffer x = ((derivedOfLength len f).words x).map some from rfl,
    words_derivedOfLength h]

end Slot

/-- Decoding the encoding of a vector of words decodes its entries. -/
theorem decv_ofFn_apply [Inhabited K] (dec : K → ℝ) {n : ℕ} (v : Fin n → K) :
    decv dec n (List.ofFn v) = fun i => dec (v i) :=
  funext fun i => by simp [decv, vec, List.getD_eq_getElem?_getD]

/-- A real matrix stored column by column, one word per entry, decodes to itself. -/
theorem StoredOperator.denseMatrix_packFinMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    StoredOperator.denseMatrix m n ((EntryCodec.scalar ℝ).packFinMatrix A) = A := by
  have h : StoredOperator.denseMatrix m n ((EntryCodec.scalar ℝ).packFinMatrix A) =
      (EntryCodec.scalar ℝ).matrix m n ((EntryCodec.scalar ℝ).packFinMatrix A) := by
    funext i j
    simp only [StoredOperator.denseMatrix, EntryCodec.matrix, EntryCodec.scalar_entry, vec,
      Matrix.of_apply]
    rfl
  rw [h, EntryCodec.matrix_packFinMatrix]

/-! ### Selections of the operands of an interface -/

namespace Routine

variable {α : Type}

/-- A selection of operands that are in pairs: the entries selected from a list of pairs. -/
private theorem sel_cons (p : Port) (ps : List Port) (q : Access → Bool) (x : α) (xs : List α) :
    ((((p :: ps).zip (x :: xs)).filter fun z => q z.1.access).map Prod.snd) =
      if q p.access then x :: ((ps.zip xs).filter fun z => q z.1.access).map Prod.snd
      else ((ps.zip xs).filter fun z => q z.1.access).map Prod.snd := by
  simp only [List.zip_cons_cons, List.filter_cons]
  split <;> rfl

/-- The blocks at the selected operands are read one by one. -/
private theorem readBlocks_selList (m : Mem K) (q : Access → Bool) :
    ∀ (ps : List Port) (args : List (ℕ × ℕ)) (ls : List ℕ) (ws : List (List K)),
      args.length = ps.length → ls.length = ps.length → ws.length = ps.length →
      (∀ j p, ps[j]? = some p → q p.access = true →
        m.store.readBlock (args.getD j (0, 0)).1 (args.getD j (0, 0)).2 (ls.getD j 0) =
          some (ws.getD j [])) →
      m.readBlocks (((ps.zip args).filter fun z => q z.1.access).map Prod.snd)
          (((ps.zip ls).filter fun z => q z.1.access).map Prod.snd) =
        some (((ps.zip ws).filter fun z => q z.1.access).map Prod.snd)
  | [], _, _, _, _, _, _, _ => by simp
  | p :: ps, a :: args, l :: ls, w :: ws, ha, hl, hw, h => by
    have ih := readBlocks_selList m q ps args ls ws (by simpa using ha) (by simpa using hl)
      (by simpa using hw) fun j p' hp hq => by simpa using h (j + 1) p' (by simpa using hp) hq
    rw [sel_cons, sel_cons, sel_cons]
    by_cases hq : q p.access = true
    · rw [if_pos hq, if_pos hq, if_pos hq]
      exact Mem.readBlocks_of_cons (by simpa using h 0 p rfl hq) ih
    · rw [if_neg hq, if_neg hq, if_neg hq]
      exact ih
  | _ :: _, [], _, _, ha, _, _, _ => by simp at ha
  | _ :: _, _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, _ :: _, [], _, _, hw, _ => by simp at hw

/-- There is room at the selected operands when there is room at each. -/
private theorem room_selList (m : Mem K) (q : Access → Bool) :
    ∀ (ps : List Port) (args : List (ℕ × ℕ)) (ls : List ℕ),
      args.length = ps.length → ls.length = ps.length →
      (∀ j p, ps[j]? = some p → q p.access = true →
        (args.getD j (0, 0)).2 + ls.getD j 0 ≤ m.store.len (args.getD j (0, 0)).1) →
      m.Room (((ps.zip args).filter fun z => q z.1.access).map Prod.snd)
          (((ps.zip ls).filter fun z => q z.1.access).map Prod.snd)
  | [], _, _, _, _, _ => by simp
  | p :: ps, a :: args, l :: ls, ha, hl, h => by
    have ih := room_selList m q ps args ls (by simpa using ha) (by simpa using hl)
      fun j p' hp hq => by simpa using h (j + 1) p' (by simpa using hp) hq
    rw [sel_cons, sel_cons]
    by_cases hq : q p.access = true
    · rw [if_pos hq, if_pos hq]
      exact ⟨by simpa using h 0 p rfl hq, ih⟩
    · rw [if_neg hq, if_neg hq]
      exact ih
  | _ :: _, [], _, ha, _, _ => by simp at ha
  | _ :: _, _ :: _, [], _, hl, _ => by simp at hl

end Routine

/-! ### The admitted inputs of a routine and its problem -/

variable {r b : ℕ}

/-- **The admitted inputs of a routine**: the sizes, the type of the inputs, which of them are
admitted, and the buffer supplied for each operand. Everything here is mathematics or follows
the interface: `valid` and `accepts` are the conditions a reader checks; the slots say which
input each operand holds. -/
structure Routine.Domain (R : Routine Op Tst) (K : Type) (r b : ℕ) where
  /-- The storage of the supplied buffers. -/
  formats : Fin b → StorageFormat := fun _ => .cell
  /-- The admitted sizes. -/
  valid : (Fin r → ℕ) → Prop
  /-- The inputs at the sizes. -/
  In : (Fin r → ℕ) → Type
  /-- The admitted inputs. -/
  accepts : (d : Fin r → ℕ) → In d → Prop
  /-- The buffer supplied for each operand. -/
  slot : (d : Fin r → ℕ) → Fin b → Slot K (In d)
  /-- The sizes are the dimensions and the buffers the operands. -/
  shape : R.nd = r ∧ R.ports.length = b := by exact ⟨rfl, rfl⟩
  /-- The slots follow the interface: the length of each is that of its port, and a buffer
  holds words exactly when its operand is read. -/
  fits : ∀ (d : Fin r → ℕ) (i : Fin b) (p : Port), R.ports[i.val]? = some p →
    p.len (List.ofFn d) = (slot d i).len ∧ (slot d i).held = p.access.readable
  /-- The type of the part of the inputs that is in no buffer (an operator reached only through
  operations of the model). Most routines have none. -/
  Unstored : (Fin r → ℕ) → Type := fun _ => Unit
  /-- The part of the inputs that is in no buffer. It can affect a run only through an operation
  whose contract mentions it; `NLAlib.Ops.Routine.Domain.Oracles` declares which. -/
  unstored : (d : Fin r → ℕ) → In d → Unstored d := by exact fun _ _ => ()
  /-- The inputs are determined by the declared unstored part and the buffers that hold the
  rest: no other input is in no buffer. -/
  faithful : ∀ (d : Fin r → ℕ) (x y : In d), unstored d x = unstored d y →
    (∀ i, (slot d i).input x = (slot d i).input y) → x = y
  /-- Some size is admitted. -/
  admitted : ∃ d, valid d
  /-- Some input is admitted at every admitted size. -/
  inhabited : ∀ d, valid d → ∃ x, accepts d x

namespace Routine.Domain

variable {R : Routine Op Tst} (D : R.Domain K r b)

/-- The operands whose buffer holds words computed from the inputs. -/
def derived (d : Fin r → ℕ) : List (Fin b) :=
  (List.finRange b).filter fun i => (D.slot d i).isDerived

/-- The supplied buffers at the inputs `x`. -/
def buffers (d : Fin r → ℕ) (x : D.In d) : Fin b → Buf K := fun i => (D.slot d i).buffer x

@[simp] theorem length_buffers (d : Fin r → ℕ) (x : D.In d) (i : Fin b) :
    (D.buffers d x i).length = (D.slot d i).len := Slot.length_buffer _ _

/-- **The problem of a routine**: the admitted inputs, with exactly the buffers of the slots. -/
def problem : Problem K r b where
  formats := D.formats
  valid := D.valid
  Data := D.In
  admissible d x bufs := D.accepts d x ∧ bufs = D.buffers d x
  admitted := D.admitted
  supply d hd := by
    obtain ⟨x, hx⟩ := D.inhabited d hd
    exact ⟨x, D.buffers d x, hx, rfl⟩

/-- The input of the problem at an admitted tuple of inputs. -/
def input (d : Fin r → ℕ) (x : D.In d) (hx : D.accepts d x) : D.problem.Input d :=
  ⟨(x, D.buffers d x), hx, rfl⟩

/-- **The inputs of the problem are the admitted inputs.** -/
def inputEquiv (d : Fin r → ℕ) : D.problem.Input d ≃ { x : D.In d // D.accepts d x } where
  toFun X := ⟨X.val.1, X.property.1⟩
  invFun x := D.input d x.val x.property
  left_inv X := Subtype.ext (Prod.ext rfl X.property.2.symm)
  right_inv _ := rfl

/-- Coverage: every admitted tuple of inputs is the data of exactly one input of the
problem. -/
theorem covers (d : Fin r → ℕ) (x : D.In d) (hx : D.accepts d x) :
    ∃! X : D.problem.Input d, X.val.1 = x := by
  refine ⟨D.input d x hx, rfl, fun X hX => Subtype.ext (Prod.ext hX ?_)⟩
  rw [X.property.2]
  exact congrArg (D.buffers d) hX

/-- The inputs of an input of the problem are admitted. -/
theorem accepts_data {d : Fin r → ℕ} (X : D.problem.Input d) : D.accepts d X.val.1 :=
  X.property.1

/-- The buffers of an input of the problem are those of the slots. -/
theorem buffers_eq {d : Fin r → ℕ} (X : D.problem.Input d) : X.val.2 = D.buffers d X.val.1 :=
  X.property.2

/-- The initial memory at the inputs `x`: the buffers of the slots, at tape position zero. -/
def memory (d : Fin r → ℕ) (x : D.In d) : Mem K := ⟨List.ofFn (D.buffers d x), 0⟩

theorem initial_eq {d : Fin r → ℕ} (X : D.problem.Input d) :
    D.problem.initial d X = D.memory d X.val.1 := by
  unfold Problem.initial memory
  rw [D.buffers_eq X]

/-- The blocks the routine reads at the inputs `x`, in the order of its readable operands. -/
def blocks (d : Fin r → ℕ) (x : D.In d) : List (List K) :=
  R.sel Access.readable (List.ofFn fun i => (D.slot d i).words x)

end Routine.Domain

namespace Routine.Domain

variable {R : Routine Op Tst} (D : R.Domain K r b)

private theorem getD_slots {j : ℕ} (hj : j < b) : (slots b).getD j (0, 0) = (j, 0) := by
  simp [slots, hj]

private theorem getD_lens (d : List ℕ) {j : ℕ} {p : Port} (hp : R.ports[j]? = some p) :
    (R.lens d).getD j 0 = p.len d := by
  simp [Routine.lens, List.getD_eq_getElem?_getD, hp]

private theorem getD_words (d : Fin r → ℕ) (x : D.In d) {j : ℕ} (hj : j < b) :
    (List.ofFn fun i => (D.slot d i).words x).getD j [] = (D.slot d ⟨j, hj⟩).words x := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- The initial memory holds the blocks read: the readable operands of the routine, at the
supplied buffers, read the words of their slots. -/
theorem readBlocks_initial {d : Fin r → ℕ} (X : D.problem.Input d) :
    (D.problem.initial d X).readBlocks (R.readArgs (slots b)) (R.readLens (List.ofFn d)) =
      some (D.blocks d X.val.1) := by
  refine Routine.readBlocks_selList _ _ R.ports (slots b) (R.lens (List.ofFn d)) _
    (by simp [slots, D.shape.2]) (by simp [Routine.lens]) (by simp [D.shape.2]) ?_
  intro j p hp hq
  have hj : j < b := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    rwa [D.shape.2] at this
  obtain ⟨hlen, hheld⟩ := D.fits d ⟨j, hj⟩ p hp
  rw [hq] at hheld
  rw [getD_slots hj, getD_lens _ hp, D.getD_words d X.val.1 hj, hlen,
    ← Slot.length_words_of_held hheld X.val.1]
  refine Problem.initial_readBlock d X ⟨j, hj⟩ ?_
  rw [D.buffers_eq X]
  exact Slot.buffer_of_held hheld _

/-- The initial memory has room for the blocks written. -/
theorem room_initial {d : Fin r → ℕ} (X : D.problem.Input d) :
    (D.problem.initial d X).Room (R.writeArgs (slots b)) (R.writeLens (List.ofFn d)) := by
  refine Routine.room_selList _ _ R.ports (slots b) (R.lens (List.ofFn d))
    (by simp [slots, D.shape.2]) (by simp [Routine.lens]) ?_
  intro j p hp _
  have hj : j < b := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    rwa [D.shape.2] at this
  rw [getD_slots hj, getD_lens _ hp, (D.fits d ⟨j, hj⟩ p hp).1,
    Problem.initial_len d X ⟨j, hj⟩, D.buffers_eq X]
  exact (Nat.zero_add _).trans_le (D.length_buffers d X.val.1 ⟨j, hj⟩).ge

/-- **The certificate of a routine on its problem.** The routine meets `Sp` at the admitted
inputs under every interpretation of the model, the blocks read satisfy the precondition
(`hpre`), and the output of `S` follows from the postcondition (`hgood`). That the supplied
buffers hold the blocks read and have room for the blocks written is not a hypothesis: it holds
by the construction of the problem. The resource hypotheses are those of
`NLAlib.Ops.Routine.algorithm`. -/
def algorithm {M : AccessModel Op Tst D.problem} {S : Specification Op Tst D.problem}
    (Sp : (d : Fin r → ℕ) → D.In d → Routine.Spec K)
    (hmeets : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (I : Interp Op Tst K),
      M.contracts d X I → R.Meets I (Sp d X.val.1))
    (hpre : ∀ d, D.valid d → ∀ x, D.accepts d x → ∀ τ : Tape K,
      (Sp d x).pre (List.ofFn d) τ (D.blocks d x))
    (hgood : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (τ : Tape K) (m' : Mem K),
      (D.problem.initial d X).store.EqOff
        (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) m'.store →
      R.Advances (List.ofFn d) 0 m'.pos → ∀ ys,
      m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys →
      (Sp d X.val.1).post (List.ofFn d) τ (D.blocks d X.val.1) ys →
      ∀ c, c ≤ S.budget d → S.good d X τ c m')
    (hcost : ∀ d, D.valid d → staticCost (R.close r b) d ≤ S.budget d := by
      intro _ _; exact le_rfl)
    (hspace : ∀ d, D.valid d → staticPeak M.resources (R.close r b) d ≤ S.scratch d := by
      intro _ _; exact le_rfl)
    (hwork : ∀ d, D.valid d → M.resources.work (S.budget d) ≤ S.work d := by
      intro _ _; exact le_rfl)
    (hspan : ∀ d, D.valid d → M.resources.span (S.budget d) ≤ S.span d := by
      intro _ _; exact le_rfl)
    (hmemory : ∀ d, D.valid d → ∀ X : D.problem.Input d,
      D.problem.initialBytes d X + S.scratch d ≤ S.memory d)
    (ht : (R.close r b).wellTyped M.resources D.problem.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) : Algorithm M S :=
  R.algorithm (P := D.problem) (fun d X => Sp d X.val.1) (fun d X => D.blocks d X.val.1) hmeets
    (fun d hd X => ⟨D.readBlocks_initial X, fun τ => hpre d hd _ (D.accepts_data X) τ,
      D.room_initial X⟩)
    hgood hcost hspace hwork hspan hmemory D.shape ht hfit hflat hcontig

/-- The certificate of a routine on its problem, when the specification depends on the input
of the problem and not only on its data: a model may supply further data at an input (the
matrix of a matrix-free solver). The same construction as
`NLAlib.Ops.Routine.Domain.algorithm`. -/
def algorithmAt {M : AccessModel Op Tst D.problem} {S : Specification Op Tst D.problem}
    (Sp : (d : Fin r → ℕ) → D.problem.Input d → Routine.Spec K)
    (hmeets : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (I : Interp Op Tst K),
      M.contracts d X I → R.Meets I (Sp d X))
    (hpre : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (τ : Tape K),
      (Sp d X).pre (List.ofFn d) τ (D.blocks d X.val.1))
    (hgood : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (τ : Tape K) (m' : Mem K),
      (D.problem.initial d X).store.EqOff
        (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) m'.store →
      R.Advances (List.ofFn d) 0 m'.pos → ∀ ys,
      m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys →
      (Sp d X).post (List.ofFn d) τ (D.blocks d X.val.1) ys →
      ∀ c, c ≤ S.budget d → S.good d X τ c m')
    (hcost : ∀ d, D.valid d → staticCost (R.close r b) d ≤ S.budget d := by
      intro _ _; exact le_rfl)
    (hspace : ∀ d, D.valid d → staticPeak M.resources (R.close r b) d ≤ S.scratch d := by
      intro _ _; exact le_rfl)
    (hwork : ∀ d, D.valid d → M.resources.work (S.budget d) ≤ S.work d := by
      intro _ _; exact le_rfl)
    (hspan : ∀ d, D.valid d → M.resources.span (S.budget d) ≤ S.span d := by
      intro _ _; exact le_rfl)
    (hmemory : ∀ d, D.valid d → ∀ X : D.problem.Input d,
      D.problem.initialBytes d X + S.scratch d ≤ S.memory d)
    (ht : (R.close r b).wellTyped M.resources D.problem.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) : Algorithm M S :=
  R.algorithm (P := D.problem) Sp (fun d X => D.blocks d X.val.1) hmeets
    (fun d hd X => ⟨D.readBlocks_initial X, fun τ => hpre d hd X τ, D.room_initial X⟩)
    hgood hcost hspace hwork hspan hmemory D.shape ht hfit hflat hcontig

/-- The resident payload of the problem: the cells of the slots, in their storage. -/
theorem initialBytes_eq {d : Fin r → ℕ} (X : D.problem.Input d) :
    D.problem.initialBytes d X =
      (List.ofFn fun i => (D.formats i).bytes * (D.slot d i).len).sum := by
  refine Problem.initialBytes_of_lengths d X _ fun i => ?_
  exact (congrArg List.length (congrFun (D.buffers_eq X) i)).trans
    (D.length_buffers d X.val.1 i)

/-- What a certificate states, for the admitted inputs. For every admitted size, every
tuple of inputs satisfying `accepts`, every interpretation satisfying the contracts of the model
and every tape, the run of the fixed program from the buffers of the slots succeeds, within
the scratch, the budget, the work, the span and the memory of the specification, and its final
memory satisfies the output condition. -/
theorem checked {M : AccessModel Op Tst D.problem} {S : Specification Op Tst D.problem}
    (A : Algorithm M S) (d : Fin r → ℕ) (hd : D.valid d) (x : D.In d) (hx : D.accepts d x)
    (I : Interp Op Tst K) (hI : M.contracts d (D.input d x hx) I) (τ : Tape K) :
    ∃ st, exec A.program I M.resources D.formats τ d (D.memory d x) = some st ∧
      st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
      M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
      S.good d (D.input d x hx) τ st.cost st.mem := by
  obtain ⟨st, hr, hp, hc, hw, hs, -, hg⟩ := A.correct d hd (D.input d x hx) I hI τ
  exact ⟨st, hr, hp, hc, hw, hs, hg⟩

/-- The resident payload at the sizes: the cells of the slots, in their storage. -/
def bytes (d : Fin r → ℕ) : ℕ := (List.ofFn fun i => (D.formats i).bytes * (D.slot d i).len).sum

/-- **The counted certificate of a routine on its problem**: `NLAlib.Ops.Routine.certify` with
the obligations about the initial memory and the payload proved from the slots. The author
gives the judgment, the precondition at the admitted inputs, and a bound `work` of the
instruction polynomial of the tree; every weight of the model is at most one. -/
noncomputable def certify {M : AccessModel Op Tst D.problem}
    (Sp : (d : Fin r → ℕ) → D.In d → Routine.Spec K) (work : (Fin r → ℕ) → ℕ)
    (hmeets : ∀ d, D.valid d → ∀ (X : D.problem.Input d) (I : Interp Op Tst K),
      M.contracts d X I → R.Meets I (Sp d X.val.1))
    (hpre : ∀ d, D.valid d → ∀ x, D.accepts d x → ∀ τ : Tape K,
      (Sp d x).pre (List.ofFn d) τ (D.blocks d x))
    (hop : ∀ o d, M.resources.operationWork o d ≤ 1)
    (hcore : ∀ k d, M.resources.coreWork k d ≤ 1) (hq : ∀ q d, M.resources.queryWork q d ≤ 1)
    (hwork : ∀ d, D.valid d → CountPoly.eval (List.ofFn d) (R.close r b).countPoly ≤ work d)
    (ht : (R.close r b).wellTyped M.resources D.problem.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) :
    Algorithm M (R.specification (P := D.problem) (fun d X => Sp d X.val.1) M.resources
      (fun d X => D.blocks d X.val.1) D.bytes work) :=
  R.certify (P := D.problem) (fun d X => Sp d X.val.1) (fun d X => D.blocks d X.val.1) D.bytes
    work hmeets
    (fun d hd X => ⟨D.readBlocks_initial X, fun τ => hpre d hd _ (D.accepts_data X) τ,
      D.room_initial X⟩)
    (fun _ _ X => (D.initialBytes_eq X).le) hop hcore hq hwork D.shape ht hfit hflat hcontig

/-- What a counted certificate states, for the admitted inputs: the run of the fixed program
from the buffers of the slots succeeds, its work is at most `work`, and the reported operands
hold blocks satisfying the postcondition of the routine at the blocks of the inputs. -/
theorem checked_post {M : AccessModel Op Tst D.problem}
    {Sp : (d : Fin r → ℕ) → D.In d → Routine.Spec K} {work : (Fin r → ℕ) → ℕ}
    (A : Algorithm M (R.specification (P := D.problem) (fun d X => Sp d X.val.1) M.resources
      (fun d X => D.blocks d X.val.1) D.bytes work))
    (d : Fin r → ℕ) (hd : D.valid d) (x : D.In d) (hx : D.accepts d x)
    (I : Interp Op Tst K) (hI : M.contracts d (D.input d x hx) I) (τ : Tape K) :
    ∃ st, exec A.program I M.resources D.formats τ d (D.memory d x) = some st ∧
      M.resources.work st.cost ≤ work d ∧ ∃ ys,
        st.mem.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys ∧
          (Sp d x).post (List.ofFn d) τ (D.blocks d x) ys := by
  obtain ⟨st, hr, -, -, hw, -, -, ys, hys, hpost⟩ := D.checked A d hd x hx I hI τ
  exact ⟨st, hr, hw, ys, hys, hpost⟩

/-- A domain depends on its routine only through the interface: the admitted inputs of a
routine are those of any routine with the same dimensions and operands (a routine with another
tree, or with a parameter the problem does not mention). -/
def cast (R' : Routine Op Tst) (hnd : R'.nd = R.nd) (hports : R'.ports = R.ports) :
    R'.Domain K r b where
  formats := D.formats
  valid := D.valid
  In := D.In
  accepts := D.accepts
  slot := D.slot
  shape := ⟨hnd.trans D.shape.1, (congrArg List.length hports).trans D.shape.2⟩
  fits d i p hp := D.fits d i p (hports ▸ hp)
  Unstored := D.Unstored
  unstored := D.unstored
  faithful := D.faithful
  admitted := D.admitted
  inhabited := D.inhabited

/-- The problem of a domain read at another routine with the same interface is the same. -/
@[simp] theorem problem_cast (R' : Routine Op Tst) (hnd : R'.nd = R.nd)
    (hports : R'.ports = R.ports) : (D.cast R' hnd hports).problem = D.problem := rfl

end Routine.Domain

namespace Routine.Domain

variable {R : Routine Op Tst}

/-- **The oracles of a model on the problem of a routine.** Data that is in no buffer can
affect a run only through an operation whose contract mentions it. This declares those
operations: every other operation and every query has one contract at all sizes and inputs
(as for `NLAlib.Ops.AccessModel.Uniform`), and the contract of a declared operation depends on
the input only through its declared unstored part. A reader of a certificate whose inputs are
not all in memory checks the contracts and the costs of the operations in `ops`: the cost of
the certificate is counted in calls of them. -/
structure Oracles (D : R.Domain K r b) (M : AccessModel Op Tst D.problem) where
  /-- The operations whose contract may depend on the unstored inputs or on the sizes. -/
  ops : List Op
  /-- Every other operation has the same contract at every size and input. -/
  operation : ∀ o, o ∉ ops → ∀ d x d' x', M.operation d x o = M.operation d' x' o
  /-- Every query has the same contract at every size and input. -/
  query : ∀ d x d' x' q, M.query d x q = M.query d' x' q
  /-- A declared operation sees the input only through its unstored part. -/
  through : ∀ o, o ∈ ops → ∀ d (X Y : D.problem.Input d),
    D.unstored d X.val.1 = D.unstored d Y.val.1 → M.operation d X o = M.operation d Y o

/-- A model with no declared oracle is uniform. -/
theorem Oracles.uniform {D : R.Domain K r b} {M : AccessModel Op Tst D.problem}
    (O : D.Oracles M) (h : O.ops = []) : M.Uniform :=
  ⟨fun d x d' x' o => O.operation o (by simp [h]) d x d' x', O.query⟩

/-- A uniform model declares no oracle. -/
def Oracles.ofUniform (D : R.Domain K r b) (M : AccessModel Op Tst D.problem) [hM : M.Uniform] :
    D.Oracles M where
  ops := []
  operation o _ := fun d x d' x' => hM.operation d x d' x' o
  query := hM.query
  through o ho := absurd ho (by simp)

end Routine.Domain

/-- Prove `NLAlib.Ops.Routine.Domain.fits` for a routine with a literal interface: for each
operand, the length of its slot is that of its port and it holds words exactly when it is
read. -/
macro (name := domainFits) "domain_fits" : tactic => `(tactic| (
  intro d i p hp
  fin_cases i <;> (
    have hport := Option.some.inj hp
    subst hport
    first
      | exact ⟨rfl, rfl⟩
      | (constructor <;>
          simp [Slot.len, Slot.held, Access.readable, List.ofFn_succ, Codec.vector,
            Codec.scalar, Codec.words, Codec.matrix, Codec.prod, Codec.map]))))

end NLAlib.Ops
