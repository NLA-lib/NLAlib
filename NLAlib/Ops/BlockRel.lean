/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Attr
public import NLAlib.Ops.Contract

/-!
# Contracts in operand form

**One structure for every contract of the library.** A `NLAlib.Ops.BlockRel` gives, at the
dimensions of a call: the lengths of the input blocks, the lengths of the output blocks (any
number of each), the stream and the length of a tape window, a domain (what the inputs must
satisfy for the call to succeed) and a relation between the input blocks, the entries of the
window and the output blocks. Its contract `NLAlib.Ops.BlockRel.spec` says: on admitted operands,
the call reads the input blocks, writes output blocks of the declared lengths that are related to
the inputs and to the window, advances the tape by the window, and changes nothing else.

The three kinds of contract are instances.

* **Relational**: the relation is a bound (`dot`, `axpy`, a factorization `qr` with two output
  blocks, a rotation that updates two vectors).
* **Functional**: the relation is the graph of a function (`NLAlib.Ops.BlockFn.rel`, file
  `NLAlib.Ops.Blocks`); the domain is where the function is defined.
* **With a window**: the relation mentions the window. A visible draw returns the window
  (`NLAlib.Ops.drawRel`); an operation with hidden randomness returns a function of its inputs
  and of the window, and takes no random operand.

The contract reads the operand blocks and the window, and nothing else, by construction.

## Main results

* `NLAlib.Ops.BlockRel.spec`: the contract.
* `NLAlib.Ops.Mem.writes_eq_some_iff`: guarded writes of several blocks.
* `NLAlib.Ops.Mem.readBlocks_one`, `NLAlib.Ops.Mem.room_one` and their analogues: the operands of
  a call with a given number of blocks.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

namespace Mem

/-- Write the blocks `ys` at the operands `zs`, in order; total. -/
def updBlocks (m : Mem K) : List (ℕ × ℕ) → List (List K) → Mem K
  | z :: zs, y :: ys => (m.updBlock z y).updBlocks zs ys
  | _, _ => m

/-- There is room for blocks of the lengths `ls` at the operands `zs`. -/
def Room (m : Mem K) : List (ℕ × ℕ) → List ℕ → Prop
  | [], [] => True
  | z :: zs, l :: ls => z.2 + l ≤ m.store.len z.1 ∧ m.Room zs ls
  | _, _ => False

/-- Write the blocks `ys` at the operands `zs`, in order, if there is room. -/
def writes (m : Mem K) : List (ℕ × ℕ) → List (List K) → Option (Mem K)
  | [], [] => some m
  | z :: zs, y :: ys => (m.write z y).bind fun m' => m'.writes zs ys
  | _, _ => none

@[simp, storeNF] theorem updBlocks_nil (m : Mem K) : m.updBlocks [] [] = m := rfl

@[simp, storeNF] theorem updBlocks_cons (m : Mem K) (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (y : List K)
    (ys : List (List K)) : m.updBlocks (z :: zs) (y :: ys) = (m.updBlock z y).updBlocks zs ys :=
  rfl

@[simp] theorem pos_updBlocks (m : Mem K) (zs : List (ℕ × ℕ)) (ys : List (List K)) :
    (m.updBlocks zs ys).pos = m.pos := by
  induction zs generalizing m ys with
  | nil => cases ys <;> rfl
  | cons z zs ih => cases ys with
    | nil => rfl
    | cons y ys => simp [updBlocks, ih]

@[simp] theorem shape_updBlocks (m : Mem K) (zs : List (ℕ × ℕ)) (ys : List (List K)) :
    (m.updBlocks zs ys).store.shape = m.store.shape := by
  induction zs generalizing m ys with
  | nil => cases ys <;> rfl
  | cons z zs ih => cases ys with
    | nil => rfl
    | cons y ys => simp [updBlocks, ih]

@[simp, storeNF] theorem room_nil (m : Mem K) : m.Room [] [] ↔ True := Iff.rfl

@[simp, storeNF] theorem room_cons (m : Mem K) (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (l : ℕ)
    (ls : List ℕ) : m.Room (z :: zs) (l :: ls) ↔ z.2 + l ≤ m.store.len z.1 ∧ m.Room zs ls :=
  Iff.rfl

/-- Room depends on the lengths of the buffers only. -/
theorem Room.congr {m m' : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : m.Room zs ls)
    (hs : ∀ b, m'.store.len b = m.store.len b) : m'.Room zs ls := by
  induction zs generalizing ls with
  | nil => cases ls <;> exact h
  | cons z zs ih => cases ls with
    | nil => exact h
    | cons l ls => exact ⟨by rw [hs]; exact h.1, ih h.2⟩

theorem Room.length_eq {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : m.Room zs ls) :
    zs.length = ls.length := by
  induction zs generalizing ls with
  | nil => cases ls with
    | nil => rfl
    | cons l ls => exact h.elim
  | cons z zs ih => cases ls with
    | nil => exact h.elim
    | cons l ls => simp [ih h.2]

instance (m : Mem K) (zs : List (ℕ × ℕ)) (ls : List ℕ) : Decidable (m.Room zs ls) := by
  induction zs generalizing ls with
  | nil => cases ls with
    | nil => exact isTrue trivial
    | cons l ls => exact isFalse id
  | cons z zs ih => cases ls with
    | nil => exact isFalse id
    | cons l ls =>
      have := ih ls
      exact inferInstanceAs (Decidable (_ ∧ _))

/-- **Guarded writes of several blocks** succeed exactly when there is room, and are then the
total writes. -/
theorem writes_eq_some_iff {m m' : Mem K} {zs : List (ℕ × ℕ)} {ys : List (List K)} :
    m.writes zs ys = some m' ↔ m.Room zs (ys.map List.length) ∧ m' = m.updBlocks zs ys := by
  induction zs generalizing m ys with
  | nil => cases ys with
    | nil => simp [writes, eq_comm]
    | cons y ys => simp [writes, Room]
  | cons z zs ih => cases ys with
    | nil => simp [writes, Room]
    | cons y ys =>
      simp only [writes, write, List.map_cons, room_cons, updBlocks_cons]
      by_cases hz : z.2 + y.length ≤ m.store.len z.1
      · simp only [hz, if_true, Option.bind_some, ih, true_and]
        exact and_congr_left fun _ => ⟨fun h => h.congr (by simp), fun h => h.congr (by simp)⟩
      · simp [hz]

/-- Reading one block. -/
theorem readBlocks_one {m : Mem K} {as : List (ℕ × ℕ)} {p : ℕ} {X : List (List K)}
    (h : m.readBlocks as [p] = some X) : ∃ x xs, as = [x] ∧
      m.store.readBlock x.1 x.2 p = some xs ∧ X = [xs] := by
  rcases as with _ | ⟨x, _ | ⟨y, as⟩⟩
  · simp [readBlocks] at h
  · cases hx : m.store.readBlock x.1 x.2 p with
    | none => simp [readBlocks, hx] at h
    | some xs =>
      simp only [readBlocks, hx, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨x, xs, rfl, hx, h.symm⟩
  · simp [readBlocks] at h

/-- Reading two blocks. -/
theorem readBlocks_two {m : Mem K} {as : List (ℕ × ℕ)} {p q : ℕ} {X : List (List K)}
    (h : m.readBlocks as [p, q] = some X) : ∃ x y xs ys, as = [x, y] ∧
      m.store.readBlock x.1 x.2 p = some xs ∧ m.store.readBlock y.1 y.2 q = some ys ∧
      X = [xs, ys] := by
  rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨w, as⟩⟩⟩
  · simp [readBlocks] at h
  · simp [readBlocks] at h
  · cases hx : m.store.readBlock x.1 x.2 p with
    | none => simp [readBlocks, hx] at h
    | some xs =>
      cases hy : m.store.readBlock y.1 y.2 q with
      | none => simp [readBlocks, hx, hy] at h
      | some ys =>
        simp only [readBlocks, hx, hy, Option.bind_some, Option.map_some, Option.some.injEq] at h
        exact ⟨x, y, xs, ys, rfl, hx, hy, h.symm⟩
  · simp [readBlocks] at h

/-- Reading three blocks. -/
theorem readBlocks_three {m : Mem K} {as : List (ℕ × ℕ)} {p q r : ℕ} {X : List (List K)}
    (h : m.readBlocks as [p, q, r] = some X) : ∃ x y w xs ys ws, as = [x, y, w] ∧
      m.store.readBlock x.1 x.2 p = some xs ∧ m.store.readBlock y.1 y.2 q = some ys ∧
      m.store.readBlock w.1 w.2 r = some ws ∧ X = [xs, ys, ws] := by
  rcases as with _ | ⟨x, _ | ⟨y, _ | ⟨w, _ | ⟨v, as⟩⟩⟩⟩
  · simp [readBlocks] at h
  · simp [readBlocks] at h
  · simp [readBlocks] at h
  · cases hx : m.store.readBlock x.1 x.2 p with
    | none => simp [readBlocks, hx] at h
    | some xs =>
      cases hy : m.store.readBlock y.1 y.2 q with
      | none => simp [readBlocks, hx, hy] at h
      | some ys =>
        cases hw : m.store.readBlock w.1 w.2 r with
        | none => simp [readBlocks, hx, hy, hw] at h
        | some ws =>
          simp only [readBlocks, hx, hy, hw, Option.bind_some, Option.map_some,
            Option.some.injEq] at h
          exact ⟨x, y, w, xs, ys, ws, rfl, hx, hy, hw, h.symm⟩
  · simp [readBlocks] at h

/-- Reading no block. -/
theorem readBlocks_zero {m : Mem K} {as : List (ℕ × ℕ)} {X : List (List K)}
    (h : m.readBlocks as [] = some X) : as = [] ∧ X = [] := by
  rcases as with _ | ⟨x, as⟩
  · simp only [readBlocks, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [readBlocks] at h

/-- Room for one block. -/
theorem room_one {m : Mem K} {zs : List (ℕ × ℕ)} {l : ℕ} (h : m.Room zs [l]) :
    ∃ z, zs = [z] ∧ z.2 + l ≤ m.store.len z.1 := by
  rcases zs with _ | ⟨z, _ | ⟨y, zs⟩⟩
  · exact h.elim
  · exact ⟨z, rfl, h.1⟩
  · exact h.2.elim

/-- Room for two blocks. -/
theorem room_two {m : Mem K} {zs : List (ℕ × ℕ)} {l₁ l₂ : ℕ} (h : m.Room zs [l₁, l₂]) :
    ∃ z₁ z₂, zs = [z₁, z₂] ∧ z₁.2 + l₁ ≤ m.store.len z₁.1 ∧ z₂.2 + l₂ ≤ m.store.len z₂.1 := by
  rcases zs with _ | ⟨z₁, _ | ⟨z₂, _ | ⟨y, zs⟩⟩⟩
  · exact h.elim
  · exact h.2.elim
  · exact ⟨z₁, z₂, rfl, h.1, h.2.1⟩
  · exact h.2.2.elim

end Mem

/-- The first dimension of a call. -/
@[storeNF] theorem headD_cons_dims (n : ℕ) (l : List ℕ) (d : ℕ) : (n :: l).headD d = n := rfl

/-- A list of one block of the length `l`. -/
theorem map_length_eq_one {ys : List (List K)} {l : ℕ} (h : ys.map List.length = [l]) :
    ∃ y, ys = [y] ∧ y.length = l := by
  rcases ys with _ | ⟨y, _ | ⟨y', ys⟩⟩
  · simp at h
  · exact ⟨y, rfl, by simpa using h⟩
  · simp at h

/-- A list of two blocks of the lengths `l₁`, `l₂`. -/
theorem map_length_eq_two {ys : List (List K)} {l₁ l₂ : ℕ}
    (h : ys.map List.length = [l₁, l₂]) :
    ∃ y₁ y₂, ys = [y₁, y₂] ∧ y₁.length = l₁ ∧ y₂.length = l₂ := by
  rcases ys with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y', ys⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨y₁, y₂, rfl, h.1, h.2⟩
  · simp at h

/-- **A contract in operand form.** At `nd` dimensions `d`, a call reads input blocks of the
lengths `inLens d` and the window of `win d` entries of the stream `stream` at the position,
writes output blocks `ys` of the lengths `outLens d` with `rel d xs w ys`, and advances the
position by `win d`. It succeeds on inputs in the domain `dom d xs w`. -/
structure BlockRel (K : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The stream of the tape that is read. -/
  stream : ℕ := 0
  /-- The length of the window. -/
  win : List ℕ → ℕ := fun _ => 0
  /-- The lengths of the input blocks. -/
  inLens : List ℕ → List ℕ
  /-- The lengths of the output blocks. -/
  outLens : List ℕ → List ℕ
  /-- The domain: what the input blocks and the window must satisfy for the call to succeed. -/
  dom : List ℕ → List (List K) → List K → Prop := fun _ _ _ => True
  /-- The relation between the input blocks, the window and the output blocks. -/
  rel : List ℕ → List (List K) → List K → List (List K) → Prop

namespace BlockRel

/-- **The postcondition of a contract in operand form**, from the input blocks `xs` and the
window `w`: output blocks of the declared lengths, related to the inputs and the window, are
written at the operands `outs`; the position advances by the window; nothing else changes. -/
def Post (R : BlockRel K) (d : List ℕ) (xs : List (List K)) (outs : List (ℕ × ℕ)) (w : List K)
    (m m' : Mem K) : Prop :=
  ∃ ys, ys.map List.length = R.outLens d ∧ R.rel d xs w ys ∧
    m' = (m.updBlocks outs ys).advance (R.win d)

/-- **The contract of a relation in operand form** on the admitted operands `adm`. Live
handles, readable inputs in the domain and room for the outputs are needed only for success; a
successful call has read its inputs and had room for its outputs. The contract reads the operand
blocks and the window, and nothing else. -/
def spec (R : BlockRel K) (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) : Contract K where
  stream := R.stream
  win := R.win
  spec md d ins outs w :=
    { pre := fun m => d.length = R.nd ∧ adm d ins outs ∧
        md.Needs (m.Live (ins ++ outs) ∧ (∃ xs, m.readBlocks ins (R.inLens d) = some xs ∧
          R.dom d xs w) ∧ m.Room outs (R.outLens d))
      post := fun m m' => ∃ xs, m.readBlocks ins (R.inLens d) = some xs ∧
        m.Room outs (R.outLens d) ∧ R.Post d xs outs w m m' }

end BlockRel

end NLAlib.Ops
