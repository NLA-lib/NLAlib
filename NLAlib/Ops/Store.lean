/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic

/-!
# The store and the memory of a run

A store is a stack of buffers of possibly uninitialised cells over a carrier `K` of opaque words;
a handle is a position in the stack. A read fails outside a buffer and at an uninitialised cell.
Updates (`NLAlib.Ops.Store.upd`, `NLAlib.Ops.Store.updBlock`) are total functions that do nothing
out of bounds; the failing writes of the evaluator (`NLAlib.Ops.Mem.write`) are an update guarded
by a bounds check. So the memory after a run is written as an equation between updates, and
bounds are separate facts.

The memory `NLAlib.Ops.Mem` of a run is the store and the position on the tape of draws.

## Main results

* `NLAlib.Ops.Store.get_upd_self`, `NLAlib.Ops.Store.get_upd_of_ne`: a read after an update.
* `NLAlib.Ops.Store.get_updBlock`, `NLAlib.Ops.Store.get_updBlock_of_buf_ne`,
  `NLAlib.Ops.Store.get_updBlock_of_lt`, `NLAlib.Ops.Store.get_updBlock_of_ge`: a read after a
  block update.
* `NLAlib.Ops.Store.updBlock_append`, `NLAlib.Ops.Store.updBlock_concat`: a block is filled
  piece by piece.
* `NLAlib.Ops.Store.get_append_of_lt`, `NLAlib.Ops.Store.upd_append_of_lt`,
  `NLAlib.Ops.Store.upd_append_top`: reads and updates below and in a scratch buffer on top.
* `NLAlib.Ops.Store.readBlock_eq_some_iff`: a block read, cell by cell.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A buffer: a list of possibly uninitialised cells. -/
abbrev Buf (K : Type) := List (Option K)

/-- The store: a stack of buffers; the handle of a buffer is its position. -/
abbrev Store (K : Type) := List (Buf K)

variable {K : Type}

namespace Store

/-- Cell `i` of buffer `b`; `none` outside the store or at an uninitialised cell. -/
def get (s : Store K) (b i : ℕ) : Option K := (s[b]?).bind fun buf => (buf[i]?).join

/-- The length of buffer `b`; `0` if there is no such buffer. -/
def len (s : Store K) (b : ℕ) : ℕ := ((s[b]?).map List.length).getD 0

/-- The shape of a store: the lengths of its buffers. -/
def shape (s : Store K) : List ℕ := s.map List.length

/-- Put `v` in cell `i` of buffer `b`; nothing happens out of bounds. -/
def upd (s : Store K) (b i : ℕ) (v : K) : Store K := s.modify b fun buf => buf.set i (some v)

/-- Put the values `xs` in the cells `off, off + 1, …` of buffer `b`. -/
def updBlock (s : Store K) (b : ℕ) : ℕ → List K → Store K
  | _, [] => s
  | off, x :: xs => (s.upd b off x).updBlock b (off + 1) xs

/-- Read the `n` cells `off, …, off + n - 1` of buffer `b`; `none` if one read fails. -/
def readBlock (s : Store K) (b : ℕ) : ℕ → ℕ → Option (List K)
  | _, 0 => some []
  | off, n + 1 => (s.get b off).bind fun x => (s.readBlock b (off + 1) n).map fun xs => x :: xs

/-- Push a buffer of `n` uninitialised cells. -/
def push (s : Store K) (n : ℕ) : Store K := s ++ [List.replicate n none]

/-- Pop the last buffer. -/
def pop (s : Store K) : Store K := s.dropLast

/-! ### Updates -/

@[simp] theorem length_upd (s : Store K) (b i : ℕ) (v : K) : (s.upd b i v).length = s.length := by
  simp [upd]

theorem getElem?_upd (s : Store K) (b i : ℕ) (v : K) (b' : ℕ) :
    (s.upd b i v)[b']? = if b = b' then (s[b']?).map fun buf => buf.set i (some v) else s[b']? := by
  simp only [upd, List.getElem?_modify]
  cases s[b']? <;> by_cases h : b = b' <;> simp [h]

@[simp] theorem shape_upd (s : Store K) (b i : ℕ) (v : K) : (s.upd b i v).shape = s.shape := by
  apply List.ext_getElem?
  intro j
  simp only [shape, List.getElem?_map, getElem?_upd]
  cases s[j]? <;> by_cases h : b = j <;> simp [h]

@[simp] theorem len_upd (s : Store K) (b i : ℕ) (v : K) (b' : ℕ) :
    (s.upd b i v).len b' = s.len b' := by
  simp only [len, getElem?_upd]
  cases s[b']? <;> by_cases h : b = b' <;> simp [h]

theorem get_upd_self {s : Store K} {b i : ℕ} (h : i < s.len b) (v : K) :
    (s.upd b i v).get b i = some v := by
  simp only [get, getElem?_upd, if_true]
  simp only [len] at h
  cases hb : s[b]? with
  | none => simp [hb] at h
  | some buf =>
    simp only [hb, Option.map_some, Option.getD_some] at h
    simp [h]

theorem get_upd_of_ne {s : Store K} {b i b' i' : ℕ} (h : b' ≠ b ∨ i' ≠ i) (v : K) :
    (s.upd b i v).get b' i' = s.get b' i' := by
  simp only [get, getElem?_upd]
  by_cases hb : b = b'
  · subst hb
    have hi : ¬ i = i' := fun e => by simp [e] at h
    cases hs : s[b]? <;> simp [hi]
  · simp [hb]

@[simp] theorem upd_upd (s : Store K) (b i : ℕ) (v w : K) :
    (s.upd b i v).upd b i w = s.upd b i w := by
  apply List.ext_getElem?
  intro j
  simp only [getElem?_upd]
  by_cases h : b = j <;> cases s[j]? <;> simp [h]

theorem lt_len_of_get {s : Store K} {b i : ℕ} {a : K} (h : s.get b i = some a) : i < s.len b := by
  simp only [get, len] at h ⊢
  cases hb : s[b]? with
  | none => simp [hb] at h
  | some buf =>
    simp only [hb, Option.bind_some, Option.map_some, Option.getD_some] at h ⊢
    by_contra hc
    simp [List.getElem?_eq_none (not_lt.mp hc)] at h

theorem lt_length_of_lt_len {s : Store K} {b i : ℕ} (h : i < s.len b) : b < s.length := by
  by_contra hc
  simp [len, List.getElem?_eq_none (not_lt.mp hc)] at h

theorem lt_length_of_get {s : Store K} {b i : ℕ} {a : K} (h : s.get b i = some a) :
    b < s.length :=
  lt_length_of_lt_len (lt_len_of_get h)

theorem upd_comm {s : Store K} {b i b' i' : ℕ} (h : b' ≠ b ∨ i' ≠ i) (v v' : K) :
    (s.upd b i v).upd b' i' v' = (s.upd b' i' v').upd b i v := by
  apply List.ext_getElem?
  intro j
  simp only [getElem?_upd]
  by_cases h1 : b = j
  · by_cases h2 : b' = j
    · subst h1 h2
      have hi : i' ≠ i := by simpa using h
      simp only [↓reduceIte]
      cases s[b']? with
      | none => rfl
      | some buf => exact congrArg some (List.set_comm _ _ hi.symm)
    · simp [h1, h2]
  · by_cases h2 : b' = j <;> simp [h1, h2]

/-! ### Block updates -/

@[simp] theorem updBlock_nil (s : Store K) (b off : ℕ) : s.updBlock b off [] = s := rfl

@[simp] theorem updBlock_cons (s : Store K) (b off : ℕ) (x : K) (xs : List K) :
    s.updBlock b off (x :: xs) = (s.upd b off x).updBlock b (off + 1) xs := rfl

theorem updBlock_singleton (s : Store K) (b off : ℕ) (x : K) :
    s.updBlock b off [x] = s.upd b off x := rfl

@[simp] theorem length_updBlock (s : Store K) (b off : ℕ) (xs : List K) :
    (s.updBlock b off xs).length = s.length := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem shape_updBlock (s : Store K) (b off : ℕ) (xs : List K) :
    (s.updBlock b off xs).shape = s.shape := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem len_updBlock (s : Store K) (b off : ℕ) (xs : List K) (b' : ℕ) :
    (s.updBlock b off xs).len b' = s.len b' := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem updBlock_append (s : Store K) (b off : ℕ) (xs ys : List K) :
    s.updBlock b off (xs ++ ys) = (s.updBlock b off xs).updBlock b (off + xs.length) ys := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, updBlock_cons, ih, List.length_cons]
    congr 1
    omega

theorem updBlock_concat (s : Store K) (b off : ℕ) (xs : List K) (x : K) :
    s.updBlock b off (xs ++ [x]) = (s.updBlock b off xs).upd b (off + xs.length) x := by
  rw [updBlock_append, updBlock_singleton]

theorem get_updBlock_of_buf_ne {s : Store K} {b b' : ℕ} (h : b' ≠ b) (off : ℕ) (xs : List K)
    (i : ℕ) : (s.updBlock b off xs).get b' i = s.get b' i := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [updBlock_cons, ih, get_upd_of_ne (Or.inl h)]

theorem get_updBlock_of_lt {s : Store K} {b off i : ℕ} (h : i < off) (xs : List K) :
    (s.updBlock b off xs).get b i = s.get b i := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [updBlock_cons, ih (by omega), get_upd_of_ne (Or.inr (by omega))]

theorem get_updBlock_of_ge {s : Store K} {b off i : ℕ} {xs : List K} (h : off + xs.length ≤ i) :
    (s.updBlock b off xs).get b i = s.get b i := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at h
    rw [updBlock_cons, ih (by omega), get_upd_of_ne (Or.inr (by omega))]

/-- A read inside an updated block. -/
theorem get_updBlock {s : Store K} {b off : ℕ} {xs : List K} (hlen : off + xs.length ≤ s.len b)
    {j : ℕ} (hj : j < xs.length) : (s.updBlock b off xs).get b (off + j) = xs[j]? := by
  induction xs generalizing s off j with
  | nil => simp at hj
  | cons x xs ih =>
    simp only [List.length_cons] at hlen hj
    rw [updBlock_cons]
    cases j with
    | zero =>
      change ((s.upd b off x).updBlock b (off + 1) xs).get b off = some x
      rw [get_updBlock_of_lt (by omega), get_upd_self (by omega)]
    | succ j =>
      have := ih (s := s.upd b off x) (off := off + 1) (j := j) (by simpa using by omega)
        (by omega)
      rw [show off + (j + 1) = off + 1 + j by omega, this]
      rfl

/-- An update outside a block commutes with the block update. -/
theorem upd_updBlock_comm {s : Store K} {b off b' i : ℕ} (h : b' ≠ b ∨ i < off) (xs : List K)
    (v : K) : (s.updBlock b off xs).upd b' i v = (s.upd b' i v).updBlock b off xs := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih =>
    rw [updBlock_cons, ih (by omega), updBlock_cons,
      upd_comm (b := b) (i := off) (b' := b') (i' := i) (by omega)]

/-- A block put over a block of the same length replaces it. -/
theorem updBlock_updBlock {s : Store K} {b off : ℕ} {xs ys : List K}
    (h : xs.length = ys.length) :
    (s.updBlock b off xs).updBlock b off ys = s.updBlock b off ys := by
  induction xs generalizing s off ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [updBlock_cons, updBlock_cons, upd_updBlock_comm (Or.inr (by omega)), upd_upd,
        ih (by simpa using h), updBlock_cons]

/-! ### A scratch buffer on top -/

theorem get_append_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (t : Store K) (i : ℕ) :
    (s ++ t).get b i = s.get b i := by
  simp [get, List.getElem?_append_left h]

theorem len_append_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (t : Store K) :
    (s ++ t).len b = s.len b := by
  simp [len, List.getElem?_append_left h]

theorem upd_append_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (t : Store K) (i : ℕ) (v : K) :
    (s ++ t).upd b i v = s.upd b i v ++ t := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < s.length
  · rw [getElem?_upd, List.getElem?_append_left hj,
      List.getElem?_append_left (by simpa using hj), getElem?_upd]
  · have hbj : ¬ b = j := by omega
    rw [getElem?_upd, if_neg hbj, List.getElem?_append_right (not_lt.mp hj),
      List.getElem?_append_right (by simpa using not_lt.mp hj), length_upd]

theorem updBlock_append_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (t : Store K) (off : ℕ)
    (xs : List K) : (s ++ t).updBlock b off xs = s.updBlock b off xs ++ t := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [updBlock_cons, upd_append_of_lt h, ih (by simpa using h), updBlock_cons]

theorem get_append_top (s : Store K) (tb : Buf K) (i : ℕ) :
    (s ++ [tb]).get s.length i = (tb[i]?).join := by
  simp [get]

@[simp] theorem len_append_top (s : Store K) (tb : Buf K) :
    (s ++ [tb]).len s.length = tb.length := by
  simp [len]

theorem upd_append_top (s : Store K) (tb : Buf K) (i : ℕ) (v : K) :
    (s ++ [tb]).upd s.length i v = s ++ [tb.set i (some v)] := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_upd]
  by_cases hj : s.length = j
  · subst hj
    simp
  · rw [if_neg hj]
    by_cases hlt : j < s.length
    · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
    · rw [List.getElem?_append_right (not_lt.mp hlt), List.getElem?_append_right (not_lt.mp hlt)]
      have : j - s.length ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      simp [hk]

theorem get_top {s : Store K} {b : ℕ} (hb : b = s.length) (tb : Buf K) (i : ℕ) :
    (s ++ [tb]).get b i = (tb[i]?).join := hb ▸ get_append_top s tb i

theorem len_top {s : Store K} {b : ℕ} (hb : b = s.length) (tb : Buf K) :
    (s ++ [tb]).len b = tb.length := hb ▸ len_append_top s tb

theorem upd_top {s : Store K} {b : ℕ} (hb : b = s.length) (tb : Buf K) (i : ℕ) (v : K) :
    (s ++ [tb]).upd b i v = s ++ [tb.set i (some v)] := hb ▸ upd_append_top s tb i v

@[simp] theorem pop_append_top (s : Store K) (tb : Buf K) : pop (s ++ [tb]) = s := by
  simp [pop]

@[simp] theorem shape_append (s t : Store K) : (s ++ t).shape = s.shape ++ t.shape := by
  simp [shape]

theorem shape_pop (s : Store K) : s.pop.shape = s.shape.dropLast := by
  simp [shape, pop, List.map_dropLast]

/-! ### Block reads -/

@[simp] theorem readBlock_zero (s : Store K) (b off : ℕ) : s.readBlock b off 0 = some [] := rfl

theorem readBlock_succ (s : Store K) (b off n : ℕ) :
    s.readBlock b off (n + 1) =
      (s.get b off).bind fun x => (s.readBlock b (off + 1) n).map fun xs => x :: xs := rfl

/-- A block read succeeds with `xs` exactly when `xs` lists the cells of the block. -/
theorem readBlock_eq_some_iff {s : Store K} {b off n : ℕ} {xs : List K} :
    s.readBlock b off n = some xs ↔ xs.length = n ∧ ∀ j < n, s.get b (off + j) = xs[j]? := by
  induction n generalizing off xs with
  | zero =>
    simp only [readBlock_zero, Option.some.injEq, Nat.not_lt_zero, false_imp_iff, implies_true,
      and_true]
    constructor
    · rintro rfl
      rfl
    · intro h
      exact (List.length_eq_zero_iff.mp h).symm
  | succ n ih =>
    rw [readBlock_succ]
    constructor
    · intro h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hl, hg⟩ := ih.mp hys
      refine ⟨by simp [hl], fun j hj => ?_⟩
      cases j with
      | zero => simpa using hx
      | succ j =>
        rw [show off + (j + 1) = off + 1 + j by omega, hg j (by omega)]
        rfl
    · rintro ⟨hl, hg⟩
      cases xs with
      | nil => simp at hl
      | cons x ys =>
        have h0 := hg 0 (by omega)
        simp only [Nat.add_zero, List.getElem?_cons_zero] at h0
        have hys : s.readBlock b (off + 1) n = some ys :=
          ih.mpr ⟨by simpa using hl, fun j hj => by
            have := hg (j + 1) (by omega)
            rw [show off + (j + 1) = off + 1 + j by omega] at this
            simpa using this⟩
        simp [h0, hys]

theorem length_of_readBlock {s : Store K} {b off n : ℕ} {xs : List K}
    (h : s.readBlock b off n = some xs) : xs.length = n :=
  (readBlock_eq_some_iff.mp h).1

/-- Cell `j` of a block that was read, with any default value. -/
theorem get_of_readBlock {s : Store K} {b off n : ℕ} {xs : List K}
    (h : s.readBlock b off n = some xs) {j : ℕ} (hj : j < n) (d : K) :
    s.get b (off + j) = some (xs.getD j d) := by
  obtain ⟨hl, hg⟩ := readBlock_eq_some_iff.mp h
  rw [hg j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- A part of a block that was read. -/
theorem readBlock_sub {s : Store K} {b off N : ℕ} {xs : List K}
    (h : s.readBlock b off N = some xs) {o n : ℕ} (hn : o + n ≤ N) :
    s.readBlock b (off + o) n = some ((xs.drop o).take n) := by
  obtain ⟨hl, hg⟩ := readBlock_eq_some_iff.mp h
  refine readBlock_eq_some_iff.mpr ⟨by simp; omega, fun j hj => ?_⟩
  rw [add_assoc, hg (o + j) (by omega), List.getElem?_take_of_lt hj, List.getElem?_drop]

theorem getD_drop_take (xs : List K) (o n j : ℕ) (hj : j < n) (d : K) :
    ((xs.drop o).take n).getD j d = xs.getD (o + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

/-- A block read sees only the cells of the block. -/
theorem readBlock_congr {s s' : Store K} {b off n : ℕ}
    (h : ∀ j < n, s'.get b (off + j) = s.get b (off + j)) :
    s'.readBlock b off n = s.readBlock b off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [readBlock_succ, readBlock_succ, h0, ih fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show off + (j + 1) = off + 1 + j by omega] at this]

/-- Reading back a block that was just put. -/
theorem readBlock_updBlock_self {s : Store K} {b off : ℕ} {xs : List K}
    (hlen : off + xs.length ≤ s.len b) :
    (s.updBlock b off xs).readBlock b off xs.length = some xs :=
  readBlock_eq_some_iff.mpr ⟨rfl, fun _ hj => get_updBlock hlen hj⟩

end Store

/-- The memory of a run: the store and the position on the tape of draws. -/
structure Mem (K : Type) where
  /-- The store. -/
  store : Store K
  /-- The next unread position of the tape. -/
  pos : ℕ

namespace Mem

/-- The memory with the store replaced. -/
def setStore (m : Mem K) (s : Store K) : Mem K := ⟨s, m.pos⟩

/-- Put `v` in the cell `z` (a handle and an offset). -/
def upd (m : Mem K) (z : ℕ × ℕ) (v : K) : Mem K := ⟨m.store.upd z.1 z.2 v, m.pos⟩

/-- Put the block `ys` at `z` (a handle and an offset). -/
def updBlock (m : Mem K) (z : ℕ × ℕ) (ys : List K) : Mem K :=
  ⟨m.store.updBlock z.1 z.2 ys, m.pos⟩

/-- Advance the tape position by `k`. -/
def advance (m : Mem K) (k : ℕ) : Mem K := ⟨m.store, m.pos + k⟩

/-- The failing block write of the evaluator: the block must lie inside its buffer. -/
def write (m : Mem K) (z : ℕ × ℕ) (ys : List K) : Option (Mem K) :=
  if z.2 + ys.length ≤ m.store.len z.1 then some (m.updBlock z ys) else none

/-- Read the blocks at `as` with the lengths `ns`; `none` if a read fails or the two lists have
different lengths. -/
def readBlocks (m : Mem K) : List (ℕ × ℕ) → List ℕ → Option (List (List K))
  | [], [] => some []
  | a :: as, n :: ns =>
      (m.store.readBlock a.1 a.2 n).bind fun x => (m.readBlocks as ns).map fun xs => x :: xs
  | _, _ => none

@[simp] theorem store_upd (m : Mem K) (z : ℕ × ℕ) (v : K) :
    (m.upd z v).store = m.store.upd z.1 z.2 v := rfl

@[simp] theorem pos_upd (m : Mem K) (z : ℕ × ℕ) (v : K) : (m.upd z v).pos = m.pos := rfl

@[simp] theorem store_updBlock (m : Mem K) (z : ℕ × ℕ) (ys : List K) :
    (m.updBlock z ys).store = m.store.updBlock z.1 z.2 ys := rfl

@[simp] theorem pos_updBlock (m : Mem K) (z : ℕ × ℕ) (ys : List K) :
    (m.updBlock z ys).pos = m.pos := rfl

@[simp] theorem store_advance (m : Mem K) (k : ℕ) : (m.advance k).store = m.store := rfl

@[simp] theorem pos_advance (m : Mem K) (k : ℕ) : (m.advance k).pos = m.pos + k := rfl

@[simp] theorem advance_zero (m : Mem K) : m.advance 0 = m := rfl

theorem updBlock_singleton (m : Mem K) (z : ℕ × ℕ) (v : K) : m.updBlock z [v] = m.upd z v := rfl

theorem write_eq_some {m : Mem K} {z : ℕ × ℕ} {ys : List K}
    (h : z.2 + ys.length ≤ m.store.len z.1) : m.write z ys = some (m.updBlock z ys) :=
  if_pos h

theorem shape_of_write {m m' : Mem K} {z : ℕ × ℕ} {ys : List K} (h : m.write z ys = some m') :
    m'.store.shape = m.store.shape ∧ m'.pos = m.pos := by
  unfold write at h
  split_ifs at h
  cases h
  simp

@[simp] theorem readBlocks_nil (m : Mem K) : m.readBlocks [] [] = some [] := rfl

theorem readBlocks_cons (m : Mem K) (a : ℕ × ℕ) (as : List (ℕ × ℕ)) (n : ℕ) (ns : List ℕ) :
    m.readBlocks (a :: as) (n :: ns) =
      (m.store.readBlock a.1 a.2 n).bind fun x => (m.readBlocks as ns).map fun xs => x :: xs :=
  rfl

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

end Mem

end NLAlib.Ops
