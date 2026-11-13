/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.List.Range
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.DefEqTransformations
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

/-!
# The store

The store `NLAlib.Computation.Store P K` of a run is a stack of buffers, each with a tag of type
`P` and an array of possibly uninitialised cells over the carrier `K`; a handle is a position in
the stack. Reads and writes fail outside a buffer, at another tag or past its end, and a read
fails at an uninitialised cell. Block reads and writes are reads and writes of consecutive cells.
The shape of a store, the tag and the length of each buffer, decides which writes succeed.

The store lemmas say what a read sees after a write, an allocation (a push), a deallocation (a
pop) or a block write, and when a write succeeds. The frame invariant
`NLAlib.Computation.Store.BlockFrame` is what a kernel or an oracle implementation that writes
one block through a scratch buffer keeps along its loops; popping the scratch buffer then gives
the block write. Design: `docs/design/Computation.md` (D3, D11).

## Main definitions

* `NLAlib.Computation.Store`: the store; `NLAlib.Computation.Store.read`,
  `NLAlib.Computation.Store.write`, `NLAlib.Computation.Store.readBlock`,
  `NLAlib.Computation.Store.writeBlock`, `NLAlib.Computation.Store.shape`.
* `NLAlib.Computation.Store.readBlocks`, `NLAlib.Computation.Store.writeBlocks`: the reads and
  writes of several blocks, `(handle, offset, length)`, of a kernel call.
* `NLAlib.Computation.Store.BlockFrame`: the frame invariant of a block write with a scratch
  buffer.

## Main results

* `NLAlib.Computation.Store.read_of_write_eq_some`,
  `NLAlib.Computation.Store.read_of_write_eq_some_of_ne`: a read after a write.
* `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_lt`,
  `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_ne`: a read after a block write.
* `NLAlib.Computation.Store.ext_of_shape_eq`: two stores of the same shape with the same reads
  are equal.
* `NLAlib.Computation.Store.BlockFrame.pop_eq`: popping the scratch buffer from a store in the
  frame of a block write gives the block write.
* `NLAlib.Computation.Store.read_of_writeBlocks_eq_some_of_forall`: the frame of several block
  writes.
-/

@[expose] public section

namespace NLAlib.Computation

/-- The store: a stack of tagged buffers of possibly uninitialised cells. -/
abbrev Store (P K : Type) := Array (P × Array (Option K))

section Store

variable {P K : Type} [DecidableEq P]

/-- Cell `i` of buffer `b` at tag `p`; `none` if the buffer does not exist, has another tag, the
index is out of bounds or the cell is uninitialised. -/
def Store.read (s : Store P K) (p : P) (b i : ℕ) : Option K :=
  match s[b]? with
  | some (q, arr) => if q = p then (arr[i]?).join else none
  | none => none

/-- Write `v` into cell `i` of buffer `b` at tag `p`; `none` if the buffer does not exist, has
another tag or the index is out of bounds. -/
def Store.write (s : Store P K) (p : P) (b i : ℕ) (v : K) : Option (Store P K) :=
  match s[b]? with
  | some (q, arr) => if q = p ∧ i < arr.size then some (s.set! b (q, arr.set! i (some v)))
      else none
  | none => none

/-- The `len` cells of buffer `b` from offset `off`. -/
def Store.readBlock (s : Store P K) (p : P) (b off len : ℕ) : Option (Array K) :=
  (List.range len).toArray.mapM fun i => s.read p b (off + i)

/-- Write `xs` into buffer `b` from offset `off`, one cell at a time. -/
def Store.writeBlock (s : Store P K) (p : P) (b off : ℕ) (xs : Array K) : Option (Store P K) :=
  (List.range xs.size).foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s

/-- The shape of a store: the tag and the length of each buffer. Two stores of the same shape
accept the same writes. -/
def Store.shape (s : Store P K) : Array (P × ℕ) := s.map fun x => (x.1, x.2.size)

/-- The blocks `bs`, each `(handle, offset, length)`, read in order at tag `p`. -/
def Store.readBlocks (s : Store P K) (p : P) (bs : List (ℕ × ℕ × ℕ)) : Option (List (Array K)) :=
  bs.mapM fun b => s.readBlock p b.1 b.2.1 b.2.2

/-- The arrays `ys` written in order into the blocks `bs`, each `(handle, offset, length)`, at tag
`p`; `none` if the numbers of blocks and arrays differ or an array does not have the length of
its block. -/
def Store.writeBlocks (s : Store P K) (p : P) :
    List (ℕ × ℕ × ℕ) → List (Array K) → Option (Store P K)
  | [], [] => some s
  | b :: bs, y :: ys => if y.size = b.2.2 then
      (s.writeBlock p b.1 b.2.1 y).bind fun s' => s'.writeBlocks p bs ys else none
  | _, _ => none

/-- Read after write, at the written cell. -/
theorem Store.read_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.read p b i = some v := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp [Store.read, Array.set!, hb', hi]

/-- Read after write, at another cell. -/
theorem Store.read_of_write_eq_some_of_ne {s s' : Store P K} {p q : P} {b i b' i' : ℕ} {v : K}
    (h : s.write p b i v = some s') (hne : b' ≠ b ∨ i' ≠ i) : s'.read q b' i' = s.read q b' i' := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q', arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    unfold Store.read
    by_cases hbb : b' = b
    · subst hbb
      have hii : i' ≠ i := hne.resolve_left (fun h => h rfl)
      have heq : s[b'] = (q', arr) := (Array.getElem?_eq_some_iff.mp hb).2
      simp [Array.set!, hb', heq, Ne.symm hii]
    · simp [Array.set!, Ne.symm hbb]

/-- A write keeps the number of buffers. -/
theorem Store.size_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.size = s.size := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    cases h
    simp [Array.set!]

/-- A write keeps the shape of the store. -/
theorem Store.shape_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : s'.shape = s.shape := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h
    split_ifs at h with hq
    cases h
    obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hb
    apply Array.ext
    · simp [Store.shape, Array.set!]
    · intro k hk₁ hk₂
      by_cases hkb : k = b
      · subst hkb
        simp [Store.shape, Array.set!, heq]
      · simp only [Store.shape, Array.set!, Array.getElem_map]
        rw [Array.getElem_setIfInBounds_ne (by simpa [Store.shape] using hk₂) (Ne.symm hkb)]

/-- A write succeeds where a read of the same cell succeeds. -/
theorem Store.exists_write_eq_some_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v w : K}
    (h : s.read p b i = some w) : ∃ s', s.write p b i v = some s' := by
  unfold Store.read at h
  unfold Store.write
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    have hi : i < arr.size := by
      rcases hi : arr[i]? with _ | x
      · simp [hi] at h
      · exact (Array.getElem?_eq_some_iff.mp hi).1
    exact ⟨_, if_pos ⟨hq, hi⟩⟩

/-- A read of a pushed buffer: the old buffers are unchanged. -/
theorem Store.read_push_of_lt {s : Store P K} {p q : P} {arr : Array (Option K)} {b i : ℕ}
    (hb : b < s.size) : Store.read (s.push (q, arr)) p b i = s.read p b i := by
  simp [Store.read, Array.getElem?_push, Nat.ne_of_lt hb]

/-- The writes of a block write, at indices of a list, keep every other cell. -/
private theorem Store.read_of_foldlM_write_eq_some_of_ne {s s' : Store P K} {p q : P}
    {b off b' i' : ℕ} {xs : Array K} (l : List ℕ)
    (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s')
    (hne : ∀ i ∈ l, b' ≠ b ∨ i' ≠ off + i) : s'.read q b' i' = s.read q b' i' := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    change (Option.bind _ fun s => List.foldlM _ s l) = some s' at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
    obtain ⟨v, -, hw⟩ := Option.bind_eq_some_iff.mp h₂
    rw [ih h₃ (fun j hj => hne j (List.mem_cons_of_mem _ hj))]
    exact Store.read_of_write_eq_some_of_ne hw (hne i List.mem_cons_self)

/-- The writes of a block write, at the indices of a list without repetition, leave entry `j` of
the block in cell `off + j`. -/
private theorem Store.read_of_foldlM_write_eq_some_of_mem {s s' : Store P K} {p : P} {b off j : ℕ}
    {xs : Array K} (l : List ℕ) (hl : l.Nodup)
    (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s') (hj : j ∈ l) :
    s'.read p b (off + j) = xs[j]? := by
  induction l generalizing s with
  | nil => simp at hj
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    change (Option.bind _ fun s => List.foldlM _ s l) = some s' at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
    obtain ⟨v, hv, hw⟩ := Option.bind_eq_some_iff.mp h₂
    rcases List.mem_cons.mp hj with rfl | hj'
    · have hnot : j ∉ l := (List.nodup_cons.mp hl).1
      rw [Store.read_of_foldlM_write_eq_some_of_ne l h₃ (fun i hi => Or.inr (fun he => hnot (by
        have : j = i := by omega
        exact this ▸ hi))), Store.read_of_write_eq_some hw, hv]
    · exact ih (List.nodup_cons.mp hl).2 h₃ hj'

/-- Read after a block write, inside the block. -/
theorem Store.read_of_writeBlock_eq_some_of_lt {s s' : Store P K} {p : P} {b off j : ℕ}
    {xs : Array K}
    (h : s.writeBlock p b off xs = some s') (hj : j < xs.size) :
    s'.read p b (off + j) = xs[j]? := by
  exact Store.read_of_foldlM_write_eq_some_of_mem _ List.nodup_range h (List.mem_range.mpr hj)

/-- Read after a block write, outside the block. -/
theorem Store.read_of_writeBlock_eq_some_of_ne {s s' : Store P K} {p q : P} {b off b' i' : ℕ}
    {xs : Array K}
    (h : s.writeBlock p b off xs = some s') (hne : b' ≠ b ∨ i' < off ∨ off + xs.size ≤ i') :
    s'.read q b' i' = s.read q b' i' := by
  refine Store.read_of_foldlM_write_eq_some_of_ne _ h fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rcases hne with hb | hlt | hge
  · exact Or.inl hb
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)

/-- A read that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : b < s.size := by
  unfold Store.read at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · exact (Array.getElem?_eq_some_iff.mp hb).1

/-- A write that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') : b < s.size := by
  unfold Store.write at h
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · exact (Array.getElem?_eq_some_iff.mp hb).1

/-- A write succeeds where a write of another value into the same cell succeeds. -/
theorem Store.exists_write_eq_some_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ}
    {v : K} (h : s.write p b i v = some s') (w : K) : ∃ s'', s.write p b i w = some s'' := by
  unfold Store.write at h ⊢
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    exact ⟨_, if_pos hq⟩

/-- Two writes into one cell: the second overwrites the first. -/
theorem Store.write_of_write_eq_some {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') (w : K) : s'.write p b i w = s.write p b i w := by
  unfold Store.write at h ⊢
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h ⊢
    split_ifs at h with hq
    obtain ⟨rfl, hi⟩ := hq
    cases h
    have hb' : b < s.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp [Array.set!, hb', hi]

/-- A write below the top of a pushed store is a write in the store under it. -/
theorem Store.write_push_of_lt {s : Store P K} {x : P × Array (Option K)} {p : P} {b i : ℕ}
    {v : K} (hb : b < s.size) :
    Store.write (s.push x) p b i v = (s.write p b i v).map fun s' => s'.push x := by
  unfold Store.write
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hb)]
  rcases hb' : s[b]? with _ | ⟨q, arr⟩
  · rfl
  · dsimp only
    split_ifs
    · simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.size_push,
        Option.map_some, Array.set_push, hb, Nat.lt_succ_of_lt hb,
        dite_true]
    · rfl

/-- A write into the top buffer of a pushed store. -/
theorem Store.write_push_size {s : Store P K} {p : P} {arr : Array (Option K)} {i : ℕ} {v : K}
    (hi : i < arr.size) :
    Store.write (s.push (p, arr)) p s.size i v = some (s.push (p, arr.set! i (some v))) := by
  simp [Store.write, hi, Array.setIfInBounds_def, Array.set_push]

/-- A read of the top buffer of a pushed store. -/
theorem Store.read_push_size {s : Store P K} {p q : P} {arr : Array (Option K)} {i : ℕ} :
    Store.read (s.push (q, arr)) p s.size i = if q = p then (arr[i]?).join else none := by
  simp [Store.read]

/-- The cell just written in the top buffer of a pushed store reads back. -/
theorem Store.read_push_size_set!_zero {s : Store P K} {p : P} {arr : Array (Option K)} {v : K}
    (h : 0 < arr.size) : Store.read (s.push (p, arr.set! 0 (some v))) p s.size 0 = some v := by
  simp [Store.read_push_size, h]

/-- A write keeps the number of buffers: the writes of a fold. -/
theorem Store.size_of_foldlM_write_eq_some {s s' : Store P K} {p : P} {b : ℕ} (l : List ℕ)
    (idx : ℕ → ℕ) (f : ℕ → K) (h : l.foldlM (fun s j => s.write p b (idx j) (f j)) s = some s') :
    s'.size = s.size := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    rw [ih h₃, Store.size_of_write_eq_some h₂]

/-- The writes of a fold keep every cell they do not write. -/
theorem Store.read_of_foldlM_write_eq_some_of_forall_ne {s s' : Store P K} {p q : P}
    {b b' i' : ℕ} (l : List ℕ) (idx : ℕ → ℕ) (f : ℕ → K)
    (h : l.foldlM (fun s j => s.write p b (idx j) (f j)) s = some s')
    (hne : ∀ j ∈ l, b' ≠ b ∨ i' ≠ idx j) : s'.read q b' i' = s.read q b' i' := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    rw [ih h₃ (fun j hj => hne j (List.mem_cons_of_mem _ hj))]
    exact Store.read_of_write_eq_some_of_ne h₂ (hne i List.mem_cons_self)

/-- A block write of the values $f(0), \dots, f(n-1)$ is the fold of their writes. -/
theorem Store.writeBlock_map_range (s : Store P K) (p : P) (b off n : ℕ) (f : ℕ → K) :
    s.writeBlock p b off ((List.range n).toArray.map f) =
      (List.range n).foldlM (fun s j => s.write p b (off + j) (f j)) s := by
  unfold Store.writeBlock
  have hsize : ((List.range n).toArray.map f).size = n := by simp
  rw [hsize]
  have key : ∀ (l : List ℕ), (∀ j ∈ l, j < n) → ∀ s : Store P K,
      l.foldlM (fun s i => do s.write p b (off + i) (← ((List.range n).toArray.map f)[i]?)) s =
        l.foldlM (fun s j => s.write p b (off + j) (f j)) s := by
    intro l hl
    induction l with
    | nil => intro s; rfl
    | cons i l ih =>
      intro s
      have hi : i < n := hl i List.mem_cons_self
      have hxs : ((List.range n).toArray.map f)[i]? = some (f i) := by simp [hi]
      have ih' := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      rw [List.foldlM_cons, List.foldlM_cons]
      change Option.bind (Option.bind _ fun v => s.write p b (off + i) v) _ = _
      rw [hxs, Option.bind_some]
      exact congrArg _ (funext ih')
  exact key _ (fun j hj => List.mem_range.mp hj) s

/-- Two stores of the same shape accept the same writes. -/
theorem Store.exists_write_eq_some_of_shape_eq {s s' s₁ : Store P K} {p : P} {b i : ℕ} {v : K}
    (hsh : s'.shape = s.shape) (h : s.write p b i v = some s₁) (w : K) :
    ∃ s₂, s'.write p b i w = some s₂ := by
  unfold Store.write at h ⊢
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · exact absurd h (by simp)
  · dsimp only at h
    split_ifs at h with hq
    have hsh' : s'.shape[b]? = s.shape[b]? := by rw [hsh]
    simp only [Store.shape, Array.getElem?_map, hb, Option.map_some] at hsh'
    rcases hb' : s'[b]? with _ | ⟨q', arr'⟩ <;> rw [hb'] at hsh'
    · exact absurd hsh' (by simp)
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsh'
      obtain ⟨rfl, hsz⟩ := hsh'
      exact ⟨_, if_pos ⟨hq.1, hsz ▸ hq.2⟩⟩

/-- A block write keeps the shape of the store. -/
theorem Store.shape_of_writeBlock_eq_some {s s' : Store P K} {p : P} {b off : ℕ}
    {xs : Array K} (h : s.writeBlock p b off xs = some s') : s'.shape = s.shape := by
  unfold Store.writeBlock at h
  have key : ∀ (l : List ℕ) (s : Store P K),
      l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s' →
        s'.shape = s.shape := by
    intro l
    induction l with
    | nil =>
      intro s h
      simp only [List.foldlM_nil, pure, Option.some.injEq] at h
      rw [h]
    | cons i l ih =>
      intro s h
      rw [List.foldlM_cons] at h
      obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
      change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
      obtain ⟨v, -, hw⟩ := Option.bind_eq_some_iff.mp h₂
      rw [ih s₂ h₃, Store.shape_of_write_eq_some hw]
  exact key _ s h

/-- Block writes keep the shape of the store. -/
theorem Store.shape_of_writeBlocks_eq_some {p : P} :
    ∀ {s s' : Store P K} {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)},
      s.writeBlocks p bs ys = some s' → s'.shape = s.shape
  | _, _, [], [], h => by cases h; rfl
  | _, _, [], _ :: _, h => by cases h
  | _, _, _ :: _, [], h => by cases h
  | s, s', b :: bs, y :: ys, h => by
    rw [Store.writeBlocks] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [Store.shape_of_writeBlocks_eq_some h₂, Store.shape_of_writeBlock_eq_some h₁]

/-- A block write succeeds where every cell of the block can be written. -/
theorem Store.exists_writeBlock_eq_some_of_write {s : Store P K} {p : P} {b off : ℕ}
    {xs : Array K} (h : ∀ j < xs.size, ∃ v s', s.write p b (off + j) v = some s') :
    ∃ s', s.writeBlock p b off xs = some s' := by
  unfold Store.writeBlock
  have key : ∀ l : List ℕ, (∀ j ∈ l, j < xs.size) → ∀ s' : Store P K, s'.shape = s.shape →
      ∃ s'', l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s' = some s'' := by
    intro l
    induction l with
    | nil => intro _ s' _; exact ⟨s', rfl⟩
    | cons i l ih =>
      intro hl s' hsh
      have hi := hl i List.mem_cons_self
      obtain ⟨v, s₀, hs₀⟩ := h i hi
      obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ xs[i]
      obtain ⟨s₃, hs₃⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) s₂
        ((Store.shape_of_write_eq_some hs₂).trans hsh)
      refine ⟨s₃, ?_⟩
      rw [List.foldlM_cons]
      change Option.bind (Option.bind xs[i]? fun v => s'.write p b (off + i) v) _ = _
      rw [Array.getElem?_eq_getElem hi, Option.bind_some, hs₂, Option.bind_some, hs₃]
  exact key _ (fun j hj => List.mem_range.mp hj) s rfl

/-- A block write succeeds where every cell of the block can be read. -/
theorem Store.exists_writeBlock_eq_some {s : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (h : ∀ j < xs.size, ∃ w, s.read p b (off + j) = some w) :
    ∃ s', s.writeBlock p b off xs = some s' :=
  Store.exists_writeBlock_eq_some_of_write fun j hj =>
    let ⟨w, hw⟩ := h j hj
    ⟨w, Store.exists_write_eq_some_of_read_eq_some hw⟩

/-- A write changes no read of another tag. -/
theorem Store.read_of_write_eq_some_of_ne_tag {s s' : Store P K} {p q : P} {b i b' i' : ℕ}
    {v : K} (h : s.write p b i v = some s') (hq : q ≠ p) : s'.read q b' i' = s.read q b' i' := by
  by_cases hbi : b' = b ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := hbi
    unfold Store.write at h
    rcases hb : s[b']? with _ | ⟨q', arr⟩ <;> rw [hb] at h
    · exact absurd h (by simp)
    · dsimp only at h
      split_ifs at h with hq'
      obtain ⟨rfl, hi⟩ := hq'
      cases h
      obtain ⟨hb', heq⟩ := Array.getElem?_eq_some_iff.mp hb
      simp [Store.read, Array.set!, hb', heq, Ne.symm hq]
  · exact Store.read_of_write_eq_some_of_ne h (by tauto)

/-- Extensionality of stores: two stores of the same shape with the same reads are equal. -/
theorem Store.ext_of_shape_eq {s s' : Store P K} (hsh : s.shape = s'.shape)
    (h : ∀ q b i, s.read q b i = s'.read q b i) : s = s' := by
  have hsize : s.size = s'.size := by
    simpa [Store.shape] using congrArg Array.size hsh
  apply Array.ext hsize
  intro b hb hb'
  have hshb : s.shape[b]? = s'.shape[b]? := by rw [hsh]
  simp only [Store.shape, Array.getElem?_map, Array.getElem?_eq_getElem hb,
    Array.getElem?_eq_getElem hb', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshb
  obtain ⟨htag, hlen⟩ := hshb
  refine Prod.ext htag (Array.ext hlen fun i hi hi' => ?_)
  have hr := h s[b].1 b i
  simp only [Store.read, Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hb', ← htag,
    if_true, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi', Option.join_some] at hr
  exact hr

/-- A read of a pushed store, below or above its top: the store under it. -/
theorem Store.read_push_of_ne {s : Store P K} {x : P × Array (Option K)} {q : P} {b i : ℕ}
    (hb : b ≠ s.size) : Store.read (s.push x) q b i = s.read q b i := by
  simp [Store.read, Array.getElem?_push, hb]

/-- A read past the last buffer fails. -/
theorem Store.read_eq_none_of_size_le {s : Store P K} {q : P} {b i : ℕ} (hb : s.size ≤ b) :
    s.read q b i = none := by
  simp [Store.read, Array.getElem?_eq_none hb]

/-- A read of a popped store, below its new top. -/
theorem Store.read_pop_of_lt {s : Store P K} {q : P} {b i : ℕ} (hb : b < s.size - 1) :
    Store.read s.pop q b i = s.read q b i := by
  unfold Store.read
  rw [Array.getElem?_pop, if_pos hb]

omit [DecidableEq P] in
/-- Two stores of the same shape have the same number of buffers. -/
theorem Store.size_eq_of_shape_eq {s s' : Store P K} (h : s.shape = s'.shape) :
    s.size = s'.size := by
  simpa [Store.shape] using congrArg Array.size h


/-! #### Shapes, block reads and block writes -/

omit [DecidableEq P] in
/-- The shape of a store at one buffer: its tag and its length. -/
theorem Store.getElem?_shape {s : Store P K} {b : ℕ} :
    s.shape[b]? = s[b]?.map fun x => (x.1, x.2.size) := by
  simp [Store.shape]

omit [DecidableEq P] in
/-- The shape has one entry per buffer. -/
theorem Store.size_shape (s : Store P K) : s.shape.size = s.size := by
  simp [Store.shape]

omit [DecidableEq P] in
/-- The shape of a popped store is the popped shape. -/
theorem Store.shape_pop (s : Store P K) : Store.shape (Array.pop s) = s.shape.pop := by
  simp [Store.shape]

omit [DecidableEq P] in
/-- The shape of a pushed store, below its top: the shape of the store under it. -/
theorem Store.getElem?_shape_push_of_lt {s : Store P K} {b : ℕ} (x : P × Array (Option K))
    (hb : b < s.size) : (Store.shape (s.push x))[b]? = s.shape[b]? := by
  simp [Store.shape, Array.getElem?_push, Nat.ne_of_lt hb]

omit [DecidableEq P] in
/-- The shape of a pushed buffer of $n$ uninitialised cells, at the top. -/
theorem Store.getElem?_shape_push_size (s : Store P K) (p : P) (n : ℕ) :
    (Store.shape (s.push (p, Array.replicate n none)))[s.size]? = some (p, n) := by
  simp only [Store.shape, Array.map_push, Array.getElem?_push, Array.size_map, if_true]
  simp

omit [DecidableEq P] in
/-- The shape of a store with three buffers of uninitialised cells pushed, below the first of
them: the shape of the store under them. -/
theorem Store.getElem?_shape_push_push_push_of_lt {s : Store P K} {p : P} {a b c β : ℕ}
    (hβ : β < s.size) :
    (Store.shape (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
      (p, Array.replicate c none)))[β]? = s.shape[β]? := by
  rw [Store.getElem?_shape_push_of_lt _ (by simp only [Array.size_push]; omega),
    Store.getElem?_shape_push_of_lt _ (by simp only [Array.size_push]; omega),
    Store.getElem?_shape_push_of_lt _ hβ]

omit [DecidableEq P] in
/-- The shapes of three pushed buffers of $a$, $b$, $c$ uninitialised cells, at their handles. -/
theorem Store.getElem?_shape_push_push_push (s : Store P K) (p : P) (a b c : ℕ) :
    (Store.shape (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
        (p, Array.replicate c none)))[s.size]? = some (p, a) ∧
      (Store.shape (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
        (p, Array.replicate c none)))[(s.push (p, Array.replicate a none)).size]? =
        some (p, b) ∧
      (Store.shape (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
        (p, Array.replicate c none)))[((s.push (p, Array.replicate a none)).push
          (p, Array.replicate b none)).size]? = some (p, c) := by
  refine ⟨?_, ?_, Store.getElem?_shape_push_size _ _ _⟩
  · rw [Store.getElem?_shape_push_of_lt _ (by simp only [Array.size_push]; omega),
      Store.getElem?_shape_push_of_lt _ (by simp only [Array.size_push]; omega),
      Store.getElem?_shape_push_size]
  · rw [Store.getElem?_shape_push_of_lt _ (by simp only [Array.size_push]; omega),
      Store.getElem?_shape_push_size]

/-- A read of a store with three buffers popped, below the popped ones: the read of the store. -/
theorem Store.read_pop_pop_pop_of_lt {s : Store P K} {q : P} {b i : ℕ} (hb : b + 3 < s.size) :
    Store.read (Array.pop (Array.pop (Array.pop s))) q b i = s.read q b i := by
  rw [Store.read_pop_of_lt (by simp only [Array.size_pop]; omega),
    Store.read_pop_of_lt (by simp only [Array.size_pop]; omega), Store.read_pop_of_lt (by omega)]

/-- A read of a store with three buffers of uninitialised cells pushed, below the first of them:
the read of the store under them. -/
theorem Store.read_push_push_push_of_lt {s : Store P K} {p q : P} {a b c β i : ℕ}
    (hβ : β < s.size) :
    Store.read (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
      (p, Array.replicate c none)) q β i = s.read q β i := by
  rw [Store.read_push_of_lt (by simp only [Array.size_push]; omega),
    Store.read_push_of_lt (by simp only [Array.size_push]; omega), Store.read_push_of_lt hβ]

/-- A write succeeds at a cell inside a buffer of its tag, as the shape gives it. -/
theorem Store.exists_write_eq_some_of_getElem?_shape {s : Store P K} {p : P} {b i n : ℕ}
    (v : K) (hs : s.shape[b]? = some (p, n)) (hi : i < n) : ∃ s', s.write p b i v = some s' := by
  rw [Store.getElem?_shape] at hs
  unfold Store.write
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at hs
  · simp at hs
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, if_pos ⟨rfl, hi⟩⟩

/-- A read that succeeds is inside a buffer of its tag, as the shape gives it. -/
theorem Store.exists_getElem?_shape_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : ∃ n, s.shape[b]? = some (p, n) ∧ i < n := by
  unfold Store.read at h
  rw [Store.getElem?_shape]
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · simp at h
  · dsimp only at h
    split_ifs at h with hq
    subst hq
    refine ⟨arr.size, rfl, ?_⟩
    rcases hi : arr[i]? with _ | x
    · simp [hi] at h
    · exact (Array.getElem?_eq_some_iff.mp hi).1

/-- A read at a tag other than its buffer's fails. -/
theorem Store.read_eq_none_of_getElem?_shape_of_ne {s : Store P K} {p q : P} {b i n : ℕ}
    (hs : s.shape[b]? = some (p, n)) (hq : q ≠ p) : s.read q b i = none := by
  rw [Store.getElem?_shape] at hs
  unfold Store.read
  rcases hb : s[b]? with _ | ⟨r, arr⟩
  · rfl
  · rw [hb] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    simp [Ne.symm hq]

private theorem mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys →
      ys.length = l.length ∧ ∀ k (hk : k < l.length) (hk' : k < ys.length), f l[k] = some ys[k]
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | a :: l, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hk⟩ := mapM_eq_some hbs
    refine ⟨by simp [hlen], fun k hk₁ hk₂ => ?_⟩
    rcases k with _ | k
    · simpa using hb
    · simpa using hk k (by simpa using hk₁) (by simpa using hk₂)

/-- A block read that succeeds reads as many cells as asked. -/
theorem Store.size_of_readBlock_eq_some {s : Store P K} {p : P} {b off len : ℕ} {X : Array K}
    (h : s.readBlock p b off len = some X) : X.size = len := by
  unfold Store.readBlock at h
  rw [List.mapM_toArray] at h
  obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using (mapM_eq_some hys).1

/-- A block read that succeeds reads each cell of the block. -/
theorem Store.read_of_readBlock_eq_some_of_lt {s : Store P K} {p : P} {b off len m : ℕ}
    {X : Array K} (h : s.readBlock p b off len = some X) (hm : m < len) :
    s.read p b (off + m) = X[m]? := by
  unfold Store.readBlock at h
  rw [List.mapM_toArray] at h
  obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hlen, hk⟩ := mapM_eq_some hys
  have hm' : m < ys.length := by simpa [hlen] using hm
  have := hk m (by simpa using hm) hm'
  simp only [List.getElem_range] at this
  rw [this]
  simp [List.getElem?_eq_getElem hm']

/-- A block read succeeds where every cell of the block can be read, and reads their values. -/
theorem Store.readBlock_eq_some_map_range {s : Store P K} {p : P} {b off len : ℕ} (g : ℕ → K)
    (h : ∀ i < len, s.read p b (off + i) = some (g i)) :
    s.readBlock p b off len = some ((List.range len).toArray.map g) := by
  unfold Store.readBlock
  rw [Array.mapM_eq_mapM_toList, List.toList_toArray,
    List.mapM_eq_some_map _ fun i hi => h i (List.mem_range.mp hi)]
  change some _ = some _
  congr 1
  apply Array.ext (by simp)
  intro i h1 h2
  simp

/-- A block read of a nonempty block that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_readBlock_eq_some {s : Store P K} {p : P} {b off len : ℕ}
    {X : Array K} (h : s.readBlock p b off len = some X) (hlen : 0 < len) : b < s.size :=
  Store.lt_size_of_read_eq_some ((Store.read_of_readBlock_eq_some_of_lt h hlen).trans
    (Array.getElem?_eq_getElem (by rw [Store.size_of_readBlock_eq_some h]; exact hlen)))

/-- A block write that succeeds is inside a buffer of its tag, as the shape gives it. -/
theorem Store.exists_getElem?_shape_of_writeBlock_eq_some {s s' : Store P K} {p : P}
    {b off j : ℕ} {xs : Array K} (h : s.writeBlock p b off xs = some s') (hj : j < xs.size) :
    ∃ n, s.shape[b]? = some (p, n) ∧ off + j < n := by
  obtain ⟨n, hn, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some
    ((Store.read_of_writeBlock_eq_some_of_lt h hj).trans (Array.getElem?_eq_getElem hj))
  exact ⟨n, Store.shape_of_writeBlock_eq_some h ▸ hn, hlt⟩

/-- A block write of a nonempty block that succeeds is in a buffer of the store. -/
theorem Store.lt_size_of_writeBlock_eq_some {s s' : Store P K} {p : P} {b off : ℕ}
    {xs : Array K} (h : s.writeBlock p b off xs = some s') (hxs : 0 < xs.size) : b < s.size := by
  obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_writeBlock_eq_some h hxs
  simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hn).1

/-- A block write succeeds where the block lies inside a buffer of its tag, as the shape
gives it. -/
theorem Store.exists_writeBlock_eq_some_of_getElem?_shape {s : Store P K} {p : P} {b off : ℕ}
    {xs : Array K} (h : ∀ i < xs.size, ∃ n, s.shape[b]? = some (p, n) ∧ off + i < n) :
    ∃ s', s.writeBlock p b off xs = some s' :=
  Store.exists_writeBlock_eq_some_of_write fun j hj =>
    let ⟨_, hn, hlt⟩ := h j hj
    ⟨xs[j], Store.exists_write_eq_some_of_getElem?_shape _ hn hlt⟩

end Store

/-! ### The frame of a block write -/

section Frame

variable {P K : Type} [DecidableEq P]

/-- The frame of a run that writes the block of $L$ cells of buffer `dst` from offset `dOff` at
tag `p`, with the scratch buffer `T`, started from the store `s₀`: the store `s` has the shape of
`s₀`, every cell outside the block and the scratch buffer reads as in `s₀`, and cell
`dOff + m` of the block reads `g m` for $m < L$. A kernel or an oracle implementation carries it
through its loops; popping the scratch buffer then gives the block write
(`NLAlib.Computation.Store.BlockFrame.pop_eq`). -/
def Store.BlockFrame (s₀ : Store P K) (p : P) (T dst dOff L : ℕ) (s : Store P K)
    (g : ℕ → Option K) : Prop :=
  s.shape = s₀.shape ∧
    (∀ q b i, b ≠ T → ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L) →
      s.read q b i = s₀.read q b i) ∧
    ∀ m < L, s.read p dst (dOff + m) = g m

variable {s₀ s s' : Store P K} {p : P} {T dst dOff L : ℕ} {g : ℕ → Option K}

/-- A write into cell `dOff + m` of the block keeps the frame, with the written value at $m$. -/
theorem Store.BlockFrame.write_of_lt (h : Store.BlockFrame s₀ p T dst dOff L s g) {m : ℕ} {v : K}
    (hm : m < L) (hw : s.write p dst (dOff + m) v = some s') :
    Store.BlockFrame s₀ p T dst dOff L s' (Function.update g m (some v)) := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m' hm' => ?_⟩
  · rw [← hfr q b i hbT hout]
    by_cases hq : q = p
    · subst hq
      refine Store.read_of_write_eq_some_of_ne hw ?_
      by_cases hb : b = dst
      · subst hb
        exact Or.inr fun he => hout ⟨rfl, rfl, by omega, by omega⟩
      · exact Or.inl hb
    · exact Store.read_of_write_eq_some_of_ne_tag hw hq
  · by_cases hmm : m' = m
    · subst hmm
      rw [Function.update_self]
      exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hmm, ← hblk m' hm']
      exact Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega))

/-- A write into the scratch buffer keeps the frame. -/
theorem Store.BlockFrame.write_scratch (h : Store.BlockFrame s₀ p T dst dOff L s g) {k : ℕ}
    {v : K} (hdT : 0 < L → dst ≠ T) (hw : s.write p T k v = some s') :
    Store.BlockFrame s₀ p T dst dOff L s' g := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m hm => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hbT), hfr _ b i hbT hout]
    · rw [Store.read_of_write_eq_some_of_ne_tag hw hq, hfr q b i hbT hout]
  · rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (hdT (by omega))), hblk m hm]

/-- In the frame, a write succeeds at every cell of a buffer of `s₀` of its tag. -/
theorem Store.BlockFrame.exists_write_eq_some (h : Store.BlockFrame s₀ p T dst dOff L s g)
    {b i n : ℕ} (v : K) (hs : s₀.shape[b]? = some (p, n)) (hi : i < n) :
    ∃ s', s.write p b i v = some s' :=
  Store.exists_write_eq_some_of_getElem?_shape v (h.1 ▸ hs) hi

/-- The frame depends only on the values of the block below its length. -/
theorem Store.BlockFrame.congr (h : Store.BlockFrame s₀ p T dst dOff L s g) {g' : ℕ → Option K}
    (hg : ∀ m < L, g m = g' m) : Store.BlockFrame s₀ p T dst dOff L s g' :=
  ⟨h.1, h.2.1, fun m hm => (h.2.2 m hm).trans (hg m hm)⟩

/-- In the frame, a cell outside the block and the scratch buffer reads as in `s₀`. -/
theorem Store.BlockFrame.read_of_ne (h : Store.BlockFrame s₀ p T dst dOff L s g) {q : P}
    {b i : ℕ} (hbT : b ≠ T) (hout : ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L)) :
    s.read q b i = s₀.read q b i :=
  h.2.1 q b i hbT hout

/-- A block write inside the block keeps the frame, with the written values. -/
theorem Store.BlockFrame.writeBlock (h : Store.BlockFrame s₀ p T dst dOff L s g) {off : ℕ}
    {xs : Array K} (hw : s.writeBlock p dst (dOff + off) xs = some s') (hL : off + xs.size ≤ L) :
    Store.BlockFrame s₀ p T dst dOff L s'
      (fun k => if off ≤ k ∧ k < off + xs.size then xs[k - off]? else g k) := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  have hsh' := Store.shape_of_writeBlock_eq_some hw
  refine ⟨hsh'.trans hsh, fun q b i hbT hout => ?_, fun k hk => ?_⟩
  · by_cases hin : b = dst ∧ dOff + off ≤ i ∧ i < dOff + off + xs.size
    · obtain ⟨rfl, h₁, h₂⟩ := hin
      have hq : q ≠ p := fun hq => hout ⟨hq, rfl, by omega, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, xs[i - (dOff + off)]? = some v :=
        ⟨_, Array.getElem?_eq_getElem (by omega)⟩
      obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_read_eq_some
        ((Store.read_of_writeBlock_eq_some_of_lt (j := i - (dOff + off)) hw (by omega)).trans hv)
      rw [← hfr q b i hbT hout, Store.read_eq_none_of_getElem?_shape_of_ne hn hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hsh' ▸ hn) hq]
    · rw [Store.read_of_writeBlock_eq_some_of_ne hw (by omega), hfr q b i hbT hout]
  · beta_reduce
    by_cases hin : off ≤ k ∧ k < off + xs.size
    · rw [if_pos hin, show dOff + k = dOff + off + (k - off) by omega]
      exact Store.read_of_writeBlock_eq_some_of_lt hw (by omega)
    · rw [if_neg hin, Store.read_of_writeBlock_eq_some_of_ne hw (by omega), hblk k hk]

/-- A frame whose scratch buffer is the next free handle of `s₀` carries over to both stores with
one buffer pushed: the pushed buffer becomes the scratch buffer. -/
theorem Store.BlockFrame.push (h : Store.BlockFrame s₀ p s₀.size dst dOff L s g)
    (x : P × Array (Option K)) (hdT : 0 < L → dst < s₀.size) :
    Store.BlockFrame (s₀.push x) p s₀.size dst dOff L (s.push x) g := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  have hsz : s.size = s₀.size := by simpa [Store.size_shape] using congrArg Array.size hsh
  have hsh' := hsh
  simp only [Store.shape] at hsh'
  refine ⟨by simp [Store.shape, hsh'], fun q b i hbT hout => ?_, fun m hm => ?_⟩
  · by_cases hb : b < s₀.size
    · rw [Store.read_push_of_lt (by omega), Store.read_push_of_lt hb, hfr q b i hbT hout]
    · rw [Store.read_eq_none_of_size_le (by simp; omega),
        Store.read_eq_none_of_size_le (by simp; omega)]
  · rw [Store.read_push_of_lt (by have := hdT (by omega); omega), hblk m hm]

/-- Popping the scratch buffer: a store in the frame of a block write over `st₀` with a pushed
scratch buffer, whose block reads the entries of `Y`, pops to the block write of `Y` into
`st₀`. -/
theorem Store.BlockFrame.pop_eq {st₀ s₁ sF : Store P K} {arr : Array (Option K)} {Y : Array K}
    (hI : Store.BlockFrame (st₀.push (p, arr)) p st₀.size dst dOff L sF g)
    (hs₁ : st₀.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L)
    (hg : ∀ m < L, g m = Y[m]?) : Array.pop sF = s₁ := by
  obtain ⟨hsh, hfr, hblk⟩ := hI
  have hsh₁ := Store.shape_of_writeBlock_eq_some hs₁
  have hsize : sF.size = st₀.size + 1 := by
    simpa [Store.size_shape] using congrArg Array.size hsh
  have hsize₁ : s₁.size = st₀.size := by
    simpa [Store.size_shape] using congrArg Array.size hsh₁
  have hread₁ : ∀ m < L, s₁.read p dst (dOff + m) = Y[m]? := fun m hm =>
    Store.read_of_writeBlock_eq_some_of_lt hs₁ (by omega)
  refine Store.ext_of_shape_eq ?_ fun q b i => ?_
  · rw [Store.shape_pop, hsh, hsh₁]
    simp [Store.shape]
  by_cases hb : b < st₀.size
  swap
  · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le (by omega)]
  rw [Store.read_pop_of_lt (by omega)]
  by_cases hin : b = dst ∧ dOff ≤ i ∧ i < dOff + L
  · obtain ⟨rfl, h₁, h₂⟩ := hin
    have hi : i = dOff + (i - dOff) := by omega
    obtain ⟨v, hv⟩ : ∃ v, Y[i - dOff]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_read_eq_some
      ((hread₁ _ (by omega)).trans hv)
    by_cases hq : q = p
    · subst hq
      rw [hi, hblk _ (by omega), hg _ (by omega), hread₁ _ (by omega)]
    · rw [Store.read_eq_none_of_getElem?_shape_of_ne hn hq, hfr q b i (by omega) (by tauto),
        Store.read_push_of_lt hb, Store.read_eq_none_of_getElem?_shape_of_ne (hsh₁ ▸ hn) hq]
  · rw [hfr q b i (by omega) (by tauto), Store.read_push_of_lt hb,
      Store.read_of_writeBlock_eq_some_of_ne hs₁ (by omega)]

end Frame

/-! ### Reads after several block writes -/

section WriteBlocks

variable {P K : Type} [DecidableEq P]

/-- The frame of several block writes: if `s.writeBlocks p bs ys = some s'` and the cell
$(b, i)$ lies outside every block $(b', \mathit{off}, \ell)$ of `bs` ($b \ne b'$,
$i < \mathit{off}$ or $\mathit{off} + \ell \le i$), it reads the same after the writes as before,
at every tag. No printed source. -/
theorem Store.read_of_writeBlocks_eq_some_of_forall {p : P} {s s' : Store P K}
    {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)} (h : s.writeBlocks p bs ys = some s')
    {q : P} {b i : ℕ} (hb : ∀ x ∈ bs, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) :
    s'.read q b i = s.read q b i := by
  induction bs generalizing s ys with
  | nil => cases ys <;> cases h; rfl
  | cons x bs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      rw [Store.writeBlocks] at h
      split_ifs at h with hy
      obtain ⟨s₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      rw [ih h₂ fun z hz => hb z (List.mem_cons_of_mem _ hz)]
      refine Store.read_of_writeBlock_eq_some_of_ne h₁ ?_
      have := hb x List.mem_cons_self
      omega

end WriteBlocks

end NLAlib.Computation
