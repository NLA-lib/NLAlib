/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Order.Lattice
public import Mathlib.Order.PropInstances
public import NLAlib.Ops.Store

/-!
# Reads after writes, and the frame of a run

The state of a run is written as a chain of updates over a store that is kept opaque. This file
has the lemmas that push a read (`get`, `readBlock`, `len`) through an update (`upd`, `updBlock`)
or a scratch buffer (`push`, `pop`), each with a side condition on handles or offsets; the tactic
`store_simp` (file `StoreSimp`) applies them and discharges the side conditions.

An invariant does not describe the whole store. It says what the written blocks hold, and that
the store agrees with the initial one off a footprint: `NLAlib.Ops.Store.EqOff F s s'`. A write
inside the footprint keeps it (`EqOff.upd`, `EqOff.updBlock`), a read outside it is a read of the
initial store (`EqOff.get_eq`, `EqOff.readBlock_eq`), and a scratch buffer leaves it when it is
popped (`EqOff.pop`). Footprints are built from `NLAlib.Ops.Store.inBlock`,
`NLAlib.Ops.Store.inBuf` and `⊔`.

## Main results

* `NLAlib.Ops.Store.readBlock_updBlock_same`, `NLAlib.Ops.Store.readBlock_upd_concat`: reading
  what was written.
* `NLAlib.Ops.Store.EqOff.eq_updBlock`: a store that agrees with `s` off a block and holds `xs`
  in it is `s.updBlock b off xs`.
* `NLAlib.Ops.Store.EqOff.pop`: the frame after a scratch buffer is freed.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

namespace Store

/-! ### Reads through updates -/

theorem get_upd_of_buf_ne {s : Store K} {b i b' : ℕ} (h : b' ≠ b) (v : K) (i' : ℕ) :
    (s.upd b i v).get b' i' = s.get b' i' := get_upd_of_ne (Or.inl h) v

theorem get_upd_of_idx_ne {s : Store K} {b i i' : ℕ} (h : i' ≠ i) (v : K) :
    (s.upd b i v).get b i' = s.get b i' := get_upd_of_ne (Or.inr h) v

theorem readBlock_upd_of_buf_ne {s : Store K} {b i b' : ℕ} (h : b' ≠ b) (v : K) (off n : ℕ) :
    (s.upd b i v).readBlock b' off n = s.readBlock b' off n :=
  readBlock_congr fun _ _ => get_upd_of_buf_ne h v _

theorem readBlock_upd_of_lt {s : Store K} {b i off : ℕ} (h : i < off) (v : K) (n : ℕ) :
    (s.upd b i v).readBlock b off n = s.readBlock b off n :=
  readBlock_congr fun _ _ => get_upd_of_idx_ne (by omega) v

theorem readBlock_upd_of_ge {s : Store K} {b i off n : ℕ} (h : off + n ≤ i) (v : K) :
    (s.upd b i v).readBlock b off n = s.readBlock b off n :=
  readBlock_congr fun _ _ => get_upd_of_idx_ne (by omega) v

theorem readBlock_updBlock_of_buf_ne {s : Store K} {b b' : ℕ} (h : b' ≠ b) (off : ℕ)
    (xs : List K) (off' n : ℕ) :
    (s.updBlock b off xs).readBlock b' off' n = s.readBlock b' off' n :=
  readBlock_congr fun _ _ => get_updBlock_of_buf_ne h _ _ _

theorem readBlock_updBlock_of_le {s : Store K} {b off off' n : ℕ} (h : off' + n ≤ off)
    (xs : List K) : (s.updBlock b off xs).readBlock b off' n = s.readBlock b off' n :=
  readBlock_congr fun _ _ => get_updBlock_of_lt (by omega) _

theorem readBlock_updBlock_of_ge {s : Store K} {b off off' : ℕ} {xs : List K}
    (h : off + xs.length ≤ off') (n : ℕ) :
    (s.updBlock b off xs).readBlock b off' n = s.readBlock b off' n :=
  readBlock_congr fun _ _ => get_updBlock_of_ge (by omega)

/-- Reading back a block that was put. -/
theorem readBlock_updBlock_same {s : Store K} {b off n : ℕ} {xs : List K} (hn : xs.length = n)
    (hlen : off + n ≤ s.len b) : (s.updBlock b off xs).readBlock b off n = some xs := by
  subst hn
  exact readBlock_updBlock_self hlen

theorem readBlock_one_of_get {s : Store K} {b off : ℕ} {v : K} (h : s.get b off = some v) :
    s.readBlock b off 1 = some [v] := by
  simp [readBlock_succ, h]

/-- Two adjacent blocks are one block. -/
theorem readBlock_add {s : Store K} {b off n k : ℕ} {xs ys : List K}
    (h1 : s.readBlock b off n = some xs) (h2 : s.readBlock b (off + n) k = some ys) :
    s.readBlock b off (n + k) = some (xs ++ ys) := by
  obtain ⟨hl1, hg1⟩ := readBlock_eq_some_iff.mp h1
  obtain ⟨hl2, hg2⟩ := readBlock_eq_some_iff.mp h2
  refine readBlock_eq_some_iff.mpr ⟨by simp [hl1, hl2], fun j hj => ?_⟩
  by_cases hjn : j < n
  · rw [hg1 j hjn, List.getElem?_append_left (by omega)]
  · have := hg2 (j - n) (by omega)
    rw [show off + n + (j - n) = off + j by omega] at this
    rw [this, List.getElem?_append_right (by omega), hl1]

/-- A block and the cell that follows it. -/
theorem readBlock_succ_of {s : Store K} {b off n : ℕ} {xs : List K} {v : K}
    (h1 : s.readBlock b off n = some xs) (h2 : s.get b (off + n) = some v) :
    s.readBlock b off (n + 1) = some (xs ++ [v]) :=
  readBlock_add h1 (readBlock_one_of_get h2)

/-- A block that was read, extended by a cell that is put after it. -/
theorem readBlock_upd_concat {s : Store K} {b off n : ℕ} {xs : List K}
    (h : s.readBlock b off n = some xs) (hlen : off + n < s.len b) (v : K) :
    (s.upd b (off + n) v).readBlock b off (n + 1) = some (xs ++ [v]) :=
  readBlock_succ_of (by rw [readBlock_upd_of_ge le_rfl, h]) (get_upd_self hlen v)

/-- A block from offset zero that was read, extended by a cell that is put after it. -/
theorem readBlock_upd_concat_zero {s : Store K} {b n : ℕ} {xs : List K}
    (h : s.readBlock b 0 n = some xs) (hlen : n < s.len b) (v : K) :
    (s.upd b n v).readBlock b 0 (n + 1) = some (xs ++ [v]) := by
  have := readBlock_upd_concat h (by simpa using hlen) v
  rwa [Nat.zero_add] at this

/-! ### Shapes -/

theorem length_eq_of_shape {s s' : Store K} (h : s'.shape = s.shape) : s'.length = s.length := by
  simpa [shape] using congrArg List.length h

theorem len_eq_of_shape {s s' : Store K} (h : s'.shape = s.shape) (b : ℕ) :
    s'.len b = s.len b := by
  have := congrArg (fun l : List ℕ => (l[b]?).getD 0) h
  simpa [shape, len, List.getElem?_map] using this

/-- Two stores with the same shape and the same cells are equal. -/
theorem ext_get {s s' : Store K} (hs : s'.shape = s.shape)
    (hg : ∀ b i, s'.get b i = s.get b i) : s' = s := by
  apply List.ext_getElem?
  intro b
  have hb := congrArg (fun l : List ℕ => l[b]?) hs
  simp only [shape, List.getElem?_map] at hb
  have hgb := hg b
  simp only [get] at hgb
  cases h' : s'[b]? with
  | none => cases h : s[b]? with
    | none => rfl
    | some buf => simp [h, h'] at hb
  | some buf' => cases h : s[b]? with
    | none => simp [h, h'] at hb
    | some buf =>
      have hl : buf'.length = buf.length := by simpa [h, h'] using hb
      refine congrArg some (List.ext_getElem? fun i => ?_)
      have hi := hgb i
      simp only [h, h', Option.bind_some] at hi
      by_cases hlt : i < buf.length
      · rw [List.getElem?_eq_getElem (hl ▸ hlt), List.getElem?_eq_getElem hlt] at hi ⊢
        exact congrArg some (by simpa using hi)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ### Scratch buffers -/

@[simp] theorem length_push (s : Store K) (n : ℕ) : (s.push n).length = s.length + 1 := by
  simp [push]

theorem lt_length_push {s : Store K} {b : ℕ} (h : b < s.length) (n : ℕ) :
    b < (s.push n).length := by
  rw [length_push]
  exact Nat.lt_succ_of_lt h

theorem length_lt_length_push (s : Store K) (n : ℕ) : s.length < (s.push n).length := by simp

theorem get_push_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (n i : ℕ) :
    (s.push n).get b i = s.get b i := get_append_of_lt h _ i

theorem readBlock_push_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (n off k : ℕ) :
    (s.push n).readBlock b off k = s.readBlock b off k := readBlock_append_of_lt h _ off k

theorem len_push_of_lt {s : Store K} {b : ℕ} (h : b < s.length) (n : ℕ) :
    (s.push n).len b = s.len b := len_append_of_lt h _

@[simp] theorem len_push_top (s : Store K) (n : ℕ) : (s.push n).len s.length = n := by
  simp [push]

theorem shape_push (s : Store K) (n : ℕ) : (s.push n).shape = s.shape ++ [n] := by
  simp [push, shape]

theorem length_pop (s : Store K) : s.pop.length = s.length - 1 := by simp [pop]

theorem getElem?_pop_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) : s.pop[b]? = s[b]? := by
  simp only [pop, List.getElem?_dropLast]
  rw [if_pos (by omega)]

theorem get_pop_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) (i : ℕ) :
    s.pop.get b i = s.get b i := by
  simp only [get, getElem?_pop_of_lt h]

theorem get_pop_of_ge {s : Store K} {b : ℕ} (h : s.length ≤ b + 1) (i : ℕ) :
    s.pop.get b i = none := by
  simp [get, pop, List.getElem?_eq_none (show (s.dropLast).length ≤ b by simp; omega)]

theorem readBlock_pop_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) (off n : ℕ) :
    s.pop.readBlock b off n = s.readBlock b off n :=
  readBlock_congr fun _ _ => get_pop_of_lt h _

theorem len_pop_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) : s.pop.len b = s.len b := by
  simp only [len, getElem?_pop_of_lt h]

theorem pop_push (s : Store K) (n : ℕ) : (s.push n).pop = s := by simp [push, pop]

/-- An update below the top buffer commutes with the pop. -/
theorem pop_upd_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) (i : ℕ) (v : K) :
    (s.upd b i v).pop = s.pop.upd b i v := by
  refine ext_get (by simp [shape_pop]) fun b' i' => ?_
  by_cases hb' : b' + 1 < s.length
  · rw [get_pop_of_lt (by simpa using hb')]
    by_cases hc : b' = b ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := hc
      by_cases hi : i' < s.len b'
      · rw [get_upd_self hi, get_upd_self (by rwa [len_pop_of_lt hb'])]
      · have h1 : (s.upd b' i' v).get b' i' = none := by
          cases hg : (s.upd b' i' v).get b' i' with
          | none => rfl
          | some a => exact absurd (by simpa using lt_len_of_get hg) hi
        have h2 : (s.pop.upd b' i' v).get b' i' = none := by
          cases hg : (s.pop.upd b' i' v).get b' i' with
          | none => rfl
          | some a => exact absurd (by simpa [len_pop_of_lt hb'] using lt_len_of_get hg) hi
        rw [h1, h2]
    · have hne : b' ≠ b ∨ i' ≠ i := by tauto
      rw [get_upd_of_ne hne, get_upd_of_ne hne, get_pop_of_lt hb']
  · rw [get_pop_of_ge (by simpa using not_lt.mp hb')]
    have hne : b' ≠ b := by omega
    rw [get_upd_of_buf_ne hne, get_pop_of_ge (not_lt.mp hb')]

/-- An update of the top buffer is lost by the pop. -/
theorem pop_upd_top {s : Store K} {b : ℕ} (h : b + 1 = s.length) (i : ℕ) (v : K) :
    (s.upd b i v).pop = s.pop := by
  refine ext_get (by simp [shape_pop]) fun b' i' => ?_
  by_cases hb' : b' + 1 < s.length
  · rw [get_pop_of_lt (by simpa using hb'), get_upd_of_buf_ne (by omega), get_pop_of_lt hb']
  · rw [get_pop_of_ge (by simpa using not_lt.mp hb'), get_pop_of_ge (not_lt.mp hb')]

theorem pop_updBlock_of_lt {s : Store K} {b : ℕ} (h : b + 1 < s.length) (off : ℕ)
    (xs : List K) : (s.updBlock b off xs).pop = s.pop.updBlock b off xs := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [updBlock_cons, ih (by simpa using h), pop_upd_of_lt h, updBlock_cons]

theorem pop_updBlock_top {s : Store K} {b : ℕ} (h : b + 1 = s.length) (off : ℕ) (xs : List K) :
    (s.updBlock b off xs).pop = s.pop := by
  induction xs generalizing s off with
  | nil => rfl
  | cons x xs ih => rw [updBlock_cons, ih (by simpa using h), pop_upd_top h]

/-! ### Footprints and frames -/

/-- The cells `off, …, off + n - 1` of the buffer `b`. -/
def inBlock (b off n : ℕ) : ℕ → ℕ → Prop := fun b' i => b' = b ∧ off ≤ i ∧ i < off + n

/-- The cells of the buffer `b`. -/
def inBuf (b : ℕ) : ℕ → ℕ → Prop := fun b' _ => b' = b

/-- **The frame of a run**: `s'` has the shape of `s` and the same cells off the footprint `F`. -/
def EqOff (F : ℕ → ℕ → Prop) (s s' : Store K) : Prop :=
  s'.shape = s.shape ∧ ∀ b i, ¬ F b i → s'.get b i = s.get b i

namespace EqOff

variable {F F' : ℕ → ℕ → Prop} {s s' : Store K}

theorem refl (F : ℕ → ℕ → Prop) (s : Store K) : EqOff F s s := ⟨rfl, fun _ _ _ => rfl⟩

theorem mono (h : EqOff F s s') (hF : ∀ b i, F b i → F' b i) : EqOff F' s s' :=
  ⟨h.1, fun b i hn => h.2 b i fun hf => hn (hF b i hf)⟩

/-- A write inside the footprint. -/
theorem upd (h : EqOff F s s') {b i : ℕ} (hF : F b i) (v : K) : EqOff F s (s'.upd b i v) :=
  ⟨by rw [shape_upd, h.1], fun b' i' hn => by
    have hne : b' ≠ b ∨ i' ≠ i := by
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hn (hc.1 ▸ hc.2 ▸ hF)
    rw [get_upd_of_ne hne, h.2 b' i' hn]⟩

/-- A block write inside the footprint. -/
theorem updBlock (h : EqOff F s s') {b off : ℕ} {xs : List K}
    (hF : ∀ j < xs.length, F b (off + j)) : EqOff F s (s'.updBlock b off xs) := by
  induction xs generalizing s' off with
  | nil => exact h
  | cons x xs ih =>
    rw [updBlock_cons]
    refine ih (h.upd (by simpa using hF 0 (by simp)) x) fun j hj => ?_
    have := hF (j + 1) (by simpa using hj)
    rwa [show off + (j + 1) = off + 1 + j by omega] at this

theorem length_eq (h : EqOff F s s') : s'.length = s.length := length_eq_of_shape h.1

theorem len_eq (h : EqOff F s s') (b : ℕ) : s'.len b = s.len b := len_eq_of_shape h.1 b

/-- A read outside the footprint. -/
theorem get_eq (h : EqOff F s s') {b i : ℕ} (hF : ¬ F b i) : s'.get b i = s.get b i := h.2 b i hF

/-- A block read outside the footprint. -/
theorem readBlock_eq (h : EqOff F s s') {b off n : ℕ} (hF : ∀ j < n, ¬ F b (off + j)) :
    s'.readBlock b off n = s.readBlock b off n :=
  readBlock_congr fun j hj => h.2 b _ (hF j hj)

/-- A fact about a block outside the footprint is kept. -/
theorem readBlock_of (h : EqOff F s s') {b off n : ℕ} {xs : List K}
    (hr : s.readBlock b off n = some xs) (hF : ∀ j < n, ¬ F b (off + j)) :
    s'.readBlock b off n = some xs := (h.readBlock_eq hF).trans hr

/-- **A store that agrees with `s` off a block and holds `xs` in it is `s.updBlock b off xs`.** -/
theorem eq_updBlock {b off n : ℕ} {xs : List K} (h : EqOff (inBlock b off n) s s')
    (hr : s'.readBlock b off n = some xs) : s' = s.updBlock b off xs := by
  obtain ⟨hl, hg⟩ := readBlock_eq_some_iff.mp hr
  refine ext_get (by rw [shape_updBlock, h.1]) fun b' i => ?_
  by_cases hin : inBlock b off n b' i
  · obtain ⟨rfl, h1, h2⟩ := hin
    have hlen : off + xs.length ≤ s.len b' := by
      have := le_len_of_readBlock hr (by omega)
      rwa [h.len_eq, ← hl] at this
    have := hg (i - off) (by omega)
    rw [show off + (i - off) = i by omega] at this
    rw [this, ← get_updBlock hlen (j := i - off) (by omega), show off + (i - off) = i by omega]
  · rw [h.2 b' i hin]
    simp only [inBlock, not_and, not_lt] at hin
    by_cases hb : b' = b
    · subst hb
      by_cases hlt : i < off
      · rw [get_updBlock_of_lt hlt]
      · rw [get_updBlock_of_ge (by have := hin rfl (by omega); omega)]
    · rw [get_updBlock_of_buf_ne hb]

/-- **The frame after a scratch buffer is freed**: a run on `s.push n` that kept the store off
`F` and the scratch buffer leaves, after the pop, a store that agrees with `s` off `F`. -/
theorem pop {n : ℕ} (h : EqOff (F ⊔ inBuf s.length) (s.push n) s') : EqOff F s s'.pop := by
  have hlen : s'.length = s.length + 1 := by rw [h.length_eq, length_push]
  refine ⟨by rw [shape_pop, h.1, shape_push]; simp, fun b i hF => ?_⟩
  by_cases hb : b < s.length
  · rw [get_pop_of_lt (by omega), h.2 b i (by simp [inBuf, hF, hb.ne]), get_push_of_lt hb]
  · rw [get_pop_of_ge (by omega)]
    simp [get, List.getElem?_eq_none (not_lt.mp hb)]

/-- A run on `s.push n` that wrote only the scratch buffer leaves `s` after the pop. -/
theorem pop_eq {n : ℕ} (h : EqOff (inBuf s.length) (s.push n) s') : s'.pop = s :=
  ext_get (h.mono (F' := (fun _ _ => False) ⊔ inBuf s.length) fun _ _ hf => Or.inr hf).pop.1
    fun b i => (h.mono (F' := (fun _ _ => False) ⊔ inBuf s.length)
      fun _ _ hf => Or.inr hf).pop.2 b i not_false

end EqOff

end Store

end NLAlib.Ops
