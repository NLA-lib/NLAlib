/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Allocation
public import NLAlib.Computation.Exact
public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.ScalarFrames

/-!
# Frames of certified routines

The effect of a certified routine (`NLAlib.Computation.IsMatvecRoutine`,
`NLAlib.Computation.IsOrthRoutine`) on the store is an *equation*: the final store is the initial
store after a list of block writes (`NLAlib.Computation.Store.writeBlocks`). Counts, peak memory
and tape positions are outside the equation. This file gives the lemmas that
produce and consume that equation, so that a routine proves its effect and a consumer uses it
without re-deriving frames: the extensionality lemma from reads to block writes, the algebra of
block writes (append, overwrite, commutation of disjoint blocks, popping a scratch buffer), the
named input and output predicates, the frame of a precondition, the scoped-scratch and
one-word-per-iteration run lemmas, and the footprint certificate
`NLAlib.Computation.IsBlockRoutine` with its sequencing. Design:
`docs/design/Computation-CertifiedRoutines.md` §3.

## Main definitions

* `NLAlib.Computation.ReadsDecoded`, `NLAlib.Computation.Writable`: a decoded input block and a
  writable output block.
* `NLAlib.Computation.IsFramed`: a precondition that reads only some buffers.
* `NLAlib.Computation.IsBlockRoutine`: a routine that succeeds and writes exactly some blocks.

## Main results

* `NLAlib.Computation.Store.writeBlocks_eq_some_of_read`: reads to block writes.
* `NLAlib.Computation.Store.writeBlock_comm`, `NLAlib.Computation.Store.writeBlock_writeBlock_self`,
  `NLAlib.Computation.Store.writeBlock_pop_of_lt`: the algebra of block writes.
* `NLAlib.Computation.exists_exec_alloc`: a scoped scratch buffer.
* `NLAlib.Computation.exists_exec_loop_writeBlock`: a loop writing one word per iteration.
* `NLAlib.Computation.IsBlockRoutine.bind`: a routine after a routine.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### Block writes -/

section Store

/-- Two blocks `(handle, offset, length)` are disjoint iff they lie in different buffers, one of
them is empty, or one ends before the other starts; the form `omega` closes. An empty block has
no cell, so it is disjoint from every block even when its offset lies inside the other block
(`NLAlib.Computation.blockDisjoint_eq_true_iff`). -/
theorem blockDisjoint_iff {x y : ℕ × ℕ × ℕ} :
    blockDisjoint x y = true ↔ x.1 ≠ y.1 ∨ x.2.2 = 0 ∨ y.2.2 = 0 ∨ x.2.1 + x.2.2 ≤ y.2.1 ∨
      y.2.1 + y.2.2 ≤ x.2.1 := by
  simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, or_assoc]

/-- Two nonempty blocks `(handle, offset, length)` are disjoint iff they lie in different buffers
or one ends before the other starts. -/
theorem blockDisjoint_iff_of_pos {x y : ℕ × ℕ × ℕ} (hx : 0 < x.2.2) (hy : 0 < y.2.2) :
    blockDisjoint x y = true ↔ x.1 ≠ y.1 ∨ x.2.1 + x.2.2 ≤ y.2.1 ∨ y.2.1 + y.2.2 ≤ x.2.1 := by
  rw [blockDisjoint_iff]
  constructor <;> intro h <;> omega

/-- Block writes on a cons are a block write followed by the rest. -/
theorem Store.writeBlocks_cons_eq_some_iff {s s' : Store P K} {p : P} {x : ℕ × ℕ × ℕ}
    {bs : List (ℕ × ℕ × ℕ)} {y : Array K} {ys : List (Array K)} :
    s.writeBlocks p (x :: bs) (y :: ys) = some s' ↔
      y.size = x.2.2 ∧
        ∃ m, s.writeBlock p x.1 x.2.1 y = some m ∧ m.writeBlocks p bs ys = some s' := by
  rw [Store.writeBlocks]
  split_ifs with hy
  · simp [hy, Option.bind_eq_some_iff]
  · simp [hy]

/-- One block write in the list form. -/
theorem Store.writeBlocks_singleton_eq_some_iff {s s' : Store P K} {p : P} {b o n : ℕ}
    {y : Array K} :
    s.writeBlocks p [(b, o, n)] [y] = some s' ↔ y.size = n ∧ s.writeBlock p b o y = some s' := by
  simp [Store.writeBlocks]

/-- Two block writes in the list form: the `mid` form of `NLAlib.Computation.IsOrthRoutine`. -/
theorem Store.writeBlocks_pair_eq_some_iff {s s' : Store P K} {p : P} {b₁ o₁ n₁ b₂ o₂ n₂ : ℕ}
    {y₁ y₂ : Array K} :
    s.writeBlocks p [(b₁, o₁, n₁), (b₂, o₂, n₂)] [y₁, y₂] = some s' ↔ y₁.size = n₁ ∧
      y₂.size = n₂ ∧ ∃ m, s.writeBlock p b₁ o₁ y₁ = some m ∧ m.writeBlock p b₂ o₂ y₂ = some s' := by
  rw [Store.writeBlocks_cons_eq_some_iff]
  simp only [Store.writeBlocks_singleton_eq_some_iff]
  constructor
  · rintro ⟨h₁, m, hm, h₂, hs⟩
    exact ⟨h₁, h₂, m, hm, hs⟩
  · rintro ⟨h₁, h₂, m, hm, hs⟩
    exact ⟨h₁, m, hm, h₂, hs⟩

/-- Writing an empty block changes nothing. -/
theorem Store.writeBlock_eq_some_of_size_eq_zero {s : Store P K} {p : P} {b o : ℕ}
    {y : Array K} (hy : y.size = 0) : s.writeBlock p b o y = some s := by
  simp [Store.writeBlock, hy]

/-- A block write keeps the number of buffers. -/
theorem Store.size_of_writeBlock_eq_some {s s' : Store P K} {p : P} {b o : ℕ} {y : Array K}
    (h : s.writeBlock p b o y = some s') : s'.size = s.size :=
  Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some h)

/-- Reads to block writes. If `s'` has the shape of `s`, reads the array `ys[k]` on the block
`bs[k]` at tag `p` for each `k`, the blocks are pairwise disjoint
(`NLAlib.Computation.blockDisjoint`) and every cell outside them reads as in `s` at every tag,
then `s'` is `s` after the block writes. The converse of
`NLAlib.Computation.Store.read_of_writeBlocks_eq_some` and
`NLAlib.Computation.Store.read_of_writeBlocks_eq_some_of_forall`. -/
theorem Store.writeBlocks_eq_some_of_read {s s' : Store P K} {p : P}
    {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)}
    (hlen : List.Forall₂ (fun (y : Array K) (x : ℕ × ℕ × ℕ) => y.size = x.2.2) ys bs)
    (hpw : bs.Pairwise fun x y => blockDisjoint x y = true) (hsh : s'.shape = s.shape)
    (hin : ∀ (k : ℕ) (x : ℕ × ℕ × ℕ) (y : Array K), bs[k]? = some x → ys[k]? = some y →
      ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]?)
    (hout : ∀ q b i, (∀ x ∈ bs, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) →
      s'.read q b i = s.read q b i) :
    s.writeBlocks p bs ys = some s' := by
  induction hlen generalizing s with
  | nil =>
    rw [Store.writeBlocks]
    exact congrArg some (Store.ext_of_shape_eq hsh.symm fun q b i => (hout q b i (by simp)).symm)
  | @cons y x ys bs hyx hF ih =>
    obtain ⟨hx, hpw⟩ := List.pairwise_cons.mp hpw
    have hin₀ : ∀ j < y.size, s'.read p x.1 (x.2.1 + j) = y[j]? := fun j hj =>
      hin 0 x y (by simp) (by simp) j (hyx ▸ hj)
    have hsh₀ : ∀ j < y.size, ∃ n, s'.shape[x.1]? = some (p, n) ∧ x.2.1 + j < n := fun j hj =>
      Store.exists_getElem?_shape_of_read_eq_some ((hin₀ j hj).trans (Array.getElem?_eq_getElem hj))
    obtain ⟨m, hm⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := s) (p := p)
      (b := x.1) (off := x.2.1) (xs := y) fun j hj => hsh ▸ hsh₀ j hj
    have hshm : m.shape = s'.shape := (Store.shape_of_writeBlock_eq_some hm).trans hsh.symm
    rw [Store.writeBlocks, if_pos hyx, hm, Option.bind_some]
    refine ih hpw hshm.symm (fun k x' y' hx' hy' => hin (k + 1) x' y' hx' hy') fun q b i hb => ?_
    by_cases hbx : b = x.1 ∧ x.2.1 ≤ i ∧ i < x.2.1 + x.2.2
    · obtain ⟨rfl, hi, hi'⟩ := hbx
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
      have hj : j < y.size := by omega
      obtain ⟨n, hn, -⟩ := hsh₀ j hj
      by_cases hq : q = p
      · subst hq
        rw [hin₀ j hj, Store.read_of_writeBlock_eq_some_of_lt hm hj]
      · rw [Store.read_eq_none_of_getElem?_shape_of_ne hn hq,
          Store.read_eq_none_of_getElem?_shape_of_ne (hshm ▸ hn) hq]
    · have hb' : b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i := by omega
      rw [hout q b i fun z hz => (List.mem_cons.mp hz).elim (fun h => h ▸ hb') (hb z),
        Store.read_of_writeBlock_eq_some_of_ne hm (by omega)]

/-- Reads to one block write: a store of the shape of `s` that reads `y` on the block of
buffer `b` from offset `o` at tag `p`, and as `s` outside it at every tag, is `s` after writing
`y` there. -/
theorem Store.writeBlock_eq_some_of_read {s s' : Store P K} {p : P} {b o : ℕ} {y : Array K}
    (hsh : s'.shape = s.shape) (hin : ∀ j < y.size, s'.read p b (o + j) = y[j]?)
    (hout : ∀ q b' i, (b' ≠ b ∨ i < o ∨ o + y.size ≤ i) → s'.read q b' i = s.read q b' i) :
    s.writeBlock p b o y = some s' := by
  refine (Store.writeBlocks_singleton_eq_some_iff.mp (Store.writeBlocks_eq_some_of_read
    (bs := [(b, o, y.size)]) (ys := [y]) (.cons rfl .nil) (List.pairwise_singleton _ _) hsh
    (fun k x z hx hz j hj => ?_) fun q b' i h => hout q b' i (h _ List.mem_cons_self))).2
  rcases k with _ | k
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hz
    subst hx hz
    exact hin j hj
  · simp at hx

/-- Block writes to frame style: after successful pairwise disjoint block writes the store
has the old shape, reads back each array on its block, and reads as before outside the blocks,
at every tag. -/
theorem Store.frame_of_writeBlocks_eq_some {s s' : Store P K} {p : P} {bs : List (ℕ × ℕ × ℕ)}
    {ys : List (Array K)} (h : s.writeBlocks p bs ys = some s')
    (hpw : bs.Pairwise fun x y => blockDisjoint x y = true) :
    s'.shape = s.shape ∧
      (∀ (k : ℕ) (x : ℕ × ℕ × ℕ) (y : Array K), bs[k]? = some x → ys[k]? = some y →
        y.size = x.2.2 ∧ ∀ j < x.2.2, s'.read p x.1 (x.2.1 + j) = y[j]?) ∧
      ∀ q b i, (∀ x ∈ bs, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) →
        s'.read q b i = s.read q b i :=
  ⟨Store.shape_of_writeBlocks_eq_some h, Store.read_of_writeBlocks_eq_some h hpw,
    fun _ _ _ hb => Store.read_of_writeBlocks_eq_some_of_forall h hb⟩

/-- Block writes in sequence are the block writes of the concatenated lists. -/
theorem Store.writeBlocks_append_of_eq_some {s m s' : Store P K} {p : P}
    {bs₁ bs₂ : List (ℕ × ℕ × ℕ)} {ys₁ ys₂ : List (Array K)}
    (h₁ : s.writeBlocks p bs₁ ys₁ = some m) (h₂ : m.writeBlocks p bs₂ ys₂ = some s') :
    s.writeBlocks p (bs₁ ++ bs₂) (ys₁ ++ ys₂) = some s' := by
  induction bs₁ generalizing s ys₁ with
  | nil =>
    cases ys₁ with
    | nil =>
      simp only [Store.writeBlocks, Option.some.injEq] at h₁
      subst h₁
      exact h₂
    | cons => simp [Store.writeBlocks] at h₁
  | cons x bs ih =>
    cases ys₁ with
    | nil => simp [Store.writeBlocks] at h₁
    | cons y ys =>
      obtain ⟨hy, m₁, hm₁, hrest⟩ := Store.writeBlocks_cons_eq_some_iff.mp h₁
      exact Store.writeBlocks_cons_eq_some_iff.mpr ⟨hy, m₁, hm₁, ih hrest⟩

/-- Writing the same block twice is the second write. -/
theorem Store.writeBlock_writeBlock_self {s s₁ s₂ : Store P K} {p : P} {b o : ℕ}
    {x y : Array K} (h₁ : s.writeBlock p b o x = some s₁) (h₂ : s₁.writeBlock p b o y = some s₂)
    (hxy : x.size = y.size) : s.writeBlock p b o y = some s₂ :=
  Store.writeBlock_eq_some_of_read
    ((Store.shape_of_writeBlock_eq_some h₂).trans (Store.shape_of_writeBlock_eq_some h₁))
    (fun _ hj => Store.read_of_writeBlock_eq_some_of_lt h₂ hj) fun _ _ _ hb => by
      rw [Store.read_of_writeBlock_eq_some_of_ne h₂ hb,
        Store.read_of_writeBlock_eq_some_of_ne h₁ (by rw [hxy]; exact hb)]

/-- Block writes into disjoint blocks commute; an empty block commutes with every block. -/
theorem Store.writeBlock_comm {s s₁ s₂ : Store P K} {p : P} {b₁ o₁ b₂ o₂ : ℕ} {x y : Array K}
    (h₁ : s.writeBlock p b₁ o₁ x = some s₁) (h₂ : s₁.writeBlock p b₂ o₂ y = some s₂)
    (hd : 0 < x.size → 0 < y.size → blockDisjoint (b₁, o₁, x.size) (b₂, o₂, y.size) = true) :
    ∃ m, s.writeBlock p b₂ o₂ y = some m ∧ m.writeBlock p b₁ o₁ x = some s₂ := by
  rcases Nat.eq_zero_or_pos x.size with hx | hx
  · rw [Store.writeBlock_eq_some_of_size_eq_zero hx, Option.some.injEq] at h₁
    subst h₁
    exact ⟨s₂, h₂, Store.writeBlock_eq_some_of_size_eq_zero hx⟩
  rcases Nat.eq_zero_or_pos y.size with hy | hy
  · rw [Store.writeBlock_eq_some_of_size_eq_zero hy, Option.some.injEq] at h₂
    subst h₂
    exact ⟨s, Store.writeBlock_eq_some_of_size_eq_zero hy, h₁⟩
  have hd := (blockDisjoint_iff_of_pos (x := (b₁, o₁, x.size)) (y := (b₂, o₂, y.size)) hx hy).mp
    (hd hx hy)
  dsimp only at hd
  clear hx hy
  have key : s.writeBlocks p [(b₂, o₂, y.size), (b₁, o₁, x.size)] [y, x] = some s₂ := by
    refine Store.writeBlocks_eq_some_of_read (.cons rfl (.cons rfl .nil))
      (by simp [blockDisjoint_iff]; omega)
      ((Store.shape_of_writeBlock_eq_some h₂).trans (Store.shape_of_writeBlock_eq_some h₁))
      (fun k z w hz hw j hj => ?_) fun q b i hb => ?_
    · rcases k with _ | _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hz hw
        subst hz hw
        exact Store.read_of_writeBlock_eq_some_of_lt h₂ hj
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hz hw
        subst hz hw
        dsimp only at hj ⊢
        rw [Store.read_of_writeBlock_eq_some_of_ne h₂ (by omega),
          Store.read_of_writeBlock_eq_some_of_lt h₁ hj]
      · simp at hz
    · rw [Store.read_of_writeBlock_eq_some_of_ne h₂ (hb _ List.mem_cons_self),
        Store.read_of_writeBlock_eq_some_of_ne h₁ (hb (b₁, o₁, x.size) (by simp))]
  obtain ⟨-, -, m, hm, hs⟩ := Store.writeBlocks_pair_eq_some_iff.mp key
  exact ⟨m, hm, hs⟩

/-- A block write followed by a write of the next cell is the block write of the extended
array. -/
theorem Store.writeBlock_push_eq_some {s m m' : Store P K} {p : P} {b o : ℕ} {ys : Array K}
    {v : K} (h : s.writeBlock p b o ys = some m) (hw : m.write p b (o + ys.size) v = some m') :
    s.writeBlock p b o (ys.push v) = some m' :=
  Store.writeBlock_eq_some_of_read
    ((Store.shape_of_write_eq_some hw).trans (Store.shape_of_writeBlock_eq_some h))
    (fun j hj => by
      rw [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega)),
          Store.read_of_writeBlock_eq_some_of_lt h hj]
        simp [Array.getElem?_push, Nat.ne_of_lt hj]
      · rw [Store.read_of_write_eq_some hw]
        simp)
    fun q b' i hb => by
      rw [Array.size_push] at hb
      rw [Store.read_of_write_eq_some_of_ne hw (by omega),
        Store.read_of_writeBlock_eq_some_of_ne h (by omega)]

/-- A block write below the top buffer commutes with popping the top buffer. -/
theorem Store.writeBlock_pop_of_lt {s s' : Store P K} {p : P} {b o : ℕ} {y : Array K}
    (h : s.writeBlock p b o y = some s') (hb : 0 < y.size → b + 1 < s.size) :
    Store.writeBlock s.pop p b o y = some s'.pop := by
  have hsz : s'.size = s.size := Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some h)
  refine Store.writeBlock_eq_some_of_read
    (by rw [Store.shape_pop, Store.shape_pop, Store.shape_of_writeBlock_eq_some h])
    (fun j hj => ?_) fun q b' i hb' => ?_
  · rw [Store.read_pop_of_lt (by have := hb (by omega); omega),
      Store.read_of_writeBlock_eq_some_of_lt h hj]
  · by_cases hlt : b' < s.size - 1
    · rw [Store.read_pop_of_lt (by omega), Store.read_pop_of_lt hlt,
        Store.read_of_writeBlock_eq_some_of_ne h hb']
    · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega)]

/-- A block write into the top buffer is undone by popping it. -/
theorem Store.pop_of_writeBlock_top {s s' : Store P K} {p : P} {b o : ℕ} {y : Array K}
    (h : s.writeBlock p b o y = some s') (hb : s.size ≤ b + 1) : s'.pop = s.pop := by
  have hsz : s'.size = s.size := Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some h)
  refine Store.ext_of_shape_eq
    (by rw [Store.shape_pop, Store.shape_pop, Store.shape_of_writeBlock_eq_some h]) fun q b' i => ?_
  by_cases hlt : b' < s.size - 1
  · rw [Store.read_pop_of_lt (by omega), Store.read_pop_of_lt hlt,
      Store.read_of_writeBlock_eq_some_of_ne h (Or.inl (by omega))]
  · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
      Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega)]

/-- A write into the top buffer is undone by popping it. -/
theorem Store.pop_of_write_top {s s' : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') (hb : s.size ≤ b + 1) : s'.pop = s.pop := by
  have hsz : s'.size = s.size := Store.size_of_write_eq_some h
  refine Store.ext_of_shape_eq
    (by rw [Store.shape_pop, Store.shape_pop, Store.shape_of_write_eq_some h]) fun q b' i' => ?_
  by_cases hlt : b' < s.size - 1
  · rw [Store.read_pop_of_lt (by omega), Store.read_pop_of_lt hlt,
      Store.read_of_write_eq_some_of_ne h (Or.inl (by omega))]
  · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
      Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega)]

end Store

/-! ### Inputs, outputs and preconditions -/

section Predicates

/-- Block `b` holds, from offset `off`, words that decode at tag `p` to the vector
$\mathbf{x} \in \mathbb{R}^N$: cell $\mathit{off} + i$ reads a word decoding to $x_i$. -/
def ReadsDecoded {N : ℕ} (s : Store P K) (dec : P → K → ℝ) (p : P) (b off : ℕ)
    (x : Fin N → ℝ) : Prop :=
  ∀ i : Fin N, ∃ w, s.read p b (off + i) = some w ∧ dec p w = x i

/-- The cells $\mathit{off}, \dots, \mathit{off} + n - 1$ of buffer `b` exist at tag `p`. -/
def Writable (s : Store P K) (p : P) (b off n : ℕ) : Prop :=
  ∀ i < n, ∃ len, s.shape[b]? = some (p, len) ∧ off + i < len

/-- A readable packed matrix block has capacity for a write of the same dimensions. The
empty-block case imposes no condition on the buffer handle. -/
theorem Holds.writable {N k : ℕ} {s : Store P K} {p : P} {b off : ℕ}
    {M : Matrix (Fin N) (Fin k) K} (h : Holds s p b off M) :
    Writable s p b off (N * k) := by
  intro i hi
  have hN : 0 < N := by nlinarith
  have hj : i / N < k := (Nat.div_lt_iff_lt_mul hN).mpr
    (by simpa only [Nat.mul_comm] using hi)
  have hr := h ⟨i % N, Nat.mod_lt _ hN⟩ ⟨i / N, hj⟩
  simp only [Nat.add_assoc, Nat.mod_add_div] at hr
  exact Store.exists_getElem?_shape_of_read_eq_some hr

/-- Every block `(handle, offset, length)` of `bs` is writable at tag `p`. -/
def WritableBlocks (s : Store P K) (p : P) (bs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ bs, Writable s p x.1 x.2.1 x.2.2

/-- A precondition that reads only the buffers `ro`: it survives any change of the store that
keeps their shape entries and their cells, at every tag. -/
def IsFramed (pre : Store P K → Prop) (ro : List ℕ) : Prop :=
  ∀ s s' : Store P K, pre s → (∀ b ∈ ro, s'.shape[b]? = s.shape[b]?) →
    (∀ q, ∀ b ∈ ro, ∀ i, s'.read q b i = s.read q b i) → pre s'

variable {N : ℕ} {s s' : Store P K} {dec : P → K → ℝ} {p : P} {b off : ℕ}

/-- A decoded block survives a store that reads the same on it. -/
theorem ReadsDecoded.of_read_eq {x : Fin N → ℝ} (h : ReadsDecoded s dec p b off x)
    (hr : ∀ i < N, s'.read p b (off + i) = s.read p b (off + i)) :
    ReadsDecoded s' dec p b off x := fun i => by
  rw [hr i i.2]
  exact h i

/-- A decoded block survives pushing a buffer. -/
theorem ReadsDecoded.push {x : Fin N → ℝ} (h : ReadsDecoded s dec p b off x)
    (y : P × Array (Option K)) : ReadsDecoded (s.push y) dec p b off x := fun i => by
  obtain ⟨w, hw, hd⟩ := h i
  refine ⟨w, ?_, hd⟩
  rw [Store.read_push_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw))]
  exact hw

/-- A decoded block survives a block write into a disjoint block. -/
theorem ReadsDecoded.of_writeBlock {x : Fin N → ℝ} (h : ReadsDecoded s dec p b off x)
    {p' : P} {b' o' : ℕ} {y : Array K} (hw : s.writeBlock p' b' o' y = some s')
    (hd : 0 < N → 0 < y.size → blockDisjoint (b, off, N) (b', o', y.size) = true) :
    ReadsDecoded s' dec p b off x := by
  refine h.of_read_eq fun i hi => Store.read_of_writeBlock_eq_some_of_ne hw ?_
  rcases Nat.eq_zero_or_pos y.size with hy | hy
  · omega
  · have hN : 0 < N := by omega
    have hd := (blockDisjoint_iff_of_pos (x := (b, off, N)) (y := (b', o', y.size)) hN hy).mp
      (hd hN hy)
    dsimp only at hd
    omega

/-- A decoded matrix survives pushing a buffer. -/
theorem HoldsDecoded.push {k : ℕ} {M : Matrix (Fin N) (Fin k) ℝ}
    (h : HoldsDecoded s dec p b off M) (y : P × Array (Option K)) :
    HoldsDecoded (s.push y) dec p b off M := fun i j => by
  obtain ⟨w, hw, hd⟩ := h i j
  refine ⟨w, ?_, hd⟩
  rw [Store.read_push_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw))]
  exact hw

/-- A decoded matrix survives a block write into a disjoint block. -/
theorem HoldsDecoded.of_writeBlock {k : ℕ} {M : Matrix (Fin N) (Fin k) ℝ}
    (h : HoldsDecoded s dec p b off M) {p' : P} {b' o' : ℕ} {y : Array K}
    (hw : s.writeBlock p' b' o' y = some s')
    (hd : 0 < N * k → 0 < y.size → blockDisjoint (b, off, N * k) (b', o', y.size) = true) :
    HoldsDecoded s' dec p b off M := fun i j => by
  have hlt : (i : ℕ) + N * j < N * k := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
  rw [Store.read_of_writeBlock_eq_some_of_ne hw ?_]
  · exact h i j
  rcases Nat.eq_zero_or_pos y.size with hy | hy
  · omega
  · have hNk : 0 < N * k := by omega
    have hd := (blockDisjoint_iff_of_pos (x := (b, off, N * k)) (y := (b', o', y.size)) hNk hy).mp
      (hd hNk hy)
    dsimp only at hd
    omega

/-- A matrix block is its columns: buffer `b` holds $\mathbf{M}$ ($N \times k$,
column-major from `off`) iff column $j$ is decoded from offset $\mathit{off} + Nj$. -/
theorem holdsDecoded_iff_forall_readsDecoded {k : ℕ} {M : Matrix (Fin N) (Fin k) ℝ} :
    HoldsDecoded s dec p b off M ↔
      ∀ j : Fin k, ReadsDecoded s dec p b (off + N * j) fun i => M i j := by
  constructor
  · intro h j i
    obtain ⟨w, hw, hd⟩ := h i j
    exact ⟨w, by rwa [Nat.add_right_comm], hd⟩
  · intro h i j
    obtain ⟨w, hw, hd⟩ := h j i
    exact ⟨w, by rwa [Nat.add_right_comm], hd⟩

omit [DecidableEq P] in
/-- A writable block stays writable in a store with the same shape entry for its buffer. -/
theorem Writable.of_getElem?_shape_eq {n : ℕ} (h : Writable s p b off n)
    (hsh : s'.shape[b]? = s.shape[b]?) : Writable s' p b off n := fun i hi => by
  rw [hsh]
  exact h i hi

omit [DecidableEq P] in
/-- A writable block stays writable in a store of the same shape. -/
theorem Writable.of_shape_eq {n : ℕ} (h : Writable s p b off n) (hsh : s'.shape = s.shape) :
    Writable s' p b off n :=
  h.of_getElem?_shape_eq (by rw [hsh])

omit [DecidableEq P] in
/-- A writable block stays writable after pushing a buffer. -/
theorem Writable.push {n : ℕ} (h : Writable s p b off n) (y : P × Array (Option K)) :
    Writable (s.push y) p b off n := fun i hi => by
  obtain ⟨len, hl, hlt⟩ := h i hi
  have hb : b < s.size := by
    simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hl).1
  exact ⟨len, by rw [Store.getElem?_shape_push_of_lt _ hb]; exact hl, hlt⟩

omit [DecidableEq P] in
/-- A writable nonempty block is in a buffer of the store. -/
theorem Writable.lt_size {n : ℕ} (h : Writable s p b off n) (hn : 0 < n) : b < s.size := by
  obtain ⟨len, hl, -⟩ := h 0 hn
  simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hl).1

/-- A block write into a writable block succeeds. -/
theorem Writable.exists_writeBlock {y : Array K} (h : Writable s p b off y.size) :
    ∃ s', s.writeBlock p b off y = some s' :=
  Store.exists_writeBlock_eq_some_of_getElem?_shape h

omit [DecidableEq P] in
/-- Writable from a known shape: a block inside a buffer of tag `p` and length `len` of the
shape `ws` of the store is writable. -/
theorem writable_of_shape_eq {ws : Array (P × ℕ)} {len n : ℕ} (hs : s.shape = ws)
    (hb : ws[b]? = some (p, len)) (hn : off + n ≤ len) : Writable s p b off n :=
  fun _ hi => ⟨len, hs ▸ hb, by omega⟩

/-- The precondition `True` reads no buffer. -/
theorem isFramed_true (ro : List ℕ) : IsFramed (fun _ : Store P K => True) ro :=
  fun _ _ _ _ _ => trivial

/-- A conjunction of framed preconditions reads the union of their buffers. -/
theorem IsFramed.and {pre₁ pre₂ : Store P K → Prop} {ro₁ ro₂ : List ℕ}
    (h₁ : IsFramed pre₁ ro₁) (h₂ : IsFramed pre₂ ro₂) :
    IsFramed (fun s => pre₁ s ∧ pre₂ s) (ro₁ ++ ro₂) := fun s s' hp hsh hr =>
  ⟨h₁ s s' hp.1 (fun b hb => hsh b (List.mem_append_left _ hb))
      (fun q b hb => hr q b (List.mem_append_left _ hb)),
    h₂ s s' hp.2 (fun b hb => hsh b (List.mem_append_right _ hb))
      (fun q b hb => hr q b (List.mem_append_right _ hb))⟩

/-- A stored matrix reads only its buffer. -/
theorem isFramed_holdsDecoded {k : ℕ} (M : Matrix (Fin N) (Fin k) ℝ) :
    IsFramed (fun s => HoldsDecoded s dec p b off M) [b] := by
  intro s s' h _ hr i j
  rw [hr p b List.mem_cons_self]
  exact h i j

/-- A stored vector reads only its buffer. -/
theorem isFramed_readsDecoded (x : Fin N → ℝ) :
    IsFramed (fun s => ReadsDecoded s dec p b off x) [b] := by
  intro s s' h _ hr i
  rw [hr p b List.mem_cons_self]
  exact h i

/-- A framed precondition survives block writes outside the buffers it reads. -/
theorem IsFramed.of_writeBlocks {pre : Store P K → Prop} {ro : List ℕ} (h : IsFramed pre ro)
    {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)} (hs : pre s)
    (hw : s.writeBlocks p bs ys = some s') (hro : ∀ x ∈ bs, x.1 ∉ ro) : pre s' :=
  h s s' hs (fun _ _ => by rw [Store.shape_of_writeBlocks_eq_some hw]) fun _ _ hb _ =>
    Store.read_of_writeBlocks_eq_some_of_forall hw fun x hx => Or.inl fun e => hro x hx (e ▸ hb)

/-- A framed precondition survives pushing a scratch buffer. -/
theorem IsFramed.push {pre : Store P K → Prop} {ro : List ℕ} (h : IsFramed pre ro)
    (hs : pre s) (hro : ∀ b ∈ ro, b < s.size) (y : P × Array (Option K)) : pre (s.push y) :=
  h s _ hs (fun b hb => Store.getElem?_shape_push_of_lt _ (hro b hb)) fun _ b hb _ =>
    Store.read_push_of_ne (Nat.ne_of_lt (hro b hb))

/-- A framed precondition survives popping a scratch buffer above the buffers it reads. -/
theorem IsFramed.pop {pre : Store P K → Prop} {ro : List ℕ} (h : IsFramed pre ro)
    (hs : pre s) (hro : ∀ b ∈ ro, b + 1 < s.size) : pre s.pop :=
  h s _ hs (fun b hb => by
      have := hro b hb
      rw [Store.shape_pop, Array.getElem?_pop, if_pos (by rw [Store.size_shape]; omega)])
    fun _ b hb _ => Store.read_pop_of_lt (by have := hro b hb; omega)

end Predicates

/-! ### Runs -/

section Runs

variable [AddMonoid C]

/-- Scoped scratch: an allocation whose body succeeds from the store with the fresh buffer
pushed, in a state whose popped store satisfies `Q`, succeeds in a state satisfying `Q`. With
`NLAlib.Computation.Store.writeBlock_pop_of_lt` and
`NLAlib.Computation.Store.pop_of_writeBlock_top` the body proves `Q` as block writes of the
store before the allocation. -/
theorem exists_exec_alloc (I : Interp P ι K C) (p : P) (len : IExp ℕ)
    (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) (Q : Store P K → Prop)
    (h : ∀ σ : St P K C, σ.store = st.store.push (p, Array.replicate len.eval none) →
      ∃ out, exec I (body st.store.size) σ = some out ∧ Q out.store.pop) :
    ∃ out, exec I (.alloc p len body) st = some out ∧ Q out.store := by
  obtain ⟨out, h₁, h₂⟩ := h (st.allocate p len.eval (I.width p)) rfl
  exact ⟨_, exec_alloc_of_exec_eq_some I p len body st out h₁, h₂⟩

/-- One word per iteration: a loop whose $k$-th body, from any state that is the start after
a block write of $k$ words satisfying `Q` into buffer `b` from offset `o`, writes one word
satisfying `Q k` into cell $o + k$ and nothing else in the store, succeeds, and its net effect on
the store is one block write of $n$ words satisfying `Q`. -/
theorem exists_exec_loop_writeBlock (I : Interp P ι K C) {n : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} (p : P) (b o : ℕ) (Q : ℕ → K → Prop)
    (hstep : ∀ k < n.eval, ∀ (ys : Array K) (s : St P K C), ys.size = k →
      (∀ i (hi : i < ys.size), Q i ys[i]) → st.store.writeBlock p b o ys = some s.store →
      ∃ s' v, exec I (body k) s = some s' ∧ s.store.write p b (o + k) v = some s'.store ∧
        Q k v) :
    ∃ (s' : St P K C) (W : Fin n.eval → K), exec I (.loop n body) st = some s' ∧
      st.store.writeBlock p b o (Array.ofFn W) = some s'.store ∧ ∀ k : Fin n.eval, Q k (W k) := by
  obtain ⟨s', hrun, ys, hsz, hw, hQ⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k s => ∃ ys : Array K, ys.size = k ∧ st.store.writeBlock p b o ys = some s.store ∧
      ∀ i (hi : i < ys.size), Q i ys[i])
    ⟨#[], rfl, Store.writeBlock_eq_some_of_size_eq_zero rfl, fun i hi => absurd hi (by simp)⟩
    fun k hk s ⟨ys, hsz, hw, hQ⟩ => by
      obtain ⟨s', v, hr, hv, hq⟩ := hstep k hk ys s hsz hQ hw
      refine ⟨s', hr, ys.push v, by simp [hsz],
        Store.writeBlock_push_eq_some hw (by rw [hsz]; exact hv), fun i hi => ?_⟩
      rw [Array.size_push] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Array.getElem_push_lt hi]
        exact hQ i hi
      · rw [Array.getElem_push_eq, hsz]
        exact hq
  refine ⟨s', fun k => ys[k.1]'(by rw [hsz]; exact k.2), hrun, ?_, fun k => hQ k _⟩
  convert hw using 2
  exact Array.ext (by simp [hsz]) fun i _ _ => by simp

/-- A routine with a footprint: from every state satisfying `pre` whose blocks `outs`
(`(handle, offset, length)`) are writable at `tag`, `routine` succeeds and its final store is the
initial store after one block write per block of `outs`. This is the net effect on the store
only: the routine may write temporary cells (restored or overwritten before it returns) and
allocate scoped scratch, and the certificate constrains neither its counts, its peak memory nor
its tape positions. No guarantee on the words written; a typed certificate
(`NLAlib.Computation.IsMatvecRoutine`, `NLAlib.Computation.IsOrthRoutine`) projects to it. -/
structure IsBlockRoutine (I : Interp P ι K C) (tag : P) (pre : Store P K → Prop)
    (outs : List (ℕ × ℕ × ℕ)) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The routine composes with the following program. -/
  composable : ExecutionComposable I routine
  /-- Writable outputs imply execution and its effect. -/
  run : ∀ st : St P K C, pre st.store → WritableBlocks st.store tag outs →
    ∃ (out : St P K C) (ys : List (Array K)), exec I routine.run st = some out ∧
      st.store.writeBlocks tag outs ys = some out.store

/-- A routine after a routine: if the second routine's precondition is framed by buffers
the first does not write and follows from the first's, the sequence writes the blocks of the
first, then those of the second. -/
theorem IsBlockRoutine.bind {I : Interp P ι K C} {tag : P} {pre₁ pre₂ : Store P K → Prop}
    {bs₁ bs₂ : List (ℕ × ℕ × ℕ)} {r₁ r₂ : Builder P ι ℕ ℕ Unit} {ro₂ : List ℕ}
    (h₁ : IsBlockRoutine I tag pre₁ bs₁ r₁) (h₂ : IsBlockRoutine I tag pre₂ bs₂ r₂)
    (hf : IsFramed pre₂ ro₂) (hro : ∀ x ∈ bs₁, x.1 ∉ ro₂) (hpre : ∀ s, pre₁ s → pre₂ s) :
    IsBlockRoutine I tag pre₁ (bs₁ ++ bs₂) (r₁ >>= fun _ => r₂) where
  composable := h₁.composable.bind h₂.composable
  run st hp hw := by
    obtain ⟨o₁, ys₁, hr₁, hw₁⟩ := h₁.run st hp fun x hx => hw x (List.mem_append_left _ hx)
    obtain ⟨o₂, ys₂, hr₂, hw₂⟩ := h₂.run o₁ (hf.of_writeBlocks (hpre _ hp) hw₁ hro) fun x hx =>
      (hw x (List.mem_append_right _ hx)).of_shape_eq (Store.shape_of_writeBlocks_eq_some hw₁)
    refine ⟨o₂, ys₁ ++ ys₂, ?_, Store.writeBlocks_append_of_eq_some hw₁ hw₂⟩
    rw [h₁.composable, hr₁, Option.bind_some]
    exact hr₂

end Runs

end NLAlib.Computation
