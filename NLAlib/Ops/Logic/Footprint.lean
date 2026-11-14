/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Logic.Attr
public import NLAlib.Ops.Logic.Index
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.ClearExcept
public import Mathlib.Tactic.Common

/-!
# Footprints, disjointness and kept facts

A footprint `NLAlib.Ops.Fp` is a set of cells `(buffer, index)`: the cells a run may write. It is
a predicate, ordered by inclusion (`F ≤ G`) and joined by `⊔`, built from
`NLAlib.Ops.Store.inBlock`, `NLAlib.Ops.Store.inBuf`, the output blocks of a call
(`NLAlib.Ops.Fp.blocks`) and matrix layouts (`NLAlib.Ops.MatLayout.fp`).

A fact about a store is **kept** by a run that does not write what it reads
(`NLAlib.Ops.Store.EqOff.keep`): a predicate reads only the cells `G`
(`NLAlib.Ops.Store.ReadsOnly`), and `G` is disjoint from the footprint of the run
(`NLAlib.Ops.Fp.Disj`). This is the frame rule with a bundle of facts.

## Main results

* `NLAlib.Ops.Fp.blocks`, `NLAlib.Ops.Fp.Apart`, `NLAlib.Ops.Fp.Disj`: footprints of calls.
* `NLAlib.Ops.Store.EqOff.keep`: kept facts.
* `NLAlib.Ops.Store.EqOff.trans'`: frames compose by `⊔`.
* `NLAlib.Ops.Store.EqOff.updBlock_of_le`: the step of the `frame` tactic.
* `NLAlib.Ops.Mem.eq_updBlocks_of_eqOff`: a frame on the output blocks and the blocks read back
  give the equation of a contract in operand form (any number of outputs).
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

/-- **A footprint**: the cells `(buffer, index)` that a run may write. -/
abbrev Fp := ℕ → ℕ → Prop

namespace Fp

/-- The blocks of the lengths `ls` at the operands `zs`: the cells written by a call. -/
def blocks : List (ℕ × ℕ) → List ℕ → Fp
  | z :: zs, l :: ls => Store.inBlock z.1 z.2 l ⊔ blocks zs ls
  | _, _ => ⊥

/-- The buffers from the handle `L` on: the scratch buffers of an allocation chain. -/
def above (L : ℕ) : Fp := fun b _ => L ≤ b

/-- The cells of a list, one each. -/
def cells (zs : List (ℕ × ℕ)) : Fp := fun b i => (b, i) ∈ zs

/-- Two footprints are disjoint. -/
def Disj (F G : Fp) : Prop := ∀ b i, F b i → G b i → False

/-- The blocks of the lengths `ls` at the operands `zs` are pairwise disjoint (so that each can
be read back after a call). -/
def Apart : List (ℕ × ℕ) → List ℕ → Prop
  | z :: zs, l :: ls => Disj (Store.inBlock z.1 z.2 l) (blocks zs ls) ∧ Apart zs ls
  | _, _ => True

@[simp, fpNF] theorem blocks_nil : blocks [] [] = ⊥ := rfl

@[simp, fpNF] theorem blocks_cons (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (l : ℕ) (ls : List ℕ) :
    blocks (z :: zs) (l :: ls) = Store.inBlock z.1 z.2 l ⊔ blocks zs ls := rfl

@[fpNF] theorem inBlock_apply (b o n b' i : ℕ) :
    Store.inBlock b o n b' i ↔ b' = b ∧ o ≤ i ∧ i < o + n := Iff.rfl

@[fpNF] theorem inBuf_apply (b b' i : ℕ) : Store.inBuf b b' i ↔ b' = b := Iff.rfl

@[fpNF] theorem sup_apply (F G : Fp) (b i : ℕ) : (F ⊔ G) b i ↔ F b i ∨ G b i := Iff.rfl

@[fpNF] theorem bot_apply (b i : ℕ) : (⊥ : Fp) b i ↔ False := Iff.rfl

@[fpNF] theorem above_apply (L b i : ℕ) : above L b i ↔ L ≤ b := Iff.rfl

@[fpNF] theorem cells_apply (zs : List (ℕ × ℕ)) (b i : ℕ) : cells zs b i ↔ (b, i) ∈ zs := Iff.rfl

@[fpNF] theorem le_iff (F G : Fp) : F ≤ G ↔ ∀ b i, F b i → G b i := Iff.rfl

@[fpNF] theorem disj_iff (F G : Fp) : Disj F G ↔ ∀ b i, F b i → G b i → False := Iff.rfl

theorem Disj.symm {F G : Fp} (h : Disj F G) : Disj G F := fun b i hg hf => h b i hf hg

theorem Disj.mono {F G F' G' : Fp} (h : Disj F G) (hF : F' ≤ F) (hG : G' ≤ G) : Disj F' G' :=
  fun b i hf hg => h b i (hF b i hf) (hG b i hg)

/-- Any valid indexed block belongs to the footprint of its complete operand list. The
bounded index lies in both the operand and length lists; defaults are never selected. -/
theorem inBlock_getD_le_blocks (zs : List (ℕ × ℕ)) (ls : List ℕ) {i : ℕ}
    (hi : i < min zs.length ls.length) :
    Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0) ≤ blocks zs ls := by
  induction zs generalizing ls i with
  | nil => simp at hi
  | cons z zs ih =>
    cases ls with
    | nil => simp at hi
    | cons l ls =>
      cases i with
      | zero => simpa only [List.getD_cons_zero, blocks] using
          (le_sup_left : Store.inBlock z.1 z.2 l ≤ Store.inBlock z.1 z.2 l ⊔ blocks zs ls)
      | succ i =>
        have hi' : i < min zs.length ls.length := by simpa using hi
        simpa only [List.getD_cons_succ, blocks] using
          (ih ls hi').trans (le_sup_right : blocks zs ls ≤ Store.inBlock z.1 z.2 l ⊔ blocks zs ls)

/-- Earlier and later indexed operands in an apart list have disjoint footprints. This lets
block proofs project their local spatial facts from one declared collection of live blocks. -/
theorem Apart.disj_getD_of_lt {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : Apart zs ls)
    {i j : ℕ} (hij : i < j) (hj : j < min zs.length ls.length) :
    Disj (Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0))
      (Store.inBlock (zs.getD j (0, 0)).1 (zs.getD j (0, 0)).2 (ls.getD j 0)) := by
  induction zs generalizing ls i j with
  | nil => simp at hj
  | cons z zs ih =>
    cases ls with
    | nil => simp at hj
    | cons l ls =>
      cases j with
      | zero => omega
      | succ j =>
        have hj' : j < min zs.length ls.length := by simpa using hj
        cases i with
        | zero =>
          simpa only [List.getD_cons_zero, List.getD_cons_succ] using
            h.1.mono le_rfl (inBlock_getD_le_blocks zs ls hj')
        | succ i =>
          simpa only [List.getD_cons_succ] using ih h.2 (Nat.lt_of_succ_lt_succ hij) hj'

/-- Any two distinct valid operands in an apart list have disjoint spatial footprints.
Shared buffer handles are allowed when their word intervals are disjoint. -/
theorem Apart.disj_getD {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : Apart zs ls)
    {i j : ℕ} (hi : i < min zs.length ls.length) (hj : j < min zs.length ls.length)
    (hne : i ≠ j) :
    Disj (Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0))
      (Store.inBlock (zs.getD j (0, 0)).1 (zs.getD j (0, 0)).2 (ls.getD j 0)) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact h.disj_getD_of_lt hlt hj
  · exact (h.disj_getD_of_lt hgt hi).symm

/-- Disjointness from every indexed member gives disjointness from the whole block
collection. Operand and length lists may have different lengths; only actual pairs matter. -/
theorem disj_blocks_of_forall_getD (F : Fp) (zs : List (ℕ × ℕ)) (ls : List ℕ)
    (h : ∀ i < min zs.length ls.length,
      Disj F (Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0))) :
    Disj F (blocks zs ls) := by
  induction zs generalizing ls with
  | nil => simp only [blocks]; exact fun _ _ _ => False.elim
  | cons z zs ih =>
    cases ls with
    | nil => simp only [blocks]; exact fun _ _ _ => False.elim
    | cons l ls =>
      have hh : Disj F (Store.inBlock z.1 z.2 l) := by
        simpa only [List.getD_cons_zero] using h 0 (by simp)
      have ht : Disj F (blocks zs ls) := ih ls fun i hi => by
        simpa only [List.getD_cons_succ] using h (i + 1) (by simpa using hi)
      exact fun b q hf hb => hb.elim (hh b q hf) (ht b q hf)

/-- Two selections from an apart operand collection are spatially disjoint whenever their
source indices are distinct across the selections. Each selection can reorder or repeat its
own members; the bound premises ensure that no list default becomes an operand. -/
theorem Apart.disj_select {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : Apart zs ls)
    (left right : List ℕ)
    (hleft : ∀ i ∈ left, i < min zs.length ls.length)
    (hright : ∀ j ∈ right, j < min zs.length ls.length)
    (hcross : List.Disjoint left right) :
    Disj (blocks (left.map fun i => zs.getD i (0, 0)) (left.map fun i => ls.getD i 0))
      (blocks (right.map fun i => zs.getD i (0, 0)) (right.map fun i => ls.getD i 0)) := by
  apply disj_blocks_of_forall_getD
  intro j hj
  apply Disj.symm
  apply disj_blocks_of_forall_getD
  intro i hi
  have hi' : i < left.length := by simpa using hi
  have hj' : j < right.length := by simpa using hj
  have hli := List.getElem_mem hi'
  have hrj := List.getElem_mem hj'
  have hd := h.disj_getD (hleft _ hli) (hright _ hrj) (List.disjoint_iff_ne.mp hcross _ hli _ hrj)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
    Option.map_some, Option.getD_some] using hd.symm

/-- A standard apart-block collection can be constructed from its indexed pairwise spatial
facts. Combined with indexed projection, this supports reshaping buffer collections and
refining arena blocks into scalar or matrix subviews without bespoke list inductions. -/
theorem Apart.of_disj_getD {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : ∀ i < min zs.length ls.length, ∀ j < min zs.length ls.length, i ≠ j →
      Disj (Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0))
        (Store.inBlock (zs.getD j (0, 0)).1 (zs.getD j (0, 0)).2 (ls.getD j 0))) :
    Apart zs ls := by
  induction zs generalizing ls with
  | nil => trivial
  | cons z zs ih =>
    cases ls with
    | nil => trivial
    | cons l ls =>
      constructor
      · apply disj_blocks_of_forall_getD
        intro i hi
        simpa only [List.getD_cons_zero, List.getD_cons_succ] using
          h 0 (by simp) (i + 1) (by simpa using hi) (by omega)
      · exact ih fun i hi j hj hne => by
          simpa only [List.getD_cons_succ] using
            h (i + 1) (by simpa using hi) (j + 1) (by simpa using hj) (by omega)

/-- Cells in disjoint footprints differ in buffer or offset. This is the preservation
condition for a scalar read across a write, including disjoint regions of one buffer. -/
theorem Disj.ne_cells {F G : Fp} (h : Disj F G) {b i b' j : ℕ}
    (hf : F b i) (hg : G b' j) : b ≠ b' ∨ i ≠ j := by
  by_cases hb : b = b'
  · right
    intro hij
    subst b'
    subst j
    exact h b i hf hg
  · exact Or.inl hb

@[simp] theorem disj_sup_left {F G H : Fp} : Disj (F ⊔ G) H ↔ Disj F H ∧ Disj G H :=
  ⟨fun h => ⟨fun b i hf hh => h b i (Or.inl hf) hh, fun b i hg hh => h b i (Or.inr hg) hh⟩,
    fun h b i hfg hh => hfg.elim (fun hf => h.1 b i hf hh) fun hg => h.2 b i hg hh⟩

@[simp] theorem disj_sup_right {F G H : Fp} : Disj F (G ⊔ H) ↔ Disj F G ∧ Disj F H :=
  ⟨fun h => ⟨fun b i hf hg => h b i hf (Or.inl hg), fun b i hf hh => h b i hf (Or.inr hh)⟩,
    fun h b i hf hgh => hgh.elim (fun hg => h.1 b i hf hg) fun hh => h.2 b i hf hh⟩

@[simp] theorem disj_bot_left (F : Fp) : Disj ⊥ F := fun _ _ h _ => h

@[simp] theorem disj_bot_right (F : Fp) : Disj F ⊥ := fun _ _ _ h => h

/-- Blocks of different buffers are disjoint. -/
theorem disj_inBlock_of_ne {b b' o o' n n' : ℕ} (h : b ≠ b') :
    Disj (Store.inBlock b o n) (Store.inBlock b' o' n') :=
  fun _ _ h₁ h₂ => h (h₁.1.symm.trans h₂.1)

/-- Blocks of one buffer, one before the other, are disjoint. -/
theorem disj_inBlock_of_le {b o o' n n' : ℕ} (h : o + n ≤ o') :
    Disj (Store.inBlock b o n) (Store.inBlock b o' n') := fun _ _ h₁ h₂ => by
  obtain ⟨-, -, h₁⟩ := h₁
  obtain ⟨-, h₂, -⟩ := h₂
  omega

/-- A block inside a block. -/
theorem inBlock_le_inBlock {b o o' n n' : ℕ} (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') :
    Store.inBlock b o n ≤ Store.inBlock b o' n' :=
  fun _ _ h => ⟨h.1, by have := h.2.1; omega, by have := h.2.2; omega⟩

/-- Writes inside the tail of separated scratch blocks preserve a prefix of the head block
and any input region protected from the complete scratch collection. -/
theorem Apart.disj_tail_head {z : ℕ × ℕ} {zs : List (ℕ × ℕ)} {n m : ℕ}
    {ls : List ℕ} {H : Fp} (h : Apart (z :: zs) (n :: ls))
    (hp : Disj (blocks (z :: zs) (n :: ls)) H) (hm : m ≤ n)
    {G : Fp} (hG : G ≤ blocks zs ls) : Disj G (Store.inBlock z.1 z.2 m ⊔ H) :=
  disj_sup_right.mpr ⟨h.1.symm.mono hG (inBlock_le_inBlock le_rfl (by omega)),
    hp.mono (hG.trans le_sup_right) le_rfl⟩

/-- A block inside its buffer. -/
theorem inBlock_le_inBuf (b o n : ℕ) : Store.inBlock b o n ≤ Store.inBuf b := fun _ _ h => h.1

/-- Joining equally sized operand and length lists joins their block footprints. -/
theorem blocks_append {zs ws : List (ℕ × ℕ)} {ls ks : List ℕ}
    (hlen : zs.length = ls.length) :
    blocks (zs ++ ws) (ls ++ ks) = blocks zs ls ⊔ blocks ws ks := by
  induction zs generalizing ls with
  | nil =>
    cases ls with
    | nil => simp only [List.nil_append, blocks, bot_sup_eq]
    | cons l ls => simp at hlen
  | cons z zs ih =>
    cases ls with
    | nil => simp at hlen
    | cons l ls =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, blocks, ih hlen, sup_assoc]

/-- Operand collections can be composed without rebuilding their pairwise separation proof.
In particular, a caller's apart inputs and outputs can be joined with fresh scratch blocks. -/
theorem Apart.append {zs ws : List (ℕ × ℕ)} {ls ks : List ℕ}
    (h : Apart zs ls) (h' : Apart ws ks) (hlen : zs.length = ls.length)
    (hcross : Disj (blocks zs ls) (blocks ws ks)) :
    Apart (zs ++ ws) (ls ++ ks) := by
  induction zs generalizing ls with
  | nil =>
    cases ls with
    | nil => exact h'
    | cons l ls => simp at hlen
  | cons z zs ih =>
    cases ls with
    | nil => simp at hlen
    | cons l ls =>
      have ht : zs.length = ls.length := by simpa using hlen
      have hc := disj_sup_left.mp hcross
      change Disj (Store.inBlock z.1 z.2 l)
          (blocks (zs ++ ws) (ls ++ ks)) ∧ Apart (zs ++ ws) (ls ++ ks)
      rw [blocks_append ht]
      exact ⟨disj_sup_right.mpr ⟨h.1, hc.1⟩, ih h.2 ht hc.2⟩

/-- An apart concatenation separates each operand collection internally and from the other
collection. The first operand and length lists have matching lengths. -/
theorem Apart.append_iff {zs ws : List (ℕ × ℕ)} {ls ks : List ℕ}
    (hlen : zs.length = ls.length) :
    Apart (zs ++ ws) (ls ++ ks) ↔
      Apart zs ls ∧ Apart ws ks ∧ Disj (blocks zs ls) (blocks ws ks) := by
  constructor
  · intro h
    induction zs generalizing ls with
    | nil =>
      cases ls with
      | nil => exact ⟨trivial, h, disj_bot_left _⟩
      | cons l ls => simp at hlen
    | cons z zs ih =>
      cases ls with
      | nil => simp at hlen
      | cons l ls =>
        have ht : zs.length = ls.length := by simpa using hlen
        have hc := h.1
        change Disj (Store.inBlock z.1 z.2 l) (blocks (zs ++ ws) (ls ++ ks)) at hc
        rw [blocks_append ht] at hc
        obtain ⟨ha, hb, hd⟩ := ih ht h.2
        exact ⟨⟨(disj_sup_right.mp hc).1, ha⟩, hb,
          disj_sup_left.mpr ⟨(disj_sup_right.mp hc).2, hd⟩⟩
  · rintro ⟨h, h', hd⟩
    exact h.append h' hlen hd

/-- Split a separated operand tuple into its prefix and suffix. The cross-separation fact
is provided together with both internal apartness facts for immediate composition. -/
theorem Apart.take_drop {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : Apart zs ls)
    (hlen : zs.length = ls.length) (n : ℕ) :
    Apart (zs.take n) (ls.take n) ∧ Apart (zs.drop n) (ls.drop n) ∧
      Disj (blocks (zs.take n) (ls.take n)) (blocks (zs.drop n) (ls.drop n)) := by
  apply (Apart.append_iff (by simp only [List.length_take, hlen])).mp
  simpa only [List.take_append_drop] using h

/-- Refine an apart collection into subviews. Each view stays inside its parent block, and
views of the same parent have disjoint relative intervals. Views of different parents inherit
disjointness automatically. The resulting operand collection permits arbitrary reordering
and several scalar or matrix views of one arena. -/
theorem Apart.subviews {zs : List (ℕ × ℕ)} {ls : List ℕ} (h : Apart zs ls) {k : ℕ}
    (parent : Fin k → Fin (min zs.length ls.length)) (offset len : Fin k → ℕ)
    (hsub : ∀ a, offset a + len a ≤ ls.getD (parent a) 0)
    (hsep : ∀ a b, a ≠ b → parent a = parent b →
      offset a + len a ≤ offset b ∨ offset b + len b ≤ offset a) :
    Apart (List.ofFn fun a =>
      ((zs.getD (parent a) (0, 0)).1, (zs.getD (parent a) (0, 0)).2 + offset a))
      (List.ofFn len) := by
  apply Apart.of_disj_getD
  intro i hi j hj hne
  have hi' : i < k := by simpa using hi
  have hj' : j < k := by simpa using hj
  let a : Fin k := ⟨i, hi'⟩
  let b : Fin k := ⟨j, hj'⟩
  have hab : a ≠ b := fun he => hne (congrArg Fin.val he)
  have hview (c : Fin k) :
      Store.inBlock (zs.getD (parent c) (0, 0)).1
        ((zs.getD (parent c) (0, 0)).2 + offset c) (len c) ≤
      Store.inBlock (zs.getD (parent c) (0, 0)).1
        (zs.getD (parent c) (0, 0)).2 (ls.getD (parent c) 0) := by
    apply inBlock_le_inBlock
    · omega
    · have := hsub c; omega
  have hd : Disj
      (Store.inBlock (zs.getD (parent a) (0, 0)).1
        ((zs.getD (parent a) (0, 0)).2 + offset a) (len a))
      (Store.inBlock (zs.getD (parent b) (0, 0)).1
        ((zs.getD (parent b) (0, 0)).2 + offset b) (len b)) := by
    by_cases hp : parent a = parent b
    · rcases hsep a b hab hp with hl | hr
      · rw [hp]
        exact disj_inBlock_of_le (by omega)
      · rw [hp]
        exact (disj_inBlock_of_le (by omega)).symm
    · exact (h.disj_getD (parent a).isLt (parent b).isLt
        (fun he => hp (Fin.ext he))).mono (hview a) (hview b)
  simpa [List.getD_eq_getElem?_getD, hi', hj', a, b] using hd

/-- Two adjacent blocks are one block: the footprint of a loop after one more round. -/
@[fpNF] theorem inBlock_add (b o n n' : ℕ) :
    Store.inBlock b o n ⊔ Store.inBlock b (o + n) n' = Store.inBlock b o (n + n') := by
  funext b' i
  apply propext
  simp only [Pi.sup_apply, sup_Prop_eq, Store.inBlock]
  constructor
  · rintro (⟨h, h1, h2⟩ | ⟨h, h1, h2⟩) <;> exact ⟨h, by omega, by omega⟩
  · rintro ⟨h, h1, h2⟩
    by_cases hi : i < o + n
    · exact Or.inl ⟨h, h1, hi⟩
    · exact Or.inr ⟨h, by omega, by omega⟩

end Fp

namespace Store

/-- **A store predicate reads only the cells `G`**: it holds of every store that agrees with
one where it holds on the cells of `G`. Lengths of buffers are not read (they are kept by every
frame, `Store.EqOff.len_eq`, and by every allocation, `Store.Below`). -/
def ReadsOnly (G : Fp) (P : Store K → Prop) : Prop :=
  ∀ s s', (∀ b i, G b i → s'.get b i = s.get b i) → P s → P s'

theorem readsOnly_readBlock (b o n : ℕ) (xs : List K) :
    ReadsOnly (inBlock b o n) fun s => s.readBlock b o n = some xs := fun _ _ hg hp =>
  (readBlock_congr fun j _ => hg b (o + j) ⟨rfl, by omega, by omega⟩).trans hp

theorem readsOnly_get (b i : ℕ) (v : K) :
    ReadsOnly (inBlock b i 1) fun s => s.get b i = some v := fun _ _ hg hp =>
  (hg b i ⟨rfl, le_rfl, by omega⟩).trans hp

theorem ReadsOnly.and {G G' : Fp} {P P' : Store K → Prop} (h : ReadsOnly G P)
    (h' : ReadsOnly G' P') : ReadsOnly (G ⊔ G') fun s => P s ∧ P' s := fun s s' hg hp =>
  ⟨h s s' (fun b i g => hg b i (Or.inl g)) hp.1, h' s s' (fun b i g => hg b i (Or.inr g)) hp.2⟩

theorem ReadsOnly.mono {G G' : Fp} {P : Store K → Prop} (h : ReadsOnly G P) (hG : G ≤ G') :
    ReadsOnly G' P := fun s s' hg hp => h s s' (fun b i g => hg b i (hG b i g)) hp

/-- **Agreement below a handle**: the buffers below `L` have the same lengths and cells in `s`
and `s'`. The relation between a store and the store of a block with scratch buffers on top
(`NLAlib.Ops.writes_alloc`), in both directions. -/
def Below (L : ℕ) (s s' : Store K) : Prop :=
  ∀ b < L, s'.len b = s.len b ∧ ∀ i, s'.get b i = s.get b i

theorem Below.symm {L : ℕ} {s s' : Store K} (h : Below L s s') : Below L s' s :=
  fun b hb => ⟨(h b hb).1.symm, fun i => ((h b hb).2 i).symm⟩

theorem Below.trans {L : ℕ} {s s' s'' : Store K} (h : Below L s s') (h' : Below L s' s'') :
    Below L s s'' :=
  fun b hb => ⟨(h' b hb).1.trans (h b hb).1, fun i => ((h' b hb).2 i).trans ((h b hb).2 i)⟩

/-- Writes confined to fresh handles preserve every length and cell below the boundary. -/
theorem EqOff.below_of_above {L : ℕ} {F : Fp} {s s' : Store K}
    (h : EqOff F s s') (hAbove : ∀ b i, F b i → L ≤ b) : Below L s s' :=
  fun b hb => ⟨h.len_eq b, fun i => h.get_eq (fun hf =>
    (Nat.not_le_of_lt hb) (hAbove b i hf))⟩

theorem Below.readBlock {L : ℕ} {s s' : Store K} (h : Below L s s') {b : ℕ} (hb : b < L)
    (o n : ℕ) : s'.readBlock b o n = s.readBlock b o n :=
  readBlock_congr fun _ _ => (h b hb).2 _

/-- **A kept fact across an allocation**: a fact that reads only buffers below `L` is kept by
agreement below `L`. -/
theorem Below.keep {L : ℕ} {s s' : Store K} {G : Fp} {P : Store K → Prop} (h : Below L s s')
    (hP : ReadsOnly G P) (hG : ∀ b i, G b i → b < L) (hp : P s) : P s' :=
  hP s s' (fun b i g => (h b (hG b i g)).2 i) hp

theorem Below.refl (L : ℕ) (s : Store K) : Below L s s := fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem Below.mono {L L' : ℕ} {s s' : Store K} (h : Below L s s') (hL : L' ≤ L) :
    Below L' s s' := fun b hb => h b (by omega)

/-- The store after a pop agrees below the new length. -/
theorem below_pop {L : ℕ} {s : Store K} (h : s.length = L + 1) : Below L s s.pop :=
  fun _ hb => ⟨len_pop_of_lt (by omega), fun i => get_pop_of_lt (by omega) i⟩

/-- A store with buffers pushed on top agrees below its length. -/
theorem below_push (s : Store K) (n : ℕ) : Below s.length s (s.push n) :=
  fun _ hb => ⟨len_push_of_lt hb n, fun i => get_push_of_lt hb n i⟩

/-- A frame below `L` composes with agreement: the frame transported through an allocation. -/
theorem EqOff.below {L : ℕ} {F : Fp} {s s' t t' : Store K} (h : EqOff F t t') (hs : Below L s t)
    (hs' : Below L s' t') (hl : s'.length = s.length) (hsl : s.length = L) : EqOff F s s' := by
  subst hsl
  refine ⟨List.ext_getElem (by simp [shape, hl]) fun b h₁ h₂ => ?_, fun b i hF => ?_⟩
  · have hb : b < s.length := by simpa [shape] using h₂
    have e := ((hs' b hb).1.symm.trans (h.len_eq b)).trans (hs b hb).1
    simpa [shape, len, hl ▸ hb, hb] using e
  · by_cases hb : b < s.length
    · rw [← (hs' b hb).2 i, h.get_eq hF, (hs b hb).2 i]
    · simp [get, List.getElem?_eq_none (show s.length ≤ b by omega),
        List.getElem?_eq_none (show s'.length ≤ b by omega)]

namespace EqOff

variable {F G : Fp} {s s' s'' : Store K}

/-- **A kept fact**: a run that writes only `F` keeps every fact that reads only cells off `F`. -/
theorem keep {P : Store K → Prop} (h : EqOff F s s') (hP : ReadsOnly G P) (hD : Fp.Disj F G)
    (hp : P s) : P s' :=
  hP s s' (fun b i g => h.2 b i fun hf => hD b i hf g) hp

/-- **Frames compose by `⊔`.** The running frame of a block, from its first memory to the
current one, after one more step. -/
theorem trans' (h : EqOff F s s') (h' : EqOff G s' s'') : EqOff (F ⊔ G) s s'' :=
  (h.mono fun _ _ => Or.inl).trans (h'.mono fun _ _ => Or.inr)

/-- A block write inside the footprint, in the form of the `frame` tactic: an inclusion goal. -/
theorem updBlock_of_le (h : EqOff F s s') {b o : ℕ} {xs : List K}
    (hF : inBlock b o xs.length ≤ F) : EqOff F s (s'.updBlock b o xs) :=
  h.updBlock fun _ hj => hF _ _ ⟨rfl, by omega, by omega⟩

/-- A footprint on the buffers above the store is no footprint. -/
theorem of_above (h : EqOff (F ⊔ Fp.above s.length) s s') : EqOff F s s' := by
  refine ⟨h.1, fun b i hF => ?_⟩
  by_cases hb : s.length ≤ b
  · have hb' : s'.length ≤ b := by rw [h.length_eq]; exact hb
    simp [get, List.getElem?_eq_none hb, List.getElem?_eq_none hb']
  · exact h.2 b i fun hb' => hb'.elim hF hb

end EqOff

end Store

namespace Mem

/-- Writes of several blocks inside the footprint. -/
theorem eqOff_updBlocks {F : Fp} {m : Mem K} {s : Store K} (h : s.EqOff F m.store)
    {zs : List (ℕ × ℕ)} {ys : List (List K)} (hF : Fp.blocks zs (ys.map List.length) ≤ F) :
    s.EqOff F (m.updBlocks zs ys).store := by
  induction zs generalizing m ys with
  | nil => cases ys <;> exact h
  | cons z zs ih => cases ys with
    | nil => exact h
    | cons y ys =>
      simp only [List.map_cons, Fp.blocks_cons] at hF
      exact ih (m := m.updBlock z y) (Store.EqOff.updBlock_of_le h fun b i hb => hF b i (Or.inl hb))
        fun b i hb => hF b i (Or.inr hb)

/-- Reading blocks depends on the store only. -/
theorem readBlocks_congr {m m' : Mem K} (h : m'.store = m.store) (zs : List (ℕ × ℕ))
    (ls : List ℕ) : m'.readBlocks zs ls = m.readBlocks zs ls := by
  induction zs generalizing ls with
  | nil => cases ls <;> rfl
  | cons z zs ih => cases ls with
    | nil => rfl
    | cons l ls => simp only [readBlocks_cons, h, ih]

/-- The blocks read have the lengths asked. -/
theorem map_length_of_readBlocks {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {ys : List (List K)} (h : m.readBlocks zs ls = some ys) : ys.map List.length = ls := by
  induction zs generalizing ls ys with
  | nil => cases ls with
    | nil => simp only [readBlocks, Option.some.injEq] at h; subst h; rfl
    | cons l ls => simp [readBlocks] at h
  | cons z zs ih => cases ls with
    | nil => simp [readBlocks] at h
    | cons l ls =>
      rw [readBlocks_cons] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [Store.length_of_readBlock hx, ih hxs]

/-- Writing blocks commutes with advancing the position. -/
theorem updBlocks_advance (m : Mem K) (k : ℕ) (zs : List (ℕ × ℕ)) (ys : List (List K)) :
    (m.advance k).updBlocks zs ys = (m.updBlocks zs ys).advance k := by
  induction zs generalizing m ys with
  | nil => cases ys <;> rfl
  | cons z zs ih => cases ys with
    | nil => rfl
    | cons y ys => exact ih (m.updBlock z y) ys

/-- Reading several blocks, one at a time (for `cert_intro`, by name: not a simp lemma, so that
the core's `store_simp` is unchanged). -/
theorem readBlocks_cons_eq_some {m : Mem K} {a : ℕ × ℕ} {as : List (ℕ × ℕ)}
    {n : ℕ} {ns : List ℕ} {X : List (List K)} :
    m.readBlocks (a :: as) (n :: ns) = some X ↔
      ∃ x xs, m.store.readBlock a.1 a.2 n = some x ∧ m.readBlocks as ns = some xs ∧
        X = x :: xs := by
  rw [readBlocks_cons]
  constructor
  · intro h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, xs, hx, hxs, rfl⟩
  · rintro ⟨x, xs, hx, hxs, rfl⟩
    simp [hx, hxs]

/-- **The equation of a contract in operand form, from a frame and the blocks read back**, for
any number of output blocks (when two overlap, both read back the same cells, so the order of
the writes does not matter). Generalises `Store.EqOff.eq_updBlock₂`; used once in
`NLAlib.Ops.Impl.meets_of_writes`, so a certificate never rebuilds the equation by hand. -/
theorem eq_updBlocks_of_eqOff {m m' : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {ys : List (List K)} (h : m.store.EqOff (Fp.blocks zs ls) m'.store)
    (hr : m'.readBlocks zs ls = some ys) (hpos : m'.pos = m.pos) : m' = m.updBlocks zs ys := by
  induction zs generalizing m ls ys with
  | nil =>
    cases ls with
    | nil =>
      simp only [readBlocks, Option.some.injEq] at hr
      subst hr
      have e := Store.EqOff.eq_of_empty (s := m.store) (s' := m'.store) h
      cases m with
      | mk s p =>
        cases m' with
        | mk s' p' =>
          dsimp only at e hpos
          subst s'
          subst p'
          rfl
    | cons l ls => simp [readBlocks] at hr
  | cons z zs ih =>
    cases ls with
    | nil => simp [readBlocks] at hr
    | cons l ls =>
      obtain ⟨y, ys', hy, hys, rfl⟩ := readBlocks_cons_eq_some.mp hr
      have h' : m.store.EqOff (Fp.blocks zs ls ⊔ Store.inBlock z.1 z.2 l) m'.store :=
        h.mono fun b i hb => by
          simp only [Fp.blocks_cons, Pi.sup_apply, sup_Prop_eq] at hb ⊢
          exact hb.symm
      exact ih (m := m.updBlock z y) (h'.peel hy) hys hpos

/-- After writing pairwise disjoint blocks of the declared lengths, they are read back. -/
theorem readBlocks_updBlocks {m : Mem K} {zs : List (ℕ × ℕ)} {ys : List (List K)}
    (hap : Fp.Apart zs (ys.map List.length)) (hz : m.Room zs (ys.map List.length)) :
    (m.updBlocks zs ys).readBlocks zs (ys.map List.length) = some ys := by
  induction zs generalizing m ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => exact hz.elim
  | cons z zs ih => cases ys with
    | nil => exact hz.elim
    | cons y ys =>
      obtain ⟨hd, hap⟩ := hap
      obtain ⟨hz1, hz⟩ := hz
      have hz' : (m.updBlock z y).Room zs (ys.map List.length) := hz.congr fun b => by simp
      have hr := ih (m := m.updBlock z y) hap hz'
      have hfr := eqOff_updBlocks (Store.EqOff.refl (Fp.blocks zs (ys.map List.length)) _)
        (m := m.updBlock z y) (zs := zs) (ys := ys) le_rfl
      have hy : (m.updBlocks (z :: zs) (y :: ys)).store.readBlock z.1 z.2 y.length = some y :=
        hfr.readBlock_of (Store.readBlock_updBlock_self hz1)
          fun j hj hb => hd _ _ ⟨rfl, by omega, by omega⟩ hb
      simp only [List.map_cons]
      exact readBlocks_cons_eq_some.mpr ⟨y, ys, hy, hr, rfl⟩

end Mem

/-! ### Tactics (goal shapes; provisional implementations, completed in phase B) -/

attribute [fpNF] true_and and_true or_true true_or eq_self_iff_true not_or not_and ne_eq
  and_self or_self false_or or_false false_and and_false not_false_eq_true not_true_eq_false
  imp_false List.mem_cons List.not_mem_nil Prod.mk.injEq

/-- **`fp_mem`**: a membership goal `F b i` or `¬ F b i`, where the footprints are built from
`inBlock`, `inBuf`, `⊔`, `⊥`, `Fp.blocks`, `Fp.above`, `Fp.cells` and layouts. Unfolds them
(`fpNF`) and closes the arithmetic with `idx` (handles are numbers: an injective family `hH` is
passed as `fp_mem [hH.eq_iff]`). Fails with the goal it could not close; never leaves a goal. -/
syntax "fp_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fp_mem) => `(tactic| fp_mem [])
  | `(tactic| fp_mem [$ts,*]) => `(tactic| first
      | (simp only [fpNF, storeNF, $ts,*]; done)
      | (simp only [fpNF, storeNF, $ts,*] <;> (try intros) <;> idx)
      | fail "fp_mem: the cell is not shown to be in (or out of) the footprint")

/-- **`fp_block`**: include one block in a union by finding an enclosing block with the same
buffer handle. Offset containment is discharged by `idx`; the target union is never expanded
into an arithmetic disjunction. Fails if no enclosing block is found. -/
syntax (name := tacticFpBlock) "fp_block" : tactic

macro_rules
  | `(tactic| fp_block) => `(tactic| first
      | exact le_rfl
      | exact bot_le
      | (apply Fp.inBlock_le_inBlock <;> idx)
      | (apply le_sup_of_le_left; fp_block)
      | (apply le_sup_of_le_right; fp_block))

/-- **`fp_sub`**: prove an inclusion of footprints `F ≤ G` from normalized cell membership.
It splits source unions before reasoning about individual cells, then uses only the membership
fact, keeping unrelated program proofs out of propositional and arithmetic preprocessing.
The fallback uses the full context's index inequalities. -/
syntax "fp_sub" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fp_sub) => `(tactic| fp_sub [])
  | `(tactic| fp_sub [$ts,*]) => `(tactic| first
      | exact le_rfl
      | ((repeat' apply sup_le) <;> first
         | exact bot_le
         | fp_block
         | (intro b i h
            simp only [fpNF, storeNF, $ts,*] at h ⊢
            first
            | done
            | (clear * - h; aesop (config := { maxRuleApplications := 64, terminal := true }))
            | (clear * - h; idx)
            | idx))
      | fail "fp_sub: the footprint is not shown to be included")

/-- **`disjoint`**: a goal `Fp.Disj F G`, `Fp.Apart zs ls`, `b ≠ b'` of handles, or the side
condition `∀ j < n, ¬ F b (o + j)` of a kept block. Same method as `fp_mem`; the facts of an
injective family of handles are passed as `[hH.eq_iff]` and reduce `H x = H y` to `x = y`,
decided by `simp`. -/
syntax "disjoint" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| disjoint) => `(tactic| disjoint [])
  | `(tactic| disjoint [$ts,*]) => `(tactic| first
      | (simp only [fpNF, storeNF, Fp.Apart, $ts,*]; done)
      | (simp only [fpNF, storeNF, Fp.Apart, $ts,*] <;>
          (repeat' apply And.intro) <;> (try intros) <;> idx)
      | (simp [fpNF, storeNF, Fp.Apart, $ts,*]; done)
      | (simp [fpNF, storeNF, Fp.Apart, $ts,*] <;>
          (repeat' apply And.intro) <;> (try intros) <;> idx)
      | fail "disjoint: the footprints are not shown to be disjoint")

end NLAlib.Ops
