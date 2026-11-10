/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Logic.Attr

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

**Phase A**: statements only (`sorry`); the tactics at the end are declared with their goal
shapes, and a provisional implementation.

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

@[fpNF] theorem le_iff (F G : Fp) : F ≤ G ↔ ∀ b i, F b i → G b i := Iff.rfl

@[fpNF] theorem disj_iff (F G : Fp) : Disj F G ↔ ∀ b i, F b i → G b i → False := Iff.rfl

theorem Disj.symm {F G : Fp} (h : Disj F G) : Disj G F := fun b i hg hf => h b i hf hg

theorem Disj.mono {F G F' G' : Fp} (h : Disj F G) (hF : F' ≤ F) (hG : G' ≤ G) : Disj F' G' :=
  fun b i hf hg => h b i (hF b i hf) (hG b i hg)

@[simp] theorem disj_sup_left {F G H : Fp} : Disj (F ⊔ G) H ↔ Disj F H ∧ Disj G H := by sorry

@[simp] theorem disj_sup_right {F G H : Fp} : Disj F (G ⊔ H) ↔ Disj F G ∧ Disj F H := by sorry

@[simp] theorem disj_bot_left (F : Fp) : Disj ⊥ F := fun _ _ h _ => h

@[simp] theorem disj_bot_right (F : Fp) : Disj F ⊥ := fun _ _ _ h => h

/-- Blocks of different buffers are disjoint. -/
theorem disj_inBlock_of_ne {b b' o o' n n' : ℕ} (h : b ≠ b') :
    Disj (Store.inBlock b o n) (Store.inBlock b' o' n') := by sorry

/-- Blocks of one buffer, one before the other, are disjoint. -/
theorem disj_inBlock_of_le {b o o' n n' : ℕ} (h : o + n ≤ o') :
    Disj (Store.inBlock b o n) (Store.inBlock b o' n') := by sorry

/-- A block inside a block. -/
theorem inBlock_le_inBlock {b o o' n n' : ℕ} (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') :
    Store.inBlock b o n ≤ Store.inBlock b o' n' := by sorry

/-- A block inside its buffer. -/
theorem inBlock_le_inBuf (b o n : ℕ) : Store.inBlock b o n ≤ Store.inBuf b := fun _ _ h => h.1

/-- Two adjacent blocks are one block: the footprint of a loop after one more round. -/
@[fpNF] theorem inBlock_add (b o n n' : ℕ) :
    Store.inBlock b o n ⊔ Store.inBlock b (o + n) n' = Store.inBlock b o (n + n') := by sorry

end Fp

namespace Store

/-- **A store predicate reads only the cells `G`**: it holds of every store of the same shape
that agrees on `G`. Shapes (lengths of buffers) are always read. -/
def ReadsOnly (G : Fp) (P : Store K → Prop) : Prop :=
  ∀ s s', s'.shape = s.shape → (∀ b i, G b i → s'.get b i = s.get b i) → P s → P s'

theorem readsOnly_readBlock (b o n : ℕ) (xs : List K) :
    ReadsOnly (inBlock b o n) fun s => s.readBlock b o n = some xs := by sorry

theorem readsOnly_get (b i : ℕ) (v : K) :
    ReadsOnly (inBlock b i 1) fun s => s.get b i = some v := by sorry

/-- A fact about the lengths of the buffers reads no cell. -/
theorem readsOnly_shape (P : List ℕ → Prop) : ReadsOnly (⊥ : Fp) fun s : Store K => P s.shape :=
  fun _ _ hs _ h => by simpa only [hs] using h

theorem ReadsOnly.and {G G' : Fp} {P P' : Store K → Prop} (h : ReadsOnly G P)
    (h' : ReadsOnly G' P') : ReadsOnly (G ⊔ G') fun s => P s ∧ P' s := by sorry

theorem ReadsOnly.mono {G G' : Fp} {P : Store K → Prop} (h : ReadsOnly G P) (hG : G ≤ G') :
    ReadsOnly G' P := by sorry

namespace EqOff

variable {F G : Fp} {s s' s'' : Store K}

/-- **A kept fact**: a run that writes only `F` keeps every fact that reads only cells off `F`. -/
theorem keep {P : Store K → Prop} (h : EqOff F s s') (hP : ReadsOnly G P) (hD : Fp.Disj F G)
    (hp : P s) : P s' := by sorry

/-- **Frames compose by `⊔`.** The running frame of a block, from its first memory to the
current one, after one more step. -/
theorem trans' (h : EqOff F s s') (h' : EqOff G s' s'') : EqOff (F ⊔ G) s s'' := by sorry

/-- A write inside the footprint, in the form of the `frame` tactic: a membership goal. -/
theorem upd_of_mem (h : EqOff F s s') {b i : ℕ} (hF : F b i) (v : K) :
    EqOff F s (s'.upd b i v) := h.upd hF v

/-- A block write inside the footprint, in the form of the `frame` tactic: an inclusion goal. -/
theorem updBlock_of_le (h : EqOff F s s') {b o : ℕ} {xs : List K}
    (hF : inBlock b o xs.length ≤ F) : EqOff F s (s'.updBlock b o xs) := by sorry

/-- The frame of nothing written, against a larger footprint: the base of the `frame` tactic. -/
theorem of_le (h : EqOff G s s') (hF : G ≤ F) : EqOff F s s' := h.mono hF

end EqOff

end Store

namespace Mem

/-- Writes of several blocks inside the footprint. -/
theorem eqOff_updBlocks {F : Fp} {m : Mem K} {s : Store K} (h : s.EqOff F m.store)
    {zs : List (ℕ × ℕ)} {ys : List (List K)} (hF : Fp.blocks zs (ys.map List.length) ≤ F) :
    s.EqOff F (m.updBlocks zs ys).store := by sorry

/-- **The equation of a contract in operand form, from a frame and the blocks read back**, for
any number of pairwise disjoint output blocks. Generalises `Store.EqOff.eq_updBlock₂`; used once
in `NLAlib.Ops.Impl.meets_of_writes`, so a certificate never rebuilds the equation by hand. -/
theorem eq_updBlocks_of_eqOff {m m' : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {ys : List (List K)} (h : m.store.EqOff (Fp.blocks zs ls) m'.store) (hap : Fp.Apart zs ls)
    (hr : m'.readBlocks zs ls = some ys) (hpos : m'.pos = m.pos) : m' = m.updBlocks zs ys := by
  sorry

/-- Reading several blocks, one at a time (for `cert_intro`). -/
@[simp, storeNF] theorem readBlocks_cons_eq_some {m : Mem K} {a : ℕ × ℕ} {as : List (ℕ × ℕ)}
    {n : ℕ} {ns : List ℕ} {X : List (List K)} :
    m.readBlocks (a :: as) (n :: ns) = some X ↔
      ∃ x xs, m.store.readBlock a.1 a.2 n = some x ∧ m.readBlocks as ns = some xs ∧
        X = x :: xs := by sorry

/-- After writing pairwise disjoint blocks of the declared lengths, they are read back. -/
theorem readBlocks_updBlocks {m : Mem K} {zs : List (ℕ × ℕ)} {ys : List (List K)}
    (hap : Fp.Apart zs (ys.map List.length)) (hz : m.Room zs (ys.map List.length)) :
    (m.updBlocks zs ys).readBlocks zs (ys.map List.length) = some ys := by sorry

end Mem

/-! ### Tactics (goal shapes; provisional implementations, completed in phase B) -/

attribute [fpNF] true_and and_true or_true true_or eq_self_iff_true not_or not_and ne_eq
  and_self or_self false_or or_false false_and and_false not_false_eq_true not_true_eq_false
  imp_false

/-- **`fp_mem`**: a membership goal `F b i` or `¬ F b i`, or an inclusion `F ≤ G`, where the
footprints are built from `inBlock`, `inBuf`, `⊔`, `⊥`, `Fp.blocks` and layouts. Unfolds them
(`fpNF`), splits the cases, and closes the arithmetic with `idx` (handles are numbers: an
injective family `hH` is passed as `fp_mem [hH.eq_iff]`). Fails with the goal it could not close;
never leaves a goal. -/
syntax "fp_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fp_mem) => `(tactic| fp_mem [])
  | `(tactic| fp_mem [$ts,*]) => `(tactic| first
      | (simp only [fpNF, $ts,*]; done)
      | (simp only [fpNF, $ts,*] <;> (try intros) <;> omega)
      | fail "fp_mem: the cell is not shown to be in (or out of) the footprint")

/-- **`disjoint`**: a goal `Fp.Disj F G`, `Fp.Apart zs ls`, `b ≠ b'` of handles, or the side
condition `∀ j < n, ¬ F b (o + j)` of a kept block. Same method as `fp_mem`. -/
syntax "disjoint" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| disjoint) => `(tactic| disjoint [])
  | `(tactic| disjoint [$ts,*]) => `(tactic| first
      | (simp only [fpNF, Fp.Apart, $ts,*]; done)
      | (simp only [fpNF, Fp.Apart, $ts,*] <;> (try intros) <;> omega)
      | fail "disjoint: the footprints are not shown to be disjoint")

end NLAlib.Ops
