/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Logic.Attr
public import NLAlib.Ops.Logic.Index

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

/-- A block inside its buffer. -/
theorem inBlock_le_inBuf (b o n : ℕ) : Store.inBlock b o n ≤ Store.inBuf b := fun _ _ h => h.1

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
      cases m; cases m'; simp_all
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
  imp_false

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

/-- **`fp_sub`**: an inclusion of footprints `F ≤ G`. See `fp_mem`. -/
syntax "fp_sub" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fp_sub) => `(tactic| fp_sub [])
  | `(tactic| fp_sub [$ts,*]) => `(tactic| first
      | exact le_rfl
      | (intro b i h; simp only [fpNF, storeNF, $ts,*] at h ⊢; idx)
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
