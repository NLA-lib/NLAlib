/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Step

/-!
# Collecting stored outputs of sequential programs

A sequence of numerical subprograms produces a tuple of ordinary output blocks. The shared
rule retains earlier blocks across disjoint later writes and composes the tape position.
Program proofs supply their mathematical block results; they do not reconstruct frames or
nested read-list equations for every stage.

## Main results

* `NLAlib.Ops.Writes.seq_readBlock`: collect one block followed by the remaining output blocks.
* `NLAlib.Ops.Mem.readBlocks_getD`: obtain an indexed block read from a collected tuple.
* `NLAlib.Ops.Mem.readBlocks_of_eqOff`: retain input tuples across disjoint writes.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- Project the capacity of any valid output block from a collected room hypothesis. -/
theorem Mem.Room.getD {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : m.Room zs ls) {i : ℕ} (hi : i < min zs.length ls.length) :
    (zs.getD i (0, 0)).2 + ls.getD i 0 ≤ m.store.len (zs.getD i (0, 0)).1 := by
  induction zs generalizing ls i with
  | nil => simp at hi
  | cons z zs ih =>
    cases ls with
    | nil => simp at hi
    | cons l ls =>
      cases i with
      | zero => exact h.1
      | succ i => simpa only [List.getD_cons_succ] using ih h.2 (by simpa using hi)

/-- An indexed collection has room when each of its blocks fits its buffer. -/
theorem Mem.Room.ofFn {m : Mem K} {q : ℕ} (x : Fin q → ℕ × ℕ) (ls : Fin q → ℕ)
    (h : ∀ i, (x i).2 + ls i ≤ m.store.len (x i).1) :
    m.Room (List.ofFn x) (List.ofFn ls) := by
  induction q with
  | zero => simp only [List.ofFn_zero, Mem.room_nil]
  | succ q ih =>
    simp only [List.ofFn_succ, Mem.room_cons]
    exact ⟨h 0, ih (fun i => x i.succ) (fun i => ls i.succ) (fun i => h i.succ)⟩

/-- Capacity passes from parent blocks to any finite collection of contained subviews.
Repeated parent indices are permitted: capacity does not require disjoint views. -/
theorem Mem.Room.subviews {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : m.Room zs ls) {q : ℕ} (parent : Fin q → Fin (min zs.length ls.length))
    (offset len : Fin q → ℕ)
    (hsub : ∀ i, offset i + len i ≤ ls.getD (parent i) 0) :
    m.Room (List.ofFn fun i =>
      ((zs.getD (parent i) (0, 0)).1, (zs.getD (parent i) (0, 0)).2 + offset i))
      (List.ofFn len) := by
  apply Mem.Room.ofFn
  intro i
  have hr := h.getD (parent i).isLt
  have hs := hsub i
  dsimp only
  omega

/-- A disjoint tuple footprint protects each of its constituent blocks. -/
theorem Fp.Disj.inBlock_getD_left {F : Fp} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : Fp.Disj (Fp.blocks zs ls) F) {i : ℕ} (hi : i < min zs.length ls.length) :
    Fp.Disj (Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0)) F :=
  h.mono (Fp.inBlock_getD_le_blocks zs ls hi) le_rfl

/-- Disjoint writes preserve a whole tuple of input block reads, including failed reads. -/
theorem Mem.readBlocks_eq_of_eqOff {m m' : Mem K} {F : Fp}
    (hfr : m.store.EqOff F m'.store) (zs : List (ℕ × ℕ)) (ls : List ℕ)
    (hdis : Fp.Disj F (Fp.blocks zs ls)) : m'.readBlocks zs ls = m.readBlocks zs ls := by
  induction zs generalizing ls with
  | nil => cases ls <;> rfl
  | cons z zs ih =>
    cases ls with
    | nil => rfl
    | cons l ls =>
      have hr := hfr.readBlock_eq (b := z.1) (off := z.2) (n := l) (fun j hj hf =>
        hdis _ _ hf (Or.inl ⟨rfl, by omega, by omega⟩))
      simp only [Mem.readBlocks, hr, ih ls (hdis.mono le_rfl le_sup_right)]

/-- A collected input tuple is retained across a disjoint frame. -/
theorem Mem.readBlocks_of_eqOff {m m' : Mem K} {F : Fp} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {xs : List (List K)} (hfr : m.store.EqOff F m'.store)
    (hdis : Fp.Disj F (Fp.blocks zs ls)) (h : m.readBlocks zs ls = some xs) :
    m'.readBlocks zs ls = some xs := (Mem.readBlocks_eq_of_eqOff hfr zs ls hdis).trans h

/-- Decompose a known tuple of successful reads into its known head and tail. -/
theorem Mem.readBlocks_cons_iff {m : Mem K} {z : ℕ × ℕ} {zs : List (ℕ × ℕ)}
    {n : ℕ} {ns : List ℕ} {x : List K} {xs : List (List K)} :
    m.readBlocks (z :: zs) (n :: ns) = some (x :: xs) ↔
      m.store.readBlock z.1 z.2 n = some x ∧ m.readBlocks zs ns = some xs := by
  constructor
  · intro h
    obtain ⟨y, ys, hy, hys, he⟩ := Mem.readBlocks_cons_eq_some.mp h
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ⟨hy, hys⟩
  · rintro ⟨hx, hxs⟩
    exact Mem.readBlocks_cons_eq_some.mpr ⟨x, xs, hx, hxs, rfl⟩

/-- Concatenate two successful tuples of reads from the same memory. -/
theorem Mem.readBlocks_append {m : Mem K} {zs ws : List (ℕ × ℕ)} {ls ns : List ℕ}
    {xs ys : List (List K)} (hleft : m.readBlocks zs ls = some xs)
    (hright : m.readBlocks ws ns = some ys) :
    m.readBlocks (zs ++ ws) (ls ++ ns) = some (xs ++ ys) := by
  induction zs generalizing ls xs with
  | nil =>
    cases ls with
    | nil =>
      simp only [Mem.readBlocks, Option.some.injEq] at hleft
      subst xs
      exact hright
    | cons l ls => simp [Mem.readBlocks] at hleft
  | cons z zs ih =>
    cases ls with
    | nil => simp [Mem.readBlocks] at hleft
    | cons l ls =>
      obtain ⟨x, xs, hx, hxs, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hleft
      exact Mem.readBlocks_of_cons hx (ih hxs)

/-- A successful tuple of block reads depends only on the union of its requested cells.
The memory position plays no role in reading the tuple. -/
theorem Store.readsOnly_readBlocks {K : Type} (zs : List (ℕ × ℕ)) (ls : List ℕ)
    (xs : List (List K)) (pos : ℕ) :
    Store.ReadsOnly (Fp.blocks zs ls) (fun s => (Mem.mk s pos).readBlocks zs ls = some xs) := by
  induction zs generalizing ls xs with
  | nil => cases ls <;> exact fun _ _ _ h => h
  | cons z zs ih =>
    cases ls with
    | nil => exact fun _ _ _ h => h
    | cons l ls =>
      intro s s' h hread
      obtain ⟨x, xs, hx, hxs, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hread
      exact Mem.readBlocks_of_cons
        (Store.readsOnly_readBlock z.1 z.2 l x s s' (fun b i hi => h b i (Or.inl hi)) hx)
        (ih ls xs s s' (fun b i hi => h b i (Or.inr hi)) hxs)


namespace Writes

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}
  {c c' : Stmt Op Tst}

/-- Carry a tuple of actual readable input blocks through a disjoint mathematical block.
The next named state receives those same input reads, without an update-chain invariant. -/
theorem keep_readBlocks {F : Fp} {P : Mem K → Prop} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {xs : List (List K)} (h : Writes md I τ c ρ F P m)
    (hr : m.readBlocks zs ls = some xs) (hdis : Fp.Disj F (Fp.blocks zs ls)) :
    Writes md I τ c ρ F (fun m' => P m' ∧ m'.readBlocks zs ls = some xs) m :=
  h.mono le_rfl fun _ hfr hp => ⟨hp, Mem.readBlocks_of_eqOff hfr hdis hr⟩

/-- A known scalar result is its singleton output block, with the same frame and position. -/
theorem readBlock_of_get {z : ℕ × ℕ} {v : K}
    (h : Writes md I τ c ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some v) m) :
    Writes md I τ c ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 1 = some [v]) m :=
  h.mono le_rfl fun _ _ hp => ⟨hp.1, by simp [Store.readBlock, hp.2]⟩

/-- One known output block is a singleton tuple of output blocks. -/
theorem readBlocks_singleton {z : ℕ × ℕ} {l : ℕ} {ys : List K}
    (h : Writes md I τ c ρ (Store.inBlock z.1 z.2 l)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 l = some ys) m) :
    Writes md I τ c ρ (Fp.blocks [z] [l])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [z] [l] = some [ys]) m := by
  exact h.mono le_sup_left fun _ _ hp => ⟨hp.1, Mem.readBlocks_of_cons hp.2 rfl⟩

/-- A numerical block result followed by the remaining results is a collected output tuple.
Later writes are disjoint from the first block. The continuation receives its actual read
and frame; preserving that first result until return and composing positions is shared here. -/
theorem seq_readBlock {z : ℕ × ℕ} {l : ℕ} {ys : List K}
    {zs : List (ℕ × ℕ)} {ls : List ℕ} {yss : List (List K)}
    (h : Writes md I τ c ρ (Store.inBlock z.1 z.2 l)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 l = some ys) m)
    (hdis : Fp.Disj (Store.inBlock z.1 z.2 l) (Fp.blocks zs ls))
    (hrest : ∀ m', m.store.EqOff (Store.inBlock z.1 z.2 l) m'.store →
      m'.pos = m.pos → m'.store.readBlock z.1 z.2 l = some ys →
      Writes md I τ c' ρ (Fp.blocks zs ls)
        (fun m'' => m''.pos = m'.pos ∧ m''.readBlocks zs ls = some yss) m') :
    Writes md I τ (.seq c c') ρ (Fp.blocks (z :: zs) (l :: ls))
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks (z :: zs) (l :: ls) = some (ys :: yss)) m := by
  refine h.seq fun m' hfr ⟨hp, hr⟩ => ?_
  exact ((hrest m' hfr hp hr).keep (Store.readsOnly_readBlock z.1 z.2 l ys) hdis.symm hr).mono
    le_rfl fun _ _ ⟨⟨hp', hr'⟩, hr₀⟩ => ⟨hp'.trans hp, Mem.readBlocks_of_cons hr₀ hr'⟩

end Writes

end NLAlib.Ops
