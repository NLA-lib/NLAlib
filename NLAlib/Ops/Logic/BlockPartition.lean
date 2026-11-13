/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Footprint

/-!
# Splitting a strided block reservation

Two children reserve consecutive groups of slots. Their actual payloads may use fewer words
than the reservations. One shared rule supplies disjointness, containment and capacity even
when a child is empty.

## Main results

* `NLAlib.Ops.Fp.split_strided`: disjoint payloads inside consecutive slot reservations.
* `NLAlib.Ops.Mem.room_split_strided`: capacity inherited from the parent reservation.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Payloads bounded by consecutive slot reservations are apart and fit their parent block. -/
theorem Fp.split_strided (buf off stride a b x y : ℕ)
    (hx : x ≤ a * stride) (hy : y ≤ b * stride) :
    Fp.Apart [(buf, off), (buf, off + a * stride)] [x, y] ∧
      Fp.blocks [(buf, off), (buf, off + a * stride)] [x, y] ≤
        Store.inBlock buf off ((a + b) * stride) := by
  have hleft : Store.inBlock buf off x ≤ Store.inBlock buf off ((a + b) * stride) := by
    apply Fp.inBlock_le_inBlock le_rfl
    have h := Nat.mul_le_mul_right stride (Nat.le_add_right a b)
    omega
  have hright : Store.inBlock buf (off + a * stride) y ≤
      Store.inBlock buf off ((a + b) * stride) := by
    apply Fp.inBlock_le_inBlock (by omega)
    rw [Nat.add_mul]
    omega
  constructor
  · simp only [Fp.Apart, Fp.blocks, Fp.disj_sup_right, Fp.disj_bot_right, and_true]
    exact Fp.disj_inBlock_of_le (by omega)
  · simpa only [Fp.blocks, sup_bot_eq] using sup_le hleft hright

/-- Distinct levels of a uniformly strided arena have disjoint full-width blocks. -/
theorem Fp.disj_inBlock_strided (buf off stride : ℕ) {i j : ℕ} (h : i < j) :
    Fp.Disj (Store.inBlock buf (off + stride * i) stride)
      (Store.inBlock buf (off + stride * j) stride) := by
  apply Fp.disj_inBlock_of_le
  have := Idx.mul_add_le_mul' h stride
  omega

/-- Two pairs of adjacent payloads are the corresponding two complete blocks. -/
theorem Fp.blocks_pair_adjacent (u e : ℕ × ℕ) (a b c d : ℕ) :
    Fp.blocks [u, (u.1, u.2 + a), e, (e.1, e.2 + c)] [a, b, c, d] =
      Fp.blocks [u, e] [a + b, c + d] := by
  simp only [Fp.blocks, sup_bot_eq]
  rw [← sup_assoc, Fp.inBlock_add, Fp.inBlock_add]

/-- The enclosing reservation's capacity suffices for both payloads. -/
theorem Mem.room_split_strided {K : Type} {m : Mem K} {buf off stride a b x y : ℕ}
    (hx : x ≤ a * stride) (hy : y ≤ b * stride)
    (hroom : off + (a + b) * stride ≤ m.store.len buf) :
    m.Room [(buf, off), (buf, off + a * stride)] [x, y] := by
  have h := Nat.mul_le_mul_right stride (Nat.le_add_right a b)
  simp only [Mem.room_cons, Mem.room_nil]
  rw [Nat.add_mul] at hroom
  exact ⟨by omega, by omega, trivial⟩

/-- A finite block collection lies inside a footprint when every indexed block does. -/
theorem Fp.blocks_le_of_forall_getD {zs : List (ℕ × ℕ)} {ls : List ℕ} {F : Fp}
    (h : ∀ i < min zs.length ls.length,
      Store.inBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0) ≤ F) :
    Fp.blocks zs ls ≤ F := by
  induction zs generalizing ls with
  | nil => cases ls <;> exact bot_le
  | cons z zs ih =>
    cases ls with
    | nil => exact bot_le
    | cons l ls =>
      apply sup_le
      · simpa only [List.getD_cons_zero] using h 0 (by simp)
      · apply ih
        intro i hi
        simpa only [List.getD_cons_succ] using h (i + 1)
          (by simpa using Nat.succ_lt_succ hi)

/-- An indexed finite collection has the expected individual block subfootprints. -/
theorem Fp.inBlock_ofFn_le_blocks {m : ℕ} (x : Fin m → ℕ × ℕ) (length : Fin m → ℕ)
    (i : Fin m) : Store.inBlock (x i).1 (x i).2 (length i) ≤
      Fp.blocks (List.ofFn x) (List.ofFn length) := by
  simpa [List.getD_eq_getElem?_getD, i.isLt] using
    Fp.inBlock_getD_le_blocks (List.ofFn x) (List.ofFn length) (i := i) (by simp)

/-- Componentwise containment bounds the union of an indexed finite block collection. -/
theorem Fp.blocks_ofFn_le {m : ℕ} {x : Fin m → ℕ × ℕ} {length : Fin m → ℕ} {F : Fp}
    (h : ∀ i, Store.inBlock (x i).1 (x i).2 (length i) ≤ F) :
    Fp.blocks (List.ofFn x) (List.ofFn length) ≤ F := by
  apply Fp.blocks_le_of_forall_getD
  intro i hi
  have hi' : i < m := by simpa using hi
  simpa [List.getD_eq_getElem?_getD, hi'] using h ⟨i, hi'⟩

/-- Two collections of views are disjoint when different parent regions are apart and the two
views within each matching parent are disjoint. The same index supplies containment and local
separation; callers do not need to enumerate every cross-pair of views. -/
theorem Fp.Apart.disj_view_collections {m : ℕ} {parent x y : Fin m → ℕ × ℕ}
    {length lx ly : Fin m → ℕ}
    (h : Fp.Apart (List.ofFn parent) (List.ofFn length))
    (hx : ∀ i, Store.inBlock (x i).1 (x i).2 (lx i) ≤
      Store.inBlock (parent i).1 (parent i).2 (length i))
    (hy : ∀ i, Store.inBlock (y i).1 (y i).2 (ly i) ≤
      Store.inBlock (parent i).1 (parent i).2 (length i))
    (hxy : ∀ i, Fp.Disj (Store.inBlock (x i).1 (x i).2 (lx i))
      (Store.inBlock (y i).1 (y i).2 (ly i))) :
    Fp.Disj (Fp.blocks (List.ofFn x) (List.ofFn lx))
      (Fp.blocks (List.ofFn y) (List.ofFn ly)) := by
  apply Fp.disj_blocks_of_forall_getD
  intro j hj
  have hj' : j < m := by simpa using hj
  apply Fp.Disj.symm
  apply Fp.disj_blocks_of_forall_getD
  intro i hi
  have hi' : i < m := by simpa using hi
  have hd : Fp.Disj (Store.inBlock (x ⟨i, hi'⟩).1 (x ⟨i, hi'⟩).2 (lx ⟨i, hi'⟩))
      (Store.inBlock (y ⟨j, hj'⟩).1 (y ⟨j, hj'⟩).2 (ly ⟨j, hj'⟩)) := by
    by_cases he : i = j
    · subst j
      exact hxy ⟨i, hi'⟩
    · have hp : Fp.Disj
          (Store.inBlock (parent ⟨i, hi'⟩).1 (parent ⟨i, hi'⟩).2 (length ⟨i, hi'⟩))
          (Store.inBlock (parent ⟨j, hj'⟩).1 (parent ⟨j, hj'⟩).2 (length ⟨j, hj'⟩)) := by
        simpa [List.getD_eq_getElem?_getD, hi', hj'] using
          h.disj_getD (i := i) (j := j) (by simpa using hi') (by simpa using hj') he
      exact hp.mono (hx _) (hy _)
  simpa [List.getD_eq_getElem?_getD, hi', hj'] using hd.symm

/-- A finite family of bounded subviews writes only cells of its parent block collection.
Parent indices may repeat and the views need not be disjoint. -/
theorem Fp.blocks_subviews_le {zs : List (ℕ × ℕ)} {ls : List ℕ} {q : ℕ}
    (parent : Fin q → Fin (min zs.length ls.length)) (offset len : Fin q → ℕ)
    (hsub : ∀ i, offset i + len i ≤ ls.getD (parent i) 0) :
    Fp.blocks (List.ofFn fun i =>
      ((zs.getD (parent i) (0, 0)).1, (zs.getD (parent i) (0, 0)).2 + offset i))
      (List.ofFn len) ≤ Fp.blocks zs ls := by
  apply Fp.blocks_ofFn_le
  intro i
  refine (Fp.inBlock_le_inBlock (by omega) ?_).trans
    (Fp.inBlock_getD_le_blocks zs ls (parent i).isLt)
  have := hsub i
  omega

/-- Two independently indexed families of views are disjoint when matching parent regions
have separated relative intervals. Views from different parents inherit their separation from
the parent collection. The two families may have different sizes and repeat parent indices. -/
theorem Fp.Apart.disj_subviews {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : Fp.Apart zs ls) {p q : ℕ}
    (left : Fin p → Fin (min zs.length ls.length))
    (right : Fin q → Fin (min zs.length ls.length))
    (lo llen : Fin p → ℕ) (ro rlen : Fin q → ℕ)
    (hl : ∀ a, lo a + llen a ≤ ls.getD (left a) 0)
    (hr : ∀ b, ro b + rlen b ≤ ls.getD (right b) 0)
    (hsep : ∀ a b, left a = right b →
      lo a + llen a ≤ ro b ∨ ro b + rlen b ≤ lo a) :
    Fp.Disj (Fp.blocks (List.ofFn fun a =>
      ((zs.getD (left a) (0, 0)).1, (zs.getD (left a) (0, 0)).2 + lo a))
        (List.ofFn llen))
      (Fp.blocks (List.ofFn fun b =>
        ((zs.getD (right b) (0, 0)).1, (zs.getD (right b) (0, 0)).2 + ro b))
        (List.ofFn rlen)) := by
  have view_le {r : ℕ} (parent : Fin r → Fin (min zs.length ls.length))
      (off len : Fin r → ℕ) (hb : ∀ a, off a + len a ≤ ls.getD (parent a) 0)
      (a : Fin r) :
      Store.inBlock (zs.getD (parent a) (0, 0)).1
        ((zs.getD (parent a) (0, 0)).2 + off a) (len a) ≤
      Store.inBlock (zs.getD (parent a) (0, 0)).1
        (zs.getD (parent a) (0, 0)).2 (ls.getD (parent a) 0) := by
    apply Fp.inBlock_le_inBlock (by omega)
    have := hb a
    omega
  apply Fp.disj_blocks_of_forall_getD
  intro j hj
  have hj' : j < q := by simpa using hj
  apply Fp.Disj.symm
  apply Fp.disj_blocks_of_forall_getD
  intro i hi
  have hi' : i < p := by simpa using hi
  let a : Fin p := ⟨i, hi'⟩
  let b : Fin q := ⟨j, hj'⟩
  have hd : Fp.Disj
      (Store.inBlock (zs.getD (left a) (0, 0)).1
        ((zs.getD (left a) (0, 0)).2 + lo a) (llen a))
      (Store.inBlock (zs.getD (right b) (0, 0)).1
        ((zs.getD (right b) (0, 0)).2 + ro b) (rlen b)) := by
    by_cases hp : left a = right b
    · rcases hsep a b hp with hbefore | hafter
      · rw [hp]
        exact Fp.disj_inBlock_of_le (by omega)
      · rw [hp]
        exact (Fp.disj_inBlock_of_le (by omega)).symm
    · exact (h.disj_getD (left a).isLt (right b).isLt
        (fun he => hp (Fin.ext he))).mono
          (view_le left lo llen hl a) (view_le right ro rlen hr b)
  simpa [List.getD_eq_getElem?_getD, hi', hj', a, b] using hd.symm

end NLAlib.Ops
