/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Allocation

/-!
# The geometry of a list of views

A program that works on several views (a matrix, a stack, an output vector, scratch registers)
needs the same three facts about them in every proof: each view refers to a live buffer, each
has room for its declared length, and the views are pairwise apart. `NLAlib.Ops.Geometry` is
that conjunction for a list of views and lengths. It survives every write that keeps the buffer
lengths (`NLAlib.Ops.Geometry.of_eqOff`), gives the disjointness of any two views or of any two
disjoint selections of views, and extends to the views allocated by a scratch allocation after
the caller's buffers (`NLAlib.Ops.Geometry.allocated`). An algorithm states its own geometry as
this predicate at its list of views, instead of a structure with the same three fields and the
same lemmas re-proved.

## Main definitions

* `NLAlib.Ops.Geometry`: liveness, room and separation of a list of views.

## Main results

* `NLAlib.Ops.Geometry.of_eqOff`, `NLAlib.Ops.Geometry.live_of_subset`: preservation and
  liveness of sublists.
* `NLAlib.Ops.Geometry.disj`, `NLAlib.Ops.Geometry.disj_select`: disjointness of views.
* `NLAlib.Ops.Geometry.allocated`: the geometry after a scratch allocation.
* `NLAlib.Ops.Mem.room_append`: room for two lists of views.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

/-- Room for two lists of views is room for their concatenation. -/
theorem Mem.room_append {m : Mem K} {zs ws : List (ℕ × ℕ)} {ls ks : List ℕ}
    (h : m.Room zs ls) (h' : m.Room ws ks) : m.Room (zs ++ ws) (ls ++ ks) := by
  induction zs generalizing ls with
  | nil => cases ls with
    | nil => exact h'
    | cons l ls => exact h.elim
  | cons z zs ih => cases ls with
    | nil => exact h.elim
    | cons l ls => exact ⟨h.1, ih h.2⟩

/-- The **geometry of a list of views** in a memory: every view refers to a live buffer, each
has room for its length in `lens`, and their blocks are pairwise apart. -/
structure Geometry (views : List (ℕ × ℕ)) (lens : List ℕ) (μ : Mem K) : Prop where
  /-- Each view refers to a live buffer. -/
  live : μ.Live views
  /-- Each view has room for its length. -/
  room : μ.Room views lens
  /-- The views are pairwise apart. -/
  apart : Fp.Apart views lens

namespace Geometry

variable {views : List (ℕ × ℕ)} {lens : List ℕ} {μ μ' : Mem K}

/-- The geometry survives every write that keeps the buffer lengths. -/
theorem of_eqOff {F : Fp} (h : Geometry views lens μ) (hfr : μ.store.EqOff F μ'.store) :
    Geometry views lens μ' :=
  ⟨h.live.congr hfr.length_eq, h.room.congr hfr.len_eq, h.apart⟩

/-- Any list of the views is live. -/
theorem live_of_subset (h : Geometry views lens μ) {l : List (ℕ × ℕ)}
    (hl : ∀ x ∈ l, x ∈ views) : μ.Live l :=
  fun x hx => h.live x (hl x hx)

/-- Two distinct views have disjoint blocks. -/
theorem disj (h : Geometry views lens μ) {i j : ℕ} (hi : i < min views.length lens.length)
    (hj : j < min views.length lens.length) (hne : i ≠ j) :
    Fp.Disj (Store.inBlock (views.getD i (0, 0)).1 (views.getD i (0, 0)).2 (lens.getD i 0))
      (Store.inBlock (views.getD j (0, 0)).1 (views.getD j (0, 0)).2 (lens.getD j 0)) :=
  h.apart.disj_getD hi hj hne

/-- Two disjoint selections of the views have disjoint blocks. -/
theorem disj_select (h : Geometry views lens μ) (left right : List ℕ)
    (hleft : ∀ i ∈ left, i < min views.length lens.length)
    (hright : ∀ j ∈ right, j < min views.length lens.length)
    (hcross : List.Disjoint left right) :
    Fp.Disj (Fp.blocks (left.map fun i => views.getD i (0, 0)) (left.map fun i => lens.getD i 0))
      (Fp.blocks (right.map fun i => views.getD i (0, 0))
        (right.map fun i => lens.getD i 0)) :=
  h.apart.disj_select left right hleft hright hcross

/-- The geometry after a scratch allocation: if the views have their geometry in `μ`, and the store
`s` extends `μ`'s store (unchanged below its length $L$) by fresh buffers $L, \dots, L + k - 1$ of
the lengths `ns` ($k$ the length of `ns`), then the views followed by the fresh views $(L + i, 0)$
have their geometry, with the lengths `lens ++ ns`, in `s`. -/
theorem allocated (h : Geometry views lens μ) {ns : List ℕ} {s : Store K}
    (hs : s.length = μ.store.length + ns.length)
    (hlens : ∀ i (hi : i < ns.length), s.len (μ.store.length + i) = ns[i])
    (hBelow : Store.Below μ.store.length μ.store s) :
    Geometry (views ++ (List.range ns.length).map fun i => (μ.store.length + i, 0)) (lens ++ ns)
      ⟨s, μ.pos⟩ := by
  have hlen := h.room.length_eq
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hz with hz | hz
    · have := h.live z hz
      change z.1 < s.length
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      have := List.mem_range.mp hi
      change μ.store.length + i < s.length
      omega
  · refine Mem.room_append ?_ (Mem.room_allocs _ _ ns hlens)
    rw [Mem.room_eq_of_below hBelow (fun z hz => h.live z hz)]
    exact h.room
  · refine h.apart.append (Fp.apart_allocs _ ns) hlen ?_
    refine (Fp.blocks_disj_above (fun z hz => h.live z hz)).mono le_rfl ?_
    exact Fp.blocks_le_above fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact Nat.le_add_right _ _

end Geometry

end NLAlib.Ops
