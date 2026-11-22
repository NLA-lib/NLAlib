/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Footprint

/-!
# Views: blocks made of runs

The block of an operand is a contiguous run of cells, or several runs of the same length at a
fixed period: a vector with an increment, a row of a matrix stored by columns, a submatrix of a
matrix with a leading dimension. A `NLAlib.Ops.View` is the shape of such a block: `len` cells,
or `count` runs of `len` cells, one run every `period` cells. The contents of the block are its
cells in order, run after run.

This file gives the cells of a view, the read of a view from a store, its footprint, the room it
needs, and the lists of these that a routine uses. On a contiguous view each of them is, by
computation, the corresponding notion for blocks (`NLAlib.Ops.Store.readBlock`,
`NLAlib.Ops.Store.inBlock`, `NLAlib.Ops.Mem.Room`).

## Main definitions

* `NLAlib.Ops.View`, `NLAlib.Ops.View.cells`, `NLAlib.Ops.View.offset`: a shape, its number of
  cells and the offset of each cell.
* `NLAlib.Ops.Store.readView`, `NLAlib.Ops.Fp.inView`, `NLAlib.Ops.View.Fits`: the read, the
  footprint and the room of one view.
* `NLAlib.Ops.Mem.readViews`, `NLAlib.Ops.Fp.views`, `NLAlib.Ops.Fp.ApartViews`,
  `NLAlib.Ops.Mem.RoomViews`: the same for the operands of a call.

## Main results

* `NLAlib.Ops.Store.readView_eq_some_iff`: a view is read cell by cell.
* `NLAlib.Ops.View.offset_inj`: the cells of a view whose runs do not overlap are distinct.
* `NLAlib.Ops.Store.readView_upd`: writing one cell of a view.
* `NLAlib.Ops.Fp.disj_inView_of_residues`: two views of one buffer with the same period are
  disjoint when their runs occupy disjoint ranges of the period.
* `NLAlib.Ops.Mem.readViews_blocks`, `NLAlib.Ops.Fp.views_blocks`,
  `NLAlib.Ops.Mem.roomViews_blocks`: on contiguous views these are the notions for blocks.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

/-- **The shape of the block of an operand**: `len` cells in a row, or, with
`runs = some (count, period)`, `count` runs of `len` cells, one run every `period` cells. -/
structure View where
  /-- The number of cells of a run. -/
  len : ℕ
  /-- The number of runs and their period; `none` for one run. -/
  runs : Option (ℕ × ℕ) := none

namespace View

/-- The contiguous view of `n` cells. -/
abbrev block (n : ℕ) : View := ⟨n, none⟩

/-- The number of cells of a view. -/
def cells (v : View) : ℕ :=
  match v.runs with
  | none => v.len
  | some (c, _) => c * v.len

/-- The offset of cell `k` of a view from its position: cell `k` is cell `k % len` of run
`k / len`, and run `j` starts at `period * j`. -/
def offset (v : View) (k : ℕ) : ℕ :=
  match v.runs with
  | none => k
  | some (_, p) => p * (k / v.len) + k % v.len

/-- The cells of the view at offset `off` lie in a buffer of length `L`. -/
def Fits (v : View) (off L : ℕ) : Prop :=
  match v.runs with
  | none => off + v.len ≤ L
  | some _ => ∀ k < v.cells, off + v.offset k < L

/-- The runs of the view do not overlap: the period is at least the length of a run. -/
def Regular (v : View) : Prop :=
  match v.runs with
  | none => True
  | some (_, p) => v.len ≤ p

@[simp] theorem cells_block (n : ℕ) : (block n).cells = n := rfl

@[simp] theorem offset_block (n k : ℕ) : (block n).offset k = k := rfl

@[simp] theorem fits_block (n off L : ℕ) : (block n).Fits off L ↔ off + n ≤ L := Iff.rfl

@[simp] theorem cells_runs (l c p : ℕ) : (⟨l, some (c, p)⟩ : View).cells = c * l := rfl

theorem offset_runs (l c p k : ℕ) :
    (⟨l, some (c, p)⟩ : View).offset k = p * (k / l) + k % l := rfl

/-- The cells of runs of one cell: cell `k` is at `period * k`. -/
@[simp] theorem offset_runs_one (c p k : ℕ) : (⟨1, some (c, p)⟩ : View).offset k = p * k := by
  rw [offset_runs, Nat.div_one, Nat.mod_one, Nat.add_zero]

theorem fits_runs (l c p off L : ℕ) :
    (⟨l, some (c, p)⟩ : View).Fits off L ↔
      ∀ k < c * l, off + (p * (k / l) + k % l) < L := Iff.rfl

/-- The cells of a view whose runs do not overlap are distinct. -/
theorem offset_inj {v : View} (hv : v.Regular) {j k : ℕ} (hj : j < v.cells) (hk : k < v.cells)
    (h : v.offset j = v.offset k) : j = k := by
  obtain ⟨l, _ | ⟨c, p⟩⟩ := v
  · exact h
  · change l ≤ p at hv
    change j < c * l at hj
    change k < c * l at hk
    change p * (j / l) + j % l = p * (k / l) + k % l at h
    have hl : 0 < l := Nat.pos_of_ne_zero fun e => by subst e; simp at hj
    have hjl : j % l < p := lt_of_lt_of_le (Nat.mod_lt _ hl) hv
    have hkl : k % l < p := lt_of_lt_of_le (Nat.mod_lt _ hl) hv
    have hp : 0 < p := lt_of_lt_of_le hl hv
    have hdiv : j / l = k / l := by
      have := congrArg (· / p) h
      simpa [Nat.mul_add_div hp, Nat.div_eq_of_lt hjl, Nat.div_eq_of_lt hkl] using this
    have hmod : j % l = k % l := by
      rw [hdiv] at h
      exact Nat.add_left_cancel h
    rw [← Nat.div_add_mod j l, ← Nat.div_add_mod k l, hdiv, hmod]

end View

namespace Store

/-- Read the `n` cells at the indices `f 0, …, f (n - 1)` of buffer `b`; `none` if one read
fails. -/
def readCells (s : Store K) (b : ℕ) (f : ℕ → ℕ) : ℕ → Option (List K)
  | 0 => some []
  | n + 1 => (s.readCells b f n).bind fun xs => (s.get b (f n)).map fun x => xs ++ [x]

/-- Cells are read one by one. -/
theorem readCells_eq_some_iff {s : Store K} {b : ℕ} {f : ℕ → ℕ} {n : ℕ} {xs : List K} :
    s.readCells b f n = some xs ↔ xs.length = n ∧ ∀ j < n, s.get b (f j) = xs[j]? := by
  induction n generalizing xs with
  | zero =>
    constructor
    · rintro h
      obtain rfl : [] = xs := Option.some.inj h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rintro ⟨h, -⟩
      rw [List.length_eq_zero_iff.mp h]
      rfl
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hlen, hget⟩ := ih.mp hys
      refine ⟨by simp [hlen], fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · rw [hget j hj', List.getElem?_append_left (by omega)]
      · rw [hx, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        rfl
    · rintro ⟨hlen, hget⟩
      rcases List.eq_nil_or_concat xs with rfl | ⟨ys, x, rfl⟩
      · simp at hlen
      rw [List.concat_eq_append] at hlen hget ⊢
      have hys : ys.length = n := by simpa using hlen
      have h₁ : s.readCells b f n = some ys := ih.mpr ⟨hys, fun j hj => by
        rw [hget j (by omega), List.getElem?_append_left (by omega)]⟩
      have h₂ : s.get b (f n) = some x := by
        rw [hget n (by omega), List.getElem?_append_right (by omega), hys, Nat.sub_self]
        rfl
      change (s.readCells b f n).bind _ = _
      rw [h₁, Option.bind_some, h₂, Option.map_some]

/-- **Read the block of a view** at offset `off` of buffer `b`: its cells in order, run after
run; `none` if one read fails. On a contiguous view this is `NLAlib.Ops.Store.readBlock`. -/
def readView (s : Store K) (b off : ℕ) (v : View) : Option (List K) :=
  match v.runs with
  | none => s.readBlock b off v.len
  | some _ => s.readCells b (fun k => off + v.offset k) v.cells

@[simp] theorem readView_block (s : Store K) (b off n : ℕ) :
    s.readView b off (View.block n) = s.readBlock b off n := rfl

/-- A view is read cell by cell. -/
theorem readView_eq_some_iff {s : Store K} {b off : ℕ} {v : View} {xs : List K} :
    s.readView b off v = some xs ↔
      xs.length = v.cells ∧ ∀ j < v.cells, s.get b (off + v.offset j) = xs[j]? := by
  obtain ⟨l, _ | ⟨c, p⟩⟩ := v
  · exact readBlock_eq_some_iff
  · exact readCells_eq_some_iff

/-- A cell of a view that is read. -/
theorem get_of_readView {s : Store K} {b off : ℕ} {v : View} {xs : List K}
    (h : s.readView b off v = some xs) {k : ℕ} (hk : k < v.cells) :
    s.get b (off + v.offset k) = xs[k]? :=
  (readView_eq_some_iff.mp h).2 k hk

/-- The block read at a view has as many entries as the view has cells. -/
theorem length_of_readView {s : Store K} {b off : ℕ} {v : View} {xs : List K}
    (h : s.readView b off v = some xs) : xs.length = v.cells :=
  (readView_eq_some_iff.mp h).1

/-- The read of a view depends only on its cells. -/
theorem readView_congr {s s' : Store K} {b off : ℕ} {v : View}
    (h : ∀ k < v.cells, s'.get b (off + v.offset k) = s.get b (off + v.offset k)) :
    s'.readView b off v = s.readView b off v := by
  cases hx : s.readView b off v with
  | some xs =>
    obtain ⟨hl, hg⟩ := readView_eq_some_iff.mp hx
    exact readView_eq_some_iff.mpr ⟨hl, fun j hj => (h j hj).trans (hg j hj)⟩
  | none =>
    cases hy : s'.readView b off v with
    | none => rfl
    | some ys =>
      obtain ⟨hl, hg⟩ := readView_eq_some_iff.mp hy
      rw [readView_eq_some_iff.mpr ⟨hl, fun j hj => (h j hj).symm.trans (hg j hj)⟩] at hx
      cases hx

/-- A view that is read lies inside its buffer. -/
theorem fits_of_readView {s : Store K} {b off : ℕ} {v : View} {xs : List K}
    (h : s.readView b off v = some xs) (hv : 0 < v.cells) : v.Fits off (s.len b) := by
  obtain ⟨hl, hg⟩ := readView_eq_some_iff.mp h
  have hlt : ∀ k < v.cells, off + v.offset k < s.len b := fun k hk => by
    have hk' : k < xs.length := hl ▸ hk
    exact lt_len_of_get ((hg k hk).trans (List.getElem?_eq_getElem hk'))
  obtain ⟨l, _ | ⟨c, p⟩⟩ := v
  · change 0 < l at hv
    have := hlt (l - 1) (by change l - 1 < l; omega)
    change off + (l - 1) < s.len b at this
    change off + l ≤ s.len b
    omega
  · exact hlt

/-- Writing one cell of a view whose runs do not overlap: the block read changes at that
entry only. -/
theorem readView_upd {s : Store K} {b off : ℕ} {v : View} {xs : List K}
    (h : s.readView b off v = some xs) (hv : v.Regular) {k : ℕ} (hk : k < v.cells) (x : K) :
    (s.upd b (off + v.offset k) x).readView b off v = some (xs.set k x) := by
  obtain ⟨hl, hg⟩ := readView_eq_some_iff.mp h
  have hk' : k < xs.length := hl ▸ hk
  have hlt : off + v.offset k < s.len b :=
    lt_len_of_get ((hg k hk).trans (List.getElem?_eq_getElem hk'))
  refine readView_eq_some_iff.mpr ⟨by rw [List.length_set, hl], fun j hj => ?_⟩
  by_cases hjk : j = k
  · subst hjk
    rw [get_upd_self hlt, List.getElem?_set_self hk']
  · have hne : off + v.offset j ≠ off + v.offset k := fun e =>
      hjk (View.offset_inj hv hj hk (Nat.add_left_cancel e))
    rw [get_upd_of_idx_ne hne, hg j hj, List.getElem?_set_ne (Ne.symm hjk)]

/-- A view inside a block that is read: its block is the entries of the block at the cells
of the view. -/
theorem readView_of_readBlock {s : Store K} {b off N : ℕ} {xs : List K}
    (h : s.readBlock b off N = some xs) {r : ℕ} {v : View} {ys : List K}
    (hlen : ys.length = v.cells)
    (hys : ∀ k < v.cells, r + v.offset k < N ∧ ys[k]? = xs[r + v.offset k]?) :
    s.readView b (off + r) v = some ys :=
  readView_eq_some_iff.mpr ⟨hlen, fun k hk => by
    rw [(hys k hk).2, ← (readBlock_eq_some_iff.mp h).2 _ (hys k hk).1, Nat.add_assoc]⟩

end Store

namespace View

/-- A view inside a block that fits in a buffer fits in it. -/
theorem fits_of_block {v : View} {r N off L : ℕ} (hr : r ≤ N)
    (h : ∀ k < v.cells, r + v.offset k < N) (hL : off + N ≤ L) : v.Fits (off + r) L := by
  obtain ⟨l, _ | ⟨c, p⟩⟩ := v
  · change off + r + l ≤ L
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · omega
    · have := h (l - 1) (by change l - 1 < l; omega)
      change r + (l - 1) < N at this
      omega
  · intro k hk
    have := h k hk
    omega

end View

namespace Fp

/-- **The footprint of a view** at offset `off` of buffer `b`: its cells. On a contiguous view
this is `NLAlib.Ops.Store.inBlock`. -/
def inView (b off : ℕ) (v : View) : Fp :=
  match v.runs with
  | none => Store.inBlock b off v.len
  | some _ => fun b' i => b' = b ∧ ∃ k < v.cells, i = off + v.offset k

@[simp, fpNF] theorem inView_block (b off n : ℕ) :
    inView b off (View.block n) = Store.inBlock b off n := rfl

/-- A cell is in the footprint of a view when it is one of its cells. -/
theorem inView_apply {b off : ℕ} {v : View} {b' i : ℕ} :
    inView b off v b' i ↔ b' = b ∧ ∃ k < v.cells, i = off + v.offset k := by
  obtain ⟨l, _ | ⟨c, p⟩⟩ := v
  · constructor
    · rintro ⟨h₁, h₂, h₃⟩
      change off ≤ i at h₂
      change i < off + l at h₃
      exact ⟨h₁, i - off, by change i - off < l; omega, by change i = off + (i - off); omega⟩
    · rintro ⟨h₁, k, hk, rfl⟩
      change k < l at hk
      exact ⟨h₁, Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩
  · exact Iff.rfl

/-- The footprint of a view is in its buffer. -/
theorem inView_le_inBuf (b off : ℕ) (v : View) : inView b off v ≤ Store.inBuf b :=
  fun _ _ h => (inView_apply.mp h).1

/-- Views in different buffers are disjoint. -/
theorem disj_inView_of_ne {b b' off off' : ℕ} {v v' : View} (h : b ≠ b') :
    Disj (inView b off v) (inView b' off' v') := fun _ _ h₁ h₂ =>
  h ((inView_apply.mp h₁).1.symm.trans (inView_apply.mp h₂).1)

/-- A block of another buffer is disjoint from a view. -/
theorem disj_inView_inBlock_of_ne {b b' off off' n : ℕ} {v : View} (h : b ≠ b') :
    Disj (inView b off v) (Store.inBlock b' off' n) := fun _ _ h₁ h₂ =>
  h ((inView_apply.mp h₁).1.symm.trans h₂.1)

/-- Two views of one buffer with the same period are disjoint when, within a period, the
runs of the first end before those of the second begin: rows `i < j` of a matrix stored by
columns, or two bands of columns of its rows. -/
theorem disj_inView_of_residues {b off r r' l l' c c' p : ℕ} (h₁ : r + l ≤ r')
    (h₂ : r' + l' ≤ p) :
    Disj (inView b (off + r) ⟨l, some (c, p)⟩) (inView b (off + r') ⟨l', some (c', p)⟩) := by
  rintro b' i ⟨-, k, hk, rfl⟩ ⟨-, k', hk', e⟩
  change k < c * l at hk
  change k' < c' * l' at hk'
  rw [View.offset_runs, View.offset_runs] at e
  have hl : 0 < l := Nat.pos_of_ne_zero fun e => by subst e; simp at hk
  have hl' : 0 < l' := Nat.pos_of_ne_zero fun e => by subst e; simp at hk'
  have hu := Nat.mod_lt k hl
  have hu' := Nat.mod_lt k' hl'
  have e' : (r + k % l) + p * (k / l) = (r' + k' % l') + p * (k' / l') := by omega
  have hm := congrArg (· % p) e'
  simp only [Nat.add_mul_mod_self_left] at hm
  rw [Nat.mod_eq_of_lt (show r + k % l < p by omega),
    Nat.mod_eq_of_lt (show r' + k' % l' < p by omega)] at hm
  omega

/-- The footprints of the views `vs` at the operands `zs`: the cells written by a call. -/
def views : List (ℕ × ℕ) → List View → Fp
  | z :: zs, v :: vs => inView z.1 z.2 v ⊔ views zs vs
  | _, _ => ⊥

/-- The views `vs` at the operands `zs` are pairwise disjoint. -/
def ApartViews : List (ℕ × ℕ) → List View → Prop
  | z :: zs, v :: vs => Disj (inView z.1 z.2 v) (views zs vs) ∧ ApartViews zs vs
  | _, _ => True

@[simp, fpNF] theorem views_nil : views [] [] = ⊥ := rfl

@[simp, fpNF] theorem views_cons (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (v : View) (vs : List View) :
    views (z :: zs) (v :: vs) = inView z.1 z.2 v ⊔ views zs vs := rfl

@[simp] theorem apartViews_nil : ApartViews [] [] ↔ True := Iff.rfl

@[simp] theorem apartViews_cons (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (v : View) (vs : List View) :
    ApartViews (z :: zs) (v :: vs) ↔
      Disj (inView z.1 z.2 v) (views zs vs) ∧ ApartViews zs vs := Iff.rfl

/-- On contiguous views the footprint is that of the blocks. -/
theorem views_blocks : ∀ (zs : List (ℕ × ℕ)) (ns : List ℕ),
    views zs (ns.map View.block) = blocks zs ns
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | z :: zs, n :: ns => by
    change inView z.1 z.2 (View.block n) ⊔ views zs (ns.map View.block) = _
    rw [views_blocks zs ns]
    rfl

/-- On contiguous views, pairwise disjointness is that of the blocks. -/
theorem apartViews_blocks : ∀ (zs : List (ℕ × ℕ)) (ns : List ℕ),
    ApartViews zs (ns.map View.block) ↔ Apart zs ns
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | z :: zs, n :: ns => by
    change (Disj (inView z.1 z.2 (View.block n)) (views zs (ns.map View.block)) ∧
      ApartViews zs (ns.map View.block)) ↔ _
    rw [views_blocks zs ns, apartViews_blocks zs ns]
    exact Iff.rfl

/-- A cell of the views of a list of operands is in the buffer of one of them. -/
theorem exists_mem_of_views :
    ∀ {zs : List (ℕ × ℕ)} {vs : List View} {b i : ℕ}, views zs vs b i → ∃ z ∈ zs, b = z.1
  | [], _, _, _, h => False.elim h
  | _ :: _, [], _, _, h => False.elim h
  | z :: zs, v :: vs, b, i, h => by
    rcases h with h | h
    · exact ⟨z, List.mem_cons_self, (inView_apply.mp h).1⟩
    · obtain ⟨w, hw, e⟩ := exists_mem_of_views h
      exact ⟨w, List.mem_cons_of_mem _ hw, e⟩

/-- Views of operands in buffers different from those of other operands are disjoint from the
views of those. -/
theorem disj_views_of_ne {zs ws : List (ℕ × ℕ)} (vs us : List View)
    (h : ∀ z ∈ zs, ∀ w ∈ ws, z.1 ≠ w.1) : Disj (views zs vs) (views ws us) :=
  fun _ _ hz hw => by
    obtain ⟨z, hz, e⟩ := exists_mem_of_views hz
    obtain ⟨w, hw, e'⟩ := exists_mem_of_views hw
    exact h z hz w hw (e.symm.trans e')

/-- Views of operands in pairwise different buffers are pairwise disjoint. -/
theorem apartViews_of_nodup :
    ∀ {zs : List (ℕ × ℕ)} (vs : List View), (zs.map Prod.fst).Nodup → ApartViews zs vs
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | z :: zs, v :: vs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    refine ⟨fun b i hz hb => ?_, apartViews_of_nodup vs h.2⟩
    obtain ⟨w, hw, e⟩ := exists_mem_of_views hb
    exact h.1 (List.mem_map.mpr ⟨w, hw, e.symm.trans (inView_apply.mp hz).1⟩)

end Fp

namespace Store

/-- A predicate that reads a view reads only its cells. -/
theorem readsOnly_readView (b off : ℕ) (v : View) (xs : List K) :
    ReadsOnly (Fp.inView b off v) fun s => s.readView b off v = some xs := fun _ _ hg hp =>
  (readView_congr fun k hk => hg b _ (Fp.inView_apply.mpr ⟨rfl, k, hk, rfl⟩)).trans hp

end Store

namespace Mem

/-- Read the blocks of the views `vs` at the operands `as`. On contiguous views this is
`NLAlib.Ops.Mem.readBlocks`. -/
def readViews (m : Mem K) : List (ℕ × ℕ) → List View → Option (List (List K))
  | [], [] => some []
  | a :: as, v :: vs =>
      (m.store.readView a.1 a.2 v).bind fun x => (m.readViews as vs).map fun xs => x :: xs
  | _, _ => none

/-- There is room for the views `vs` at the operands `zs`. On contiguous views this is
`NLAlib.Ops.Mem.Room`. -/
def RoomViews (m : Mem K) : List (ℕ × ℕ) → List View → Prop
  | [], [] => True
  | z :: zs, v :: vs => v.Fits z.2 (m.store.len z.1) ∧ m.RoomViews zs vs
  | _, _ => False

@[simp] theorem readViews_nil (m : Mem K) : m.readViews [] [] = some [] := rfl

@[simp] theorem roomViews_nil (m : Mem K) : m.RoomViews [] [] ↔ True := Iff.rfl

@[simp] theorem roomViews_cons (m : Mem K) (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) (v : View)
    (vs : List View) :
    m.RoomViews (z :: zs) (v :: vs) ↔ v.Fits z.2 (m.store.len z.1) ∧ m.RoomViews zs vs :=
  Iff.rfl

/-- Reading several views, one at a time. -/
theorem readViews_cons_eq_some {m : Mem K} {a : ℕ × ℕ} {as : List (ℕ × ℕ)} {v : View}
    {vs : List View} {X : List (List K)} :
    m.readViews (a :: as) (v :: vs) = some X ↔
      ∃ x xs, m.store.readView a.1 a.2 v = some x ∧ m.readViews as vs = some xs ∧
        X = x :: xs := by
  change (m.store.readView a.1 a.2 v).bind _ = _ ↔ _
  constructor
  · intro h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, xs, hx, hxs, rfl⟩
  · rintro ⟨x, xs, hx, hxs, rfl⟩
    simp [hx, hxs]

/-- Views that are read one by one are read together. -/
theorem readViews_of_cons {m : Mem K} {a : ℕ × ℕ} {as : List (ℕ × ℕ)} {v : View}
    {vs : List View} {x : List K} {xs : List (List K)}
    (hx : m.store.readView a.1 a.2 v = some x) (hxs : m.readViews as vs = some xs) :
    m.readViews (a :: as) (v :: vs) = some (x :: xs) :=
  readViews_cons_eq_some.mpr ⟨x, xs, hx, hxs, rfl⟩

/-- On contiguous views the read is that of the blocks. -/
theorem readViews_blocks (m : Mem K) : ∀ (zs : List (ℕ × ℕ)) (ns : List ℕ),
    m.readViews zs (ns.map View.block) = m.readBlocks zs ns
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | z :: zs, n :: ns => by
    change (m.store.readView z.1 z.2 (View.block n)).bind
      (fun x => (m.readViews zs (ns.map View.block)).map fun xs => x :: xs) = _
    rw [readViews_blocks m zs ns]
    rfl

/-- On contiguous views the room is that of the blocks. -/
theorem roomViews_blocks (m : Mem K) : ∀ (zs : List (ℕ × ℕ)) (ns : List ℕ),
    m.RoomViews zs (ns.map View.block) ↔ m.Room zs ns
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | z :: zs, n :: ns => by
    change ((View.block n).Fits z.2 (m.store.len z.1) ∧ m.RoomViews zs (ns.map View.block)) ↔ _
    rw [roomViews_blocks m zs ns]
    exact Iff.rfl

end Mem

end NLAlib.Ops
