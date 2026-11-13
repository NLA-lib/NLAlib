/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.List.Range
public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.IndexBinder
public import NLAlib.Computation.Loops
public import NLAlib.Computation.Contract
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.ExecCharge
public import NLAlib.Computation.MatvecRoutine

/-!
# A program logic for runs

A program logic for `NLAlib.Computation.exec` (design note
`docs/design/Computation-ProgramLogic.md`). The run `NLAlib.Computation.exec` is
deterministic, so its weakest precondition is a definition, not an inductive judgement:
`NLAlib.Computation.Wp m I s Q st` says the run of `s` from `st` ends in a state satisfying `Q`
(mode `total`: it succeeds; mode `liberal`: if it succeeds). A triple
(`NLAlib.Computation.Triple`) relates the start and final states, so frames, counts and the
size of the store are stated against the start state, and a routine specification
(`NLAlib.Computation.Spec`) adds the blocks it may modify (`NLAlib.Computation.Modifies`). The
rules are proved once from the run equations of `NLAlib/Computation/Exec.lean`; a program proof
applies them statement by statement, each step naming the next state.

## Main definitions

* `NLAlib.Computation.Modifies`, `NLAlib.Computation.ReadsOnly`: footprints and read sets.
* `NLAlib.Computation.Mode`, `NLAlib.Computation.Wp`, `NLAlib.Computation.Triple`: the logic.
* `NLAlib.Computation.matBlock`: the canonical block of a stored matrix.
* `NLAlib.Computation.PosKept`: kept tape positions.
* `NLAlib.Computation.CellsHold`, `NLAlib.Computation.cellBlocks`: a bundle of stored cells and its
  read set.

## Main results

* `NLAlib.Computation.wp_seq`, `NLAlib.Computation.wp_alloc`, `NLAlib.Computation.wp_ite`,
  `NLAlib.Computation.wp_bindIdx_of_read`, `NLAlib.Computation.wp_kcall`: the statement rules.
* `NLAlib.Computation.Triple.loop`, `NLAlib.Computation.Triple.whileFuel`: invariant rules.
* `NLAlib.Computation.wp_run_bind`, `NLAlib.Computation.wp_run_allocBind`: builders.

Routine specifications, counts, instruction specifications, certificate bridges and the tactics
are in `NLAlib/Computation/RoutineSpec.lean`.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### Footprints and read sets -/

section Footprint

/-- **`s'` differs from `s` only in the blocks `fp`** (`(handle, offset, length)`): the two stores
have the same shape and every cell disjoint from every block of `fp` reads the same at every
tag. The cell form `blockDisjoint (b, i, 1) x` is the frame form of the kernel contracts. -/
def Modifies (fp : List (ℕ × ℕ × ℕ)) (s s' : Store P K) : Prop :=
  s'.shape = s.shape ∧
    ∀ q b i, (∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) → s'.read q b i = s.read q b i

/-- **A store predicate that reads only the blocks `rs`**: it survives any store that has the
same shape on the buffers of `rs` and reads the same on every cell of `rs`, at every tag. The
block analogue of `NLAlib.Computation.IsFramed`, which reads whole buffers. -/
def ReadsOnly (F : Store P K → Prop) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ s s', F s → (∀ x ∈ rs, s'.shape[x.1]? = s.shape[x.1]?) →
    (∀ q, ∀ x ∈ rs, ∀ j < x.2.2, s'.read q x.1 (x.2.1 + j) = s.read q x.1 (x.2.1 + j)) → F s'

/-- Every block of `rs` is disjoint from every block of `fp`; with
`NLAlib.Computation.blockDisjoint_iff` the goal is linear arithmetic. -/
def BlocksDisjoint (rs fp : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ rs, ∀ y ∈ fp, blockDisjoint x y = true

/-- A store modifies nothing of itself. -/
theorem Modifies.refl (fp : List (ℕ × ℕ × ℕ)) (s : Store P K) : Modifies fp s s :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

/-- Footprints in sequence add. -/
theorem Modifies.trans {fp₁ fp₂ : List (ℕ × ℕ × ℕ)} {s s₁ s₂ : Store P K}
    (h₁ : Modifies fp₁ s s₁) (h₂ : Modifies fp₂ s₁ s₂) : Modifies (fp₁ ++ fp₂) s s₂ :=
  ⟨h₂.1.trans h₁.1, fun q b i hb => (h₂.2 q b i fun x hx => hb x (List.mem_append_right _ hx)).trans
    (h₁.2 q b i fun x hx => hb x (List.mem_append_left _ hx))⟩

/-- A footprint may be enlarged. -/
theorem Modifies.mono {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hfp : ∀ x ∈ fp, x ∈ fp') : Modifies fp' s s' :=
  ⟨h.1, fun q b i hb => h.2 q b i fun x hx => hb x (hfp x hx)⟩

/-- A footprint may be replaced by one that covers its cells: every cell disjoint from `fp'` is
disjoint from `fp`. -/
theorem Modifies.of_cells {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hc : ∀ b i, (∀ x ∈ fp', blockDisjoint (b, i, 1) x = true) →
      ∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) : Modifies fp' s s' :=
  ⟨h.1, fun q b i hb => h.2 q b i (hc b i hb)⟩

/-- A scalar write modifies its cell. -/
theorem Modifies.of_write {p : P} {b i : ℕ} {v : K} {s s' : Store P K}
    (h : s.write p b i v = some s') : Modifies [(b, i, 1)] s s' := by
  refine ⟨Store.shape_of_write_eq_some h, fun q b' i' hb =>
    Store.read_of_write_eq_some_of_ne h ?_⟩
  have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
  dsimp only at this
  omega

/-- Block writes modify their blocks. -/
theorem Modifies.of_writeBlocks {p : P} {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)}
    {s s' : Store P K} (h : s.writeBlocks p bs ys = some s') : Modifies bs s s' := by
  refine ⟨Store.shape_of_writeBlocks_eq_some h, fun q b i hb =>
    Store.read_of_writeBlocks_eq_some_of_forall h fun x hx => ?_⟩
  have := blockDisjoint_iff.mp (hb x hx)
  dsimp only at this
  omega

/-- A block write modifies its block. -/
theorem Modifies.of_writeBlock {p : P} {b o : ℕ} {y : Array K} {s s' : Store P K}
    (h : s.writeBlock p b o y = some s') : Modifies [(b, o, y.size)] s s' := by
  refine ⟨Store.shape_of_writeBlock_eq_some h, fun q b' i hb =>
    Store.read_of_writeBlock_eq_some_of_ne h ?_⟩
  have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
  dsimp only at this
  omega

/-- A kernel call modifies its output blocks. -/
theorem Modifies.of_kcallStore {C : Type} {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s s' : Store P K} (h : I.kcallStore o p ds ins outs s = some s') :
    Modifies (kcallBlocks outs (I.kshape o ds).2) s s' := by
  unfold Interp.kcallStore at h
  split_ifs at h
  obtain ⟨xs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, -, h⟩ := Option.bind_eq_some_iff.mp h
  exact Modifies.of_writeBlocks h

/-- **The frame of a read set**: a predicate that reads only `rs` survives a change confined to
blocks disjoint from `rs`. -/
theorem ReadsOnly.of_modifies {F : Store P K → Prop} {rs fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hF : ReadsOnly F rs) (h : F s) (hm : Modifies fp s s')
    (hd : BlocksDisjoint rs fp) : F s' := by
  refine hF s s' h (fun x _ => by rw [hm.1]) fun q x hx j hj => hm.2 q _ _ fun y hy => ?_
  have := blockDisjoint_iff.mp (hd x hx y hy)
  rw [blockDisjoint_iff]
  dsimp only at this ⊢
  omega

/-- A conjunction reads the union of the read sets. -/
theorem ReadsOnly.and {F G : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (hG : ReadsOnly G ts) : ReadsOnly (fun s => F s ∧ G s) (rs ++ ts) :=
  fun s s' h hsh hrd => ⟨hF s s' h.1 (fun x hx => hsh x (List.mem_append_left _ hx))
      fun q x hx => hrd q x (List.mem_append_left _ hx),
    hG s s' h.2 (fun x hx => hsh x (List.mem_append_right _ hx))
      fun q x hx => hrd q x (List.mem_append_right _ hx)⟩

/-- A read set may be enlarged. -/
theorem ReadsOnly.mono {F : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (h : ∀ x ∈ rs, x ∈ ts) : ReadsOnly F ts :=
  fun s s' hs hsh hrd => hF s s' hs (fun x hx => hsh x (h x hx)) fun q x hx => hrd q x (h x hx)

/-- A predicate reading only buffers below the top survives pushing a buffer. -/
theorem ReadsOnly.push {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 < s.size) (y : P × Array (Option K)) :
    F (s.push y) :=
  hF s _ h (fun x hx => Store.getElem?_shape_push_of_lt y (hrs x hx)) fun _ x hx _ _ =>
    Store.read_push_of_ne (Nat.ne_of_lt (hrs x hx))

/-- A predicate reading only buffers below the top survives popping the top buffer. -/
theorem ReadsOnly.pop {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 + 1 < s.size) : F s.pop := by
  refine hF s _ h (fun x hx => ?_) fun _ x hx _ _ =>
    Store.read_pop_of_lt (by have := hrs x hx; omega)
  have := hrs x hx
  rw [Store.shape_pop, Array.getElem?_pop, if_pos (by rw [Store.size_shape]; omega)]

/-- **A predicate on buffers below `N`**: a predicate reading only blocks of buffers below `N`
survives a store with the same shapes and reads below `N` (the store after allocations or
releases on top). -/
theorem ReadsOnly.of_read_eq_below {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {N : ℕ}
    {s s' : Store P K} (hF : ReadsOnly F rs) (hrs : ∀ x ∈ rs, x.1 < N) (h : F s)
    (hsh : ∀ x < N, s'.shape[x]? = s.shape[x]?)
    (hr : ∀ q x i, x < N → s'.read q x i = s.read q x i) : F s' :=
  hF s s' h (fun x hx => hsh x.1 (hrs x hx)) fun q x hx _ _ => hr q x.1 _ (hrs x hx)

/-- One stored cell reads only itself. -/
theorem readsOnly_read (q : P) (b i : ℕ) (v : Option K) :
    ReadsOnly (fun s : Store P K => s.read q b i = v) [(b, i, 1)] :=
  fun s s' hs _ hrd => by simpa using (hrd q (b, i, 1) List.mem_cons_self 0 Nat.one_pos).trans hs

/-- **A bundle of stored cells**: every cell `(q, b, i, v)` of `cs` reads `v` at tag `q` in buffer
`b`, index `i`. One predicate for many scalar facts, so that a program proof carries them across a
step by one frame fact (`NLAlib.Computation.readsOnly_cellsHold`). -/
def CellsHold (cs : List (P × ℕ × ℕ × Option K)) (s : Store P K) : Prop :=
  ∀ c ∈ cs, s.read c.1 c.2.1 c.2.2.1 = c.2.2.2

/-- The read set of a bundle of cells: one one-cell block per cell. -/
def cellBlocks (cs : List (P × ℕ × ℕ × Option K)) : List (ℕ × ℕ × ℕ) :=
  cs.map fun c => (c.2.1, c.2.2.1, 1)

/-- A bundle of cells reads only its cells. -/
theorem readsOnly_cellsHold (cs : List (P × ℕ × ℕ × Option K)) :
    ReadsOnly (CellsHold cs) (cellBlocks cs) := fun _ _ hs _ hrd c hc => by
  simpa using (hrd c.1 _ (List.mem_map_of_mem hc) 0 Nat.one_pos).trans (hs c hc)

/-- **A block of cells with a property each**: the predicate that every cell $w < N$ of buffer `b`
at tag `q` satisfies `R w` reads only the block `(b, 0, N)` (stored words of a tape, a sample
block). -/
theorem readsOnly_forall_read (q : P) (b N : ℕ) (R : ℕ → Option K → Prop) :
    ReadsOnly (fun s : Store P K => ∀ w < N, R w (s.read q b w)) [(b, 0, N)] :=
  fun _ _ hs _ hrd w hw => by
    have e := hrd q (b, 0, N) List.mem_cons_self w hw
    simp only [Nat.zero_add] at e
    exact e ▸ hs w hw

/-- A cell of a bundle reads its value. -/
theorem CellsHold.read {cs : List (P × ℕ × ℕ × Option K)} {s : Store P K} {q : P} {b i : ℕ}
    {v : Option K} (h : CellsHold cs s) (hc : (q, b, i, v) ∈ cs) : s.read q b i = v :=
  h _ hc

/-- The empty bundle. -/
theorem cellsHold_nil (s : Store P K) : CellsHold [] s := fun _ h => absurd h List.not_mem_nil

/-- A bundle with one more cell. -/
theorem CellsHold.cons {cs : List (P × ℕ × ℕ × Option K)} {s : Store P K} {q : P} {b i : ℕ}
    {v : Option K} (hv : s.read q b i = v) (h : CellsHold cs s) :
    CellsHold ((q, b, i, v) :: cs) s :=
  fun c hc => (List.mem_cons.mp hc).elim (fun e => e ▸ hv) (h c)

/-- A bundle of two bundles. -/
theorem CellsHold.append {cs ds : List (P × ℕ × ℕ × Option K)} {s : Store P K}
    (h : CellsHold cs s) (h' : CellsHold ds s) : CellsHold (cs ++ ds) s :=
  fun c hc => (List.mem_append.mp hc).elim (h c) (h' c)

/-- A sub-bundle of a bundle. -/
theorem CellsHold.sub {cs ds : List (P × ℕ × ℕ × Option K)} {s : Store P K} (h : CellsHold cs s)
    (hsub : ∀ c ∈ ds, c ∈ cs) : CellsHold ds s :=
  fun c hc => h c (hsub c hc)

/-- A writable block reads only itself (its shape). -/
theorem readsOnly_writable (p : P) (b off n : ℕ) :
    ReadsOnly (fun s : Store P K => Writable s p b off n) [(b, off, n)] :=
  fun _ _ hs hsh _ => hs.of_getElem?_shape_eq (hsh _ List.mem_cons_self)

/-- A decoded vector reads only its block. -/
theorem readsOnly_readsDecoded {N : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ) (x : Fin N → ℝ) :
    ReadsOnly (fun s : Store P K => ReadsDecoded s dec p b off x) [(b, off, N)] :=
  fun _ _ hs _ hrd => hs.of_read_eq fun i hi => hrd p _ List.mem_cons_self i hi

/-- A decoded matrix reads only its block. -/
theorem readsOnly_holdsDecoded {N k : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ)
    (M : Matrix (Fin N) (Fin k) ℝ) :
    ReadsOnly (fun s : Store P K => HoldsDecoded s dec p b off M) [(b, off, N * k)] := by
  intro s s' hs _ hrd i j
  obtain ⟨w, hw, hd⟩ := hs i j
  have hij : (i : ℕ) + N * j < N * k := by nlinarith [i.2, j.2]
  refine ⟨w, ?_, hd⟩
  have := hrd p _ List.mem_cons_self _ hij
  simp only [← Nat.add_assoc] at this
  rw [this, hw]

/-- A buffer-framed precondition survives a change confined to other buffers. -/
theorem IsFramed.of_modifies {pre : Store P K → Prop} {ro : List ℕ} {fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hf : IsFramed pre ro) (h : pre s) (hm : Modifies fp s s')
    (hro : ∀ x ∈ fp, x.1 ∉ ro) : pre s' := by
  refine hf s s' h (fun _ _ => by rw [hm.1]) fun q b hb i => hm.2 q b i fun x hx => ?_
  exact blockDisjoint_iff.mpr (Or.inl fun he => hro x hx (he ▸ hb))

/-- **The canonical block of a stored matrix**: `rows × cols` entries of `width` words from
offset `off` of buffer `b`, of length `rows * cols * width`. Kernel and routine specifications
state their footprints in this form, so that equal blocks are syntactically equal and the
lengths of different statements (`2 * (r * k)`, `k * r * 2`) need no rewriting. -/
def matBlock (b off rows cols width : ℕ) : ℕ × ℕ × ℕ := (b, off, rows * cols * width)

/-- Blocks in different buffers are disjoint. -/
theorem blockDisjoint_of_fst_ne {x y : ℕ × ℕ × ℕ} (h : x.1 ≠ y.1) :
    blockDisjoint x y = true :=
  blockDisjoint_iff.mpr (Or.inl h)

/-- A block that ends before another starts in the same buffer is disjoint from it: the layout
lemma for blocks packed one after another. -/
theorem blockDisjoint_of_add_le {x y : ℕ × ℕ × ℕ} (h : x.2.1 + x.2.2 ≤ y.2.1) :
    blockDisjoint x y = true :=
  blockDisjoint_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- The length of a matrix block does not depend on the order of its dimensions. -/
theorem matBlock_comm (b off rows cols width : ℕ) :
    matBlock b off rows cols width = (b, off, cols * rows * width) := by
  rw [matBlock, Nat.mul_comm rows cols]

/-- **Scratch on top, dropped**: a run from the store with a buffer pushed, whose footprint
includes a block of the pushed buffer, modifies in the original store, after the pop, only the
blocks below it. -/
theorem Modifies.pop_top {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K} {y : P × Array (Option K)}
    {o l : ℕ} (h : Modifies (fp ++ [(s.size, o, l)]) (s.push y) s') : Modifies fp s s'.pop := by
  have hsz : s'.size = s.size + 1 := by
    rw [← Store.size_eq_of_shape_eq h.1.symm, Array.size_push]
  refine ⟨?_, fun q b i hb => ?_⟩
  · rw [Store.shape_pop, h.1, Store.shape, Array.map_push, Array.pop_push]
    rfl
  · by_cases hlt : b < s.size
    · rw [Store.read_pop_of_lt (by omega), h.2 q b i fun x hx => ?_,
        Store.read_push_of_ne (by omega)]
      rcases List.mem_append.mp hx with hx | hx
      · exact hb x hx
      · rw [List.mem_singleton.mp hx]
        exact blockDisjoint_of_fst_ne (Nat.ne_of_lt hlt)
    · rw [Store.read_eq_none_of_size_le (by rw [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by omega)]

/-- Scratch on top: a run from the store with a buffer pushed, popped at the end, modifies in
the original store only the blocks it modified below the top. -/
theorem Modifies.pop {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K} {y : P × Array (Option K)}
    (h : Modifies fp (s.push y) s') : Modifies fp s s'.pop :=
  Modifies.pop_top (o := 0) (l := 0) (h.mono fun _ hx => List.mem_append_left _ hx)

/-- A writable block stays writable through any modification (by the shape clause; the frame
rule does not apply to a block that was just written). -/
theorem Writable.of_modifies {p : P} {b off n : ℕ} {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K}
    (h : Writable s p b off n) (hm : Modifies fp s s') : Writable s' p b off n :=
  h.of_shape_eq hm.1

/-- Writable blocks stay writable through any modification. -/
theorem WritableBlocks.of_modifies {p : P} {bs fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K}
    (h : WritableBlocks s p bs) (hm : Modifies fp s s') : WritableBlocks s' p bs :=
  fun x hx => (h x hx).of_modifies hm

end Footprint

/-! ### Modes, weakest preconditions and triples -/

/-- **The mode of a judgement**: `total` asserts that the run succeeds, `liberal` only constrains
a successful run (Dijkstra's weakest liberal precondition). -/
inductive Mode where
  /-- The run succeeds and its final state satisfies the postcondition. -/
  | total
  /-- If the run succeeds, its final state satisfies the postcondition. -/
  | liberal

/-- What a mode needs of the arithmetic: the total mode needs `A`, the liberal mode nothing. A
specification proved for every mode `m` under `m.Needs A` gives, at `liberal`, the refinement
without `A` and, at `total`, success under `A`, from one proof. -/
def Mode.Needs : Mode → Prop → Prop
  | .total, A => A
  | .liberal, _ => True

/-- The outcome `o` of a step satisfies `Q` in mode `m`. -/
def Mode.Sat {α : Type} : Mode → (α → Prop) → Option α → Prop
  | .total, Q, o => ∃ x, o = some x ∧ Q x
  | .liberal, Q, o => ∀ x, o = some x → Q x

/-- A satisfied outcome satisfies a weaker predicate. -/
theorem Mode.Sat.mono {α : Type} {m : Mode} {Q Q' : α → Prop} {o : Option α}
    (h : m.Sat Q o) (hQ : ∀ x, Q x → Q' x) : m.Sat Q' o := by
  cases m
  · obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx, hQ x hq⟩
  · exact fun x hx => hQ x (h x hx)

/-- A satisfied outcome is also an outcome that occurred. -/
theorem Mode.Sat.and_eq {α : Type} {m : Mode} {Q : α → Prop} {o : Option α} (h : m.Sat Q o) :
    m.Sat (fun x => o = some x ∧ Q x) o := by
  cases m
  · obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx, hx, hq⟩
  · exact fun x hx => ⟨hx, h x hx⟩

/-- A successful outcome satisfies `Q` iff its value does. -/
theorem Mode.sat_some {α : Type} {m : Mode} {Q : α → Prop} {x : α} :
    m.Sat Q (some x) ↔ Q x := by
  cases m <;> simp [Mode.Sat]

/-- An outcome in sequence: the bind of the outcome monad. -/
theorem Mode.sat_bind {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α}
    {f : α → Option β} : m.Sat Q (o.bind f) ↔ m.Sat (fun x => m.Sat Q (f x)) o := by
  cases m <;> cases o <;> simp [Mode.Sat]

/-- An outcome mapped. -/
theorem Mode.sat_map {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α} {f : α → β} :
    m.Sat Q (o.map f) ↔ m.Sat (fun x => Q (f x)) o := by
  cases m <;> cases o <;> simp [Mode.Sat]

/-- A requirement of the total mode holds in the liberal mode. -/
theorem Mode.needs_liberal (A : Prop) : Mode.liberal.Needs A := trivial

/-- A requirement that holds holds in every mode. -/
theorem Mode.needs_of {A : Prop} (h : A) (m : Mode) : m.Needs A := by
  cases m
  · exact h
  · trivial

/-- A requirement of a conjunction is the conjunction of the requirements. -/
theorem Mode.needs_and {m : Mode} {A B : Prop} : m.Needs (A ∧ B) ↔ m.Needs A ∧ m.Needs B := by
  cases m
  · exact Iff.rfl
  · exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- A requirement implies its consequences. -/
theorem Mode.Needs.mono {m : Mode} {A B : Prop} (h : A → B) (hA : m.Needs A) : m.Needs B := by
  cases m
  · exact h hA
  · trivial

/-- A requirement used to establish another. -/
theorem Mode.Needs.elim {m : Mode} {A B : Prop} (hA : m.Needs A) (h : A → m.Needs B) :
    m.Needs B := by
  cases m
  · exact h hA
  · trivial

omit [DecidableEq P] in
/-- A state whose tape positions are those of another. -/
def PosKept {C : Type} (st st' : St P K C) : Prop := st'.pos = st.pos

variable [AddMonoid C]

/-- A state with its count raised by `c`: the state after a charged step that writes nothing. -/
def St.addCnt (st : St P K C) (c : C) : St P K C := { st with cnt := st.cnt + c }

/-- **The weakest precondition** of `s` for `Q` in mode `m`: the run of `s` from `st` under `I`
ends (`total`: succeeds and ends; `liberal`: if it succeeds, ends) in a state satisfying `Q`. -/
def Wp (m : Mode) (I : Interp P ι K C) (s : Stmt P ι ℕ ℕ) (Q : St P K C → Prop)
    (st : St P K C) : Prop :=
  m.Sat Q (exec I s st)

/-- **A triple** in mode `m`: from every state satisfying `pre`, the run of `s` ends in a state
related to the start by `post`. -/
def Triple (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (post : St P K C → St P K C → Prop) : Prop :=
  ∀ st, pre st → Wp m I s (post st) st

section Core

variable {m : Mode} {I : Interp P ι K C} {s t : Stmt P ι ℕ ℕ} {Q Q' : St P K C → Prop}
  {st : St P K C}

/-- The weakest precondition is monotone in the postcondition. -/
theorem wp_mono (h : Wp m I s Q st) (hQ : ∀ st', Q st' → Q' st') : Wp m I s Q' st :=
  Mode.Sat.mono h hQ

/-- **The application rule**: a triple gives the weakest precondition of any postcondition its
own implies, at a state satisfying its precondition. -/
theorem Triple.wp_of {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : pre st) (hQ : ∀ st', post st st' → Q st') :
    Wp m I s Q st :=
  wp_mono (h st hpre) hQ

/-- **The rule of consequence.** -/
theorem Triple.conseq {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : ∀ st, pre' st → pre st)
    (hpost : ∀ st st', pre' st → post st st' → post' st st') : Triple m I pre' s post' :=
  fun st hst => wp_mono (h st (hpre st hst)) fun st' hp => hpost st st' hst hp

/-- A total triple is a liberal one. -/
theorem Triple.liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) : Triple .liberal I pre s post := by
  intro st hst x hx
  obtain ⟨y, hy, hq⟩ := h st hst
  rw [hy] at hx
  cases hx
  exact hq

/-- A liberal triple and success give a total triple (the run is deterministic). -/
theorem Triple.total_of_liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .liberal I pre s post) (hs : ∀ st, pre st → ∃ st', exec I s st = some st') :
    Triple .total I pre s post := by
  intro st hst
  obtain ⟨st', hs⟩ := hs st hst
  exact ⟨st', hs, h st hst st' hs⟩

/-- A total triple: the run succeeds. -/
theorem Triple.exists_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) (hpre : pre st) :
    ∃ st', exec I s st = some st' ∧ post st st' :=
  h st hpre

/-- A liberal triple: what a successful run satisfies. -/
theorem Triple.holds_of_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    {st' : St P K C} (h : Triple .liberal I pre s post) (hpre : pre st)
    (hrun : exec I s st = some st') : post st st' :=
  h st hpre st' hrun

/-! #### Statement rules -/

/-- `skip`. -/
theorem wp_skip : Wp m I .skip Q st ↔ Q st := by
  rw [Wp, exec_skip, Mode.sat_some]

/-- **Sequence**: the weakest precondition of `t` is the postcondition of `s`. -/
theorem wp_seq : Wp m I (.seq s t) Q st ↔ Wp m I s (Wp m I t Q) st := by
  rw [Wp, exec_seq, Mode.sat_bind]
  rfl

/-- A scalar instruction. -/
theorem wp_instr (i : Instr P ℕ ℕ) :
    Wp m I (.instr i) Q st ↔
      m.Sat (fun r => Q ({ st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }))
        (i.run I.sem I.tape st.store st.pos) := by
  rw [Wp, exec_instr, Mode.sat_map]

/-- **Allocation**: the body runs from the state with the fresh buffer at handle
`st.store.size`, and the postcondition is read after its release. -/
theorem wp_alloc (p : P) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) :
    Wp m I (.alloc p len body) Q st ↔
      Wp m I (body st.store.size) (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) := by
  rw [Wp, exec_alloc, Mode.sat_map]
  rfl

/-- **A conditional**, from the comparison step. -/
theorem wp_ite (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) :
    Wp m I (.ite p c x y s t) Q st ↔
      m.Sat (fun r => if r.1 then Wp m I s Q r.2 else Wp m I t Q r.2) (cmpStep I p c x y st) := by
  rw [Wp, exec_ite, Mode.sat_bind]
  refine iff_of_eq (congrArg (m.Sat · _) (funext fun r => ?_))
  split <;> rfl

/-- A conditional on stored values: with the cells read and compared, the branch taken. -/
theorem wp_ite_of_read {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {a b : K} {r : Bool}
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hr : I.sem.cmp p c a b = some r) :
    Wp m I (.ite p c x y s t) Q st ↔
      if r then Wp m I s Q (st.addCnt (I.charge (.cmp p)))
      else Wp m I t Q (st.addCnt (I.charge (.cmp p))) := by
  rw [wp_ite]
  simp only [cmpStep, hx, hy, hr, Option.bind_some, Option.map_some, Mode.sat_some]
  rfl

/-- **An index binder** on a stored value: the body runs at every converted value $k$ with the
fact $k \le \mathit{bound}$; the total mode needs the bound. -/
theorem wp_bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {v : K} (hx : st.store.read p x.buf x.idx.eval = some v)
    (h : m.Sat (fun k => m.Needs (k ≤ bound.eval) ∧
      (k ≤ bound.eval → Wp m I (body k) Q (st.addCnt (I.charge (.toNat p)))))
      (I.sem.toNat p v)) :
    Wp m I (.bindIdx p x bound body) Q st := by
  rw [Wp, exec_bindIdx, toNatStep, hx, Option.bind_some]
  cases hk : I.sem.toNat p v with
  | none =>
    rw [hk] at h
    cases m
    · obtain ⟨_, h, _⟩ := h
      cases h
    · intro x hx
      cases hx
  | some k =>
    rw [hk, Mode.sat_some] at h
    rw [Option.map_some, Option.bind_some]
    dsimp only
    split_ifs with hkb
    · exact h.2 hkb
    · cases m
      · exact absurd h.1 hkb
      · intro x hx
        cases hx

/-- **A kernel call**: the black box's store, charged once. -/
theorem wp_kcall (o : ι) (p : P) (dims : List (IExp ℕ)) (ins outs : List (ℕ × IExp ℕ)) :
    Wp m I (.kcall o p dims ins outs) Q st ↔
      m.Sat (fun s => Q ({ st with store := s } |>.addCnt
          (I.charge (.kcall p o (dims.map IExp.eval)))))
        (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
          (outs.map fun x => (x.1, x.2.eval)) st.store) := by
  rw [Wp, exec_kcall, Mode.sat_map]
  rfl

/-- A named kernel runs as its body (the label is transparent to the logic). -/
theorem wp_named (name : String) (args : List (Arg ℕ ℕ)) :
    Wp m I (.named name args s) Q st ↔ Wp m I s Q st := by
  rw [Wp, exec_named, Wp]

/-! #### Composite rules -/

/-- **Sequence of triples**: the first routine's output feeds the second (`hmid`), and the
composite postcondition names the intermediate state. -/
theorem Triple.seq {pre pre₂ : St P K C → Prop} {mid post : St P K C → St P K C → Prop}
    (h₁ : Triple m I pre s mid) (h₂ : Triple m I pre₂ t post)
    (hmid : ∀ st st₁, pre st → mid st st₁ → pre₂ st₁) :
    Triple m I pre (.seq s t) fun st st₂ => ∃ st₁, mid st st₁ ∧ post st₁ st₂ :=
  fun st hst => (wp_seq).mpr <| wp_mono (h₁ st hst) fun st₁ hmid₁ =>
    wp_mono (h₂ st₁ (hmid st st₁ hst hmid₁)) fun _ hp => ⟨st₁, hmid₁, hp⟩

/-- **A loop with an invariant**: `Inv st₀ k` holds of the state after `k` iterations from
`st₀`, and the body keeps it. -/
theorem Triple.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {pre : St P K C → Prop}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Triple m I (Inv st₀ k) (body k) fun _ st' => Inv st₀ (k + 1) st') :
    Triple m I pre (.loop n body) fun st₀ st' => Inv st₀ n.eval st' := by
  intro st₀ hst
  rw [Wp, exec_loop]
  suffices ∀ j ≤ n.eval, m.Sat (Inv st₀ j)
      ((List.range j).foldlM (fun st i => exec I (body i) st) st₀) from this _ le_rfl
  intro j
  induction j with
  | zero => exact fun _ => Mode.sat_some.mpr (h0 st₀ hst)
  | succ j ih =>
    intro hj
    rw [List.foldlM_range_succ, Option.bind_eq_bind, Mode.sat_bind]
    exact (ih (by omega)).mono fun st₁ h₁ => hstep st₀ hst j (by omega) st₁ h₁

/-- **A fueled loop with an invariant**: `Inv st₀ j` holds of the state before the $j$-th test;
a test that holds runs the body to `Inv st₀ (j + 1)`, and in the total mode leaves fuel for the
next test. The final state is the state of a failed test. -/
theorem Triple.whileFuel {fuel : IExp ℕ} {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {body : Stmt P ι ℕ ℕ} {pre : St P K C → Prop} (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → m.Needs (0 < fuel.eval) ∧ Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st →
      m.Sat (fun r => r.1 = true → m.Needs (j + 1 < fuel.eval) ∧
        Wp m I body (Inv st₀ (j + 1)) r.2) (cmpStep I p c x y st)) :
    Triple m I pre (.whileFuel fuel p c x y body) fun st₀ st' =>
      ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st') := by
  intro st₀ hst
  let Post : St P K C → Prop := fun st' =>
    ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st')
  let R : ℕ → St P K C × Bool → Prop := fun i r =>
    (r.2 = true → Inv st₀ i r.1 ∧ m.Needs (i < fuel.eval)) ∧ (r.2 = false → Post r.1)
  have hfold : ∀ i ≤ fuel.eval, m.Sat (R i) ((List.range i).foldlM (fun (s : St P K C × Bool) _ =>
      if s.2 then (cmpStep I p c x y s.1).bind fun r =>
        if r.1 then (exec I body r.2).map fun st' => (st', true) else some (r.2, false)
      else some s) (st₀, true)) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨hf, h0'⟩ := h0 st₀ hst
      exact Mode.sat_some.mpr ⟨fun _ => ⟨h0', hf⟩, fun h => absurd h (by simp)⟩
    | succ i ih =>
      intro hi
      rw [List.foldlM_range_succ, Option.bind_eq_bind, Mode.sat_bind]
      refine (ih (by omega)).mono fun ⟨s, b⟩ ⟨hT, hF⟩ => ?_
      cases b with
      | false => exact Mode.sat_some.mpr ⟨fun h => absurd h (by simp), hF⟩
      | true =>
        obtain ⟨hinv, -⟩ := hT rfl
        rw [if_pos rfl, Mode.sat_bind]
        refine (hstep st₀ hst i s hinv).and_eq.mono fun ⟨r, s'⟩ ⟨heq, hr⟩ => ?_
        cases r with
        | false => exact Mode.sat_some.mpr ⟨fun h => absurd h (by simp), fun _ => ⟨i, s, hinv, heq⟩⟩
        | true =>
          obtain ⟨hneeds, hwp⟩ := hr rfl
          rw [if_pos rfl, Mode.sat_map]
          exact Mode.Sat.mono hwp fun st' h' => ⟨fun _ => ⟨h', hneeds⟩, fun h => absurd h (by simp)⟩
  rw [Wp, exec, Mode.sat_bind]
  refine (hfold _ le_rfl).mono fun ⟨s, b⟩ ⟨hT, hF⟩ => ?_
  cases b with
  | false => exact Mode.sat_some.mpr (hF rfl)
  | true =>
    cases m
    · exact absurd (hT rfl).2 (lt_irrefl _)
    · intro _ h
      cases h

/-- **Scoped scratch**: a body that runs from the state with the fresh buffer at the relative
handle `b` (the size of the store, fixed by the precondition) gives the allocation, its
postcondition read after the release. -/
theorem Triple.alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre' (body b) post') (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Triple m I pre (.alloc p len body) post := by
  intro st hst
  rw [wp_alloc, hb st hst]
  exact wp_mono (h _ (hpre st hst)) fun st₂ hp => hpost st st₂ hst hp

omit [AddMonoid C] in
/-- The allocated state has one buffer more. -/
theorem St.size_allocate (st : St P K C) (p : P) (len w : ℕ) :
    (st.allocate p len w).store.size = st.store.size + 1 := by
  simp [St.allocate]

omit [AddMonoid C] in
/-- The fresh buffer is writable on its whole length, at its relative handle. -/
theorem St.writable_allocate (st : St P K C) (p : P) (len w : ℕ) :
    Writable (st.allocate p len w).store p st.store.size 0 len := by
  intro i hi
  refine ⟨len, ?_, by omega⟩
  rw [St.shape_allocate, Array.getElem?_push, if_pos (Store.size_shape _).symm]

omit [AddMonoid C] in
/-- Releasing the top buffer keeps every read below it. -/
theorem St.read_release_of_lt (st : St P K C) (p : P) (len w : ℕ) (q : P) {b : ℕ}
    (hb : b + 1 < st.store.size) (i : ℕ) :
    (st.release p len w).store.read q b i = st.store.read q b i :=
  Store.read_pop_of_lt (by omega)

end Core

/-! ### Builders -/

section Builder

variable {m : Mode} {I : Interp P ι K C} {Q : St P K C → Prop} {st : St P K C}

/-- **A builder in sequence**: a composable prefix, then the rest. -/
theorem wp_run_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : ExecutionComposable I x) :
    Wp m I (x >>= f).run Q st ↔ Wp m I x.run (Wp m I (f ()).run Q) st := by
  rw [Wp, hx f st, Mode.sat_bind]
  rfl

/-- **An allocation in a builder**: the rest of the block runs on the fresh handle. -/
theorem wp_run_allocBind {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} :
    Wp m I (Builder.alloc p len >>= f).run Q st ↔
      Wp m I (f st.store.size).run (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) :=
  wp_alloc p len fun b => (f b).run

/-- The empty builder. -/
theorem wp_run_pure : Wp m I (pure () : Builder P ι ℕ ℕ Unit).run Q st ↔ Q st :=
  wp_skip

/-- A statement is a composable prefix. -/
theorem executionComposable_stmt (s : Stmt P ι ℕ ℕ) :
    ExecutionComposable I (Builder.stmt s) :=
  executionComposable_single I fun _ => rfl

/-- A scalar instruction is a composable prefix. -/
theorem executionComposable_ins (i : Instr P ℕ ℕ) :
    ExecutionComposable I (Builder.ins (ι := ι) i) :=
  executionComposable_single I fun _ => rfl

/-- A scope is a composable prefix. -/
theorem executionComposable_scope (x : Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.scope x) :=
  executionComposable_single I fun _ => rfl

/-- A named kernel is a composable prefix. -/
theorem executionComposable_named (name : String) (args : List (Arg ℕ ℕ))
    (x : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.named name args x) :=
  executionComposable_single I fun _ => rfl

/-- A loop is a composable prefix. -/
theorem executionComposable_forRange (n : IExp ℕ) (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.forRange n body) :=
  executionComposable_single I fun _ => rfl

/-- A conditional is a composable prefix. -/
theorem executionComposable_ifThenElse (p : P) (c : CmpOp) (x y : Cell ℕ ℕ)
    (t e : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.ifThenElse p c x y t e) :=
  executionComposable_single I fun _ => rfl

/-- An index binder is a composable prefix. -/
theorem executionComposable_bindIdx (p : P) (x : Cell ℕ ℕ) (bound : IExp ℕ)
    (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.bindIdx p x bound body) :=
  executionComposable_single I fun _ => rfl

end Builder

end NLAlib.Computation
