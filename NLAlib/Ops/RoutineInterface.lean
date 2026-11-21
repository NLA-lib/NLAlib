/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import NLAlib.Ops.Logic.Writes

/-!
# The interface of a routine

A routine (`NLAlib.Ops.Routine`) is a fixed tree with an interface: its dimensions and, for each
operand (`NLAlib.Ops.Port`), how it is used (`NLAlib.Ops.Access`: read, written, updated in
place, or isolated) and its length as a function of the dimensions. Operands are written with
`NLAlib.Ops.Port.read`, `.write`, `.update`, `.isolated`. This file defines interfaces and the
separation they require; the judgment and certificates are in `NLAlib/Ops/Routine.lean`.

An operand may continue the operand before it (`NLAlib.Ops.Port.continuing`): its block is in
the same buffer and starts where that block ends, as the columns appended to a stored basis. Its
position is fixed by the interface, so a call supplies one operand for each region of the
interface (`NLAlib.Ops.Port.regions`), and `NLAlib.Ops.Routine.operands` gives the positions of
all operands. Separation is required of the regions.

A written operand may be unreported (`NLAlib.Ops.Port.unreported`): the judgment says nothing
of its final contents. Caller-supplied scratch and a matrix destroyed in place are such
operands.

The separation of operands is one of two fixed rules named by the interface
(`NLAlib.Ops.Separation`: by buffer, or by block so that operands may be disjoint blocks of one
buffer); the author cannot state another. Under either rule, operands that are only read may
overlap, except an isolated one.

A routine declares the number of tape positions it draws; one whose draws depend on the data
declares none.

## Main definitions

* `NLAlib.Ops.Access`, `NLAlib.Ops.Port`, `NLAlib.Ops.Routine`: interfaces and routines.
* `NLAlib.Ops.Separation`, `NLAlib.Ops.Routine.SeparatedAt`: the two fixed separation rules
  and the separation a routine requires.

## Main results

* `NLAlib.Ops.Routine.separated_iff_pairwise`: separation by buffer is a condition on pairs of
  operands.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}


/-- How a routine uses an operand. -/
inductive Access where
  /-- The block is read and left unchanged. -/
  | read
  /-- The block is written; its initial contents are not read. -/
  | write
  /-- The block is read and written in place. -/
  | update
  /-- The block is read and left unchanged, and it is apart from every other operand: in a
  buffer of its own under separation by buffer, disjoint from every other block under separation
  by block. Operands that are merely read may overlap one another; an isolated operand may not.
  Stored data forwarded to a linked operation needs exactly this, because the operation must
  find it unchanged whatever the routine writes or passes on. -/
  | isolated
  deriving DecidableEq

/-- The operand has contents that the routine may read. -/
def Access.readable : Access → Bool
  | .write => false
  | _ => true

/-- The operand is one that the routine may write. -/
def Access.writable : Access → Bool
  | .write => true
  | .update => true
  | _ => false

/-- The operand is read and never written. -/
def Access.readOnly : Access → Bool
  | .read => true
  | .isolated => true
  | _ => false

/-- The operand is isolated. -/
def Access.isIsolated : Access → Bool
  | .isolated => true
  | _ => false

/-- Two operands with these accesses must be apart: every pair except two operands that are
merely read. -/
def Access.apart : Access → Access → Bool
  | .read, .read => false
  | _, _ => true

/-- The separation rule of an interface, chosen from two fixed rules. -/
inductive Separation where
  /-- Operands are separated by buffer (`NLAlib.Ops.Routine.Separated`). -/
  | buffers
  /-- Operands are separated by block (`NLAlib.Ops.Routine.SeparatedBlocks`): operands may be
  blocks of one buffer at different offsets. -/
  | blocks
  deriving DecidableEq

/-- The access of a region made of two consecutive blocks: written if either is, read if
either is, and isolated if neither is written and either is isolated. -/
def Access.join (a b : Access) : Access :=
  match a.writable || b.writable, a.readable || b.readable, a.isIsolated || b.isIsolated with
  | true, true, _ => .update
  | true, false, _ => .write
  | false, _, true => .isolated
  | false, _, false => .read

/-- One operand of an interface: how it is used, its length at the dimensions, and whether its
block continues that of the operand before it. -/
structure Port where
  /-- How the routine uses the operand. -/
  access : Access
  /-- The length of the block at the dimensions of the call. -/
  len : List ℕ → ℕ
  /-- The block continues the block of the operand before it in the interface: it is in the
  same buffer and starts where that block ends at the dimensions of the call. The position is
  fixed by the interface, so a call supplies no operand for it. A basis with `k` columns read
  and the next `b` columns written is two operands, the second continuing the first. The flag
  has no effect on the first operand. -/
  cont : Bool := false
  /-- The judgment reports the final contents of the block, when the operand is written. An
  operand that is written and not reported is left with unspecified contents: the judgment
  states that nothing outside it changes and claims nothing of what it holds, not even that it
  is initialized. Scratch supplied by the caller, and a matrix destroyed by a factorization, are
  such operands. The flag has no effect on an operand that is not written. -/
  reported : Bool := true

namespace Port

/-- An operand that is read and left unchanged. -/
@[simp] protected def read (len : List ℕ → ℕ) : Port := { access := .read, len }

/-- An operand that is written; its initial contents are not read. -/
@[simp] protected def write (len : List ℕ → ℕ) : Port := { access := .write, len }

/-- An operand that is read and written in place. -/
@[simp] protected def update (len : List ℕ → ℕ) : Port := { access := .update, len }

/-- An operand that is read, left unchanged, and apart from every other operand. -/
@[simp] protected def isolated (len : List ℕ → ℕ) : Port := { access := .isolated, len }

/-- The operand continues the operand before it (`NLAlib.Ops.Port.cont`). -/
@[simp] def continuing (p : Port) : Port := { p with cont := true }

/-- The final contents of the operand are not reported (`NLAlib.Ops.Port.reported`). -/
@[simp] def unreported (p : Port) : Port := { p with reported := false }

/-- The regions of an interface, with a first region in progress: an operand that continues
the one before it is merged into its region, whose length is the sum of the lengths and whose
access is the join of the accesses. -/
@[simp] def regionsFrom (cur : Port) : List Port → List Port
  | [] => [cur]
  | p :: ps =>
    match p.cont with
    | true => regionsFrom ⟨cur.access.join p.access, fun d => cur.len d + p.len d, cur.cont,
        cur.reported⟩ ps
    | false => cur :: regionsFrom p ps

/-- **The regions of an interface**: one per operand that a call supplies, each the operand
together with the operands that continue it. Operands are separated by region. -/
@[simp] def regions : List Port → List Port
  | [] => []
  | p :: ps => regionsFrom p ps

/-- The positions of the operands of an interface after an operand at `prev` of length
`prevLen`: a continuing operand is at the end of the one before it, and every other operand is
the next one supplied. -/
@[simp] def placeFrom (d : List ℕ) (prev : ℕ × ℕ) (prevLen : ℕ) :
    List Port → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], _ => []
  | p :: ps, args =>
    match p.cont, args with
    | true, args =>
        (prev.1, prev.2 + prevLen) :: placeFrom d (prev.1, prev.2 + prevLen) (p.len d) ps args
    | false, [] => []
    | false, a :: as => a :: placeFrom d a (p.len d) ps as

/-- **The positions of all operands of an interface** at the dimensions and the supplied
operands of a call, one per operand of the interface. -/
@[simp] def place (d : List ℕ) : List Port → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], _ => []
  | _ :: _, [] => []
  | p :: ps, a :: as => a :: placeFrom d a (p.len d) ps as

/-- No operand of the list continues another. -/
def flat (ps : List Port) : Bool := ps.all fun p => !p.cont

theorem regionsFrom_of_flat : ∀ {ps : List Port} (cur : Port), flat ps = true →
    regionsFrom cur ps = cur :: ps
  | [], _, _ => rfl
  | p :: ps, cur, h => by
    have hp : p.cont = false ∧ flat ps = true := by simpa [flat] using h
    simp only [regionsFrom, hp.1, regionsFrom_of_flat p hp.2]

/-- An interface in which no operand continues another has its operands as regions. -/
theorem regions_of_flat : ∀ {ps : List Port}, flat ps = true → regions ps = ps
  | [], _ => rfl
  | p :: ps, h => by
    have hp : flat ps = true := by
      have h' : p.cont = false ∧ flat ps = true := by simpa [flat] using h
      exact h'.2
    exact regionsFrom_of_flat p hp

theorem placeFrom_of_flat (d : List ℕ) : ∀ {ps : List Port} (prev : ℕ × ℕ) (l : ℕ)
    {args : List (ℕ × ℕ)}, flat ps = true → args.length = ps.length →
    placeFrom d prev l ps args = args
  | [], _, _, [], _, _ => rfl
  | p :: ps, _, _, a :: as, h, hl => by
    have hp : p.cont = false ∧ flat ps = true := by simpa [flat] using h
    simp only [placeFrom, hp.1, placeFrom_of_flat d a (p.len d) hp.2 (Nat.succ.inj hl)]

/-- In an interface in which no operand continues another, the operands are those supplied. -/
theorem place_of_flat (d : List ℕ) : ∀ {ps : List Port} {args : List (ℕ × ℕ)},
    flat ps = true → args.length = ps.length → place d ps args = args
  | [], [], _, _ => rfl
  | p :: ps, a :: as, h, hl => by
    have hp : p.cont = false ∧ flat ps = true := by simpa [flat] using h
    simp only [place, placeFrom_of_flat d a (p.len d) hp.2 (Nat.succ.inj hl)]

theorem fst_mem_of_mem_placeFrom (d : List ℕ) : ∀ {ps : List Port} {prev : ℕ × ℕ} {l : ℕ}
    {args : List (ℕ × ℕ)} {z : ℕ × ℕ}, z ∈ placeFrom d prev l ps args →
    z.1 = prev.1 ∨ ∃ a ∈ args, z.1 = a.1
  | [], _, _, _, _, h => by cases h
  | p :: ps, prev, l, args, z, h => by
    cases hc : p.cont with
    | true =>
      simp only [placeFrom, hc] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact .inl rfl
      · exact fst_mem_of_mem_placeFrom d (prev := (prev.1, prev.2 + l)) h
    | false =>
      cases args with
      | nil =>
        simp only [placeFrom, hc] at h
        cases h
      | cons a as =>
        simp only [placeFrom, hc] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact .inr ⟨z, List.mem_cons_self, rfl⟩
        · rcases fst_mem_of_mem_placeFrom d h with h | ⟨c, hc', e⟩
          · exact .inr ⟨a, List.mem_cons_self, h⟩
          · exact .inr ⟨c, List.mem_cons_of_mem _ hc', e⟩

/-- Every operand of an interface is in the buffer of a supplied operand. -/
theorem fst_mem_of_mem_place (d : List ℕ) : ∀ {ps : List Port} {args : List (ℕ × ℕ)}
    {z : ℕ × ℕ}, z ∈ place d ps args → ∃ a ∈ args, z.1 = a.1
  | [], _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | p :: ps, a :: as, z, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨z, List.mem_cons_self, rfl⟩
    · rcases fst_mem_of_mem_placeFrom d h with h | ⟨c, hc, e⟩
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨c, List.mem_cons_of_mem _ hc, e⟩

end Port

/-- **A routine**: a fixed tree with its number of dimensions and its operands. The index
variables of the tree are the dimensions followed by the offsets of its buffer variables; the
buffer variables are the operands, one each, unless a layout (`binds`) says which operand each
one is. A call supplies one operand for each region of the
interface (`NLAlib.Ops.Port.regions`); the positions of the operands that continue another are
fixed by the interface (`NLAlib.Ops.Routine.operands`). -/
structure Routine (Op Tst : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The operands. -/
  ports : List Port
  /-- The number of tape positions the routine consumes at the dimensions. With `none` the
  number is not a function of the dimensions (a rejection loop, an early stop), and the judgment
  makes no claim on the final tape position. -/
  draws : List ℕ → Option ℕ := fun _ => some 0
  /-- The tree. -/
  body : Stmt Op Tst
  /-- The layout of the buffer variables of the tree. With `none`, buffer variable `i` is
  operand `i`. With `some l`, buffer variable `i` is operand `l[i]`.

  A layout exists for two reasons. The contract of an operation, and the tree a table links
  in its place, list the input operands and then the output operands: a block updated in place
  is an input and an output, hence two buffer variables of such a tree, and one operand of the
  interface (three vectors updated in place are `some [0, 1, 2, 0, 1, 2]`). And a tree that is
  correct on several aliasing patterns of its operands is one routine for each pattern, all
  with the same tree and different layouts. A routine that is only ever called by a frame of
  its own operands, or closed into a program, needs none. -/
  binds : Option (List ℕ) := none
  /-- The separation rule of the operands. -/
  sep : Separation := .buffers

namespace Routine

/-- No operand of the routine continues another: a call supplies every operand. -/
def flat (R : Routine Op Tst) : Bool := Port.flat R.ports

/-- The number of operands that a call supplies: one per region. -/
def arity (R : Routine Op Tst) : ℕ := (Port.regions R.ports).length

/-- **The operands of a call** at its dimensions and supplied operands: one per operand of the
interface, a continuing operand at the end of the one before it. -/
@[simp] def operands (R : Routine Op Tst) (d : List ℕ) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  Port.place d R.ports args

/-- The routine whose operands are the regions of a routine. Separation is stated on it. -/
@[simp] def regions (R : Routine Op Tst) : Routine Op Tst :=
  { R with ports := Port.regions R.ports }

/-- A routine in which no operand continues another is its own routine of regions. -/
theorem regions_of_flat {R : Routine Op Tst} (h : R.flat = true) : R.regions = R := by
  unfold Routine.regions
  rw [Port.regions_of_flat h]

/-- A call of a routine in which no operand continues another supplies every operand. -/
theorem arity_of_flat {R : Routine Op Tst} (h : R.flat = true) : R.arity = R.ports.length := by
  unfold arity
  rw [Port.regions_of_flat h]

/-- The operands of a call of a routine in which no operand continues another are those
supplied. -/
theorem operands_of_flat {R : Routine Op Tst} (h : R.flat = true) (d : List ℕ)
    {args : List (ℕ × ℕ)} (hl : args.length = R.ports.length) : R.operands d args = args :=
  Port.place_of_flat d h hl

/-- Live supplied operands give live operands. -/
theorem live_operands {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)} {m : Mem K}
    (hl : m.Live args) : m.Live (R.operands d args) := fun z hz => by
  obtain ⟨a, ha, e⟩ := Port.fst_mem_of_mem_place d hz
  rw [e]
  exact hl a ha

/-- The values of the buffer variables of the tree at the operands of a call. -/
def env (R : Routine Op Tst) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match R.binds with
  | none => args
  | some l => l.filterMap fun i => args[i]?

/-- The buffer variables of the tree are operands of the call. -/
theorem mem_of_mem_env {R : Routine Op Tst} {args : List (ℕ × ℕ)} {z : ℕ × ℕ}
    (hz : z ∈ R.env args) : z ∈ args := by
  unfold env at hz
  split at hz
  · exact hz
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hz
    exact List.mem_of_getElem? hi

/-- Live operands give live buffer variables. -/
theorem live_env {R : Routine Op Tst} {args : List (ℕ × ℕ)} {m : Mem K} (hl : m.Live args) :
    m.Live (R.env args) :=
  fun z hz => hl z (mem_of_mem_env hz)

/-- Without a layout the buffer variables are the operands. -/
theorem env_of_binds_eq_none {R : Routine Op Tst} (h : R.binds = none) (args : List (ℕ × ℕ)) :
    R.env args = args := by
  unfold env
  rw [h]

/-- The entries of a list aligned with the operands whose access satisfies `p`. -/
def sel {α : Type} (R : Routine Op Tst) (p : Access → Bool) (xs : List α) : List α :=
  ((R.ports.zip xs).filter fun q => p q.1.access).map Prod.snd

/-- The lengths of the operands at the dimensions. -/
def lens (R : Routine Op Tst) (d : List ℕ) : List ℕ := R.ports.map fun p => p.len d

/-- The operands that are read. -/
abbrev readArgs (R : Routine Op Tst) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  R.sel Access.readable args

/-- The lengths of the operands that are read. -/
abbrev readLens (R : Routine Op Tst) (d : List ℕ) : List ℕ := R.sel Access.readable (R.lens d)

/-- The operands that are written. -/
abbrev writeArgs (R : Routine Op Tst) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  R.sel Access.writable args

/-- The lengths of the operands that are written. -/
abbrev writeLens (R : Routine Op Tst) (d : List ℕ) : List ℕ := R.sel Access.writable (R.lens d)

/-- **The separation of the operands by buffer**: the written operands are in
pairwise different buffers, and in buffers different from those of the operands that are only
read. Operands that are only read may share a buffer or overlap, except that the buffer of a
isolated operand is different from that of every other operand. -/
def Separated (R : Routine Op Tst) (args : List (ℕ × ℕ)) : Prop :=
  ((R.writeArgs args).map Prod.fst).Nodup ∧
    (∀ w ∈ R.writeArgs args, ∀ a ∈ R.sel Access.readOnly args, w.1 ≠ a.1) ∧
    ((R.sel Access.isIsolated args).map Prod.fst).Nodup ∧
    ∀ a ∈ R.sel Access.isIsolated args, ∀ z ∈ R.sel (fun c => !c.isIsolated) args, a.1 ≠ z.1

/-! ### Separation by buffer as a condition on pairs of operands -/

private theorem nodup_sel_iff (R : Routine Op Tst) (p : Access → Bool) (args : List (ℕ × ℕ)) :
    ((R.sel p args).map Prod.fst).Nodup ↔ (R.ports.zip args).Pairwise
      (fun u v => p u.1.access = true → p v.1.access = true → u.2.1 ≠ v.2.1) := by
  simp only [sel, List.Nodup, List.pairwise_map, List.pairwise_filter]

private theorem pairwise_forall {α : Type} {R : α → α → Prop} (hs : ∀ x y, R x y → R y x)
    (hr : ∀ x, R x x) : ∀ {l : List α}, l.Pairwise R → ∀ u ∈ l, ∀ v ∈ l, R u v
  | [], _, u, hu, _, _ => by cases hu
  | a :: l, h, u, hu, v, hv => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hu with rfl | hu'
    · rcases List.mem_cons.mp hv with rfl | hv'
      · exact hr _
      · exact ha v hv'
    · rcases List.mem_cons.mp hv with rfl | hv'
      · exact hs _ _ (ha u hu')
      · exact pairwise_forall hs hr hl u hu' v hv'

private theorem cross_sel_iff (R : Routine Op Tst) (p q : Access → Bool) (args : List (ℕ × ℕ))
    (hpq : ∀ c, p c = true → q c = true → False) :
    (∀ w ∈ R.sel p args, ∀ a ∈ R.sel q args, w.1 ≠ a.1) ↔ (R.ports.zip args).Pairwise
      (fun u v => (p u.1.access = true → q v.1.access = true → u.2.1 ≠ v.2.1) ∧
        (q u.1.access = true → p v.1.access = true → u.2.1 ≠ v.2.1)) := by
  constructor
  · intro h
    refine List.pairwise_of_forall_mem_list fun u hu v hv => ⟨fun hp hq => ?_, fun hq hp => ?_⟩
    · exact h u.2 (List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, hp⟩, rfl⟩) v.2
        (List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv, hq⟩, rfl⟩)
    · exact (h v.2 (List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv, hp⟩, rfl⟩) u.2
        (List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, hq⟩, rfl⟩)).symm
  · intro h w hw a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    obtain ⟨huZ, hup⟩ := List.mem_filter.mp hu
    obtain ⟨hvZ, hvq⟩ := List.mem_filter.mp hv
    exact (pairwise_forall
      (R := fun u v : Port × (ℕ × ℕ) =>
        (p u.1.access = true → q v.1.access = true → u.2.1 ≠ v.2.1) ∧
          (q u.1.access = true → p v.1.access = true → u.2.1 ≠ v.2.1))
      (fun x y hxy => ⟨fun hp hq => (hxy.2 hq hp).symm, fun hq hp => (hxy.1 hp hq).symm⟩)
      (fun x => ⟨fun hp hq => (hpq _ hp hq).elim, fun hq hp => (hpq _ hp hq).elim⟩) h
      u huZ v hvZ).1 hup hvq

/-- Separation by buffer is a condition on pairs of operands: two operands are in different
buffers unless both are merely read (`NLAlib.Ops.Access.apart`). -/
theorem separated_iff_pairwise (R : Routine Op Tst) (args : List (ℕ × ℕ)) :
    R.Separated args ↔ (R.ports.zip args).Pairwise
      (fun u v => u.1.access.apart v.1.access = true → u.2.1 ≠ v.2.1) := by
  change (((R.sel Access.writable args).map Prod.fst).Nodup ∧
    (∀ w ∈ R.sel Access.writable args, ∀ a ∈ R.sel Access.readOnly args, w.1 ≠ a.1) ∧
    ((R.sel Access.isIsolated args).map Prod.fst).Nodup ∧
    ∀ a ∈ R.sel Access.isIsolated args, ∀ z ∈ R.sel (fun c => !c.isIsolated) args,
      a.1 ≠ z.1) ↔ _
  rw [nodup_sel_iff, nodup_sel_iff,
    cross_sel_iff R Access.writable Access.readOnly args (fun c => by cases c <;> simp
      [Access.writable, Access.readOnly]),
    cross_sel_iff R Access.isIsolated (fun c => !c.isIsolated) args (fun c => by simp),
    ← List.pairwise_and_iff, ← List.pairwise_and_iff, ← List.pairwise_and_iff]
  refine List.Pairwise.iff fun u v => ?_
  generalize u.1.access = a
  generalize v.1.access = b
  generalize (u.2.1 ≠ v.2.1) = P
  cases a <;> cases b <;>
    simp [Access.apart, Access.writable, Access.readOnly, Access.isIsolated]

/-- Operands `i` and `j` of the interface must be apart. -/
def apartAt (R : Routine Op Tst) (i j : ℕ) : Bool :=
  match R.ports[i]?, R.ports[j]? with
  | some p, some q => p.access.apart q.access
  | _, _ => false

/-- Two operands that the interface requires apart are in different buffers. With the operands
of a call named, `h.ne (i := 1) (j := 2) (by decide) rfl rfl rfl` is the fact for the second
and third; it does not typecheck for a pair that need not be apart. -/
theorem Separated.ne {R : Routine Op Tst} {args : List (ℕ × ℕ)} (h : R.Separated args)
    {i j : ℕ} (hij : i < j) (hne : R.apartAt i j = true) {a b : ℕ × ℕ}
    (ha : args[i]? = some a) (hb : args[j]? = some b) : a.1 ≠ b.1 := by
  unfold apartAt at hne
  cases hp : R.ports[i]? with
  | none => simp [hp] at hne
  | some p =>
    cases hq : R.ports[j]? with
    | none => simp [hp, hq] at hne
    | some q =>
      simp only [hp, hq] at hne
      obtain ⟨hi, ei⟩ := List.getElem?_eq_some_iff.mp
        (List.getElem?_zip_eq_some.mpr ⟨hp, ha⟩ : (R.ports.zip args)[i]? = some (p, a))
      obtain ⟨hj, ej⟩ := List.getElem?_eq_some_iff.mp
        (List.getElem?_zip_eq_some.mpr ⟨hq, hb⟩ : (R.ports.zip args)[j]? = some (q, b))
      have hrel := List.pairwise_iff_getElem.mp ((separated_iff_pairwise R args).mp h) i j hi
        hj hij
      rw [ei, ej] at hrel
      exact hrel hne

/-- An operand at `a` with port `p` is apart from each of the listed operands that the
interface requires apart from it. The proposition reduces, on a list literal, to a conjunction
of the inequalities of buffers and `True`. -/
def apartFrom (p : Port) (a : ℕ × ℕ) : List (Port × (ℕ × ℕ)) → Prop
  | [] => True
  | (q, b) :: rest =>
    match p.access.apart q.access with
    | true => a.1 ≠ b.1 ∧ apartFrom p a rest
    | false => apartFrom p a rest

/-- The listed operands are pairwise apart where the interface requires it. The proposition
reduces, on a list literal, to nested conjunctions of inequalities of buffers and `True`. -/
def apartAll : List (Port × (ℕ × ℕ)) → Prop
  | [] => True
  | (p, a) :: rest => apartFrom p a rest ∧ apartAll rest

private theorem apartFrom_iff (p : Port) (a : ℕ × ℕ) : ∀ l : List (Port × (ℕ × ℕ)),
    apartFrom p a l ↔ ∀ v ∈ l, p.access.apart v.1.access = true → a.1 ≠ v.2.1
  | [] => by simp [apartFrom]
  | (q, b) :: rest => by
    unfold apartFrom
    cases h : p.access.apart q.access <;> simp [h, apartFrom_iff p a rest]

private theorem apartAll_iff : ∀ l : List (Port × (ℕ × ℕ)),
    apartAll l ↔ l.Pairwise (fun u v => u.1.access.apart v.1.access = true → u.2.1 ≠ v.2.1)
  | [] => by simp [apartAll]
  | (p, a) :: rest => by
    unfold apartAll
    rw [List.pairwise_cons, apartFrom_iff, apartAll_iff rest]

/-- Operands that are pairwise apart where the interface requires it are separated by buffer.
On named operands the hypothesis reduces to the inequalities of buffers; the tactic
`routine_sep` proves them from the context. -/
theorem separated_of_apartAll {R : Routine Op Tst} {args : List (ℕ × ℕ)}
    (h : apartAll (R.ports.zip args)) : R.Separated args :=
  (separated_iff_pairwise R args).mpr ((apartAll_iff _).mp h)

/-- The operands that are only read. -/
abbrev roArgs (R : Routine Op Tst) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  R.sel Access.readOnly args

/-- The lengths of the operands that are only read. -/
abbrev roLens (R : Routine Op Tst) (d : List ℕ) : List ℕ := R.sel Access.readOnly (R.lens d)

/-- **The separation of the operands by block**: the written blocks are pairwise disjoint and
disjoint from the blocks that are only read; the isolated blocks are pairwise disjoint and disjoint
from every other block. Blocks that are only read may overlap, and operands may be blocks of one
buffer. -/
def SeparatedBlocks (R : Routine Op Tst) (d : List ℕ) (args : List (ℕ × ℕ)) : Prop :=
  Fp.Apart (R.writeArgs args) (R.writeLens d) ∧
    (Fp.blocks (R.writeArgs args) (R.writeLens d)).Disj
      (Fp.blocks (R.roArgs args) (R.roLens d)) ∧
    Fp.Apart (R.sel Access.isIsolated args) (R.sel Access.isIsolated (R.lens d)) ∧
    (Fp.blocks (R.sel Access.isIsolated args) (R.sel Access.isIsolated (R.lens d))).Disj
      (Fp.blocks (R.sel (fun c => !c.isIsolated) args) (R.sel (fun c => !c.isIsolated) (R.lens d)))

/-- A selection by a property that no operand has is empty. -/
theorem sel_eq_nil {α : Type} (R : Routine Op Tst) {p : Access → Bool} (xs : List α)
    (h : ∀ q ∈ R.ports, p q.access = false) : R.sel p xs = [] := by
  unfold sel
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro q hq
  simp [h q.1 (List.of_mem_zip hq).1]

/-- Operands of a routine without isolated operands are separated by block when the written blocks
are pairwise disjoint and disjoint from the blocks that are only read. -/
theorem separatedBlocks_of_noIsolated {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (hiso : ∀ q ∈ R.ports, q.access.isIsolated = false)
    (hw : Fp.Apart (R.writeArgs args) (R.writeLens d))
    (hro : (Fp.blocks (R.writeArgs args) (R.writeLens d)).Disj
      (Fp.blocks (R.roArgs args) (R.roLens d))) : R.SeparatedBlocks d args := by
  refine ⟨hw, hro, ?_, ?_⟩
  · rw [sel_eq_nil R args hiso]
    trivial
  · rw [sel_eq_nil R args hiso]
    exact fun _ _ h _ => False.elim h

/-- **The separation that a routine requires of the supplied operands** at the dimensions of a
call: the rule its interface names, by buffer or by block, applied to the regions of the
interface. An operand and those that continue it are one region, written if any of them is; they
are consecutive, hence disjoint from each other, and are separated from the other regions as
one block. The author of a routine chooses between the two rules and cannot state another. -/
def SeparatedAt (R : Routine Op Tst) (d : List ℕ) (args : List (ℕ × ℕ)) : Prop :=
  match R.sep with
  | .buffers => R.regions.Separated args
  | .blocks => R.regions.SeparatedBlocks d args

/-- For a routine separated by block in which no operand continues another, the required
separation is that of the blocks of the operands. -/
theorem separatedAt_of_blocks {R : Routine Op Tst} (h : R.sep = .blocks) {d : List ℕ}
    {args : List (ℕ × ℕ)} (hs : R.SeparatedBlocks d args) (hflat : R.flat = true := by rfl) :
    R.SeparatedAt d args := by
  unfold SeparatedAt
  rw [h, Routine.regions_of_flat hflat]
  exact hs

/-- Operands separated by buffer are separated by block, at any dimensions. -/
theorem Separated.blocks {R : Routine Op Tst} {args : List (ℕ × ℕ)} (h : R.Separated args)
    (d : List ℕ) : R.SeparatedBlocks d args :=
  ⟨Fp.apart_of_nodup _ h.1, Fp.disj_blocks_of_ne _ _ h.2.1, Fp.apart_of_nodup _ h.2.2.1,
    Fp.disj_blocks_of_ne _ _ h.2.2.2⟩

/-- Operands separated by buffer satisfy the separation of every routine in which no operand
continues another. -/
theorem separatedAt_of_separated {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : R.Separated args) (hflat : R.flat = true := by rfl) : R.SeparatedAt d args := by
  unfold SeparatedAt
  rw [Routine.regions_of_flat hflat]
  split
  · exact h
  · exact h.blocks d

/-- Operands that are pairwise apart where the interface requires it satisfy the separation of
every routine in which no operand continues another. -/
theorem separatedAt_of_apartAll {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : apartAll (R.ports.zip args)) (hflat : R.flat = true := by rfl) :
    R.SeparatedAt d args :=
  separatedAt_of_separated (separated_of_apartAll h) hflat

/-- For a routine separated by buffer, operands whose regions are pairwise apart where the
interface requires it are separated: an operand and the operands that continue it are one
region. -/
theorem separatedAt_of_regions {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : apartAll (R.regions.ports.zip args)) (hsep : R.sep = .buffers := by rfl) :
    R.SeparatedAt d args := by
  unfold SeparatedAt
  rw [hsep]
  exact separated_of_apartAll h

/-- The separation required by a routine separated by buffer, on its regions: an operand with
its continuations is one operand. For a routine in which no operand continues another the regions
are the operands. -/
theorem SeparatedAt.regions {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : R.SeparatedAt d args) (hsep : R.sep = .buffers := by rfl) : R.regions.Separated args := by
  unfold SeparatedAt at h
  rw [hsep] at h
  exact h

/-- The separation required by a routine separated by block, on its regions. -/
theorem SeparatedAt.regionBlocks {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : R.SeparatedAt d args) (hsep : R.sep = .blocks := by rfl) :
    R.regions.SeparatedBlocks d args := by
  unfold SeparatedAt at h
  rw [hsep] at h
  exact h

end Routine

end NLAlib.Ops
