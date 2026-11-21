/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineInterface
public import NLAlib.Ops.OperationCount

/-!
# Routines: an interface, one judgment, a checkable certificate

A routine (`NLAlib.Ops.Routine`) is a fixed tree with an interface: its dimensions and, for each
operand (`NLAlib.Ops.Port`), how it is used (`NLAlib.Ops.Access`: read, written, updated in
place, or isolated) and its length as a function of the dimensions. Operands are written with
`NLAlib.Ops.Port.read`, `.write`, `.update`, `.isolated`. Interfaces and their separation are
defined in `NLAlib/Ops/RoutineInterface.lean`.

`NLAlib.Ops.Routine.Meets` is what an author states about a routine, `NLAlib.Ops.Interp.Satisfies`
says that an interpretation satisfies the contract of a primitive operation, and
`NLAlib.Ops.Impl.Satisfies` says that an implementation of an operation, the entry of a linking
table, satisfies that contract; it is derived from the judgments of the routines that share the
entry's tree (`NLAlib.Ops.Routine.Meets.satisfies_ofRel`).
A caller uses the first (`NLAlib.Ops.Routine.Meets.call`); the operation model of a certificate
is made of the second; the third is obtained by `NLAlib.Ops.Routine.Meets.satisfies`
(`NLAlib/Ops/RoutineLink.lean`).

## The judgment

`NLAlib.Ops.Routine.Meets`: on live separated operands (`NLAlib.Ops.Routine.SeparatedAt`), with
the readable blocks satisfying the precondition of the specification, the tree terminates,
changes nothing outside the written blocks, advances the tape position by exactly the declared
number of draws, and the reported blocks satisfy the postcondition. The postcondition names the
draws relative to the position of the call, on any stream. The judgment holds at every memory,
so a routine is called by framing its tree (`NLAlib.Ops.Routine.Meets.call`).

## Certificates

A certificate is the judgment read at the initial memory of a problem
(`NLAlib.Ops.Routine.algorithm`); its program is the routine run on the supplied buffers
(`NLAlib.Ops.Routine.close`): the tree itself, or, for a routine with a layout, the tree framed
once by its layout.
`NLAlib.Ops.Routine.certify` is that certificate with its work replaced by a bound on the
instruction polynomial that the kernel computes from the tree. What it states is in
`NLAlib.Ops.Routine.specification`:

* the output: the reported buffers hold blocks satisfying the postcondition for the supplied
  input blocks;
* the cost: the work and span of the run are at most `work`, under weights at most one. The
  bound is not supplied by a proof of the routine;
* the memory: the supplied payload plus the static scratch of the tree.

A reader checks an algorithm by reading its `NLAlib.Ops.Routine.Spec`, its `work` and its
operation model; the rest is checked by the kernel.

## Main definitions

* `NLAlib.Ops.Routine.Spec`, `NLAlib.Ops.Routine.Meets`: the specification and the judgment.
* `NLAlib.Ops.Routine.close`, `NLAlib.Ops.Routine.specification`: the program of a routine on a
  problem and what its counted certificate states.

## Main results

* `NLAlib.Ops.Routine.Meets.call`: a routine that meets its specification is called by a frame.
* `NLAlib.Ops.Routine.separated_slots`, `NLAlib.Ops.Problem.live_slots`: the supplied buffers of
  a problem are live separated operands of every interface.
* `NLAlib.Ops.Routine.algorithm`: the certificate against any specification, for any weights.
* `NLAlib.Ops.Routine.certify`: the same certificate with kernel-computed work.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

namespace Routine

/-- **A specification of a routine**: a precondition on the dimensions, the draws and the
blocks that are read, and a postcondition relating them to the blocks that are written and
reported. The draws are the tape seen from the position of the call: position `j` of stream `s`
is the `j`-th word the routine may draw from that stream. It mentions no memory, operand
position, absolute tape position or tree. -/
structure Spec (K : Type) where
  /-- What the dimensions, the draws and the blocks read must satisfy. -/
  pre : List ℕ → Tape K → List (List K) → Prop
  /-- What the reported blocks satisfy, given the dimensions, the draws and the blocks read. -/
  post : List ℕ → Tape K → List (List K) → List (List K) → Prop

/-- The specification that claims nothing of the reported blocks: under `pre` the routine
terminates and changes nothing outside the operands it writes. It is the deterministic content
of a routine whose accuracy is a statement about the distribution of its draws, proved
separately as a probability theorem about the same run. -/
def Spec.terminates (pre : List ℕ → Tape K → List (List K) → Prop) : Spec K where
  pre := pre
  post _ _ _ _ := True

/-- The claim of a routine on the tape positions before and after a call: the position
advances by exactly the declared number of draws, when there is one. -/
def Advances (R : Routine Op Tst) (d : List ℕ) (p p' : ℕ) : Prop :=
  match R.draws d with
  | some k => p' = p + k
  | none => True

/-- A routine that declares `k` draws advances the tape position by `k`. -/
theorem Advances.eq_of_draws {R : Routine Op Tst} {d : List ℕ} {p p' k : ℕ}
    (h : R.Advances d p p') (hk : R.draws d = some k) : p' = p + k := by
  unfold Advances at h
  rw [hk] at h
  exact h

/-- A run from tape position zero of a routine that declares `k` draws ends at position
`k`. -/
theorem Advances.eq_of_start {R : Routine Op Tst} {d : List ℕ} {p' k : ℕ}
    (h : R.Advances d 0 p') (hk : R.draws d = some k) : p' = k :=
  (h.eq_of_draws hk).trans (Nat.zero_add k)

/-- The entries of a list aligned with the operands that are written and reported. -/
def outs {α : Type} (R : Routine Op Tst) (xs : List α) : List α :=
  ((R.ports.zip xs).filter fun q => q.1.access.writable && q.1.reported).map Prod.snd

/-- The written operands whose final blocks the judgment reports. -/
abbrev outArgs (R : Routine Op Tst) (args : List (ℕ × ℕ)) : List (ℕ × ℕ) := R.outs args

/-- The lengths of the written operands whose final blocks the judgment reports. -/
abbrev outLens (R : Routine Op Tst) (d : List ℕ) : List ℕ := R.outs (R.lens d)

/-- Every operand of the routine is reported. -/
def allReported (R : Routine Op Tst) : Bool := R.ports.all fun q => q.reported

/-- When every operand is reported, the reported operands are the written ones. -/
theorem outs_eq_sel {α : Type} {R : Routine Op Tst} (h : R.allReported = true)
    (xs : List α) : R.outs xs = R.sel Access.writable xs := by
  unfold outs sel
  congr 1
  refine List.filter_congr fun q hq => ?_
  rw [List.all_eq_true.mp h q.1 (List.of_mem_zip hq).1, Bool.and_true]

/-! ### The blocks of a call

The blocks that a call reads, writes and reports are those of the shapes of its operands
(`NLAlib.Ops.Port.view`). The four definitions below are stated by cases on
`NLAlib.Ops.Routine.contiguous` only so that, for an interface whose operands are all
contiguous, they are by computation the reads, the room and the footprint of blocks
(`NLAlib.Ops.Mem.readBlocks`, `NLAlib.Ops.Mem.Room`, `NLAlib.Ops.Fp.blocks`); the two cases
agree (`NLAlib.Ops.Routine.readAt_eq_readViews` and the lemmas after it). -/

/-- The shapes of the operands that are read. -/
abbrev readViews (R : Routine Op Tst) (d : List ℕ) : List View :=
  R.sel Access.readable (R.views d)

/-- The shapes of the operands that are written. -/
abbrev writeViews (R : Routine Op Tst) (d : List ℕ) : List View :=
  R.sel Access.writable (R.views d)

/-- The shapes of the written operands whose final blocks the judgment reports. -/
abbrev outViews (R : Routine Op Tst) (d : List ℕ) : List View := R.outs (R.views d)

/-- **The blocks that a call reads**: one per operand that is read, at the positions `ops` of
the operands and the dimensions `d`. -/
def readAt (R : Routine Op Tst) (m : Mem K) (d : List ℕ) (ops : List (ℕ × ℕ)) :
    Option (List (List K)) :=
  match R.contiguous with
  | true => m.readBlocks (R.readArgs ops) (R.readLens d)
  | false => m.readViews (R.readArgs ops) (R.readViews d)

/-- **There is room for the blocks that a call writes.** -/
def RoomAt (R : Routine Op Tst) (m : Mem K) (d : List ℕ) (ops : List (ℕ × ℕ)) : Prop :=
  match R.contiguous with
  | true => m.Room (R.writeArgs ops) (R.writeLens d)
  | false => m.RoomViews (R.writeArgs ops) (R.writeViews d)

/-- **The footprint of a call**: the cells of the operands that are written. -/
def footprint (R : Routine Op Tst) (d : List ℕ) (ops : List (ℕ × ℕ)) : Fp :=
  match R.contiguous with
  | true => Fp.blocks (R.writeArgs ops) (R.writeLens d)
  | false => Fp.views (R.writeArgs ops) (R.writeViews d)

/-- **The blocks that a call reports**: one per operand that is written and reported. -/
def reportAt (R : Routine Op Tst) (m : Mem K) (d : List ℕ) (ops : List (ℕ × ℕ)) :
    Option (List (List K)) :=
  match R.contiguous with
  | true => m.readBlocks (R.outArgs ops) (R.outLens d)
  | false => m.readViews (R.outArgs ops) (R.outViews d)

theorem readAt_of_contiguous {R : Routine Op Tst} (h : R.contiguous = true) (m : Mem K)
    (d : List ℕ) (ops : List (ℕ × ℕ)) :
    R.readAt m d ops = m.readBlocks (R.readArgs ops) (R.readLens d) := by
  unfold readAt
  rw [h]

theorem roomAt_of_contiguous {R : Routine Op Tst} (h : R.contiguous = true) (m : Mem K)
    (d : List ℕ) (ops : List (ℕ × ℕ)) :
    R.RoomAt m d ops ↔ m.Room (R.writeArgs ops) (R.writeLens d) := by
  unfold RoomAt
  rw [h]

theorem footprint_of_contiguous {R : Routine Op Tst} (h : R.contiguous = true) (d : List ℕ)
    (ops : List (ℕ × ℕ)) : R.footprint d ops = Fp.blocks (R.writeArgs ops) (R.writeLens d) := by
  unfold footprint
  rw [h]

theorem reportAt_of_contiguous {R : Routine Op Tst} (h : R.contiguous = true) (m : Mem K)
    (d : List ℕ) (ops : List (ℕ × ℕ)) :
    R.reportAt m d ops = m.readBlocks (R.outArgs ops) (R.outLens d) := by
  unfold reportAt
  rw [h]

/-- The shapes of the operands of an interface whose operands are contiguous are blocks of
their lengths. -/
theorem views_of_contiguous {R : Routine Op Tst} (h : R.contiguous = true) (d : List ℕ) :
    R.views d = (R.lens d).map View.block := by
  unfold views lens
  rw [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hp' : p.stride = none := by
    have := List.all_eq_true.mp h p hp
    simpa using this
  simp [Port.view, hp']

private theorem zip_filter_map {α β : Type} (f : α → β) (q : Port × β → Bool) :
    ∀ (ps : List Port) (xs : List α),
      ((ps.zip (xs.map f)).filter q).map Prod.snd =
        (((ps.zip xs).filter fun u => q (u.1, f u.2)).map Prod.snd).map f
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, x :: xs => by
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
    split <;> simp [zip_filter_map f q ps xs]

/-- Selecting operands commutes with a map of the aligned list. -/
theorem sel_map {α β : Type} (R : Routine Op Tst) (p : Access → Bool) (f : α → β)
    (xs : List α) : R.sel p (xs.map f) = (R.sel p xs).map f :=
  zip_filter_map f (fun q => p q.1.access) R.ports xs

/-- Selecting reported operands commutes with a map of the aligned list. -/
theorem outs_map {α β : Type} (R : Routine Op Tst) (f : α → β) (xs : List α) :
    R.outs (xs.map f) = (R.outs xs).map f :=
  zip_filter_map f (fun q => q.1.access.writable && q.1.reported) R.ports xs

/-- The blocks a call reads are the blocks of the shapes of the operands read, whether or not
the operands are contiguous. -/
theorem readAt_eq_readViews (R : Routine Op Tst) (m : Mem K) (d : List ℕ)
    (ops : List (ℕ × ℕ)) : R.readAt m d ops = m.readViews (R.readArgs ops) (R.readViews d) := by
  unfold readAt
  cases h : R.contiguous with
  | false => rfl
  | true =>
    change _ = m.readViews _ (R.sel Access.readable (R.views d))
    rw [views_of_contiguous h, sel_map, Mem.readViews_blocks]

/-- The room of a call is that of the shapes of the operands written. -/
theorem roomAt_iff_roomViews (R : Routine Op Tst) (m : Mem K) (d : List ℕ)
    (ops : List (ℕ × ℕ)) : R.RoomAt m d ops ↔ m.RoomViews (R.writeArgs ops) (R.writeViews d) := by
  unfold RoomAt
  cases h : R.contiguous with
  | false => exact Iff.rfl
  | true =>
    change _ ↔ m.RoomViews _ (R.sel Access.writable (R.views d))
    rw [views_of_contiguous h, sel_map, Mem.roomViews_blocks]

/-- The footprint of a call is that of the shapes of the operands written. -/
theorem footprint_eq_views (R : Routine Op Tst) (d : List ℕ) (ops : List (ℕ × ℕ)) :
    R.footprint d ops = Fp.views (R.writeArgs ops) (R.writeViews d) := by
  unfold footprint
  cases h : R.contiguous with
  | false => rfl
  | true =>
    change _ = Fp.views _ (R.sel Access.writable (R.views d))
    rw [views_of_contiguous h, sel_map, Fp.views_blocks]

/-- The blocks a call reports are the blocks of the shapes of the operands reported. -/
theorem reportAt_eq_readViews (R : Routine Op Tst) (m : Mem K) (d : List ℕ)
    (ops : List (ℕ × ℕ)) : R.reportAt m d ops = m.readViews (R.outArgs ops) (R.outViews d) := by
  unfold reportAt
  cases h : R.contiguous with
  | false => rfl
  | true =>
    change _ = m.readViews _ (R.outs (R.views d))
    rw [views_of_contiguous h, outs_map, Mem.readViews_blocks]

/-- **A routine meets a specification** over an interpretation. At every memory, on live
operands separated as the interface requires, with the readable blocks satisfying the
precondition and room for the written blocks, the tree terminates, changes only the written
blocks, advances the tape position by exactly the declared number of draws (no claim when the
routine declares none), and the written blocks that are reported satisfy the postcondition.
The call supplies one operand per region; the blocks read, written and reported are those of
all operands of the interface (`NLAlib.Ops.Routine.operands`), each of the shape its operand
declares (`NLAlib.Ops.Routine.readAt`, `NLAlib.Ops.Routine.RoomAt`,
`NLAlib.Ops.Routine.footprint`, `NLAlib.Ops.Routine.reportAt`): for an interface of contiguous
operands these are, by computation, the reads, the room and the footprint of blocks.

This is the one judgment that the author of a routine states and that a caller uses
(`NLAlib.Ops.Routine.Meets.call`). -/
def Meets (R : Routine Op Tst) (I : Interp Op Tst K) (S : Spec K) : Prop :=
  ∀ (d : List ℕ) (args : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) (xs : List (List K)),
    d.length = R.nd → args.length = R.arity → m.Live args → R.SeparatedAt d args →
    R.readAt m d (R.operands d args) = some xs →
    S.pre d (τ.shift m.pos) xs →
    R.RoomAt m d (R.operands d args) →
    Writes .total I τ R.body (Env.frame d (R.env (R.operands d args)))
      (R.footprint d (R.operands d args))
      (fun m' => R.Advances d m.pos m'.pos ∧ ∃ ys,
        R.reportAt m' d (R.operands d args) = some ys ∧
          S.post d (τ.shift m.pos) xs ys) m

/-- Calling a routine. A routine that meets its specification is used by framing its tree
at dimensions and buffer variables that evaluate to a call satisfying the hypotheses of the
judgment; the frame lists the operands in the layout of the routine.
The caller learns the footprint and the postcondition, and nothing of the tree. -/
theorem Meets.call {R : Routine Op Tst} {I : Interp Op Tst K} {S : Spec K} (h : R.Meets I S)
    {ρ : Env} {ds : List IExp} {ops : List Operand} {d : List ℕ} {args : List (ℕ × ℕ)}
    {τ : Tape K} {m : Mem K} {xs : List (List K)}
    (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ops = some (R.env (R.operands d args)))
    (hnd : d.length = R.nd) (hlen : args.length = R.arity) (hl : m.Live args)
    (hsep : R.SeparatedAt d args)
    (hr : R.readAt m d (R.operands d args) = some xs)
    (hpre : S.pre d (τ.shift m.pos) xs)
    (hroom : R.RoomAt m d (R.operands d args)) :
    Writes .total I τ (.frame ds ops R.body) ρ
      (R.footprint d (R.operands d args))
      (fun m' => R.Advances d m.pos m'.pos ∧ ∃ ys,
        R.reportAt m' d (R.operands d args) = some ys ∧
          S.post d (τ.shift m.pos) xs ys) m :=
  (h d args τ m xs hnd hlen hl hsep hr hpre hroom).in_frame hd ha (live_env (live_operands hl))

/-! ### Operands in different buffers -/

private theorem map_snd_zip_sublist {α β : Type} :
    ∀ (ps : List α) (xs : List β), ((ps.zip xs).map Prod.snd).Sublist xs
  | [], _ => List.nil_sublist _
  | _ :: _, [] => List.Sublist.refl _
  | _ :: ps, x :: xs => (map_snd_zip_sublist ps xs).cons_cons x

private theorem nodup_zip {R : Routine Op Tst} {args : List (ℕ × ℕ)}
    (h : (args.map Prod.fst).Nodup) :
    ((R.ports.zip args).map fun q => q.2.1).Nodup := by
  have hs : ((R.ports.zip args).map fun q => q.2.1).Sublist (args.map Prod.fst) := by
    have := (map_snd_zip_sublist R.ports args).map Prod.fst
    rwa [List.map_map] at this
  exact h.sublist hs

private theorem nodup_sel {R : Routine Op Tst} {args : List (ℕ × ℕ)}
    (h : (args.map Prod.fst).Nodup) (p : Access → Bool) :
    ((R.sel p args).map Prod.fst).Nodup := by
  have hs : (R.sel p args).Sublist args :=
    (List.filter_sublist.map Prod.snd).trans (map_snd_zip_sublist R.ports args)
  exact h.sublist (hs.map Prod.fst)

private theorem ne_of_sel {R : Routine Op Tst} {args : List (ℕ × ℕ)}
    (h : (args.map Prod.fst).Nodup) {p q : Access → Bool}
    (hpq : ∀ c, p c = true → q c = true → False) :
    ∀ w ∈ R.sel p args, ∀ a ∈ R.sel q args, w.1 ≠ a.1 := by
  intro w hw a ha e
  obtain ⟨⟨pw, w'⟩, hw', rfl⟩ := List.mem_map.mp hw
  obtain ⟨⟨pa, a'⟩, ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨hwL, hwp⟩ := List.mem_filter.mp hw'
  obtain ⟨haL, haq⟩ := List.mem_filter.mp ha'
  have heq := List.inj_on_of_nodup_map (nodup_zip (R := R) h) hwL haL e
  rw [← heq] at haq
  exact hpq pw.access hwp haq

/-- Operands in pairwise different buffers are separated by buffer, for every interface. -/
theorem separated_of_nodup (R : Routine Op Tst) {args : List (ℕ × ℕ)}
    (h : (args.map Prod.fst).Nodup) : R.Separated args :=
  ⟨nodup_sel h _, ne_of_sel h (fun c => by cases c <;> simp [Access.writable, Access.readOnly]),
    nodup_sel h _, ne_of_sel h (fun c => by cases c <;> simp)⟩

end Routine

/-! ### The program of a routine on a problem -/

/-- The supplied buffers of a problem as operands: buffer `i` at offset zero. -/
def slots (b : ℕ) : List (ℕ × ℕ) := (List.range b).map fun i => (i, 0)

/-- The initial environment of a program is the environment of a call at the sizes and the
supplied buffers. -/
theorem Program.environment_eq_slots {r : ℕ} (d : Fin r → ℕ) (b : ℕ) :
    Program.environment (b := b) d = Env.frame (List.ofFn d) (slots b) := by
  simp [Program.environment, Env.frame, slots, Function.comp_def]

/-- The supplied buffers of a problem are live in its initial memory. -/
theorem Problem.live_slots {r b : ℕ} (P : Problem K r b) (d : Fin r → ℕ) (x : P.Input d) :
    (P.initial d x).Live (slots b) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  simpa [Problem.initial] using List.mem_range.mp hi

namespace Routine

variable {r b : ℕ}

/-- The supplied buffers of a problem are different buffers, hence separated operands of every
interface. -/
theorem separated_slots (R : Routine Op Tst) (b : ℕ) : R.Separated (slots b) :=
  R.separated_of_nodup (by
    simp only [slots, List.map_map, Function.comp_def, List.map_id']
    exact List.nodup_range)

/-- The dimensions of a framed call from the initial environment of a program: its sizes. -/
def closeDims (r : ℕ) : List IExp := (List.range r).map IExp.var

/-- The operands of a framed call from the initial environment of a program, in a layout:
buffer variable `i` of the tree is the supplied buffer `l[i]`, at its start. -/
def closeOps (l : List ℕ) : List Operand := l.map fun i => ⟨i, .const 0⟩

/-- The layout of the routine names supplied buffers only. -/
def bindsFit (R : Routine Op Tst) (b : ℕ) : Bool :=
  match R.binds with
  | none => true
  | some l => l.all fun i => i < b

/-- The program of a routine on a problem: the sizes are the dimensions and the supplied
buffers, in order and at offset zero, are the operands. The initial environment of a program has
one buffer variable for each supplied buffer. A routine without a layout has one buffer variable
for each operand, so its program is its tree. A routine with a layout (an operand updated in
place is two buffer variables of its tree) is called once, by a frame that lists the supplied
buffers in the layout; the frame is part of the certified tree and is counted. A routine of
another shape, or one with an operand that continues another (whose position is not the start of
a buffer), has no program and elaborates to failure. The supplied buffers are whole buffers, so
the certificates below are for interfaces of contiguous operands. -/
def close (R : Routine Op Tst) (r b : ℕ) : Program Op Tst r b :=
  ⟨if R.nd = r ∧ R.ports.length = b ∧ R.bindsFit b = true ∧ R.flat = true then
      match R.binds with
      | none => R.body
      | some l => .frame (closeDims r) (closeOps l) R.body
    else .abort⟩

private theorem evalList_map_var (idx : List ℕ) :
    ∀ js : List ℕ, (∀ j ∈ js, j < idx.length) →
      IExp.evalList idx (js.map IExp.var) = some (js.map fun j => idx.getD j 0)
  | [], _ => rfl
  | j :: js, h => by
    have hj : j < idx.length := h j (by simp)
    rw [List.map_cons, IExp.evalList_cons, IExp.eval_var,
      evalList_map_var idx js fun i hi => h i (by simp [hi])]
    simp [hj]

/-- The sizes of a program evaluate to themselves in its initial environment. -/
theorem evalList_closeDims {r : ℕ} (d : Fin r → ℕ) (t : List ℕ) :
    IExp.evalList (List.ofFn d ++ t) (closeDims r) = some (List.ofFn d) := by
  rw [closeDims, evalList_map_var _ _ fun j hj => by
    have := List.mem_range.mp hj
    simp only [List.length_append, List.length_ofFn]
    omega]
  refine congrArg some (List.ext_getElem (by simp) fun i h₁ h₂ => ?_)
  have hi : i < r := by simpa using h₁
  have hlt : i < (List.ofFn d).length := by simpa using hi
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt, Option.getD_some]

/-- The layout operands of a program evaluate to the supplied buffers they name. -/
theorem evalList_closeOps (d : List ℕ) (b : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < b) →
      Operand.evalList (Env.frame d (slots b)) (closeOps l) =
        some (l.filterMap fun i => (slots b)[i]?)
  | [], _ => rfl
  | i :: l, h => by
    have hi : i < b := h i (by simp)
    have he : Operand.eval (Env.frame d (slots b)) ⟨i, .const 0⟩ = some (i, 0) := by
      simp [Operand.eval_eq, Env.frame, slots, hi]
    have hs : (slots b)[i]? = some (i, 0) := by simp [slots, hi]
    change Operand.evalList _ (⟨i, .const 0⟩ :: closeOps l) = _
    rw [Operand.evalList_cons, he, evalList_closeOps d b l fun j hj => h j (by simp [hj])]
    simp [hs]

/-- A routine that meets its specification, run as a program. From a memory in which the
supplied buffers are live, hold the blocks read and have room for the blocks written, the
program of the routine terminates, changes only the written buffers, advances the tape as
declared and leaves reported blocks satisfying the postcondition. -/
theorem Meets.close {R : Routine Op Tst} {I : Interp Op Tst K} {S : Spec K} (h : R.Meets I S)
    {r b : ℕ} (hshape : R.nd = r ∧ R.ports.length = b) (hfit : R.bindsFit b = true)
    (hflat : R.flat = true) (hcontig : R.contiguous = true) (d : Fin r → ℕ) (τ : Tape K)
    (m : Mem K) (xs : List (List K))
    (hl : m.Live (slots b))
    (hr : m.readBlocks (R.readArgs (slots b)) (R.readLens (List.ofFn d)) = some xs)
    (hpre : S.pre (List.ofFn d) (τ.shift m.pos) xs)
    (hroom : m.Room (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) :
    Writes .total I τ (R.close r b).body (Program.environment (b := b) d)
      (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d)))
      (fun m' => R.Advances (List.ofFn d) m.pos m'.pos ∧ ∃ ys,
        m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys ∧
          S.post (List.ofFn d) (τ.shift m.pos) xs ys) m := by
  have hlen : (slots b).length = R.ports.length := by simp [slots, hshape.2]
  have hops := operands_of_flat hflat (List.ofFn d) hlen
  have hnd : (List.ofFn d).length = R.nd := by rw [List.length_ofFn, hshape.1]
  have harity := hlen.trans (arity_of_flat hflat).symm
  have hsep : R.SeparatedAt (List.ofFn d) (slots b) :=
    separatedAt_of_separated (R.separated_slots b) hflat
  have hb : (R.close r b).body = match R.binds with
      | none => R.body
      | some l => .frame (closeDims r) (closeOps l) R.body :=
    if_pos ⟨hshape.1, hshape.2, hfit, hflat⟩
  rw [hb, Program.environment_eq_slots]
  cases hbinds : R.binds with
  | none =>
    have hm := h (List.ofFn d) (slots b) τ m xs hnd harity hl hsep
    rw [hops, R.env_of_binds_eq_none hbinds] at hm
    simp only [readAt_of_contiguous hcontig, roomAt_of_contiguous hcontig,
      footprint_of_contiguous hcontig, reportAt_of_contiguous hcontig] at hm
    exact hm hr hpre hroom
  | some l =>
    have hfit' : ∀ i ∈ l, i < b := by
      unfold bindsFit at hfit
      rw [hbinds] at hfit
      exact fun i hi => of_decide_eq_true (List.all_eq_true.mp hfit i hi)
    have hc := h.call (ρ := Env.frame (List.ofFn d) (slots b)) (ds := closeDims r)
      (ops := closeOps l) (d := List.ofFn d) (args := slots b) (τ := τ) (m := m) (xs := xs)
      (evalList_closeDims d _) (by
        rw [hops]
        unfold env
        rw [hbinds]
        exact evalList_closeOps _ b l hfit') hnd harity hl hsep
    rw [hops] at hc
    simp only [readAt_of_contiguous hcontig, roomAt_of_contiguous hcontig,
      footprint_of_contiguous hcontig, reportAt_of_contiguous hcontig] at hc
    exact hc hr hpre hroom

/-- **A certificate of a routine.** The program of a routine that meets `Sp` under every
interpretation of the model is certified against a specification `S` of the problem, for any
weights. The supplied buffers hold the blocks `input`, which satisfy the precondition, and have
room for the written blocks (`hinit`); the output of `S` follows from the postcondition, the
declared draws and the frame of the run (`hgood`); the resource fields of `S` bound the static
count and scratch of the tree as in `NLAlib.Ops.Algorithm.ofWp`.

This is the one constructor of certificates from routines. A certificate normally uses it
through `NLAlib.Ops.Routine.Domain.algorithm`, on the problem derived from the routine, where
`hinit` holds by construction; used directly it serves a problem that is not derived from a
routine. Liveness and separation of the supplied buffers are not hypotheses: they hold for
every problem
(`NLAlib.Ops.Problem.live_slots`, `NLAlib.Ops.Routine.separated_slots`). When the budget, the
scratch, the work and the span of `S` are those of the tree (`staticCost`, `staticPeak` and their
weights, as in `NLAlib.Ops.Routine.manifest`), `hcost`, `hspace`, `hwork` and `hspan` hold by
`le_rfl` and may be omitted: write `(hmemory := …)`.

A **counted certificate**, whose work and span are a closed polynomial in the sizes, is this
certificate followed by `NLAlib.Ops.Algorithm.withCountPoly`: the instruction polynomial of the
tree is evaluated by the kernel (`kernel_rfl`) and bounded by the polynomial (`poly_eval`).
`NLAlib.Ops.Routine.certify` is that construction for the canonical specification
`NLAlib.Ops.Routine.manifest`; a family whose certificate states its own output (a state of the
iteration, say) applies `withCountPoly` to its own `algorithm`. -/
def algorithm (R : Routine Op Tst) {P : Problem K r b} {M : AccessModel Op Tst P}
    {S : Specification Op Tst P} (Sp : (d : Fin r → ℕ) → P.Input d → Spec K)
    (input : (d : Fin r → ℕ) → P.Input d → List (List K))
    (hmeets : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K),
      M.contracts d x I → R.Meets I (Sp d x))
    (hinit : ∀ d, P.valid d → ∀ x : P.Input d,
      (P.initial d x).readBlocks (R.readArgs (slots b)) (R.readLens (List.ofFn d)) =
        some (input d x) ∧
      (∀ τ : Tape K, (Sp d x).pre (List.ofFn d) τ (input d x)) ∧
      (P.initial d x).Room (R.writeArgs (slots b)) (R.writeLens (List.ofFn d)))
    (hgood : ∀ d, P.valid d → ∀ (x : P.Input d) (τ : Tape K) (m' : Mem K),
      (P.initial d x).store.EqOff
        (Fp.blocks (R.writeArgs (slots b)) (R.writeLens (List.ofFn d))) m'.store →
      R.Advances (List.ofFn d) 0 m'.pos → ∀ ys,
      m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys →
      (Sp d x).post (List.ofFn d) τ (input d x) ys → ∀ c, c ≤ S.budget d → S.good d x τ c m')
    (hcost : ∀ d, P.valid d → staticCost (R.close r b) d ≤ S.budget d := by
      intro _ _; exact le_rfl)
    (hspace : ∀ d, P.valid d → staticPeak M.resources (R.close r b) d ≤ S.scratch d := by
      intro _ _; exact le_rfl)
    (hwork : ∀ d, P.valid d → M.resources.work (S.budget d) ≤ S.work d := by
      intro _ _; exact le_rfl)
    (hspan : ∀ d, P.valid d → M.resources.span (S.budget d) ≤ S.span d := by
      intro _ _; exact le_rfl)
    (hmemory : ∀ d, P.valid d → ∀ x : P.Input d,
      P.initialBytes d x + S.scratch d ≤ S.memory d)
    (hshape : R.nd = r ∧ R.ports.length = b := by exact ⟨rfl, rfl⟩)
    (ht : (R.close r b).wellTyped M.resources P.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) : Algorithm M S :=
  Algorithm.ofWp (R.close r b) ht
    (fun d hd x I hI τ => by
      obtain ⟨hr, hpre, hroom⟩ := hinit d hd x
      have hτ : τ.shift (P.initial d x).pos = τ := by
        funext p s
        exact congrArg (fun q => τ q s) (Nat.zero_add p)
      refine ((hmeets d hd x I hI).close hshape hfit hflat hcontig d τ (P.initial d x)
        (input d x)
        (P.live_slots d x) hr (hτ.symm ▸ hpre τ) hroom).wp ?_
      rintro m' hfr ⟨hpos, ys, hys, hpost⟩
      rw [hτ] at hpost
      exact hgood d hd x τ m' hfr hpos ys hys hpost)
    hcost hspace hwork hspan hmemory

/-- The canonical specification of a routine on a problem, with the work and span that the
static count of the tree gives under the weights of the model. The specification may depend on
the size and the input (the matrix of a solver); `input` names the blocks read; `bytes` bounds
the supplied payload. -/
noncomputable def manifest (R : Routine Op Tst) {P : Problem K r b}
    (S : (d : Fin r → ℕ) → P.Input d → Spec K)
    (W : ResourceModel Op Tst) (input : (d : Fin r → ℕ) → P.Input d → List (List K))
    (bytes : (Fin r → ℕ) → ℕ) : Specification Op Tst P where
  budget := staticCost (R.close r b)
  scratch := staticPeak W (R.close r b)
  work d := W.work (staticCost (R.close r b) d)
  span d := W.span (staticCost (R.close r b) d)
  memory d := bytes d + staticPeak W (R.close r b) d
  good d x τ _ m' := R.Advances (List.ofFn d) 0 m'.pos ∧ ∃ ys,
    m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys ∧
      (S d x).post (List.ofFn d) τ (input d x) ys

/-- **What the counted certificate of a routine states**: from tape position zero the run
advances by the declared number of draws, and the reported buffers hold blocks satisfying the
postcondition for the tape and the supplied input blocks; the work and the span of the run are
at most `work`; the resident payload is at most `bytes` plus the static scratch of the tree. -/
noncomputable def specification (R : Routine Op Tst) {P : Problem K r b}
    (S : (d : Fin r → ℕ) → P.Input d → Spec K)
    (W : ResourceModel Op Tst) (input : (d : Fin r → ℕ) → P.Input d → List (List K))
    (bytes work : (Fin r → ℕ) → ℕ) : Specification Op Tst P :=
  { R.manifest S W input bytes with work := work, span := work }

/-- **The counted certificate of a routine**: the certificate
`NLAlib.Ops.Routine.algorithm` against the canonical specification, with its work and span
replaced by any bound `work` of the instruction polynomial of the tree
(`NLAlib.Ops.Algorithm.withCountPoly`).

The instruction polynomial is computed by the kernel from the fixed instrumented tree; no
statement about the cost of the routine is taken from its author. Every weight of the model
must be at most one, because an instruction count bounds the work only then: the count is of
the primitives of the model, each counted once. -/
noncomputable def certify (R : Routine Op Tst) {P : Problem K r b}
    (S : (d : Fin r → ℕ) → P.Input d → Spec K)
    {M : AccessModel Op Tst P} (input : (d : Fin r → ℕ) → P.Input d → List (List K))
    (bytes work : (Fin r → ℕ) → ℕ)
    (hmeets : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K),
      M.contracts d x I → R.Meets I (S d x))
    (hinit : ∀ d, P.valid d → ∀ x : P.Input d,
      (P.initial d x).readBlocks (R.readArgs (slots b)) (R.readLens (List.ofFn d)) =
        some (input d x) ∧
      (∀ τ : Tape K, (S d x).pre (List.ofFn d) τ (input d x)) ∧
      (P.initial d x).Room (R.writeArgs (slots b)) (R.writeLens (List.ofFn d)))
    (hbytes : ∀ d, P.valid d → ∀ x : P.Input d, P.initialBytes d x ≤ bytes d)
    (hop : ∀ o d, M.resources.operationWork o d ≤ 1)
    (hcore : ∀ k d, M.resources.coreWork k d ≤ 1) (hq : ∀ q d, M.resources.queryWork q d ≤ 1)
    (hwork : ∀ d, P.valid d → CountPoly.eval (List.ofFn d) (R.close r b).countPoly ≤ work d)
    (hshape : R.nd = r ∧ R.ports.length = b := by exact ⟨rfl, rfl⟩)
    (ht : (R.close r b).wellTyped M.resources P.formats = true := by rfl)
    (hfit : R.bindsFit b = true := by rfl) (hflat : R.flat = true := by rfl)
    (hcontig : R.contiguous = true := by rfl) :
    Algorithm M (R.specification S M.resources input bytes work) :=
  (R.algorithm (S := R.manifest S M.resources input bytes) S input hmeets hinit
    (fun _ _ _ _ _ _ hpos ys hys hpost _ _ => ⟨hpos, ys, hys, hpost⟩)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d hd x => Nat.add_le_add_right (hbytes d hd x) _) hshape ht hfit hflat
    hcontig).withCountPoly
    hop hcore hq work hwork

end Routine

end NLAlib.Ops
