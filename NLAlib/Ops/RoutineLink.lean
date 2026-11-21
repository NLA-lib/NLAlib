/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.Step
public import NLAlib.Ops.Logic.BlockPost

/-!
# Linking with routines

A table implements an operation of a model by a tree over the operations below it, and the
induced interpretation satisfies the contract of that operation when the tree does
(`NLAlib.Ops.Interp.link_satisfies`). The contract of an operation is in operand form
(`NLAlib.Ops.BlockRel.spec`): input operands, output operands, an admission of operands.

This file states that step for a routine. A routine *implements* an operation contract
(`NLAlib.Ops.Routine.Implements`) when the admitted input and output operands of the contract
are, through a map `port`, separated operands of the routine: the buffer variables of the tree
are the inputs followed by the outputs, the blocks the routine reads are the inputs and the
blocks it writes are the outputs, with the same lengths, and it draws the window of the
contract. Then a routine that meets a specification whose precondition follows from the domain
of the contract and whose postcondition gives its relation satisfies the contract as an
implementation, and the operation of the induced interpretation meets it.

An operation contract may admit several layouts of its operands that no single interface
covers: an output that is either apart from an input or exactly that input (a copy, a scaling
or an update that may run in place). Such a contract is implemented by one routine for each
layout, all with the same tree: one with separate operands, one with an operand updated in
place and its buffer variables bound to it. The contract follows by cases on the admission,
each case a run of the routine of that layout (`NLAlib.Ops.Routine.Meets.writes_ofRel`). An
output placed in the buffer of an input, where that input ends, is an operand that continues
it (`NLAlib.Ops.Port.cont`).

The three statements of the layer, `NLAlib.Ops.Routine.Meets`, `NLAlib.Ops.Interp.Satisfies` and
`NLAlib.Ops.Impl.Satisfies`, and their roles are described once, in `NLAlib/Ops/README.md`
("Three statements") and the header of `NLAlib/Ops/Routine.lean`.

## Main definitions

* `NLAlib.Ops.Routine.impl`: a routine as an implementation.
* `NLAlib.Ops.Routine.Implements`: the operands of a contract are operands of the routine.

## Main results

* `NLAlib.Ops.Routine.Meets.satisfies`: a routine that meets its specification satisfies the
  operation
  contract it implements.
* `NLAlib.Ops.Routine.Meets.satisfies_ofRel`: the same for the specification read off the block
  relation of the contract (`NLAlib.Ops.Routine.Spec.ofRel`).
* `NLAlib.Ops.Routine.meets_ofRel_of_post`: the judgment from a run stated in operand form.
* `NLAlib.Ops.Routine.Meets.writes_ofRel`: the run of a routine as a call of an operation.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

namespace Routine

/-- The number of input operands of a routine in the two-list form of a contract: its
readable operands. -/
def nin (R : Routine Op Tst) : ℕ := (R.ports.filter fun q => q.access.readable).length

/-- The number of output operands of a routine in the two-list form of a contract: its
writable operands. An operand updated in place is an input and an output. -/
def nout (R : Routine Op Tst) : ℕ := (R.ports.filter fun q => q.access.writable).length

/-- A routine as an implementation: the same tree, with the numbers of input and output buffer
variables of the two-list form. -/
def impl (R : Routine Op Tst) : Impl Op Tst := ⟨R.nd, R.nin, R.nout, R.body⟩

/-- **A routine linked through a table**: the same interface, with the tree linked. -/
def link (R : Routine Op₁ Tst) (T : Table Op₁ Op₂ Tst) : Routine Op₂ Tst :=
  { nd := R.nd, ports := R.ports, draws := R.draws, body := R.body.link T, binds := R.binds,
    sep := R.sep }

/-- A specification that a routine meets under the linked interpretation is met by the linked
routine under the interpretation of the operations it is linked to. -/
theorem Meets.of_link {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {R : Routine Op₁ Tst}
    {S : Spec K} (h : R.Meets (I.link T) S) : (R.link T).Meets I S :=
  fun d args τ m xs hnd hlen hl hsep hr hpre hroom =>
    Writes.link I T (h d args τ m xs hnd hlen hl hsep hr hpre hroom)

/-- Operands of an operation contract with relation `B` and admission `adm` at which a call can
succeed: admitted, with the number of dimensions of the contract and one operand for each
declared input and output block. -/
def _root_.NLAlib.Ops.BlockRel.Shaped (B : BlockRel K)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) (d : List ℕ)
    (ins outs : List (ℕ × ℕ)) : Prop :=
  d.length = B.nd ∧ adm d ins outs ∧ ins.length = (B.inLens d).length ∧
    outs.length = (B.outLens d).length

/-- **A routine implements an operation contract** with relation `B` and admission `adm`,
through the map `port` from the input and output operands of the contract to the operands of the
routine: at admitted operands of the shape of the contract (`NLAlib.Ops.BlockRel.Shaped`), the
numbers of operands are those of the routine (`NLAlib.Ops.Routine.nin`,
`NLAlib.Ops.Routine.nout`); `port` gives
separated operands of the routine, all of them operands of the contract; the buffer variables of
the tree are the inputs followed by the outputs; the routine reads the inputs and writes the
outputs, with the lengths of the contract; and it draws the window of the contract. -/
structure Implements (R : Routine Op Tst) (B : BlockRel K)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (port : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)) : Prop where
  /-- The numbers of dimensions agree. -/
  nd : B.nd = R.nd
  /-- The routine draws the window of the contract. -/
  draws : ∀ d, R.draws d = some (B.win d)
  /-- Admitted operands have the numbers of the implementation. -/
  fits : ∀ d ins outs, B.Shaped adm d ins outs →
    ins.length = R.nin ∧ outs.length = R.nout
  /-- The supplied operands of the routine, one per region. -/
  length : ∀ d ins outs, B.Shaped adm d ins outs → (port ins outs).length = R.arity
  /-- The operands of the routine are operands of the contract. -/
  mem : ∀ d ins outs, B.Shaped adm d ins outs → ∀ z ∈ port ins outs, z ∈ ins ++ outs
  /-- Admitted operands are separated operands of the routine. -/
  separated : ∀ d ins outs, B.Shaped adm d ins outs → R.SeparatedAt d (port ins outs)
  /-- The buffer variables of the tree are the inputs followed by the outputs. -/
  env : ∀ d ins outs, B.Shaped adm d ins outs →
    R.env (R.operands d (port ins outs)) = ins ++ outs
  /-- The routine reads the inputs. -/
  reads : ∀ d ins outs, B.Shaped adm d ins outs →
    R.readArgs (R.operands d (port ins outs)) = ins ∧ R.readLens d = B.inLens d
  /-- The routine writes the outputs. -/
  writes : ∀ d ins outs, B.Shaped adm d ins outs →
    R.writeArgs (R.operands d (port ins outs)) = outs ∧ R.writeLens d = B.outLens d
  /-- Every operand is reported: the contract of an operation states all its outputs. -/
  reported : R.allReported = true := by rfl

/-- A routine implements an operation contract when the seven facts of
`NLAlib.Ops.Routine.Implements` about admitted operands hold together at every admitted operands
of the shape of the contract. The tactic `implements` applies this with the dimensions and the
operands named, where all but the separation hold by computation. -/
theorem Implements.of_shaped {R : Routine Op Tst} {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {port : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)} (hnd : B.nd = R.nd)
    (hdraws : ∀ d, R.draws d = some (B.win d))
    (h : ∀ d ins outs, B.Shaped adm d ins outs →
      (ins.length = R.nin ∧ outs.length = R.nout) ∧ (port ins outs).length = R.arity ∧
      (∀ z ∈ port ins outs, z ∈ ins ++ outs) ∧ R.SeparatedAt d (port ins outs) ∧
      R.env (R.operands d (port ins outs)) = ins ++ outs ∧
      (R.readArgs (R.operands d (port ins outs)) = ins ∧ R.readLens d = B.inLens d) ∧
      (R.writeArgs (R.operands d (port ins outs)) = outs ∧ R.writeLens d = B.outLens d))
    (hrep : R.allReported = true := by rfl) : R.Implements B adm port where
  nd := hnd
  draws := hdraws
  fits d ins outs hs := (h d ins outs hs).1
  length d ins outs hs := (h d ins outs hs).2.1
  mem d ins outs hs := (h d ins outs hs).2.2.1
  separated d ins outs hs := (h d ins outs hs).2.2.2.1
  env d ins outs hs := (h d ins outs hs).2.2.2.2.1
  reads d ins outs hs := (h d ins outs hs).2.2.2.2.2.1
  writes d ins outs hs := (h d ins outs hs).2.2.2.2.2.2
  reported := hrep

/-- A routine that meets a specification meets, as an implementation, the operation contract it
implements, when at admitted operands the domain of the contract gives the precondition and the
postcondition gives the relation of the contract. The window of the contract is the window of
its stream at the position of the call. -/
theorem Meets.satisfies {R : Routine Op Tst} {I : Interp Op Tst K} {S : Spec K} (h : R.Meets I S)
    {B : BlockRel K} {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {port : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)} (hi : R.Implements B adm port)
    (hpre : ∀ d ins outs (τ : Tape K) p xs, B.Shaped adm d ins outs →
      B.dom d xs (τ.window B.stream p (B.win d)) → S.pre d (τ.shift p) xs)
    (hpost : ∀ d ins outs (τ : Tape K) p xs ys, B.Shaped adm d ins outs →
      S.post d (τ.shift p) xs ys → B.rel d xs (τ.window B.stream p (B.win d)) ys) :
    R.impl.Satisfies I .total (B.spec adm) := by
  refine Impl.satisfies_of_writes fun d ins outs τ m xs hnd hadm' hl hr hdom hz => ?_
  have hadm : B.Shaped adm d ins outs :=
    ⟨hnd, hadm', Mem.length_eq_of_readBlocks hr, hz.length_eq⟩
  obtain ⟨hin, hout⟩ := hi.fits d ins outs hadm
  obtain ⟨hra, hrl⟩ := hi.reads d ins outs hadm
  obtain ⟨hwa, hwl⟩ := hi.writes d ins outs hadm
  refine ⟨⟨hnd.trans hi.nd, hin, hout⟩, ?_⟩
  have hw := h d (port ins outs) τ m xs (hnd.trans hi.nd) (hi.length d ins outs hadm)
    (fun z hz => hl z (hi.mem d ins outs hadm z hz)) (hi.separated d ins outs hadm)
    (by rw [hra, hrl]; exact hr) (hpre d ins outs τ m.pos xs hadm hdom)
    (by rw [hwa, hwl]; exact hz)
  rw [hi.env d ins outs hadm, hwa, hwl] at hw
  refine hw.mono le_rfl fun m' _ ⟨hpos, ys, hys, hp⟩ =>
    ⟨hpos.eq_of_draws (hi.draws d), ys, ?_, hpost d ins outs τ m.pos xs ys hadm hp⟩
  change m'.readBlocks (R.outs (R.operands d (port ins outs))) (R.outs (R.lens d)) =
    some ys at hys
  rw [outs_eq_sel hi.reported, outs_eq_sel hi.reported] at hys
  change m'.readBlocks (R.writeArgs (R.operands d (port ins outs))) (R.writeLens d) =
    some ys at hys
  rw [hwa, hwl] at hys
  exact hys

/-! ### Specifications read off an operation contract -/

/-- The specification of a routine read off a block relation `B`, with a condition `ok` on the
dimensions: the precondition is `ok` and the domain of `B`, the postcondition is the relation of
`B`, both at the window of the stream of `B` drawn from the position of the call. -/
def Spec.ofRel (B : BlockRel K) (ok : List ℕ → Prop) : Spec K where
  pre d ω X := ok d ∧ B.dom d X (ω.window B.stream 0 (B.win d))
  post d ω X Y := B.rel d X (ω.window B.stream 0 (B.win d)) Y

/-- A routine that meets the specification read off a block relation meets, as an
implementation, every operation contract of that relation it implements whose admission gives
the condition on the dimensions. -/
theorem Meets.satisfies_ofRel {R : Routine Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {ok : List ℕ → Prop} (h : R.Meets I (Spec.ofRel B ok))
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {port : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)} (hi : R.Implements B adm port)
    (hok : ∀ d ins outs, B.Shaped adm d ins outs → ok d) :
    R.impl.Satisfies I .total (B.spec adm) :=
  h.satisfies hi
    (fun d ins outs τ p xs hs hdom => ⟨hok d ins outs hs, by
      rw [Tape.window_shift]
      exact hdom⟩)
    (fun d ins outs τ p xs ys _ hp => by
      change B.rel d xs ((τ.shift p).window B.stream 0 (B.win d)) ys at hp
      rw [Tape.window_shift] at hp
      exact hp)

/-- A routine that meets the specification read off a block relation `B` and draws its window
runs, at separated operands whose readable blocks are in the domain, as a call of an operation
with the relation `B`: the position advances by the window and the written blocks satisfy the
relation at the window of the tape. This is the form in which an operation contract with
several admitted layouts of its operands is derived from one routine for each layout. -/
theorem Meets.writes_ofRel {R : Routine Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {ok : List ℕ → Prop} (h : R.Meets I (Spec.ofRel B ok)) {d : List ℕ} {args : List (ℕ × ℕ)}
    {τ : Tape K} {m : Mem K} {xs : List (List K)} (hnd : d.length = R.nd)
    (hlen : args.length = R.arity) (hl : m.Live args) (hsep : R.SeparatedAt d args)
    (hr : m.readBlocks (R.readArgs (R.operands d args)) (R.readLens d) = some xs) (hok : ok d)
    (hdom : B.dom d xs (τ.window B.stream m.pos (B.win d)))
    (hroom : m.Room (R.writeArgs (R.operands d args)) (R.writeLens d))
    (hdraws : R.draws d = some (B.win d))
    (hrep : R.allReported = true := by rfl) :
    Writes .total I τ R.body (Env.frame d (R.env (R.operands d args)))
      (Fp.blocks (R.writeArgs (R.operands d args)) (R.writeLens d))
      (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys,
        m'.readBlocks (R.writeArgs (R.operands d args)) (R.writeLens d) = some ys ∧
          B.rel d xs (τ.window B.stream m.pos (B.win d)) ys) m := by
  refine (h d args τ m xs hnd hlen hl hsep hr ⟨hok, ?_⟩ hroom).mono le_rfl
    fun m' _ ⟨hpos, ys, hys, hp⟩ => ⟨hpos.eq_of_draws hdraws, ys, ?_, ?_⟩
  · rw [Tape.window_shift]
    exact hdom
  · change m'.readBlocks (R.outs (R.operands d args)) (R.outs (R.lens d)) = some ys at hys
    rwa [outs_eq_sel hrep, outs_eq_sel hrep] at hys
  · change B.rel d xs ((τ.shift m.pos).window B.stream 0 (B.win d)) ys at hp
    rw [Tape.window_shift] at hp
    exact hp

/-- The counted form of `NLAlib.Ops.Routine.Meets.writes_ofRel`: the run is within the static
count and workspace of the tree, and its final memory satisfies the update equation of the
relation at the written operands. This is how the counted statement of a routine, used to
account a linked operation, is derived from its judgment. -/
theorem Meets.runs_ofRel {R : Routine Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {ok : List ℕ → Prop} (h : R.Meets I (Spec.ofRel B ok)) (W : Op → List ℕ → ℕ) {d : List ℕ}
    {args : List (ℕ × ℕ)} {τ : Tape K} {m : Mem K} {xs : List (List K)} (hnd : d.length = R.nd)
    (hlen : args.length = R.arity) (hl : m.Live args) (hsep : R.SeparatedAt d args)
    (hr : m.readBlocks (R.readArgs (R.operands d args)) (R.readLens d) = some xs) (hok : ok d)
    (hdom : B.dom d xs (τ.window B.stream m.pos (B.win d)))
    (hroom : m.Room (R.writeArgs (R.operands d args)) (R.writeLens d))
    (hdraws : R.draws d = some (B.win d)) (hout : R.writeLens d = B.outLens d)
    (hrep : R.allReported = true := by rfl) :
    ConditionalRuns I W τ R.body (Env.frame d (R.env (R.operands d args))) m
      (stmtCost R.body (Env.frame d (R.env (R.operands d args))).idx)
      (stmtPeak W R.body (Env.frame d (R.env (R.operands d args))).idx)
      (B.Post d xs (R.writeArgs (R.operands d args)) (τ.window B.stream m.pos (B.win d)) m) := by
  have hw := h.writes_ofRel hnd hlen hl hsep hr hok hdom hroom hdraws hrep
  rw [hout] at hw
  exact Writes.runs_post W hw

/-- The written blocks of separated operands are pairwise disjoint, for a routine in which no
operand continues another. -/
theorem SeparatedAt.apart {R : Routine Op Tst} {d : List ℕ} {args : List (ℕ × ℕ)}
    (h : R.SeparatedAt d args) (hflat : R.flat = true := by rfl) :
    Fp.Apart (R.writeArgs args) (R.writeLens d) := by
  unfold SeparatedAt at h
  rw [Routine.regions_of_flat hflat] at h
  split at h
  · exact (h.blocks d).1
  · exact h.1

/-- A routine judgment from a run in operand form. If the routine draws the window of a
block relation `B` and writes blocks of its output lengths, and at separated operands with the
readable blocks in the domain the run ends in the memory of `B` in operand form
(`NLAlib.Ops.BlockRel.Post` at the written operands), then the routine meets the specification
read off `B`: the frame and the blocks read back follow from the separation. The routine has
no operand that continues another. -/
theorem meets_ofRel_of_post {R : Routine Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {ok : List ℕ → Prop} (hdraws : ∀ d, R.draws d = some (B.win d))
    (hout : ∀ d, d.length = R.nd → R.writeLens d = B.outLens d)
    (h : ∀ (d : List ℕ) (args : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) (xs : List (List K)),
      d.length = R.nd → args.length = R.ports.length → m.Live args → R.SeparatedAt d args →
      m.readBlocks (R.readArgs args) (R.readLens d) = some xs → ok d →
      B.dom d xs (τ.window B.stream m.pos (B.win d)) →
      m.Room (R.writeArgs args) (R.writeLens d) →
      Wp .total I τ R.body (Env.frame d (R.env args))
        (B.Post d xs (R.writeArgs args) (τ.window B.stream m.pos (B.win d)) m) m)
    (hflat : R.flat = true := by rfl)
    (hrep : R.allReported = true := by rfl) :
    R.Meets I (Spec.ofRel B ok) := by
  intro d args τ m xs hnd hlen hl hsep hr hpre hroom
  replace hlen := hlen.trans (arity_of_flat hflat)
  rw [operands_of_flat hflat d hlen] at hr hroom ⊢
  obtain ⟨hok, hdom⟩ := hpre
  change B.dom d xs ((τ.shift m.pos).window B.stream 0 (B.win d)) at hdom
  rw [Tape.window_shift] at hdom
  refine (h d args τ m xs hnd hlen hl hsep hr hok hdom hroom).mono fun m' hp => ?_
  obtain ⟨ys, hlens, hrel, rfl⟩ := hp
  have hL : ys.map List.length = R.writeLens d := hlens.trans (hout d hnd).symm
  refine ⟨?_, ?_, ys, ?_, ?_⟩
  · have hfr := Mem.eqOff_updBlocks (Store.EqOff.refl (Fp.blocks (R.writeArgs args)
      (ys.map List.length)) m.store) (m := m) (zs := R.writeArgs args) (ys := ys) le_rfl
    rw [hL] at hfr
    exact hfr
  · unfold Advances
    rw [hdraws d]
    change (m.updBlocks (R.writeArgs args) ys).pos + B.win d = m.pos + B.win d
    rw [Mem.pos_updBlocks]
  · have hrb := Mem.readBlocks_updBlocks (m := m) (zs := R.writeArgs args) (ys := ys)
      (hL ▸ hsep.apart hflat) (hL ▸ hroom)
    rw [hL] at hrb
    change Mem.readBlocks _ (R.outs args) (R.outs (R.lens d)) = some ys
    rw [outs_eq_sel hrep, outs_eq_sel hrep]
    change Mem.readBlocks _ (R.writeArgs args) (R.writeLens d) = some ys
    rw [Mem.readBlocks_congr (m' := (m.updBlocks (R.writeArgs args) ys).advance (B.win d))
      (m := m.updBlocks (R.writeArgs args) ys) rfl]
    exact hrb
  · change B.rel d xs ((τ.shift m.pos).window B.stream 0 (B.win d)) ys
    rw [Tape.window_shift]
    exact hrel

end Routine

end NLAlib.Ops
