/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextLinear
public import NLAlib.Ops.Logic.IsolatedLink

/-!
# Stored dense operators in isolated buffers

The guarded source laws of `NLAlib.Ops.Profiles.ContextLinear` for isolated buffers given by a
predicate on handles, as used by `NLAlib.Ops.Wp.linkContext_of_isolated`. The stored matrix
may be in any buffer that the ordinary outputs avoid.

## Main definitions

* `NLAlib.Ops.ContextLinear.guarded`: the guarded source interpreter.

## Main results

* `NLAlib.Ops.ContextDense.callS_source_of_ne`: the dense leaf satisfies the operator contract when
  the outputs are in buffers different from that of the data.
* `NLAlib.Ops.ContextLinear.guarded_satisfies`,
  `NLAlib.Ops.ContextLinear.guarded_laws`: the guarded source contracts.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDense

variable {Op Tst : Type} [Has ScalarOp Op]

/-- A isolated data capability implements the original exact operator contract. Its
matrix is decoded from the words actually read, while the ordinary output stays outside
the buffer of the data. The premise is a local primitive precondition, never a successful run.
A step in the proof of `NLAlib.Ops.ContextDense.callS_source_of_ne`,
`NLAlib.Ops.ContextDenseRounded.callS_source_of_ne`. -/
theorem source_wp_of_ne {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n : ℕ} (raw : List ℝ)
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : (((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
      (MatvecOperands n n)).on .total d ins outs tape mem).pre mem) :
    Wp .total I tape (impl context.length index).body (Env.frame d (context ++ ins ++ outs))
      ((((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
        (MatvecOperands n n)).on .total d ins outs tape mem).post mem) mem := by
  rcases hp with ⟨_, ⟨rfl, hApart⟩, hNeed⟩
  obtain ⟨hl, ⟨vals, hRead, _⟩, hRoom⟩ := hNeed rfl
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hRead
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hRoom
  have hXY : x.1 ≠ y.1 := hApart x (by simp) y (by simp)
  have hDY : y.1 ≠ context[index].1 := hOut y (by simp)
  have hAll : mem.Live (context ++ [x, y]) := by
    exact (Mem.live_append _ _ _).mpr ⟨hLive, hl⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply (impl_writes hS context index raw xs hAll hData hx
    (Fp.disj_inBlock_of_ne hDY) (Fp.disj_inBlock_of_ne hXY.symm) hy).wp
  intro mem' hFrame hResult
  have hr : mem'.readBlocks [y] [n] =
      some [(List.range n).map (StoredDense.row n n raw xs)] :=
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], hResult.2, rfl, rfl⟩
  have hf : mem.store.EqOff (Fp.blocks [y] [n]) mem'.store := by
    simpa [Fp.blocks] using hFrame
  have he := Mem.eq_updBlocks_of_eqOff hf hr hResult.1
  refine ⟨[xs], hRead, hRoom, [(List.range n).map (StoredDense.row n n raw xs)],
    by simp [matvecRel], ?_, ?_⟩
  · change decv id n ((List.range n).map (StoredDense.row n n raw xs)) = _
    rw [StoredDense.map_row_eq, decv_ofFn]
    rfl
  · simpa [matvecRel] using he

/-- An arbitrary source operation implemented by the selected dense context leaf meets
the original local matrix-vector post. This rule supports several stored operators in the
same program without duplicating the operand, liveness or frame argument. -/
theorem callS_source_of_ne {Src : Type} {I : Interp Op Tst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {table : ContextTable Src Op Tst} {o : Src}
    (hTable : table o = .inl (impl context.length index))
    {n : ℕ} (raw : List ℝ) {τ : Tape ℝ} {mem : Mem ℝ}
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : (((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
      (MatvecOperands n n)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext table context).callS o d ins outs τ mem)
      ((((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
        (MatvecOperands n n)).on .total d ins outs τ mem).post mem) := by
  have hw := source_wp_of_ne hS context index raw hLive hData hOut hp
  obtain ⟨_, ⟨rfl, _⟩, hn⟩ := hp
  obtain ⟨hl, ⟨xs, hr, _⟩, hz⟩ := hn rfl
  obtain ⟨x, vals, rfl, _, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨y, rfl, _⟩ := Mem.room_one hz
  rw [Interp.linkContext_callS_inl I hTable, if_pos hl]
  rw [if_pos (show (impl (Op := Op) (Tst := Tst) context.length index).Fits
    [n, n].length (context.length + [x].length) [y].length from ⟨rfl, rfl, rfl⟩)]
  exact hw

end NLAlib.Ops.ContextDense

namespace NLAlib.Ops.ContextLinear

/-- The actual context-linked matvec meets its source local post on an isolated raw
snapshot. All matrix arithmetic is performed by the declared scalar leaf. -/
theorem matvec_active {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n : ℕ} {C : ℕ → Prop} {reference : Store ℝ} (raw : List ℝ)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape ℝ} {mem : Mem ℝ}
    (hs : mem.Isolated C reference) (ho : ∀ z ∈ outs, ¬ C z.1)
    (hp : (((relation (StoredOperator.denseMatrix n n raw) .matvec).spec
      (admissible n .matvec)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext (table context.length index) context).callS
      .matvec d ins outs τ mem)
      ((((relation (StoredOperator.denseMatrix n n raw) .matvec).spec
        (admissible n .matvec)).on .total d ins outs τ mem).post mem) := by
  have hi := hc context[index] (List.getElem_mem ..)
  have hd := (hs.2.readBlock hi context[index].2 (n * n)).trans hData
  exact ContextDense.callS_source_of_ne hS context index rfl raw (hs.live hc) hd
    (fun z hz he => ho z hz (he ▸ hi)) hp

/-- Isolated raw data and ordinary local primitive laws give globally valid source
contracts for the proof-side guard. The fallback is used only outside the isolated regime. -/
theorem satisfies_guarded {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : IsExactBlas1 id (fun _ => True) I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n : ℕ} {C : ℕ → Prop} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (fallback : Interp Standard.Operation CmpTst ℝ)
    (hFallback : ∀ o, fallback.Satisfies .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))) :
    ∀ o, ((I.linkContext (table context.length index) context).guardIsolated
      (fun o => (relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))
      (Mem.Isolated C reference) C fallback).Satisfies .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o)) := by
  intro o
  apply Interp.satisfies_guardIsolated _ _ _ _ _ _ (hFallback o)
  intro d ins outs τ mem hs ho hp
  cases o with
  | scalar o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    exact hS o d ins outs τ mem hp
  | blas o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    cases o with
    | sum => exact hB.sum d ins outs τ mem hp
    | dot => exact hB.dot d ins outs τ mem hp
    | axpy => exact hB.axpy d ins outs τ mem hp
    | nrm2 => exact hB.nrm2 d ins outs τ mem hp
    | scal => exact hB.scal d ins outs τ mem hp
    | copy => exact hB.copy d ins outs τ mem hp
  | matvec => exact matvec_active hS context index raw hc hData hs ho hp

/-- The guarded source interpreter, a proof device determined by the actual context and
the raw matrix snapshot. All target instructions remain the explicitly linked program. -/
noncomputable def guarded (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (C : ℕ → Prop)
    (reference : Store ℝ) (n : ℕ) (raw : List ℝ) : Interp Standard.Operation CmpTst ℝ :=
  (I.linkContext (table context.length index) context).guardIsolated
    (fun o => (relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))
    (Mem.Isolated C reference) C
    (fallback (StoredOperator.denseMatrix n n raw))

/-- Ordinary exact scalar/vector laws and isolated raw data give every guarded source
contract. No source execution assumption is required to establish these local laws. -/
theorem guarded_satisfies {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n : ℕ} {C : ℕ → Prop} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    ∀ o, (guarded I context index C reference n raw).Satisfies .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o)) :=
  satisfies_guarded hS hB.toExactBlas1 context index reference raw hc hData _
    (fallback_satisfies _)

/-- Exact numerical interfaces for reusing the source algorithm word theorem. The matrix
is the decoder of the actual raw words; comparisons remain those of the target interpreter. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n : ℕ} {C : ℕ → Prop} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    let J := guarded I context index C reference n raw
    IsScalar RCLikeBlas.machine J ∧ IsExactBlas1 id (fun _ => True) J ∧
      IsExactMatvec id (StoredOperator.denseMatrix n n raw) J ∧ IsCmp id J := by
  obtain ⟨hs, hb, ha⟩ :=
    laws (guarded_satisfies hS hB context index reference raw hc hData)
  exact ⟨hs, hb, ha, hCmp⟩

end NLAlib.Ops.ContextLinear
