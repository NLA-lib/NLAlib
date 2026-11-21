/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextLinearRounded
public import NLAlib.Ops.Logic.Isolated

/-!
# The rounded stored-operator profile, isolated as a set of buffers

The statements of `NLAlib.Ops.Profiles.ContextDenseRounded` and
`NLAlib.Ops.Profiles.ContextLinearRounded` with the isolated prefix of buffers replaced by an
arbitrary predicate on buffer handles (`NLAlib.Ops.Mem.Isolated`): an output must only be in a
buffer different from that of the data.

## Main results

* `NLAlib.Ops.ContextDenseRounded.callS_source_of_ne`,
  `NLAlib.Ops.ContextDenseRounded.callS_source_fn_of_ne`: the rounded dense leaf.
* `NLAlib.Ops.ContextLinearRounded.satisfies_guarded`,
  `NLAlib.Ops.ContextLinearRounded.guarded_laws`: the guarded source contracts.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDenseRounded

open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Functional refinement of the isolated dense leaf. The function is the actual scalar
word recurrence, and its operands retain the matrix product's separate-output admission. -/
theorem source_wp_fn_of_ne {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n : ℕ} (raw : List ℝ)
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : ((((matvecFn (wordKernel M n raw)).rel).spec
      (MatvecOperands n n)).on .total d ins outs tape mem).pre mem) :
    Wp .total I tape (ContextDense.impl context.length index).body
      (Env.frame d (context ++ ins ++ outs))
      (((((matvecFn (wordKernel M n raw)).rel).spec
        (MatvecOperands n n)).on .total d ins outs tape mem).post mem) mem := by
  rcases hp with ⟨_, ⟨rfl, hApart⟩, hNeed⟩
  obtain ⟨hl, ⟨vals, hRead, _⟩, hRoom⟩ := hNeed rfl
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hRead
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hRoom
  have hXY : x.1 ≠ y.1 := hApart x (by simp) y (by simp)
  have hDY : y.1 ≠ context[index].1 := hOut y (by simp)
  have hAll : mem.Live (context ++ [x, y]) :=
    (Mem.live_append _ _ _).mpr ⟨hLive, hl⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply (ContextDense.impl_writes_word hS context index raw xs hAll hData hx
    (Fp.disj_inBlock_of_ne hDY) (Fp.disj_inBlock_of_ne hXY.symm) hy).wp
  intro mem' hFrame hResult
  have hr : mem'.readBlocks [y] [n] =
      some [(List.range n).map (StoredDense.rowWord M n n raw xs)] :=
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], hResult.2, rfl, rfl⟩
  have hf : mem.store.EqOff (Fp.blocks [y] [n]) mem'.store := by
    simpa [Fp.blocks] using hFrame
  have he := Mem.eq_updBlocks_of_eqOff hf hr hResult.1
  refine ⟨[xs], hRead, hRoom, [(List.range n).map (StoredDense.rowWord M n n raw xs)],
    ?_, ?_, ?_⟩
  · simp [BlockFn.rel, matvecFn, BlockFn.of1]
  · simp only [BlockFn.rel, matvecFn, BlockFn.of1, ↓reduceIte]
    rw [output_eq_ofFn_wordKernel M n raw xs (Store.length_of_readBlock hx)]
    rfl
  · simpa [BlockFn.rel, matvecFn, BlockFn.of1] using he

/-- A selected context leaf supplies a functional matrix-vector call, including its actual
rounded output, without requiring a local accuracy or whole-algorithm callback. -/
theorem callS_source_fn_of_ne {Src : Type} {I : Interp Op Tst ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {table : ContextTable Src Op Tst} {o : Src}
    (hTable : table o = .inl (ContextDense.impl context.length index))
    {n : ℕ} (raw : List ℝ) {τ : Tape ℝ} {mem : Mem ℝ}
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : ((((matvecFn (wordKernel M n raw)).rel).spec
      (MatvecOperands n n)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext table context).callS o d ins outs τ mem)
      (((((matvecFn (wordKernel M n raw)).rel).spec
        (MatvecOperands n n)).on .total d ins outs τ mem).post mem) := by
  have hw := source_wp_fn_of_ne hS context index raw hLive hData hOut hp
  obtain ⟨_, ⟨rfl, _⟩, hn⟩ := hp
  obtain ⟨hl, ⟨xs, hr, _⟩, hz⟩ := hn rfl
  obtain ⟨x, vals, rfl, _, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨y, rfl, _⟩ := Mem.room_one hz
  rw [Interp.linkContext_callS_inl I hTable, if_pos hl]
  rw [if_pos (show (ContextDense.impl (Op := Op) (Tst := Tst) context.length index).Fits
    [n, n].length (context.length + [x].length) [y].length from ⟨rfl, rfl, rfl⟩)]
  exact hw

/-- A isolated data capability implements the original exact operator contract. Its
matrix is decoded from the words actually read, while the ordinary output stays outside
the buffer of the data. The premise is a local primitive precondition, never a successful run. -/
theorem source_wp_of_ne {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n : ℕ} {error : ℝ} (raw : List ℝ)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : (((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
      (MatvecOperands n n)).on .total d ins outs tape mem).pre mem) :
    Wp .total I tape (ContextDense.impl context.length index).body
      (Env.frame d (context ++ ins ++ outs))
      ((((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
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
  apply (ContextDense.impl_writes_word hS context index raw xs hAll hData hx
    (Fp.disj_inBlock_of_ne hDY) (Fp.disj_inBlock_of_ne hXY.symm) hy).wp
  intro mem' hFrame hResult
  have hr : mem'.readBlocks [y] [n] =
      some [(List.range n).map (StoredDense.rowWord M n n raw xs)] :=
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], hResult.2, rfl, rfl⟩
  have hf : mem.store.EqOff (Fp.blocks [y] [n]) mem'.store := by
    simpa [Fp.blocks] using hFrame
  have he := Mem.eq_updBlocks_of_eqOff hf hr hResult.1
  refine ⟨[xs], hRead, hRoom, [(List.range n).map (StoredDense.rowWord M n n raw xs)],
    by simp [matvecErrorRel], ?_, ?_⟩
  · exact hError xs
  · simpa [matvecErrorRel] using he

/-- An arbitrary source operation implemented by the selected dense context leaf meets
the original local matrix-vector post. This rule supports several stored operators in the
same program without duplicating the operand, liveness or frame argument. -/
theorem callS_source_of_ne {Src : Type} {I : Interp Op Tst ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {table : ContextTable Src Op Tst} {o : Src}
    (hTable : table o = .inl (ContextDense.impl context.length index))
    {n : ℕ} {error : ℝ} (raw : List ℝ)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    {τ : Tape ℝ} {mem : Mem ℝ}
    (hLive : mem.Live context)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} (hOut : ∀ z ∈ outs, z.1 ≠ context[index].1)
    (hp : (((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
      (MatvecOperands n n)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext table context).callS o d ins outs τ mem)
      ((((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
        (MatvecOperands n n)).on .total d ins outs τ mem).post mem) := by
  have hw := source_wp_of_ne hS context index raw hError hLive hData hOut hp
  obtain ⟨_, ⟨rfl, _⟩, hn⟩ := hp
  obtain ⟨hl, ⟨xs, hr, _⟩, hz⟩ := hn rfl
  obtain ⟨x, vals, rfl, _, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨y, rfl, _⟩ := Mem.room_one hz
  rw [Interp.linkContext_callS_inl I hTable, if_pos hl]
  rw [if_pos (show (ContextDense.impl (Op := Op) (Tst := Tst) context.length index).Fits
    [n, n].length (context.length + [x].length) [y].length from ⟨rfl, rfl, rfl⟩)]
  exact hw

end NLAlib.Ops.ContextDenseRounded

namespace NLAlib.Ops.ContextLinearRounded

open scoped Matrix

/-- A context-isolated scalar dense product meets its rounded local source contract. Its
error premise concerns only the actual word kernel, not an execution of the enclosing program. -/
theorem matvec_active {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    (hS : IsScalar M I) (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n : ℕ} {C : ℕ → Prop} {reference : Store ℝ} (raw : List ℝ) {e : Blas1Err} {error : ℝ}
    {ok : ℕ → Prop}
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape ℝ} {mem : Mem ℝ}
    (hs : mem.Isolated C reference) (ho : ∀ z ∈ outs, ¬ C z.1)
    (hp : (((relation M e (StoredOperator.denseMatrix n n raw) error .matvec).spec
      (admissible ok n .matvec)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext (ContextLinear.table context.length index) context).callS
      .matvec d ins outs τ mem)
      ((((relation M e (StoredOperator.denseMatrix n n raw) error .matvec).spec
        (admissible ok n .matvec)).on .total d ins outs τ mem).post mem) := by
  have hi := hc context[index] (List.getElem_mem ..)
  have hd := (hs.2.readBlock hi context[index].2 (n * n)).trans hData
  exact ContextDenseRounded.callS_source_of_ne hS context index rfl raw hError
    (hs.live hc) hd (fun z hz he => ho z hz (he ▸ hi)) hp

/-- Isolated matrix data and the target's local scalar/vector contracts give exhaustive
rounded source laws for the proof-side guarded interpretation. -/
theorem satisfies_guarded {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {e : Blas1Err} {ok : ℕ → Prop} (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) {n : ℕ} {C : ℕ → Prop}
    (reference : Store ℝ) (raw : List ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    ∀ o, ((I.linkContext (ContextLinear.table context.length index) context).guardIsolated
      (fun o => (relation M e (StoredOperator.denseMatrix n n raw) error o).spec
        (admissible ok n o)) (Mem.Isolated C reference) C
      (fallback I (StoredOperator.denseMatrix n n raw))).Satisfies .total o
      ((relation M e (StoredOperator.denseMatrix n n raw) error o).spec (admissible ok n o)) := by
  intro o
  apply Interp.satisfies_guardIsolated _ _ _ _ _ _ (fallback_satisfies hS hB _ herror o)
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
  | matvec => exact matvec_active hS context index raw hError hc hData hs ho hp

/-- Guarded rounded source laws for reusing an existing total numerical word theorem.
The isolated matrix is decoded from the raw input words and comparisons stay unchanged. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {e : Blas1Err} {ok : ℕ → Prop} (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (hCmp : IsCmp id I) (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n : ℕ} {C : ℕ → Prop} (reference : Store ℝ) (raw : List ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, C z.1)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    let J := (I.linkContext (ContextLinear.table context.length index) context).guardIsolated
      (fun o => (relation M e (StoredOperator.denseMatrix n n raw) error o).spec
        (admissible ok n o)) (Mem.Isolated C reference) C
      (fallback I (StoredOperator.denseMatrix n n raw))
    IsScalar M J ∧ IsBlas1 id e ok J ∧
      IsMatvec id (StoredOperator.denseMatrix n n raw) error J ∧ IsCmp id J := by
  obtain ⟨hs, hb, ha⟩ := laws
    (satisfies_guarded hS hB context index reference raw herror hError hc hData)
  exact ⟨hs, hb, ha, hCmp⟩

end NLAlib.Ops.ContextLinearRounded
