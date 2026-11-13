/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextDense

/-!
# Rounded dense context calls

The existing fixed dense leaf reads the declared protected raw matrix and performs the
supplied machine's scalar operations. A local numerical kernel bound transfers to its
operator contract; totality and storage preservation follow from the generic word proof.

## Main results

* `NLAlib.Ops.ContextDenseRounded.wp_source`: total rounded source postcondition.
* `NLAlib.Ops.ContextDenseRounded.callS_source`: local context-call refinement.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDenseRounded

open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The same fixed scalar leaf as the exact context profile, with the supplied machine. -/
abbrev impl (count index : ℕ) : Impl Op Tst := ContextDense.impl count index

/-- A protected data capability implements the original exact operator contract. Its
matrix is decoded from the words actually read, while the ordinary output stays outside
the protected prefix. The premise is a local primitive precondition, never a successful run. -/
theorem wp_source {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n cutoff : ℕ} {error : ℝ} (raw : List ℝ)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hLive : mem.Live context) (hProtected : context[index].1 < cutoff)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    (hOut : ∀ z ∈ outs, cutoff ≤ z.1)
    (hp : (((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
      (MatvecOperands n n)).on .total d ins outs tape mem).pre mem) :
    Wp .total I tape (impl context.length index).body (Env.frame d (context ++ ins ++ outs))
      ((((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
        (MatvecOperands n n)).on .total d ins outs tape mem).post mem) mem := by
  rcases hp with ⟨_, ⟨rfl, hApart⟩, hNeed⟩
  obtain ⟨hl, ⟨vals, hRead, _⟩, hRoom⟩ := hNeed rfl
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hRead
  obtain ⟨y, rfl, hy⟩ := Mem.room_one hRoom
  have hXY : x.1 ≠ y.1 := hApart x (by simp) y (by simp)
  have hDY : y.1 ≠ context[index].1 := by
    have := hOut y (by simp)
    omega
  have hAll : mem.Live (context ++ [x, y]) := by
    exact (Mem.live_append _ _ _).mpr ⟨hLive, hl⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply (ContextDense.writes_impl_word hS context index raw xs hAll hData hx
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
theorem callS_source {Src : Type} {I : Interp Op Tst ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {table : ContextTable Src Op Tst} {o : Src}
    (hTable : table o = .inl (impl context.length index))
    {n cutoff : ℕ} {error : ℝ} (raw : List ℝ)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    {τ : Tape ℝ} {mem : Mem ℝ}
    (hLive : mem.Live context) (hProtected : context[index].1 < cutoff)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} (hOut : ∀ z ∈ outs, cutoff ≤ z.1)
    (hp : (((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
      (MatvecOperands n n)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext table context).callS o d ins outs τ mem)
      ((((matvecErrorRel id (StoredOperator.denseMatrix n n raw) error).spec
        (MatvecOperands n n)).on .total d ins outs τ mem).post mem) := by
  have hw := wp_source hS context index raw hError hLive hProtected hData hOut hp
  obtain ⟨_, ⟨rfl, _⟩, hn⟩ := hp
  obtain ⟨hl, ⟨xs, hr, _⟩, hz⟩ := hn rfl
  obtain ⟨x, vals, rfl, _, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨y, rfl, _⟩ := Mem.room_one hz
  rw [Interp.linkContext_callS_inl I hTable, if_pos hl]
  rw [if_pos (show (impl (Op := Op) (Tst := Tst) context.length index).Fits
    [n, n].length (context.length + [x].length) [y].length from ⟨rfl, rfl, rfl⟩)]
  exact hw

end NLAlib.Ops.ContextDenseRounded
