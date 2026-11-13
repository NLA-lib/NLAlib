/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.StoredDense
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.ContextSemantics

/-!
# Explicit dense operands for operator calls with context

One fixed leaf selects a declared matrix-data capability from the leading context
operands and forwards it to the scalar dense implementation. The ordinary vector operands
retain their interface. Matrix words are read by the actual scalar program.

## Main results

* `NLAlib.Ops.ContextDense.impl` selects a matrix from a fixed context interface.
* `NLAlib.Ops.ContextDense.writes_impl` transfers the dense word execution.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDense

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Select one context input and the ordinary vector input, then execute the dense scalar
leaf. The index is fixed syntax; out-of-range context selection cannot obtain a certificate. -/
def impl (count index : ℕ) : Impl Op Tst :=
  ⟨2, count + 1, 1, .frame [.var 0, .var 1]
    [⟨index, .var (2 + index)⟩, ⟨count, .var (2 + count)⟩,
      ⟨count + 1, .var (2 + (count + 1))⟩] StoredDense.impl.body⟩

/-- Forwarding context reserves no payload. The selected dense scalar leaf needs at most
one temporary cell, independently of dimensions, input values and context arity. -/
theorem stmtPeak_impl_zero (count index m n : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (impl (Op := Op) (Tst := Tst) count index).body
      ([m, n] ++ offs) ≤ 1 :=
  stmtPeak_frame_le rfl (fun args => (StoredDense.stmtPeak_impl_zero m n args).le)

/-- A positional operand of a frame recovers its exact declared capability. -/
theorem eval_frameOperand (d : List ℕ) (args : List (ℕ × ℕ)) (i : Fin args.length) :
    (Operand.mk i (.var (d.length + i))).eval (Env.frame d args) = some args[i] := by
  simp [Operand.eval, Env.frame, IExp.eval]

/-- Context forwarding preserves the actual dense execution and its output footprint.
No abstract matrix-vector call is executed by this leaf. -/
theorem writes_impl {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {m n : ℕ} {x y : ℕ × ℕ} (ds xs : List ℝ)
    (hl : mem.Live (context ++ [x, y]))
    (hD : mem.store.readBlock context[index].1 context[index].2 (m * n) = some ds)
    (hX : mem.store.readBlock x.1 x.2 n = some xs)
    (hYD : Fp.Disj (Store.inBlock y.1 y.2 m)
      (Store.inBlock context[index].1 context[index].2 (m * n)))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock x.1 x.2 n))
    (hy : y.2 + m ≤ mem.store.len y.1) :
    Writes .total I tape (impl context.length index).body
      (Env.frame [m, n] (context ++ [x, y])) (Store.inBlock y.1 y.2 m)
      (fun mem' => mem'.pos = mem.pos ∧ mem'.store.readBlock y.1 y.2 m =
        some ((List.range m).map (StoredDense.row m n ds xs))) mem := by
  have hd : IExp.evalList (Env.frame [m, n] (context ++ [x, y])).idx [.var 0, .var 1] =
      some [m, n] := rfl
  have hc := eval_frameOperand [m, n] (context ++ [x, y])
    ⟨index, by simp; omega⟩
  have hx := eval_frameOperand [m, n] (context ++ [x, y])
    ⟨context.length, by simp⟩
  have hy' := eval_frameOperand [m, n] (context ++ [x, y])
    ⟨context.length + 1, by simp⟩
  have ha : Operand.evalList (Env.frame [m, n] (context ++ [x, y]))
      [⟨index, .var (2 + index)⟩, ⟨context.length, .var (2 + context.length)⟩,
        ⟨context.length + 1, .var (2 + (context.length + 1))⟩] =
      some [context[index], x, y] := by
    simp only [List.length_cons, List.length_nil] at hc hx hy'
    simp at hc hx hy'
    simp only [Operand.evalList_cons, Operand.evalList_nil, hc, hx, hy',
      Option.bind_some, Option.map_some]
    rfl
  exact writes_frame hd ha (fun a ha => hl a (by simp at ha ⊢; aesop))
    (StoredDense.writes_impl hS ds xs
      (fun a ha => hl a (by simp at ha ⊢; aesop)) hD hX hYD hYX hy)

/-- A protected data capability implements the original exact operator contract. Its
matrix is decoded from the words actually read, while the ordinary output stays outside
the protected prefix. The premise is a local primitive precondition, never a successful run. -/
theorem wp_source {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n cutoff : ℕ} (raw : List ℝ)
    (hLive : mem.Live context) (hProtected : context[index].1 < cutoff)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    (hOut : ∀ z ∈ outs, cutoff ≤ z.1)
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
  have hDY : y.1 ≠ context[index].1 := by
    have := hOut y (by simp)
    omega
  have hAll : mem.Live (context ++ [x, y]) := by
    exact (Mem.live_append _ _ _).mpr ⟨hLive, hl⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply (writes_impl hS context index raw xs hAll hData hx
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
theorem callS_source {Src : Type} {I : Interp Op Tst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {table : ContextTable Src Op Tst} {o : Src}
    (hTable : table o = .inl (impl context.length index))
    {n cutoff : ℕ} (raw : List ℝ) {τ : Tape ℝ} {mem : Mem ℝ}
    (hLive : mem.Live context) (hProtected : context[index].1 < cutoff)
    (hData : mem.store.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} (hOut : ∀ z ∈ outs, cutoff ≤ z.1)
    (hp : (((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
      (MatvecOperands n n)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext table context).callS o d ins outs τ mem)
      ((((matvecRel id (StoredOperator.denseMatrix n n raw)).spec
        (MatvecOperands n n)).on .total d ins outs τ mem).post mem) := by
  have hw := wp_source hS context index raw hLive hProtected hData hOut hp
  obtain ⟨_, ⟨rfl, _⟩, hn⟩ := hp
  obtain ⟨hl, ⟨xs, hr, _⟩, hz⟩ := hn rfl
  obtain ⟨x, vals, rfl, _, rfl⟩ := Mem.readBlocks_one hr
  obtain ⟨y, rfl, _⟩ := Mem.room_one hz
  rw [Interp.linkContext_callS_inl I hTable, if_pos hl]
  rw [if_pos (show (impl (Op := Op) (Tst := Tst) context.length index).Fits
    [n, n].length (context.length + [x].length) [y].length from ⟨rfl, rfl, rfl⟩)]
  exact hw

end NLAlib.Ops.ContextDense
