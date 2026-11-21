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
* `NLAlib.Ops.ContextDense.writes_impl_word` transfers the actual machine-word execution.
* `NLAlib.Ops.ContextDense.writes_impl` is its exact-arithmetic specialization.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDense

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The entry of a context table (`NLAlib.Ops.ContextTable`) for a product with a stored
matrix: select context input `index` and the ordinary vector input, then execute the dense scalar
leaf. The index is fixed syntax; out-of-range context selection cannot obtain a certificate.

It is an `Impl`, not built from a routine: its first `count` inputs are the context that
`NLAlib.Ops.Stmt.linkContext` forwards to every call (the stored data of the linked program), not
operands of the product, so it has no interface of its own; its contract is proved by the context
linking lemmas (`NLAlib.Ops.ContextLinear`). -/
def impl (count index : ℕ) : Impl Op Tst :=
  ⟨2, count + 1, 1, .frame [.var 0, .var 1]
    [⟨index, .var (2 + index)⟩, ⟨count, .var (2 + count)⟩,
      ⟨count + 1, .var (2 + (count + 1))⟩] StoredDense.impl⟩

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
theorem writes_impl_word {I : Interp Op Tst ℝ} {tape : Tape ℝ} {mem : Mem ℝ}
    {M : Machine ℝ} (hS : IsScalar M I) (context : List (ℕ × ℕ))
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
        some ((List.range m).map (StoredDense.rowWord M m n ds xs))) mem := by
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
    (StoredDense.writes_impl_word hS ds xs
      (fun a ha => hl a (by simp at ha ⊢; aesop)) hD hX hYD hYX hy)

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
        some ((List.range m).map (StoredDense.row m n ds xs))) mem  := by
  have hr : StoredDense.rowWord RCLikeBlas.machine m n ds xs =
      StoredDense.row m n ds xs := funext (StoredDense.rowWord_exact m n ds xs)
  simpa only [hr] using
    (writes_impl_word (tape := tape) (M := RCLikeBlas.machine) hS context index ds xs
      hl hD hX hYD hYX hy)

end NLAlib.Ops.ContextDense
