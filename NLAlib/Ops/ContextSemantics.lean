/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Context

/-!
# Semantics of explicitly forwarded context

The induced interpretation binds actual context operands only as a proof device. The
translated tree passes those same operands explicitly through every frame. Its run agrees
with the source run, without assuming that context values are read-only; protecting data
is a separate local-contract obligation when deriving a stored-operator algorithm.

## Main results

* `NLAlib.Ops.Interp.linkContext`: the induced proof-side interpretation.
* `NLAlib.Ops.run_linkContext_call`: exact local linking semantics.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Lo Tst K : Type}

/-- Bind actual context operands for the source interpretation. Implemented operations
receive them as extra leading inputs. The executed target syntax forwards them explicitly. -/
def Interp.linkContext (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) : Interp Op Tst K where
  call o d ins outs τ m := match T o with
    | .inl R =>
        if R.Fits d.length (context.length + ins.length) outs.length then
          eval I τ R.body (Env.frame d (context ++ ins ++ outs)) m
        else none
    | .inr o' => I.call o' d ins outs τ m
  test := I.test
  index := I.index

/-- Queries read only their original operands after shifting; context is never added. -/
theorem Interp.testAt_linkContext (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (slot : ℕ) (q : Tst) (ds : List IExp) (ins : List Operand)
    (ρ : Env) (m : Mem K) (hslot : slot ≤ ρ.idx.length) :
    I.testAt q (ds.map (IExp.liftContext context.length slot))
        (ins.map (Operand.liftContext context.length slot)) (ρ.withContext context slot) m =
      (I.linkContext T context).testAt q ds ins ρ m := by
  simp only [Interp.testAt, IExp.evalList_withContext ds context slot ρ hslot,
    Operand.evalList_liftContext context slot ρ ins hslot, Interp.linkContext]

/-- Kept operations retain exactly their original call behavior. -/
theorem Interp.linkContext_callS_inr (I : Interp Lo Tst K)
    {T : ContextTable Op Lo Tst} {o : Op} {o' : Lo} (hT : T o = .inr o')
    (context : List (ℕ × ℕ)) (d : List ℕ) (ins outs : List (ℕ × ℕ))
    (τ : Tape K) (m : Mem K) :
    (I.linkContext T context).callS o d ins outs τ m = I.callS o' d ins outs τ m := by
  simp only [Interp.callS, Interp.linkContext, hT]

/-- Implemented operations execute the declared body at the extra context inputs.
The core's shape check is redundant because every statement preserves store shape. -/
theorem Interp.linkContext_callS_inl (I : Interp Lo Tst K)
    {T : ContextTable Op Lo Tst} {o : Op} {R : Impl Lo Tst} (hT : T o = .inl R)
    (context : List (ℕ × ℕ)) (d : List ℕ) (ins outs : List (ℕ × ℕ))
    (τ : Tape K) (m : Mem K) :
    (I.linkContext T context).callS o d ins outs τ m =
      if m.Live (ins ++ outs) then
        if R.Fits d.length (context.length + ins.length) outs.length then
          eval I τ R.body (Env.frame d (context ++ ins ++ outs)) m
        else none
      else none := by
  simp only [Interp.callS, Interp.linkContext, hT]
  split_ifs with hl hfit
  · cases hr : eval I τ R.body (Env.frame d (context ++ ins ++ outs)) m with
    | none => rfl
    | some m' => simp [shape_store_of_run hr]
  · rfl
  · rfl

/-- A context-linked primitive call has the exact source semantics, including failure.
Context liveness is the only extra semantic premise; no hidden data read is performed. -/
theorem run_linkContext_call (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (context : List (ℕ × ℕ)) (slot : ℕ) (τ : Tape K) (o : Op)
    (ds : List IExp) (ins outs : List Operand) (ρ : Env) (m : Mem K)
    (hslot : slot ≤ ρ.idx.length) (hLive : m.Live context) :
    eval I τ ((Stmt.call o ds ins outs).linkContext context.length slot T)
        (ρ.withContext context slot) m =
      eval (I.linkContext T context) τ (.call o ds ins outs) ρ m := by
  have hdims : IExp.evalList (ρ.withContext context slot).idx
      (ds.map (IExp.liftContext context.length slot)) = IExp.evalList ρ.idx ds := by
    simpa only [Env.withContext, List.length_map] using
      IExp.evalList_liftContext ds ρ.idx (context.map Prod.snd) slot hslot
  have hins := Operand.evalList_liftContext context slot ρ ins hslot
  have houts := Operand.evalList_liftContext context slot ρ outs hslot
  have hctx := evalList_contextOperands context slot ρ hslot
  cases hT : T o with
  | inr o' =>
    simp only [Stmt.linkContext, hT, eval, hdims, hins, houts,
      Interp.linkContext_callS_inr I hT]
  | inl R =>
    simp only [Stmt.linkContext, hT, eval, Interp.linkContext_callS_inl I hT]
    cases hd : IExp.evalList ρ.idx ds with
    | none => split_ifs <;> simp [eval, hdims, hd]
    | some d =>
      cases ha : Operand.evalList ρ ins with
      | none => split_ifs <;> simp [eval, hdims, hins, hd, ha, Operand.evalList_append]
      | some a =>
        cases hb : Operand.evalList ρ outs with
        | none =>
          split_ifs <;> simp [eval, hdims, hins, houts, hctx, hd, ha, hb,
            Operand.evalList_append]
        | some b =>
          have h1 := IExp.length_of_evalList hd
          have h2 := Operand.length_of_evalList ha
          have h3 := Operand.length_of_evalList hb
          have hfit : R.Fits d.length (context.length + a.length) b.length ↔
              R.Fits ds.length (context.length + ins.length) outs.length := by rw [h1, h2, h3]
          simp only [Option.bind_some]
          by_cases hf : R.Fits ds.length (context.length + ins.length) outs.length
          · rw [if_pos hf, if_pos (hfit.mpr hf)]
            simp [eval, hdims, hins, houts, hctx, hd, ha, hb, Operand.evalList_append,
              Mem.live_append, hLive, List.append_assoc]
          · rw [if_neg hf, if_neg (hfit.not.mpr hf)]
            simp [eval]

end NLAlib.Ops
