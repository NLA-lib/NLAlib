/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link


/-!
# Linking with explicitly forwarded context operands

A fixed collection of context operands precedes ordinary buffer variables. Its offsets
occupy a block inserted among the index variables. Every procedure frame forwards the
context explicitly. Allocation and loop binders retain their ordinary append behavior.
Selected operations receive the context as extra implementation inputs; queries keep
only their original, shifted operands.

## Main results

* `NLAlib.Ops.Stmt.linkContext`: the fixed syntax transformation.
* `NLAlib.Ops.Env.withContext`: the corresponding environment extension.
-/

@[expose] public section

namespace NLAlib.Ops

namespace IExp

/-- Reserve an index block without changing the meaning of any original variable. -/
def liftContext (count slot : ℕ) : IExp → IExp
  | .var i => .var (if i < slot then i else i + count)
  | .const n => .const n
  | .add a b => .add (a.liftContext count slot) (b.liftContext count slot)
  | .mul a b => .mul (a.liftContext count slot) (b.liftContext count slot)
  | .sub a b => .sub (a.liftContext count slot) (b.liftContext count slot)
  | .div a b => .div (a.liftContext count slot) (b.liftContext count slot)

/-- Original expression evaluation is preserved, including unbound-variable failure. -/
theorem eval_liftContext (e : IExp) (idx added : List ℕ) (slot : ℕ)
    (hslot : slot ≤ idx.length) :
    (e.liftContext added.length slot).eval (idx.take slot ++ added ++ idx.drop slot) =
      e.eval idx := by
  induction e with
  | var i =>
    change (idx.take slot ++ added ++ idx.drop slot)[if i < slot then i else i + added.length]? =
      idx[i]?
    rw [List.append_assoc]
    have hlen : (idx.take slot).length = slot := by
      simp only [List.length_take, Nat.min_eq_left hslot]
    by_cases hi : i < slot
    · rw [if_pos hi, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
    · rw [if_neg hi, List.getElem?_append_right (by omega), hlen,
        List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1
      omega
  | const n => rfl
  | add a b ha hb | mul a b ha hb | sub a b ha hb | div a b ha hb =>
    simp only [liftContext, eval, ha, hb]

/-- A dimension list retains its exact values under the same inserted block. -/
theorem evalList_liftContext (es : List IExp) (idx added : List ℕ) (slot : ℕ)
    (hslot : slot ≤ idx.length) :
    evalList (idx.take slot ++ added ++ idx.drop slot)
      (es.map (liftContext added.length slot)) = evalList idx es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, evalList_cons, eval_liftContext, hslot, ih]

end IExp

/-- Extend an environment with context capabilities and their offsets. -/
def Env.withContext (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env) : Env :=
  ⟨ρ.idx.take slot ++ context.map Prod.snd ++ ρ.idx.drop slot,
    context.map Prod.fst ++ ρ.buf⟩

/-- Expression values agree in the corresponding context-extended environment. -/
theorem IExp.eval_withContext (e : IExp) (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env)
    (hslot : slot ≤ ρ.idx.length) :
    (e.liftContext context.length slot).eval (ρ.withContext context slot).idx = e.eval ρ.idx := by
  simpa only [Env.withContext, List.length_map] using
    e.eval_liftContext ρ.idx (context.map Prod.snd) slot hslot

/-- Dimension tuples agree in the corresponding context-extended environment. -/
theorem IExp.evalList_withContext (es : List IExp) (context : List (ℕ × ℕ)) (slot : ℕ)
    (ρ : Env) (hslot : slot ≤ ρ.idx.length) :
    evalList (ρ.withContext context slot).idx (es.map (liftContext context.length slot)) =
      evalList ρ.idx es := by
  simpa only [Env.withContext, List.length_map] using
    evalList_liftContext es ρ.idx (context.map Prod.snd) slot hslot

/-- Buffer allocation appends after the ordinary variables, preserving context positions. -/
theorem Env.withContext_pushBuf (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env) (b : ℕ) :
    (ρ.pushBuf b).withContext context slot = (ρ.withContext context slot).pushBuf b := by
  simp [Env.withContext, Env.pushBuf, List.append_assoc]

/-- An appended loop/index variable follows the inserted context-offset block. -/
theorem Env.withContext_pushIdx (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env) (i : ℕ)
    (hslot : slot ≤ ρ.idx.length) :
    (ρ.pushIdx i).withContext context slot = (ρ.withContext context slot).pushIdx i := by
  simp [Env.withContext, Env.pushIdx, List.take_append_of_le_length hslot,
    List.drop_append_of_le_length hslot, List.append_assoc]

/-- A procedure frame places context offsets between its dimensions and ordinary offsets. -/
theorem Env.withContext_frame (context : List (ℕ × ℕ)) (d : List ℕ)
    (as : List (ℕ × ℕ)) :
    (Env.frame d as).withContext context d.length = Env.frame d (context ++ as) := by
  simp [Env.withContext, Env.frame, List.map_append, List.append_assoc]

/-- Reserving context variables shifts an ordinary operand's buffer and offset expressions. -/
def Operand.liftContext (count slot : ℕ) (a : Operand) : Operand :=
  ⟨a.buf + count, a.off.liftContext count slot⟩

/-- Operand evaluation preserves both its original handle and original offset. -/
theorem Operand.eval_liftContext (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env)
    (a : Operand) (hslot : slot ≤ ρ.idx.length) :
    (a.liftContext context.length slot).eval (ρ.withContext context slot) = a.eval ρ := by
  have hb : (context.map Prod.fst ++ ρ.buf)[a.buf + context.length]? = ρ.buf[a.buf]? := by
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_right]
  have ho := a.off.eval_liftContext ρ.idx (context.map Prod.snd) slot hslot
  simp only [List.length_map] at ho
  simp only [Operand.liftContext, Operand.eval, Env.withContext]
  rw [hb, ho]

/-- Ordinary operand tuples are unchanged by context reservation. -/
theorem Operand.evalList_liftContext (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env)
    (as : List Operand) (hslot : slot ≤ ρ.idx.length) :
    evalList (ρ.withContext context slot) (as.map (liftContext context.length slot)) =
      evalList ρ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, evalList_cons, eval_liftContext, hslot, ih]

/-- Pointwise readable finite operand families evaluate to their corresponding finite values. -/
theorem Operand.evalList_ofFn {n : ℕ} {ρ : Env} {as : Fin n → Operand}
    {vs : Fin n → ℕ × ℕ} (h : ∀ i, (as i).eval ρ = some (vs i)) :
    evalList ρ (List.ofFn as) = some (List.ofFn vs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, evalList_cons, h 0]
    simp only [Option.bind_some]
    rw [ih (fun i => h i.succ)]
    rfl

/-- The visible operand list that forwards all context capabilities. -/
def contextOperands (count slot : ℕ) : List Operand :=
  List.ofFn fun i : Fin count => ⟨i, .var (slot + i)⟩

/-- The generated context operands evaluate to exactly the supplied capabilities. -/
theorem evalList_contextOperands (context : List (ℕ × ℕ)) (slot : ℕ) (ρ : Env)
    (hslot : slot ≤ ρ.idx.length) :
    Operand.evalList (ρ.withContext context slot) (contextOperands context.length slot) =
      some context := by
  have h : ∀ i : Fin context.length,
      (Operand.mk i (.var (slot + i))).eval (ρ.withContext context slot) =
        some context[i.val] := by
    intro i
    have ho : (ρ.idx.take slot ++ context.map Prod.snd ++ ρ.idx.drop slot)[slot + i.val]? =
        (context.map Prod.snd)[i.val]? := by
      have hlen : (ρ.idx.take slot).length = slot := by
        simp only [List.length_take, Nat.min_eq_left hslot]
      rw [List.append_assoc, List.getElem?_append_right (by omega), hlen,
        Nat.add_sub_cancel_left, List.getElem?_append_left (by simp)]
    simp only [Operand.eval, Env.withContext, IExp.eval]
    rw [ho, List.getElem?_append_left (by simp)]
    simp [i.isLt]
  simpa only [contextOperands, List.ofFn_getElem] using Operand.evalList_ofFn h

/-- A context table supplies ordinary implementations with extra leading inputs,
or keeps an operation under its target name. Its entries are fixed syntax. -/
abbrev ContextTable (Op Lo Tst : Type) := Table Op Lo Tst

/-- Forward context through every procedure frame and expose it to selected implementations.
Queries retain their original operands; extra context never becomes a query capability. -/
def Stmt.linkContext {Op Lo Tst : Type} (count slot : ℕ) (T : ContextTable Op Lo Tst) :
    Stmt Op Tst → Stmt Lo Tst
  | .skip => .skip
  | .abort => .abort
  | .seq s t => .seq (s.linkContext count slot T) (t.linkContext count slot T)
  | .call o ds ins outs =>
      let ds' := ds.map (IExp.liftContext count slot)
      let ins' := ins.map (Operand.liftContext count slot)
      let outs' := outs.map (Operand.liftContext count slot)
      match T o with
      | .inl R =>
          if R.Fits ds.length (count + ins.length) outs.length then
            .frame ds' (contextOperands count slot ++ ins' ++ outs') R.body
          else .abort
      | .inr o' => .call o' ds' ins' outs'
  | .ite q ds ins t e =>
      .ite q (ds.map (IExp.liftContext count slot))
        (ins.map (Operand.liftContext count slot))
        (t.linkContext count slot T) (e.linkContext count slot T)
  | .whileFuel fuel q ds ins body k =>
      .whileFuel (fuel.liftContext count slot) q (ds.map (IExp.liftContext count slot))
        (ins.map (Operand.liftContext count slot))
        (body.linkContext count slot T) (k.linkContext count slot T)
  | .bindIdx q ins bound body =>
      .bindIdx q (ins.map (Operand.liftContext count slot)) (bound.liftContext count slot)
        (body.linkContext count slot T)
  | .allocAs fmt len body =>
      .allocAs fmt (len.liftContext count slot) (body.linkContext count slot T)
  | .loop n body => .loop (n.liftContext count slot) (body.linkContext count slot T)
  | .frame ds args body =>
      .frame (ds.map (IExp.liftContext count slot))
        (contextOperands count slot ++ args.map (Operand.liftContext count slot))
        (body.linkContext count ds.length T)

end NLAlib.Ops
