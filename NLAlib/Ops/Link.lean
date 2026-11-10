/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Exec

/-!
# Linking

An implementation of the operations `Op₁` over the operations `Op₂` is a table
(`NLAlib.Ops.Table`): each operation of `Op₁` is given a tree over `Op₂` (`NLAlib.Ops.Impl`) or is
kept as an operation of `Op₂`. Linking (`NLAlib.Ops.Stmt.link`) turns each call of an implemented
operation into the frame of its tree; a call whose numbers of dimensions and operands do not fit
the implementation becomes `abort`. The linked program is a first-order tree for all sizes.

The interpretation of `Op₁` induced by a table and an interpretation of `Op₂`
(`NLAlib.Ops.Interp.link`): an implemented operation means the run of its tree.

`NLAlib.Ops.run_link`: **the linked program under `I` and the program under the induced
interpretation end in the same memory, or both fail.** This is the refinement transfer, in both
modes, with no certificate.
## Main results

* `NLAlib.Ops.run_link`: refinement transfer.
* `NLAlib.Ops.Interp.link_callS_inl`: the call of an implemented operation under the induced
  interpretation is the run of its implementation.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op₁ Op₂ K : Type}

/-- An implementation of an operation: a tree whose index variables are the `nd` dimensions of the
call followed by the offsets of its operands, and whose buffer variables are the `nin` input and
`nout` output operands. -/
structure Impl (Op : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The number of input operands. -/
  nin : ℕ
  /-- The number of output operands. -/
  nout : ℕ
  /-- The tree. -/
  body : Stmt Op

/-- **An implementation of `Op₁` over `Op₂`**: for each operation of `Op₁`, a tree over `Op₂` or
an operation of `Op₂`. -/
abbrev Table (Op₁ Op₂ : Type) := Op₁ → Impl Op₂ ⊕ Op₂

/-- The numbers of dimensions and operands fit the implementation. -/
abbrev Impl.Fits {Op : Type} (R : Impl Op) (nd nin nout : ℕ) : Prop :=
  nd = R.nd ∧ nin = R.nin ∧ nout = R.nout

/-- **Linking**: each call of an implemented operation becomes the frame of its implementation
(`abort` if the numbers of dimensions and operands do not fit); a kept operation is renamed. An
implemented operation cannot be used as a test or as an index. -/
def Stmt.link (T : Table Op₁ Op₂) : Stmt Op₁ → Stmt Op₂
  | .skip => .skip
  | .abort => .abort
  | .seq s t => .seq (s.link T) (t.link T)
  | .call o ds ins outs =>
      match T o with
      | .inl R =>
          if R.Fits ds.length ins.length outs.length then .frame ds (ins ++ outs) R.body
          else .abort
      | .inr o' => .call o' ds ins outs
  | .ite o ds ins t e =>
      match T o with
      | .inl _ => .abort
      | .inr o' => .ite o' ds ins (t.link T) (e.link T)
  | .whileFuel fuel o ds ins body =>
      match T o with
      | .inl _ => .abort
      | .inr o' => .whileFuel fuel o' ds ins (body.link T)
  | .bindIdx o ins bound body =>
      match T o with
      | .inl _ => .abort
      | .inr o' => .bindIdx o' ins bound (body.link T)
  | .alloc len body => .alloc len (body.link T)
  | .loop n body => .loop n (body.link T)
  | .frame ds args body => .frame ds args (body.link T)

/-- **The interpretation of `Op₁` induced by a table over `Op₂`**: an implemented operation means
the run of its implementation under `I` with the tape it is given; a kept operation means what it
means under `I`. -/
def Interp.link (I : Interp Op₂ K) (T : Table Op₁ Op₂) : Interp Op₁ K where
  call o d ins outs τ m :=
    match T o with
    | .inl R =>
        if R.Fits d.length ins.length outs.length then
          run I τ R.body (Env.frame d (ins ++ outs)) m
        else none
    | .inr o' => I.call o' d ins outs τ m
  test o d a m :=
    match T o with
    | .inl _ => none
    | .inr o' => I.test o' d a m
  index o a m :=
    match T o with
    | .inl _ => none
    | .inr o' => I.index o' a m

theorem Interp.link_callS_inr (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : ℕ → K) (m : Mem K) :
    (I.link T).callS o d ins outs τ m = I.callS o' d ins outs τ m := by
  simp only [Interp.callS, Interp.link, hT]

/-- The call of an implemented operation under the induced interpretation is the run of its
implementation: the run keeps the shape of the store by itself. -/
theorem Interp.link_callS_inl (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : ℕ → K) (m : Mem K) :
    (I.link T).callS o d ins outs τ m =
      if R.Fits d.length ins.length outs.length then
        run I τ R.body (Env.frame d (ins ++ outs)) m
      else none := by
  simp only [Interp.callS, Interp.link, hT]
  split_ifs with hfit
  · cases hr : run I τ R.body (Env.frame d (ins ++ outs)) m with
    | none => rfl
    | some m' => simp [shape_store_of_run hr]
  · rfl

theorem Interp.link_test_inr (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') : (I.link T).test o = I.test o' := by
  funext d a m
  simp only [Interp.link, hT]

theorem Interp.link_index_inr (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') : (I.link T).index o = I.index o' := by
  funext a m
  simp only [Interp.link, hT]

theorem Interp.link_test_inl (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) (d : List ℕ) (a : List (ℕ × ℕ)) (m : Mem K) :
    (I.link T).test o d a m = none := by
  simp only [Interp.link, hT]

theorem Interp.link_index_inl (I : Interp Op₂ K) {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) (a : List (ℕ × ℕ)) (m : Mem K) : (I.link T).index o a m = none := by
  simp only [Interp.link, hT]

/-- The run of a linked call. -/
theorem run_link_call (I : Interp Op₂ K) (T : Table Op₁ Op₂) (τ : ℕ → K) (o : Op₁)
    (ds : List IExp) (ins outs : List Operand) (ρ : Env) (m : Mem K) :
    run I τ ((Stmt.call o ds ins outs).link T) ρ m =
      run (I.link T) τ (.call o ds ins outs) ρ m := by
  cases hT : T o with
  | inr o' => simp only [Stmt.link, hT, run, Interp.link_callS_inr I hT]
  | inl R =>
    simp only [Stmt.link, hT, run, Interp.link_callS_inl I hT]
    cases hd : IExp.evalList ρ.idx ds with
    | none => split_ifs <;> simp [run, hd]
    | some d =>
      cases ha : Operand.evalList ρ ins with
      | none => split_ifs <;> simp [run, hd, ha, Operand.evalList_append]
      | some a =>
        cases hb : Operand.evalList ρ outs with
        | none => split_ifs <;> simp [run, hd, ha, hb, Operand.evalList_append]
        | some b =>
          have h1 := IExp.length_of_evalList hd
          have h2 := Operand.length_of_evalList ha
          have h3 := Operand.length_of_evalList hb
          split_ifs with hfit <;>
            simp [run, hd, ha, hb, Operand.evalList_append, h1, h2, h3, hfit]

/-- **Refinement transfer.** The linked program under `I` and the program under the induced
interpretation end in the same memory, or both fail. No certificate is needed. -/
theorem run_link (I : Interp Op₂ K) (T : Table Op₁ Op₂) (τ : ℕ → K) (s : Stmt Op₁) (ρ : Env)
    (m : Mem K) : run I τ (s.link T) ρ m = run (I.link T) τ s ρ m := by
  induction s generalizing ρ m with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.link, run, ihs, iht]
  | call o ds ins outs => exact run_link_call I T τ o ds ins outs ρ m
  | ite o ds ins t e iht ihe =>
    cases hT : T o with
    | inr o' => simp only [Stmt.link, hT, run, iht, ihe, Interp.link_test_inr I hT]
    | inl R =>
      simp only [Stmt.link, hT, run, Interp.link_test_inl I hT]
      cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;> rfl
  | whileFuel fuel o ds ins body ih =>
    cases hT : T o with
    | inr o' =>
      have hb : run I τ (Stmt.link T body) ρ = run (I.link T) τ body ρ := funext (ih ρ)
      simp only [Stmt.link, hT, run, hb, Interp.link_test_inr I hT]
    | inl R =>
      simp only [Stmt.link, hT, run]
      cases fuel.eval ρ.idx <;> cases IExp.evalList ρ.idx ds <;>
        cases Operand.evalList ρ ins <;> try rfl
      rename_i k d a
      cases k <;> simp [whileIter, Interp.link_test_inl I hT]
  | bindIdx o ins bound body ih =>
    cases hT : T o with
    | inr o' => simp only [Stmt.link, hT, run, ih, Interp.link_index_inr I hT]
    | inl R =>
      simp only [Stmt.link, hT, run, Interp.link_index_inl I hT]
      cases Operand.evalList ρ ins <;> cases bound.eval ρ.idx <;> rfl
  | alloc len body ih => simp only [Stmt.link, run, ih]
  | loop n body ih => simp only [Stmt.link, run, ih]
  | frame ds args body ih => simp only [Stmt.link, run, ih]

end NLAlib.Ops
