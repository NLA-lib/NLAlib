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
Queries (tests and index uses) have their own names `Tst`, which no table maps: they are
primitives and linking leaves them alone.

The interpretation of `Op₁` induced by a table and an interpretation of `Op₂`
(`NLAlib.Ops.Interp.link`): an implemented operation means the run of its tree.

`NLAlib.Ops.run_link`: **the linked program under `I` and the program under the induced
interpretation end in the same memory, or both fail.** This is the refinement transfer, in both
modes, with no certificate.
## Main results

* `NLAlib.Ops.run_link`: refinement transfer.
* `NLAlib.Ops.Interp.link_callS_inl`: the call of an implemented operation under the induced
  interpretation is the run of its implementation.
* `NLAlib.Ops.Stmt.link_comp`, `NLAlib.Ops.Interp.link_comp`: linking through two tables is
  linking through their composition `NLAlib.Ops.Table.comp`; `NLAlib.Ops.Table.iter` is the
  `k`-fold composition of a table of a signature over itself, which is how recursion is linked.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Op₃ Tst K : Type}

/-- An implementation of an operation: a tree whose index variables are the `nd` dimensions of the
call followed by the offsets of its operands, and whose buffer variables are the `nin` input and
`nout` output operands. -/
structure Impl (Op Tst : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The number of input operands. -/
  nin : ℕ
  /-- The number of output operands. -/
  nout : ℕ
  /-- The tree. -/
  body : Stmt Op Tst

/-- **An implementation of `Op₁` over `Op₂`**: for each operation of `Op₁`, a tree over `Op₂` or
an operation of `Op₂`. Queries are not in the table. -/
abbrev Table (Op₁ Op₂ Tst : Type) := Op₁ → Impl Op₂ Tst ⊕ Op₂

/-- The numbers of dimensions and operands fit the implementation. -/
abbrev Impl.Fits (R : Impl Op Tst) (nd nin nout : ℕ) : Prop :=
  nd = R.nd ∧ nin = R.nin ∧ nout = R.nout

/-- **Linking**: each call of an implemented operation becomes the frame of its implementation
(`abort` if the numbers of dimensions and operands do not fit); a kept operation is renamed. -/
def Stmt.link (T : Table Op₁ Op₂ Tst) : Stmt Op₁ Tst → Stmt Op₂ Tst
  | .skip => .skip
  | .abort => .abort
  | .seq s t => .seq (s.link T) (t.link T)
  | .call o ds ins outs =>
      match T o with
      | .inl R =>
          if R.Fits ds.length ins.length outs.length then .frame ds (ins ++ outs) R.body
          else .abort
      | .inr o' => .call o' ds ins outs
  | .ite q ds ins t e => .ite q ds ins (t.link T) (e.link T)
  | .whileFuel fuel q ds ins body => .whileFuel fuel q ds ins (body.link T)
  | .bindIdx q ins bound body => .bindIdx q ins bound (body.link T)
  | .alloc len body => .alloc len (body.link T)
  | .loop n body => .loop n (body.link T)
  | .frame ds args body => .frame ds args (body.link T)

/-- **The interpretation of `Op₁` induced by a table over `Op₂`**: an implemented operation means
the run of its implementation under `I` with the tape it is given; a kept operation means what it
means under `I`; a query means what it means under `I`. -/
def Interp.link (I : Interp Op₂ Tst K) (T : Table Op₁ Op₂ Tst) : Interp Op₁ Tst K where
  call o d ins outs τ m :=
    match T o with
    | .inl R =>
        if R.Fits d.length ins.length outs.length then
          run I τ R.body (Env.frame d (ins ++ outs)) m
        else none
    | .inr o' => I.call o' d ins outs τ m
  test := I.test
  index := I.index

theorem Interp.link_callS_inr (I : Interp Op₂ Tst K) {T : Table Op₁ Op₂ Tst} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : ℕ → K) (m : Mem K) :
    (I.link T).callS o d ins outs τ m = I.callS o' d ins outs τ m := by
  simp only [Interp.callS, Interp.link, hT]

/-- The call of an implemented operation under the induced interpretation is the run of its
implementation on live operands: the run keeps the shape of the store by itself. -/
theorem Interp.link_callS_inl (I : Interp Op₂ Tst K) {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {R : Impl Op₂ Tst} (hT : T o = .inl R) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : ℕ → K)
    (m : Mem K) :
    (I.link T).callS o d ins outs τ m =
      if m.Live (ins ++ outs) then
        if R.Fits d.length ins.length outs.length then
          run I τ R.body (Env.frame d (ins ++ outs)) m
        else none
      else none := by
  simp only [Interp.callS, Interp.link, hT]
  split_ifs with hl hfit
  · cases hr : run I τ R.body (Env.frame d (ins ++ outs)) m with
    | none => rfl
    | some m' => simp [shape_store_of_run hr]
  · rfl
  · rfl

/-- The run of a linked call. -/
theorem run_link_call (I : Interp Op₂ Tst K) (T : Table Op₁ Op₂ Tst) (τ : ℕ → K) (o : Op₁)
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
          have hfe : R.Fits d.length a.length b.length ↔
              R.Fits ds.length ins.length outs.length := by rw [h1, h2, h3]
          simp only [Option.bind_some]
          by_cases hfit : R.Fits ds.length ins.length outs.length
          · rw [if_pos hfit, if_pos (hfe.mpr hfit)]
            simp [run, hd, ha, hb, Operand.evalList_append]
          · rw [if_neg hfit, if_neg (hfe.not.mpr hfit)]
            simp [run]

/-- **Refinement transfer.** The linked program under `I` and the program under the induced
interpretation end in the same memory, or both fail. No certificate is needed. -/
theorem run_link (I : Interp Op₂ Tst K) (T : Table Op₁ Op₂ Tst) (τ : ℕ → K) (s : Stmt Op₁ Tst)
    (ρ : Env) (m : Mem K) : run I τ (s.link T) ρ m = run (I.link T) τ s ρ m := by
  induction s generalizing ρ m with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.link, run, ihs, iht]
  | call o ds ins outs => exact run_link_call I T τ o ds ins outs ρ m
  | ite q ds ins t e iht ihe => simp only [Stmt.link, run, iht, ihe, Interp.link]
  | whileFuel fuel q ds ins body ih =>
    have hb : run I τ (Stmt.link T body) ρ = run (I.link T) τ body ρ := funext (ih ρ)
    simp only [Stmt.link, run, hb, Interp.link]
  | bindIdx q ins bound body ih => simp only [Stmt.link, run, ih, Interp.link]
  | alloc len body ih => simp only [Stmt.link, run, ih]
  | loop n body ih => simp only [Stmt.link, run, ih]
  | frame ds args body ih => simp only [Stmt.link, run, ih]

/-! ### Composition of tables -/

/-- **The composition of two tables**: the trees of `T₁` linked through `T₂`. -/
def Table.comp (T₁ : Table Op₁ Op₂ Tst) (T₂ : Table Op₂ Op₃ Tst) : Table Op₁ Op₃ Tst := fun o =>
  match T₁ o with
  | .inl R => .inl ⟨R.nd, R.nin, R.nout, R.body.link T₂⟩
  | .inr o' => T₂ o'

/-- The table that keeps every operation. -/
def Table.id : Table Op Op Tst := fun o => .inr o

/-- **The `k`-fold composition of a table of a signature over itself.** An operation implemented
by calls of itself at smaller dimensions is linked this way, with `k` a bound on the depth. -/
def Table.iter (T : Table Op Op Tst) : ℕ → Table Op Op Tst
  | 0 => Table.id
  | k + 1 => T.comp (T.iter k)

/-- **Linking through two tables is linking through their composition.** -/
theorem Stmt.link_comp (T₁ : Table Op₁ Op₂ Tst) (T₂ : Table Op₂ Op₃ Tst) (s : Stmt Op₁ Tst) :
    (s.link T₁).link T₂ = s.link (T₁.comp T₂) := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.link, ihs, iht]
  | call o ds ins outs =>
    cases hT : T₁ o with
    | inr o' => simp only [Stmt.link, Table.comp, hT]
    | inl R =>
      simp only [Stmt.link, Table.comp, hT]
      split_ifs <;> rfl
  | ite q ds ins t e iht ihe => simp only [Stmt.link, iht, ihe]
  | whileFuel fuel q ds ins body ih => simp only [Stmt.link, ih]
  | bindIdx q ins bound body ih => simp only [Stmt.link, ih]
  | alloc len body ih => simp only [Stmt.link, ih]
  | loop n body ih => simp only [Stmt.link, ih]
  | frame ds args body ih => simp only [Stmt.link, ih]

/-- The interpretation induced through two tables is the one induced by their composition. -/
theorem Interp.link_comp (I : Interp Op₃ Tst K) (T₁ : Table Op₁ Op₂ Tst)
    (T₂ : Table Op₂ Op₃ Tst) : (I.link T₂).link T₁ = I.link (T₁.comp T₂) := by
  have hc : ((I.link T₂).link T₁).call = (I.link (T₁.comp T₂)).call := by
    funext o d ins outs τ m
    cases hT : T₁ o with
    | inr o' => simp only [Interp.link, Table.comp, hT]
    | inl R => simp only [Interp.link, Table.comp, hT, run_link]
  cases h1 : (I.link T₂).link T₁
  cases h2 : I.link (T₁.comp T₂)
  rw [h1, h2] at hc
  have ht : ((I.link T₂).link T₁).test = (I.link (T₁.comp T₂)).test := rfl
  have hi : ((I.link T₂).link T₁).index = (I.link (T₁.comp T₂)).index := rfl
  rw [h1, h2] at ht hi
  simp only at hc ht hi
  rw [hc, ht, hi]

@[simp] theorem Stmt.link_id (s : Stmt Op Tst) : s.link Table.id = s := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.link, ihs, iht]
  | call o ds ins outs => rfl
  | ite q ds ins t e iht ihe => simp only [Stmt.link, iht, ihe]
  | whileFuel fuel q ds ins body ih => simp only [Stmt.link, ih]
  | bindIdx q ins bound body ih => simp only [Stmt.link, ih]
  | alloc len body ih => simp only [Stmt.link, ih]
  | loop n body ih => simp only [Stmt.link, ih]
  | frame ds args body ih => simp only [Stmt.link, ih]

@[simp] theorem Interp.link_id (I : Interp Op Tst K) : I.link Table.id = I := rfl

end NLAlib.Ops
