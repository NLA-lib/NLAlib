/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Writes
public meta import Lean.Elab.Tactic.Basic

/-!
# The call step in named form

`step h [facts] as m₁ hfr₁ ⟨pat⟩` is one step of a program proof at a call, on the footprint
rules: the continuation is proved from a fresh memory `m₁` with the frame `hfr₁` of the call and
its postcondition, destructured by `pat`. The inputs the call reads are found by `kept`, which
looks for each block in the context at the current memory, or at an earlier memory across the
frames and the agreements (`Store.Below`) in the context, or as a sub-block of a block read there:
facts are carried lazily, where they are used, never restated after every step.

## Main results

* `NLAlib.Ops.writes_call_cell_of`, `NLAlib.Ops.writes_call1_of`, `NLAlib.Ops.writes_call2_of`:
  the call rules with the blocks read given, the form `step` applies.
* `kept`, `reads`, `step`: the tactics.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-- A block read is kept across agreement below a handle. -/
theorem Store.Below.readBlock_of {L : ℕ} {s s' : Store K} (h : Store.Below L s s') {b : ℕ}
    (hb : b < L) {o n : ℕ} {xs : List K} (hr : s.readBlock b o n = some xs) :
    s'.readBlock b o n = some xs := (h.readBlock hb o n).trans hr

/-- A cell is kept across agreement below a handle. -/
theorem Store.Below.get_of {L : ℕ} {s s' : Store K} (h : Store.Below L s s') {b : ℕ}
    (hb : b < L) {i : ℕ} {v : K} (hr : s.get b i = some v) : s'.get b i = some v :=
  ((h b hb).2 i).trans hr

/-- Reading the blocks of a call, one at a time (the form `reads` builds). -/
theorem Mem.readBlocks_of_cons {a : ℕ × ℕ} {as : List (ℕ × ℕ)} {n : ℕ} {ns : List ℕ} {x : List K}
    {xs : List (List K)} (h : m.store.readBlock a.1 a.2 n = some x)
    (h' : m.readBlocks as ns = some xs) : m.readBlocks (a :: as) (n :: ns) = some (x :: xs) :=
  Mem.readBlocks_cons_eq_some.mpr ⟨x, xs, h, h', rfl⟩

theorem Mem.readBlocks_nil' : m.readBlocks [] [] = some [] := rfl

/-- The call rule with a footprint for one output cell, with the blocks read given. -/
theorem writes_call_cell_of {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [1]) (hadm : adm d a [z])
    (hlive : m.Live (a ++ [z])) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz : z.2 < m.store.len z.1) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos + k ∧ ∃ v, m'.store.get z.1 z.2 = some v ∧
        R.rel d xs (τ.window R.stream m.pos k) [[v]]) m :=
  (writes_call_cell hI hd ha hb hnd hk hls hadm fun _ => ⟨hlive, ⟨xs, hr, hdom⟩, hz⟩).mono le_rfl
    fun _ _ ⟨hpos, xs', v, hxs, hv, hrel⟩ => by
      obtain rfl : xs' = xs := Option.some.inj (hxs.symm.trans hr)
      exact ⟨hpos, v, hv, hrel⟩

/-- The call rule with a footprint for one output block, with the blocks read given. -/
theorem writes_call1_of {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k l : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [l]) (hadm : adm d a [z])
    (hlive : m.Live (a ++ [z])) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz : z.2 + l ≤ m.store.len z.1) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z.1 z.2 l)
      (fun m' => m'.pos = m.pos + k ∧ ∃ y, m'.store.readBlock z.1 z.2 l = some y ∧
        R.rel d xs (τ.window R.stream m.pos k) [y]) m :=
  (writes_call1 hI hd ha hb hnd hk hls hadm fun _ => ⟨hlive, ⟨xs, hr, hdom⟩, hz⟩).mono le_rfl
    fun _ _ ⟨hpos, xs', y, hxs, hy, hrel⟩ => by
      obtain rfl : xs' = xs := Option.some.inj (hxs.symm.trans hr)
      exact ⟨hpos, y, hy, hrel⟩

/-- The call rule with a footprint for two output blocks, apart, with the blocks read given. -/
theorem writes_call2_of {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z₁ z₂ : ℕ × ℕ}
    {k l₁ l₂ : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z₁, z₂])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [l₁, l₂])
    (hadm : adm d a [z₁, z₂])
    (hap : Fp.Disj (Store.inBlock z₁.1 z₁.2 l₁) (Store.inBlock z₂.1 z₂.2 l₂))
    (hlive : m.Live (a ++ [z₁, z₂])) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz₁ : z₁.2 + l₁ ≤ m.store.len z₁.1)
    (hz₂ : z₂.2 + l₂ ≤ m.store.len z₂.1) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z₁.1 z₁.2 l₁ ⊔ Store.inBlock z₂.1 z₂.2 l₂)
      (fun m' => m'.pos = m.pos + k ∧ ∃ y₁ y₂, m'.store.readBlock z₁.1 z₁.2 l₁ = some y₁ ∧
        m'.store.readBlock z₂.1 z₂.2 l₂ = some y₂ ∧
        R.rel d xs (τ.window R.stream m.pos k) [y₁, y₂]) m :=
  (writes_call2 hI hd ha hb hnd hk hls hadm hap fun _ => ⟨hlive, ⟨xs, hr, hdom⟩, hz₁, hz₂⟩).mono
    le_rfl fun _ _ ⟨hpos, xs', y₁, y₂, hxs, hy₁, hy₂, hrel⟩ => by
      obtain rfl : xs' = xs := Option.some.inj (hxs.symm.trans hr)
      exact ⟨hpos, y₁, y₂, hy₁, hy₂, hrel⟩

theorem Store.Below.len_of {L : ℕ} {s s' : Store K} (h : Store.Below L s s') :
    ∀ b < L, s'.len b = s.len b := fun b hb => (h b hb).1

open Lean Meta Elab Tactic in
/-- **`frame_facts`**: for every frame `h : s.EqOff F s'` and every agreement
`h : Store.Below L s s'` in the context, add the lengths of the buffers of `s'` (and the length of
`s'`) in terms of `s`, unless they are already there, so that the side goals about room and live
handles (`wp_side`, whose `simp` uses the context) see through the named states. -/
elab "frame_facts" : tactic => withMainContext do
  let mut g ← getMainGoal
  let lctx ← getLCtx
  let mut tys ← (lctx.foldl (init := #[]) fun acc d => acc.push d.type).mapM instantiateMVars
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let cands : Array Name :=
      if ty.isAppOf ``Store.EqOff then #[``Store.EqOff.len_eq, ``Store.EqOff.length_eq]
      else if ty.isAppOf ``Store.Below then #[``Store.Below.len_of]
      else #[]
    for c in cands do
      let pf ← mkAppM c #[d.toExpr]
      let t ← instantiateMVars (← inferType pf)
      if tys.contains t then continue
      let (_, g') ← (← g.assert `hlen t pf).intro1
      g := g'
      tys := tys.push t
  replaceMainGoal [g]

/-- **`kept [facts]`**: a goal `s.readBlock b o n = some ?xs` or `s.get b i = some ?v`. Closes it
from a hypothesis about `s`, or about an earlier store across a frame `s₀.EqOff F s` (the block is
off `F`, by `disjoint`) or an agreement `Store.Below L s₀ s` (the buffer is below `L`, by `idx`),
or as a sub-block of a block read (`Store.readBlock_sub`, the bound by `idx`), or a cell as a
block of one (`Store.readBlock_one_of_get`). Fails if none applies. -/
syntax "kept" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| kept) => `(tactic| kept [])
  | `(tactic| kept [$ts,*]) => `(tactic| first
      | assumption
      | (apply Store.EqOff.readBlock_of
         · assumption
         · kept [$ts,*]
         · intro j hj hF; revert hF; disjoint [$ts,*])
      | (apply Eq.trans
         · apply Store.EqOff.get_eq
           · assumption
           · disjoint [$ts,*]
         · kept [$ts,*])
      | (apply Store.Below.readBlock_of
         · assumption
         · idx [$ts,*]
         · kept [$ts,*])
      | (apply Store.Below.get_of
         · assumption
         · idx [$ts,*]
         · kept [$ts,*])
      | (apply Store.readBlock_one_of_get; kept [$ts,*])
      | (apply Store.readBlock_sub
         · assumption
         · idx [$ts,*])
      | fail "kept: the block is not found in the context, at this or an earlier memory")

open Lean Meta Elab Tactic in
/-- The elements of a list literal, up to whnf; at most `fuel` of them. -/
meta def listElems (fuel : Nat) (e : Expr) : MetaM (Array Expr) := do
  match fuel with
  | 0 => throwError "reads: list too long"
  | f + 1 =>
    let e ← whnfD e
    match e.getAppFnArgs with
    | (``List.nil, _) => return #[]
    | (``List.cons, #[_, h, t]) => return #[h] ++ (← listElems f t)
    | _ => throwError "reads: not a list literal: {e}"

open Lean Meta Elab Tactic in
/-- **`reads`**: a goal `m.readBlocks as ns = some ?xs` (the blocks a call reads), with `as` and
`ns` lists of known length: proves `m.store.readBlock a.1 a.2 n = some ?x` for each block by
`kept`, and closes the goal with the list of the blocks found. -/
elab "reads" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "reads: not an equation"
  let (``Mem.readBlocks, #[_, m, as, ns]) := lhs.getAppFnArgs
    | throwError "reads: not a read of blocks"
  let as ← listElems 64 as
  let ns ← listElems 64 ns
  unless as.size == ns.size do throwError "reads: as many blocks as lengths expected"
  let mut pfs : Array Expr := #[]
  for (a, n) in as.zip ns do
    let st ← mkAppM ``Mem.store #[m]
    let rb ← mkAppM ``Store.readBlock #[st, ← mkAppM ``Prod.fst #[a], ← mkAppM ``Prod.snd #[a], n]
    let ty ← inferType rb
    let x ← mkFreshExprMVar (ty.appArg!)
    let goalTy ← mkEq rb (← mkAppM ``Option.some #[x])
    let hg ← mkFreshExprMVar goalTy
    let gs ← Tactic.run hg.mvarId!
      (evalTactic (← `(tactic| (try dsimp only [List.headD_cons, List.getD_cons_zero]); kept)))
    unless gs.isEmpty do throwError "reads: a block is not found"
    pfs := pfs.push (← instantiateMVars hg)
  let mut pf ← mkAppOptM ``Mem.readBlocks_nil' #[none, m]
  for h in pfs.reverse do
    pf ← mkAppM ``Mem.readBlocks_of_cons #[h, pf]
  unless ← withAssignableSyntheticOpaque (isDefEq (← inferType pf) t) do
    throwError "reads: the blocks read do not match"
  g.assign pf
  replaceMainGoal []

/-- **`room [facts]`**: a goal that the handles of a call are live or that there is room for an
output, at a named memory: rewrites the lengths through the frames and agreements of the context
(`frame_facts`), the conditions by `idx`, and closes by `idx`. -/
syntax "room" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| room) => `(tactic| room [])
  | `(tactic| room [$ts,*]) => `(tactic|
      (simp (disch := idx) only [*, Mem.live_cons, Mem.live_nil, List.cons_append,
          List.nil_append, and_true, true_and, $ts,*]
       try idx [$ts,*]
       done))

/-- **`step h [facts] as m₁ hfr₁ ⟨pat⟩`**: the call step in named form. The goal is a `Wp` or a
`Writes` of a call, or of a call followed by more (`.seq (.call …) c`). `h` says that the
operation meets its contract (`I.Meets md o (R.spec adm)`, or `I.IsFn` of a block function). The
tactic applies the footprint rule for the shape of the outputs (one cell, one block, two blocks)
and the sequence rule (`Writes.then_`; `Writes.seq_le` against the declared footprint inside a
`Writes`; `Writes.mono` for a last call), proves the side goals (shapes by `wp_shape`, the
admitted operands by `wp_adm`, live handles and room by `wp_side`, the blocks read by `reads`, the
domain by `wp_dom`, apartness by `disjoint`, the footprint by `fp_sub`), introduces the fresh
memory `m₁`, the frame `hfr₁` and the postcondition (position, outputs, relation, reduced by
`storeNF`) destructured by `pat`, and records the lengths and the length of the store at `m₁`
(from the frame) for the later side goals. A side goal that is not proved is left under its name
(`hadm`, `hlive`, `hr`, `hdom`, `hz`, `hap`, `hle`). -/
syntax "step " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? &" as " ident ident
  (ppSpace colGt Lean.Parser.Tactic.rcasesPatMed)? : tactic

macro_rules
  | `(tactic| step $h as $m $hfr $[$pat]?) => `(tactic| step $h [] as $m $hfr $[$pat]?)
  | `(tactic| step $h [$ts,*] as $m $hfr) => `(tactic| step $h [$ts,*] as $m $hfr _)
  | `(tactic| step $h [$ts,*] as $m $hfr $pat:rcasesPatMed) => `(tactic|
      ((first
         | refine Writes.seq_le (writes_call_cell_of $h rfl rfl rfl rfl
             (k := ?_) (xs := ?_) ?hk rfl ?hadm ?hlive ?hr ?hdom ?hz) ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.seq_le (writes_call1_of $h rfl rfl rfl rfl
             (k := ?_) (l := ?_) (xs := ?_) ?hk ?hls ?hadm ?hlive ?hr ?hdom ?hz)
             ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.seq_le (writes_call2_of $h rfl rfl rfl rfl
             (k := ?_) (l₁ := ?_) (l₂ := ?_) (xs := ?_)
             ?hk ?hls ?hadm ?hap ?hlive ?hr ?hdom ?hz₁ ?hz₂)
             ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.then_ (writes_call_cell_of $h rfl rfl rfl rfl
             (k := ?_) (xs := ?_) ?hk rfl ?hadm ?hlive ?hr ?hdom ?hz) fun $m $hfr hpost => ?hQ
         | refine Writes.then_ (writes_call1_of $h rfl rfl rfl rfl
             (k := ?_) (l := ?_) (xs := ?_) ?hk ?hls ?hadm ?hlive ?hr ?hdom ?hz)
             fun $m $hfr hpost => ?hQ
         | refine Writes.then_ (writes_call2_of $h rfl rfl rfl rfl
             (k := ?_) (l₁ := ?_) (l₂ := ?_) (xs := ?_)
             ?hk ?hls ?hadm ?hap ?hlive ?hr ?hdom ?hz₁ ?hz₂)
             fun $m $hfr hpost => ?hQ
         | refine Writes.mono (writes_call_cell_of $h rfl rfl rfl rfl
             (k := ?_) (xs := ?_) ?hk rfl ?hadm ?hlive ?hr ?hdom ?hz) ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.mono (writes_call1_of $h rfl rfl rfl rfl
             (k := ?_) (l := ?_) (xs := ?_) ?hk ?hls ?hadm ?hlive ?hr ?hdom ?hz)
             ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.mono (writes_call2_of $h rfl rfl rfl rfl
             (k := ?_) (l₁ := ?_) (l₂ := ?_) (xs := ?_)
             ?hk ?hls ?hadm ?hap ?hlive ?hr ?hdom ?hz₁ ?hz₂)
             ?hle fun $m $hfr hpost => ?hQ
         | refine Writes.wp (writes_call_cell_of $h rfl rfl rfl rfl
             (k := ?_) (xs := ?_) ?hk rfl ?hadm ?hlive ?hr ?hdom ?hz) fun $m $hfr hpost => ?hQ
         | refine Writes.wp (writes_call1_of $h rfl rfl rfl rfl
             (k := ?_) (l := ?_) (xs := ?_) ?hk ?hls ?hadm ?hlive ?hr ?hdom ?hz)
             fun $m $hfr hpost => ?hQ
         | refine Writes.wp (writes_call2_of $h rfl rfl rfl rfl
             (k := ?_) (l₁ := ?_) (l₂ := ?_) (xs := ?_)
             ?hk ?hls ?hadm ?hap ?hlive ?hr ?hdom ?hz₁ ?hz₂)
             fun $m $hfr hpost => ?hQ
         | fail "step: no call rule applies to this goal with this contract")
       all_goals try frame_facts
       try (case' hk => first | wp_shape | skip)
       try (case' hls => first | wp_shape | skip)
       try (case' hr => first | reads | skip)
       try (case' hadm => first | wp_adm [$ts,*] | skip)
       try (case' hlive => first | room [$ts,*] | wp_side [$ts,*] | skip)
       try (case' hdom => first | wp_dom [$ts,*] | skip)
       try (case' hz => first | room [$ts,*] | wp_side [$ts,*] | skip)
       try (case' hz₁ => first | room [$ts,*] | wp_side [$ts,*] | skip)
       try (case' hz₂ => first | room [$ts,*] | wp_side [$ts,*] | skip)
       try (case' hap => first | disjoint [$ts,*] | skip)
       try (case' hle => first | fp_sub [$ts,*] | skip)
       case' hQ =>
         try simp only [storeNF, List.headD_cons, Nat.add_zero, Mem.pos_advance, Option.map_some,
           Option.some.injEq, List.cons.injEq, and_true] at hpost
         try dsimp only at $(⟨hfr.raw⟩):term
         rcases hpost with $pat))

end NLAlib.Ops
