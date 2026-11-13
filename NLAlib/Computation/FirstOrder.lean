/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Compile
public import NLAlib.Computation.RunsWithin

/-!
# The run of a first-order program

The run `NLAlib.Computation.FStmt.exec I s ρB ρI st` of a first-order statement takes an
environment of handles `ρB` and of index values `ρI`. Its leaves are the clauses of
`NLAlib.Computation.exec`, with each index expression evaluated in the environment; `alloc` binds
the new handle `st.store.size` and `loop` the iteration index. Every charge, memory and failure
rule is that of `exec`, clause for clause. The leaves are written out rather than delegated to
`exec`, so that a statement about a first-order program does not unfold to the builder's syntax;
the copies cannot drift apart from `exec`, because the bridge below is a theorem.

`NLAlib.Computation.Prog.exec prog N n` runs a program at the sizes $N$ and $n$, declared buffer
$j$ at handle $j$, and `NLAlib.Computation.Prog.RunsWithin` is its run within a budget, the
first-order form of `NLAlib.Computation.RunsWithin`.

**The bridge** (`NLAlib.Computation.FStmt.exec_eq_exec_toStmt`): the run of a first-order
statement in the environment of the values of $\sigma$ is the current run of its instantiation by
$\sigma$. So every lemma and every invariant of `exec` holds for `Prog.exec` by one rewrite; the
invariants are restated here for programs. A `whileFuel` loop tests its comparison at most `fuel`
times and fails if every test it makes holds, so a successful run executes its body at most
`fuel - 1` times. Design: `docs/design/Computation.md`, "First-order programs and target
statements" (F3, F7).

## Main definitions

* `NLAlib.Computation.FStmt.exec`, `NLAlib.Computation.Prog.exec`: the run.
* `NLAlib.Computation.Prog.RunsWithin`: a run within a budget.
* `NLAlib.Computation.Cell.normIdx`, `NLAlib.Computation.Instr.normIdx`,
  `NLAlib.Computation.Stmt.normIdx`: the index normal form.
* `NLAlib.Computation.Instr.mapTag`, `NLAlib.Computation.FStmt.mapTags`: a first-order
  statement with its tags and oracle names renamed.

## Main results

* `NLAlib.Computation.FStmt.exec_eq_exec_toStmt`, `NLAlib.Computation.Prog.exec_eq_exec_toStmt`:
  the bridge to the run of the instantiated statement.
* `NLAlib.Computation.Prog.runsWithin_iff`: a program runs within a budget if and only if its
  instantiation does.
* `NLAlib.Computation.Prog.cnt_le_of_exec_eq_some`,
  `NLAlib.Computation.Prog.cur_eq_of_exec_eq_some`,
  `NLAlib.Computation.Prog.shape_eq_of_exec_eq_some`,
  `NLAlib.Computation.Prog.peak_le_of_exec_eq_some`: the counts and peaks of a run only grow,
  and it frees exactly what it allocates.
* `NLAlib.Computation.Prog.store_eq_of_exec_eq_some_of_cnt_le`,
  `NLAlib.Computation.Prog.pos_eq_of_exec_eq_some_of_cnt_le`: a run that charges nothing writes
  and draws nothing.
* `NLAlib.Computation.Prog.exec_eq_of_exec_eq_some_of_cnt_load_le`: a run that makes no oracle
  call is the same under any oracle.
* `NLAlib.Computation.FStmt.exec_kcall`: the run of a first-order kernel call.
* `NLAlib.Computation.FStmt.exec_bindIdx`: the run of a first-order index binder.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### The run -/

section Run

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- **The run of a first-order statement** under `I`, in an environment of handles `ρB` and of index
values `ρI`. The leaves (instructions, oracle calls, kernel calls, read-only reads, comparisons) run
by the rules of `NLAlib.Computation.exec`, with each index expression evaluated in the
environment; `alloc` binds the new handle `st.store.size`, `loop` the iteration index and
`bindIdx` the conversion of its cell, failing if it exceeds the bound. A `whileFuel` loop tests
its comparison at most `fuel` times and fails if every test it makes holds. -/
def FStmt.exec : {nb ni : ℕ} → FStmt P ι nb ni → (Fin nb → ℕ) → (Fin ni → ℕ) →
    St P K C → Option (St P K C)
  | _, _, .skip, _, _, st => some st
  | _, _, .seq s t, ρB, ρI, st => (s.exec ρB ρI st).bind (t.exec ρB ρI)
  | _, _, .instr i, ρB, ρI, st =>
      let i' := i.subst ρB fun v => .const (ρI v)
      (i'.run I.sem I.tape st.store st.pos).map fun r =>
        { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i'.kind }
  | _, _, .apply o p d dOff s sOff cols, ρB, ρI, st =>
      let L := I.height o * cols.evalIn ρI
      if ρB d ≠ ρB s ∨ dOff.evalIn ρI + L ≤ sOff.evalIn ρI ∨
          sOff.evalIn ρI + L ≤ dOff.evalIn ρI then
        (st.store.readBlock p (ρB s) (sOff.evalIn ρI) L).bind fun X =>
          (I.oracle o (cols.evalIn ρI) X).bind fun Y =>
            (st.store.writeBlock p (ρB d) (dOff.evalIn ρI) Y).map fun s' => { st with
              store := s'
              cnt := st.cnt + (I.charge (.load p o) + cols.evalIn ρI • I.charge (.matvec p o)) }
      else none
  | _, _, .rom p d i, ρB, ρI, st => (I.rom (i.evalIn ρI)).bind fun v =>
      (st.store.write p (ρB d.buf) (d.idx.evalIn ρI) v).map fun s' =>
        { st with store := s', cnt := st.cnt + I.charge (.rom p) }
  | _, _, .alloc p len body, ρB, ρI, st =>
      let n := len.evalIn ρI
      (body.exec (Fin.snoc (α := fun _ => ℕ) ρB st.store.size) ρI { st with
          store := st.store.push (p, Array.replicate n none),
          cur := Function.update st.cur p (st.cur p + n),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + n)),
          curW := st.curW + n * I.width p,
          peakW := max st.peakW (st.curW + n * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - n)
          curW := st₂.curW - n * I.width p }
  | _, _, .loop n body, ρB, ρI, st =>
      (List.range (n.evalIn ρI)).foldlM
        (fun st i => body.exec ρB (Fin.snoc (α := fun _ => ℕ) ρI i) st) st
  | _, _, .whileFuel fuel p c x y body, ρB, ρI, st =>
      ((List.range (fuel.evalIn ρI)).foldlM (fun (s : St P K C × Bool) _ =>
        if s.2 then (cmpStep I p c (x.subst ρB fun v => .const (ρI v))
            (y.subst ρB fun v => .const (ρI v)) s.1).bind fun r =>
          if r.1 then (body.exec ρB ρI r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) (st, true)).bind fun r => if r.2 then none else some r.1
  | _, _, .ite p c x y t e, ρB, ρI, st =>
      (cmpStep I p c (x.subst ρB fun v => .const (ρI v)) (y.subst ρB fun v => .const (ρI v))
        st).bind fun r => if r.1 then t.exec ρB ρI r.2 else e.exec ρB ρI r.2
  | _, _, .named _ _ body, ρB, ρI, st => body.exec ρB ρI st
  | _, _, .kcall o p dims ins outs, ρB, ρI, st =>
      (I.kcallStore o p (dims.map (·.evalIn ρI)) (ins.map fun x => (ρB x.1, x.2.evalIn ρI))
        (outs.map fun x => (ρB x.1, x.2.evalIn ρI)) st.store).map fun s =>
          { st with store := s, cnt := st.cnt + I.charge (.kcall p o (dims.map (·.evalIn ρI))) }
  | _, _, .bindIdx p x bound body, ρB, ρI, st =>
      (toNatStep I p (x.subst ρB fun v => .const (ρI v)) st).bind fun r =>
        if r.1 ≤ bound.evalIn ρI then body.exec ρB (Fin.snoc (α := fun _ => ℕ) ρI r.1) r.2
        else none

/-- **The run of a program** at the sizes $N$ and $n$: declared buffer $j$ at handle $j$, the
oracle dimension $N$ as index variable $0$ and size $i$ as index variable $i + 1$. -/
def Prog.exec {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st : St P K C) :
    Option (St P K C) :=
  FStmt.exec I prog (fun j => (j : ℕ)) (Fin.cons N n) st

end Run

/-! ### The bridge to the run of the instantiated statement -/

section Bridge

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- An instruction runs the same under two substitutions of index expressions with the same
values. -/
theorem Instr.run_subst_congr {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) (f : Fin nb → ℕ)
    {σ σ' : Fin ni → IExp ℕ} (h : ∀ v, (σ v).eval = (σ' v).eval) (sem : ScalarSem P K)
    (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ) :
    (i.subst f σ).run sem tape s pos = (i.subst f σ').run sem tape s pos := by
  have h' : (fun v => (σ v).eval) = fun v => (σ' v).eval := funext h
  cases i <;> simp only [Instr.subst, Cell.subst, Instr.run, IExp.eval_subst, h']

omit [DecidableEq P] in
/-- The kind of an instruction does not depend on its index expressions. -/
theorem Instr.kind_subst {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) (f : Fin nb → ℕ)
    (σ σ' : Fin ni → IExp ℕ) :
    Instr.kind (ι := ι) (i.subst f σ) = Instr.kind (i.subst f σ') := by
  cases i <;> rfl

/-- A comparison runs the same under two substitutions of index expressions with the same
values. -/
theorem cmpStep_subst_congr {nb ni : ℕ} (p : P) (c : CmpOp) (x y : Cell (Fin nb) (Fin ni))
    (f : Fin nb → ℕ) {σ σ' : Fin ni → IExp ℕ} (h : ∀ v, (σ v).eval = (σ' v).eval)
    (st : St P K C) :
    cmpStep I p c (x.subst f σ) (y.subst f σ) st =
      cmpStep I p c (x.subst f σ') (y.subst f σ') st := by
  have h' : (fun v => (σ v).eval) = fun v => (σ' v).eval := funext h
  simp only [cmpStep, Cell.subst, IExp.eval_subst, h']

/-- A conversion step runs the same under two substitutions of index expressions with the same
values. -/
theorem toNatStep_subst_congr {nb ni : ℕ} (p : P) (x : Cell (Fin nb) (Fin ni)) (f : Fin nb → ℕ)
    {σ σ' : Fin ni → IExp ℕ} (h : ∀ v, (σ v).eval = (σ' v).eval) (st : St P K C) :
    toNatStep I p (x.subst f σ) st = toNatStep I p (x.subst f σ') st := by
  have h' : (fun v => (σ v).eval) = fun v => (σ' v).eval := funext h
  simp only [toNatStep, Cell.subst, IExp.eval_subst, h']

omit [DecidableEq P] [AddMonoid C] in
/-- The values of the substitution under a loop binder. -/
private theorem eval_snoc {ni : ℕ} (σ : Fin ni → IExp ℕ) (i : ℕ) :
    (fun v => (Fin.snoc (α := fun _ => IExp ℕ) σ (.var i) v).eval) =
      Fin.snoc (α := fun _ => ℕ) (fun v => (σ v).eval) i := by
  funext v
  refine Fin.lastCases ?_ (fun j => ?_) v <;> simp

/-- The bridge: the run of a first-order statement in the environment of the values of the
index expressions $\sigma$ is the current run of its instantiation by $\sigma$. -/
theorem FStmt.exec_eq_exec_toStmt : ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ)
    (σ : Fin ni → IExp ℕ) (st : St P K C),
    s.exec I ρB (fun v => (σ v).eval) st = Computation.exec I (s.toStmt ρB σ) st
  | _, _, .skip, _, _, st => by rw [FStmt.exec, FStmt.toStmt, Computation.exec]
  | _, _, .seq s t, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec, s.exec_eq_exec_toStmt ρB σ st]
      congr 1; funext st'; exact t.exec_eq_exec_toStmt ρB σ st'
  | _, _, .instr i, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec,
        Instr.run_subst_congr i ρB (σ' := σ) (fun v => by simp)]
      rw [Instr.kind_subst i ρB (fun v => .const (σ v).eval) σ]
  | _, _, .apply o p d dOff s sOff cols, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
  | _, _, .rom p d i, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [Cell.subst, IExp.eval_subst]
  | _, _, .alloc p len body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      rw [body.exec_eq_exec_toStmt]
  | _, _, .loop n body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      congr 1; funext st' i
      rw [← eval_snoc, body.exec_eq_exec_toStmt]
  | _, _, .whileFuel fuel p c x y body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [IExp.eval_subst]
      congr 2; funext s' _
      rw [cmpStep_subst_congr I p c x y ρB (σ' := σ) (fun v => by simp)]
      simp only [body.exec_eq_exec_toStmt]
  | _, _, .ite p c x y t e, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec,
        cmpStep_subst_congr I p c x y ρB (σ' := σ) (fun v => by simp)]
      congr 1; funext r
      rw [t.exec_eq_exec_toStmt, e.exec_eq_exec_toStmt]
  | _, _, .named _ _ body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec, body.exec_eq_exec_toStmt]
  | _, _, .kcall o p dims ins outs, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec]
      simp only [List.map_map, Function.comp_def, IExp.eval_subst]
  | _, _, .bindIdx p x bound body, ρB, σ, st => by
      rw [FStmt.exec, FStmt.toStmt, Computation.exec,
        toNatStep_subst_congr I p x ρB (σ' := σ) (fun v => by simp)]
      simp only [IExp.eval_subst]
      congr 1; funext r
      rw [← eval_snoc, body.exec_eq_exec_toStmt]

/-- The bridge for programs: the run of a program at the sizes $N$ and $n$ is the current
run of its instantiation at these sizes. -/
theorem Prog.exec_eq_exec_toStmt {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ)
    (st : St P K C) : prog.exec I N n st = Computation.exec I (prog.toStmt N n) st := by
  rw [Prog.exec, Prog.toStmt, ← FStmt.exec_eq_exec_toStmt]
  congr 1
  funext v
  refine Fin.cases ?_ (fun j => ?_) v <;> simp

end Bridge

/-! ### Running within a budget -/

section Budget

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Preorder C]

/-- **A run of a program within a budget**: the start state `st₀` holds exactly the `b` declared
buffers of `prog` (so the program's scratch buffers cannot take a declared buffer's handle), and
the run of `prog` at the sizes $N$ and $n$ from `st₀` under `I` succeeds in a state `st` whose
counts are at most `c` more than at the start, whose peak memory plus the read-only data is at
most `m p` cells at each tag `p`, and which satisfies `Q`. -/
def Prog.RunsWithin {r b : ℕ} (I : Interp P ι K C) (prog : Prog P ι r b) (N : ℕ)
    (n : Fin r → ℕ) (st₀ : St P K C) (c : C) (m : P → ℕ) (Q : St P K C → Prop) : Prop :=
  st₀.store.size = b ∧ ∃ st, prog.exec I N n st₀ = some st ∧ st.cnt ≤ st₀.cnt + c ∧
    (∀ q, st.peak q + I.romSize q ≤ m q) ∧ Q st

/-- A program runs within a budget from a state of its `b` declared buffers if and only if its
instantiation at the same sizes does. -/
theorem Prog.runsWithin_iff {r b : ℕ} (I : Interp P ι K C) (prog : Prog P ι r b) (N : ℕ)
    (n : Fin r → ℕ) (st₀ : St P K C) (hsize : st₀.store.size = b) (c : C) (m : P → ℕ)
    (Q : St P K C → Prop) :
    prog.RunsWithin I N n st₀ c m Q ↔ Computation.RunsWithin I (prog.toStmt N n) st₀ c m Q := by
  simp only [Prog.RunsWithin, Computation.RunsWithin, Prog.exec_eq_exec_toStmt, hsize, true_and]

end Budget

/-! ### Invariants of the run -/

section Invariants

variable {P ι K : Type} [DecidableEq P] {I : Interp P ι K (OpCount P ι)} {r b : ℕ}
  {prog : Prog P ι r b} {N : ℕ} {n : Fin r → ℕ} {st st' : St P K (OpCount P ι)}

/-- The counts of a run of a program only grow. -/
theorem Prog.cnt_le_of_exec_eq_some (h : prog.exec I N n st = some st') : st.cnt ≤ st'.cnt :=
  Computation.cnt_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- Every allocation of a program is freed: a run ends with the current memory in cells, at
every tag, of its start. -/
theorem Prog.cur_eq_of_exec_eq_some (h : prog.exec I N n st = some st') : st'.cur = st.cur :=
  Computation.cur_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- A run of a program ends with the current memory in bits of its start. -/
theorem Prog.curW_eq_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st'.curW = st.curW :=
  Computation.curW_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- A run of a program frees exactly what it allocates: it ends with the shape of the store of
its start. -/
theorem Prog.shape_eq_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st'.store.shape = st.store.shape :=
  Computation.shape_eq_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- The peak memory in cells of a run of a program only grows. -/
theorem Prog.peak_le_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st.peak ≤ st'.peak :=
  Computation.peak_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- The peak memory in bits of a run of a program only grows. -/
theorem Prog.peakW_le_of_exec_eq_some (h : prog.exec I N n st = some st') :
    st.peakW ≤ st'.peakW :=
  Computation.peakW_le_of_exec_eq_some ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h)

/-- Every write of a program is charged: if no operation kind is free, a run whose counts do not
grow leaves the store unchanged. -/
theorem Prog.store_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : prog.exec I N n st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.store = st.store :=
  Computation.store_eq_of_exec_eq_some_of_cnt_le hc
    ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h) hcnt

/-- Every draw of a program is charged: if no operation kind is free, a run whose counts do not
grow leaves the tape positions unchanged. -/
theorem Prog.pos_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : prog.exec I N n st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.pos = st.pos :=
  Computation.pos_eq_of_exec_eq_some_of_cnt_le hc
    ((Prog.exec_eq_exec_toStmt I prog N n st).symm.trans h) hcnt

/-- The oracle is a program's only access to the matrix: under the standard charge, a run that
makes no oracle call (its load counts do not grow) is the same run under any other oracle. -/
theorem Prog.exec_eq_of_exec_eq_some_of_cnt_load_le (hc : IsUnitCharge I)
    (O : ι → ℕ → Array K → Option (Array K)) (h : prog.exec I N n st = some st')
    (hl : ∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) :
    prog.exec { I with oracle := O } N n st = some st' := by
  rw [Prog.exec_eq_exec_toStmt] at h ⊢
  exact Computation.exec_eq_of_exec_eq_some_of_cnt_load_le hc O _ h hl

end Invariants

/-! ### Kernel calls -/

section KernelCalls

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The run of a first-order kernel call: in the environment of handles `ρB` and of index
values `ρI`, it runs `NLAlib.Computation.Interp.kcallStore` at the values of its dimensions and
offsets, the handles renamed by `ρB`, and charges one call of its kind at those dimensions.
No printed source. -/
theorem FStmt.exec_kcall (I : Interp P ι K C) {nb ni : ℕ} (o : ι) (p : P)
    (dims : List (IExp (Fin ni))) (ins outs : List (Fin nb × IExp (Fin ni))) (ρB : Fin nb → ℕ)
    (ρI : Fin ni → ℕ) (st : St P K C) :
    (FStmt.kcall o p dims ins outs).exec I ρB ρI st =
      (I.kcallStore o p (dims.map (·.evalIn ρI)) (ins.map fun x => (ρB x.1, x.2.evalIn ρI))
        (outs.map fun x => (ρB x.1, x.2.evalIn ρI)) st.store).map fun s =>
          { st with
            store := s
            cnt := st.cnt + I.charge (.kcall p o (dims.map (·.evalIn ρI))) } := by
  rw [FStmt.exec]

/-- The run of a first-order index binder: in the environment of handles `ρB` and of index values
`ρI`, it converts the value of its cell (`NLAlib.Computation.toNatStep`) and runs the body with the
value as the new index variable if it is at most the bound, and fails otherwise. No printed
source. -/
theorem FStmt.exec_bindIdx (I : Interp P ι K C) {nb ni : ℕ} (p : P) (x : Cell (Fin nb) (Fin ni))
    (bound : IExp (Fin ni)) (body : FStmt P ι nb (ni + 1)) (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
    (st : St P K C) :
    (FStmt.bindIdx p x bound body).exec I ρB ρI st =
      (toNatStep I p (x.subst ρB fun v => .const (ρI v)) st).bind fun r =>
        if r.1 ≤ bound.evalIn ρI then body.exec I ρB (Fin.snoc (α := fun _ => ℕ) ρI r.1) r.2
        else none := by
  rw [FStmt.exec]

end KernelCalls

/-! ### Index normal form

The run of a closed statement reads every index expression only through its value.
`NLAlib.Computation.Stmt.normIdx` replaces every index expression of a statement, under every
binder, by the constant of its value (design note `docs/design/Computation-EighProgram.md`, §2.4):
two statements with the same index normal form run the same, so a run lemma of a kernel stated at
constant sizes applies at any sizes with those values. -/

section IndexNormal

variable {P ι : Type}

/-- A cell with its index replaced by the constant of its value. -/
def Cell.normIdx (c : Cell ℕ ℕ) : Cell ℕ ℕ := ⟨c.buf, .const c.idx.eval⟩

/-- An instruction with its index expressions replaced by the constants of their values. -/
def Instr.normIdx : Instr P ℕ ℕ → Instr P ℕ ℕ
  | .lit p d q => .lit p d.normIdx q
  | .litIdx p d e => .litIdx p d.normIdx (.const e.eval)
  | .bin p b d x y => .bin p b d.normIdx x.normIdx y.normIdx
  | .un p u d x => .un p u d.normIdx x.normIdx
  | .copy p d s => .copy p d.normIdx s.normIdx
  | .draw p dist d => .draw p dist d.normIdx
  | .convert p q d s => .convert p q d.normIdx s.normIdx

/-- **The index normal form** of a statement: every index expression, under every binder,
replaced by the constant of its value, and every named kernel by its body (the name is a label for
the emitter, and a named kernel runs as its body). -/
def Stmt.normIdx : Stmt P ι ℕ ℕ → Stmt P ι ℕ ℕ
  | .skip => .skip
  | .seq s t => .seq s.normIdx t.normIdx
  | .instr i => .instr i.normIdx
  | .apply o p d dOff s sOff cols =>
      .apply o p d (.const dOff.eval) s (.const sOff.eval) (.const cols.eval)
  | .rom p d i => .rom p d.normIdx (.const i.eval)
  | .alloc p len body => .alloc p (.const len.eval) fun h => (body h).normIdx
  | .loop n body => .loop (.const n.eval) fun i => (body i).normIdx
  | .whileFuel fuel p c x y body =>
      .whileFuel (.const fuel.eval) p c x.normIdx y.normIdx body.normIdx
  | .ite p c x y t e => .ite p c x.normIdx y.normIdx t.normIdx e.normIdx
  | .named _ _ body => body.normIdx
  | .kcall o p dims ins outs =>
      .kcall o p (dims.map fun e => .const e.eval) (ins.map fun x => (x.1, .const x.2.eval))
        (outs.map fun x => (x.1, .const x.2.eval))
  | .bindIdx p x bound body => .bindIdx p x.normIdx (.const bound.eval) fun i => (body i).normIdx

end IndexNormal

/-! ### Renaming tags and oracles

A program is registered at the tags `p` and oracles `mm`, `qr` of its arguments, and its
polynomial checks are decided on one instance. `NLAlib.Computation.FStmt.mapTags f g` renames the
tags by `f` and the oracle names by `g`, rebuilding every node, its `named` labels included: the
registered tree at the tags `p` is the renamed tree of one instance, and a count that reads neither
tags nor oracle names is the same on both. -/

section Rename

variable {P ι P' ι' : Type}

/-- A scalar instruction with its tags renamed by `f`. -/
def Instr.mapTag {VB VI : Type} (f : P → P') : Instr P VB VI → Instr P' VB VI
  | .lit p d q => .lit (f p) d q
  | .litIdx p d e => .litIdx (f p) d e
  | .bin p b d x y => .bin (f p) b d x y
  | .un p u d x => .un (f p) u d x
  | .copy p d s => .copy (f p) d s
  | .draw p dist d => .draw (f p) dist d
  | .convert p q d s => .convert (f p) (f q) d s

/-- A first-order statement with its tags renamed by `f` and its oracle names by `g`: every node
rebuilt, its `named` labels included. -/
def FStmt.mapTags (f : P → P') (g : ι → ι') : {nb ni : ℕ} → FStmt P ι nb ni → FStmt P' ι' nb ni
  | _, _, .skip => .skip
  | _, _, .seq s t => .seq (s.mapTags f g) (t.mapTags f g)
  | _, _, .instr i => .instr (i.mapTag f)
  | _, _, .apply o p d dOff s sOff cols => .apply (g o) (f p) d dOff s sOff cols
  | _, _, .rom p d i => .rom (f p) d i
  | _, _, .alloc p len b => .alloc (f p) len (b.mapTags f g)
  | _, _, .loop n b => .loop n (b.mapTags f g)
  | _, _, .whileFuel fu p c x y b => .whileFuel fu (f p) c x y (b.mapTags f g)
  | _, _, .ite p c x y t e => .ite (f p) c x y (t.mapTags f g) (e.mapTags f g)
  | _, _, .named n a b => .named n a (b.mapTags f g)
  | _, _, .kcall o p d i o' => .kcall (g o) (f p) d i o'
  | _, _, .bindIdx p x bd b => .bindIdx (f p) x bd (b.mapTags f g)

end Rename

end NLAlib.Computation
