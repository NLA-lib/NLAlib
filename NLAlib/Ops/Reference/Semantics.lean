/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Contract

/-!
# Declarative execution and accounting of source statements

The inference rules below run the source tree directly, with explicit structural charges.
They do not invoke an evaluator, instrumentation or static resource bounds. The auxiliary
judgments describe counted rounds and early exit; no rule admits a successful abort.

The format predicate and memory/index operations remain shared semantic definitions. The
final query reservation is conservative: it adds the largest executed query workspace to
the allocation/primitive peak. These choices are part of the reference statement.

`NLAlib/Ops/Reference/Equivalence.lean` proves equivalence with canonical execution and reads
every certificate through these rules. The rules do not replace the certificate definition.

## Main definitions

* `NLAlib.Ops.Reference.Derives`: successful execution with full source-level accounting.
* `NLAlib.Ops.Reference.Repeats`: the rounds of a counted loop.
* `NLAlib.Ops.Reference.While`: actual queries and rounds of an early-exit loop.
* `NLAlib.Ops.Reference.Execution`: checked execution and the query reservation.

## Main results

* `NLAlib.Ops.Reference.not_derives_abort`: abort has no successful derivation.
* `NLAlib.Ops.Reference.derives_note_iff`: annotations do not change execution.
-/

@[expose] public section

namespace NLAlib.Ops.Reference

variable {Op Tst K : Type}

/-- Memory, full counts, currently live scratch and its allocation/primitive peak. -/
abbrev State (Op Tst K : Type) := St (Op ⊕ Bookkeeping) Tst K

/-- One structural instruction, with allocation/release dimensions when relevant. -/
noncomputable def core (k : Bookkeeping) (ds : List ℕ := []) :
    Count (Op ⊕ Bookkeeping) Tst := Count.one (.inr k) ds

/-- The structural instructions for an index expression, specified on its syntax. -/
noncomputable def index : IExp → Count (Op ⊕ Bookkeeping) Tst
  | .var _ => core .indexVar
  | .const _ => core .indexConst
  | .add a b => index a + index b + core .indexAdd
  | .mul a b => index a + index b + core .indexMul
  | .sub a b => index a + index b + core .indexSub
  | .div a b => index a + index b + core .indexDiv

/-- Evaluating the dimension expressions charges their index instructions. -/
noncomputable def dimensions (ds : List IExp) : Count (Op ⊕ Bookkeeping) Tst :=
  (ds.map index).sum

/-- Resolving an operand charges its offset expression and one address resolution. -/
noncomputable def operands (args : List Operand) : Count (Op ⊕ Bookkeeping) Tst :=
  (args.map fun a => index a.off + core .operand).sum

/-- A structural or query charge preserves memory and current/peak scratch. -/
noncomputable def charge (c : Count (Op ⊕ Bookkeeping) Tst) (st : State Op Tst K) :
    State Op Tst K := { st with cost := st.cost + c }

/-- Successful primitive execution adds its key and reserves its workspace above live scratch. -/
noncomputable def called (R : ResourceModel Op Tst) (o : Op) (d : List ℕ)
    (m : Mem K) (st : State Op Tst K) : State Op Tst K :=
  { st with
    mem := m
    cost := st.cost + Count.one (.inl o) d
    peak := max st.peak (st.cur + R.workspace o d) }

/-- Enter an allocation, including its allocation charge and peak payload. -/
noncomputable def allocated (fmt : StorageFormat) (n : ℕ) (st : State Op Tst K) :
    State Op Tst K :=
  { mem := ⟨st.mem.store.push n, st.mem.pos⟩,
    cost := st.cost + core .allocate [fmt.bytes, n],
    cur := st.cur + fmt.bytes * n,
    peak := max st.peak (st.cur + fmt.bytes * n) }

/-- Leave a scoped allocation and charge release, restoring the outer live payload. -/
noncomputable def released (fmt : StorageFormat) (n outer : ℕ) (st : State Op Tst K) :
    State Op Tst K :=
  { mem := ⟨st.mem.store.pop, st.mem.pos⟩,
    cost := st.cost + core .release [fmt.bytes, n], cur := outer, peak := st.peak }

mutual

/-- Successful source execution. Each rule states the memory effect and structural charge;
there is no rule for abort. Calls explicitly require live operands and unchanged store shape. -/
inductive Derives (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K) :
    Stmt Op Tst → Env → State Op Tst K → State Op Tst K → Prop where
  /-- Skip changes no memory and charges one skipped instruction. -/
  | skip (ρ : Env) (a : State Op Tst K) :
      Derives I R τ .skip ρ a (charge (core .skip) a)
  /-- Sequence charges entry and runs its two parts in order. -/
  | seq {s t : Stmt Op Tst} {ρ : Env} {a b c : State Op Tst K}
      (hs : Derives I R τ s ρ (charge (core .sequence) a) b)
      (ht : Derives I R τ t ρ b c) : Derives I R τ (.seq s t) ρ a c
  /-- A live, shape-preserving call charges addressing and its primitive workspace. -/
  | call {o : Op} {ds : List IExp} {ins outs : List Operand} {ρ : Env}
      {d : List ℕ} {xs ys : List (ℕ × ℕ)} {a : State Op Tst K} {m : Mem K}
      (hd : IExp.evalList ρ.idx ds = some d)
      (hx : Operand.evalList ρ ins = some xs) (hy : Operand.evalList ρ outs = some ys)
      (hl : a.mem.Live (xs ++ ys)) (hr : I.call o d xs ys τ a.mem = some m)
      (hshape : m.store.shape = a.mem.store.shape) :
      Derives I R τ (.call o ds ins outs) ρ a
        (called R o d m (charge (dimensions ds + operands (ins ++ outs)) a))
  /-- A successful Boolean query selects exactly one branch. -/
  | ite {q : Tst} {ds : List IExp} {ins : List Operand} {s t : Stmt Op Tst}
      {ρ : Env} {d : List ℕ} {xs : List (ℕ × ℕ)} {v : Bool} {a b : State Op Tst K}
      (hd : IExp.evalList ρ.idx ds = some d) (hx : Operand.evalList ρ ins = some xs)
      (hq : I.test q d xs a.mem = some v)
      (hb : Derives I R τ (if v then s else t) ρ
        (charge (dimensions ds + operands ins + core .branch + Count.test q d) a) b) :
      Derives I R τ (.ite q ds ins s t) ρ a b
  /-- A counted loop evaluates its bound and runs that many charged rounds. -/
  | loop {n : IExp} {body : Stmt Op Tst} {ρ : Env} {k : ℕ} {a b : State Op Tst K}
      (hn : n.eval ρ.idx = some k)
      (hb : Repeats I R τ body ρ k (charge (index n + core .loop) a) b) :
      Derives I R τ (.loop n body) ρ a b
  /-- A fuelled loop runs its queries and bodies, then its charged continuation. -/
  | whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
      {body next : Stmt Op Tst} {ρ : Env} {n j : ℕ} {a b c : State Op Tst K}
      (hn : fuel.eval ρ.idx = some n)
      (hw : While I R τ q ds ins body ρ n 0 (charge (index fuel + core .loop) a) j b)
      (hk : Derives I R τ next (ρ.pushIdx j)
        (charge (dimensions ds + operands ins + core .exit) b) c) :
      Derives I R τ (.whileFuel fuel q ds ins body next) ρ a c
  /-- An index query must succeed within its bound before entering its body. -/
  | bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
      {ρ : Env} {xs : List (ℕ × ℕ)} {v n : ℕ} {a b : State Op Tst K}
      (hx : Operand.evalList ρ ins = some xs) (hn : bound.eval ρ.idx = some n)
      (hq : I.index q xs a.mem = some v) (hv : v ≤ n)
      (hb : Derives I R τ body (ρ.pushIdx v)
        (charge (operands ins + index bound + core .bindIdx + Count.test q []) a) b) :
      Derives I R τ (.bindIdx q ins bound body) ρ a b
  /-- A scoped buffer is allocated, used by the body, and released afterward. -/
  | allocAs {fmt : StorageFormat} {len : IExp} {body : Stmt Op Tst}
      {ρ : Env} {n : ℕ} {a b : State Op Tst K}
      (hn : len.eval ρ.idx = some n)
      (hb : Derives I R τ body (ρ.pushBuf a.mem.store.length)
        (allocated fmt n (charge (index len) a)) b) :
      Derives I R τ (.allocAs fmt len body) ρ a (released fmt n a.cur b)
  /-- A live frame changes the body's dimensions and operand environment. -/
  | frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst}
      {ρ : Env} {d : List ℕ} {xs : List (ℕ × ℕ)} {a b : State Op Tst K}
      (hd : IExp.evalList ρ.idx ds = some d) (hx : Operand.evalList ρ args = some xs)
      (hl : a.mem.Live xs)
      (hb : Derives I R τ body (Env.frame d xs)
        (charge (dimensions ds + operands args + core .frame) a) b) :
      Derives I R τ (.frame ds args body) ρ a b
  /-- A note preserves every execution and accounting field. -/
  | note {n : Note} {s : Stmt Op Tst} {ρ : Env} {a b : State Op Tst K}
      (hs : Derives I R τ s ρ a b) : Derives I R τ (.note n s) ρ a b

/-- A counted loop runs its body at indices zero through the number of rounds minus one.
Each executed body has one round charge; the entry charge belongs to the loop rule. -/
inductive Repeats (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K) :
    Stmt Op Tst → Env → ℕ → State Op Tst K → State Op Tst K → Prop where
  /-- Zero rounds change neither memory nor accounting. -/
  | zero (s : Stmt Op Tst) (ρ : Env) (a : State Op Tst K) : Repeats I R τ s ρ 0 a a
  /-- The next round runs after its prefix, at the prefix's length as index. -/
  | succ {s : Stmt Op Tst} {ρ : Env} {n : ℕ} {a b c : State Op Tst K}
      (hp : Repeats I R τ s ρ n a b)
      (hb : Derives I R τ s (ρ.pushIdx n) (charge (core .round) b) c) :
      Repeats I R τ s ρ (n + 1) a c

/-- An early-exit loop tests before each body and does not test at zero fuel. The returned
index determines its continuation; the enclosing statement charges the final exit allowance. -/
inductive While (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K) :
    Tst → List IExp → List Operand → Stmt Op Tst → Env → ℕ → ℕ →
      State Op Tst K → ℕ → State Op Tst K → Prop where
  /-- Exhausted fuel returns the current index without a query. -/
  | cap (q : Tst) (ds : List IExp) (ins : List Operand) (body : Stmt Op Tst)
      (ρ : Env) (i : ℕ) (a : State Op Tst K) : While I R τ q ds ins body ρ 0 i a i a
  /-- A false query is charged and stops before the body. -/
  | stop {q : Tst} {ds : List IExp} {ins : List Operand} {body : Stmt Op Tst}
      {ρ : Env} {n i : ℕ} {d : List ℕ} {xs : List (ℕ × ℕ)} {a : State Op Tst K}
      (hd : IExp.evalList (ρ.pushIdx i).idx ds = some d)
      (hx : Operand.evalList (ρ.pushIdx i) ins = some xs)
      (hq : I.test q d xs a.mem = some false) :
      While I R τ q ds ins body ρ (n + 1) i a i (charge (Count.test q d) a)
  /-- A true query is charged, runs one body, and continues with less fuel. -/
  | step {q : Tst} {ds : List IExp} {ins : List Operand} {body : Stmt Op Tst}
      {ρ : Env} {n i j : ℕ} {d : List ℕ} {xs : List (ℕ × ℕ)}
      {a b c : State Op Tst K}
      (hd : IExp.evalList (ρ.pushIdx i).idx ds = some d)
      (hx : Operand.evalList (ρ.pushIdx i) ins = some xs)
      (hq : I.test q d xs a.mem = some true)
      (hb : Derives I R τ body (ρ.pushIdx i)
        (charge (Count.test q d + dimensions ds + operands ins + core .round) a) b)
      (ht : While I R τ q ds ins body ρ n (i + 1) b j c) :
      While I R τ q ds ins body ρ (n + 1) i a j c

end

/-- A checked source derivation, with the conservative largest-query-workspace reservation
added once to its allocation/primitive peak. Format validation remains a shared definition. -/
def Execution {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) (out : State Op Tst K) : Prop :=
  p.wellTyped R formats = true ∧ m.store.length = b ∧ ∃ raw : State Op Tst K,
    Derives I R τ p.body (Program.environment (b := b) d) (St.init m) raw ∧
      out = { raw with peak := raw.peak + R.queryReserve raw.cost }

/-- Abort has no successful source derivation. -/
theorem not_derives_abort {I : Interp Op Tst K} {R : ResourceModel Op Tst} {τ : Tape K}
    {ρ : Env} {a b : State Op Tst K} : ¬ Derives I R τ .abort ρ a b := by
  intro h
  cases h

/-- An annotation has exactly the derivations of the statement it annotates. -/
theorem derives_note_iff {I : Interp Op Tst K} {R : ResourceModel Op Tst} {τ : Tape K}
    {n : Note} {s : Stmt Op Tst} {ρ : Env} {a b : State Op Tst K} :
    Derives I R τ (.note n s) ρ a b ↔ Derives I R τ s ρ a b := by
  constructor
  · intro h
    cases h with
    | note hs => exact hs
  · exact Derives.note

end NLAlib.Ops.Reference
