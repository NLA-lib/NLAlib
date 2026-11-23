/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Semantics
public import NLAlib.Ops.Static

/-!
# Structural accounting bridges for reference execution

These lemmas relate the independent source charges to the evaluator's bookkeeping tallies.
They are proof infrastructure, not definitions of the reference rules.

## Main results

* `NLAlib.Ops.Reference.consistent_of_evalCounted`: successful execution preserves the
  live-scratch/peak invariant.
* `NLAlib.Ops.Reference.eval_tally`: a bookkeeping tally has exactly its specified charge.
-/

@[expose] public section

namespace NLAlib.Ops.Reference

variable {Op Tst K : Type}

/-- Successful execution preserves the fact that live scratch does not exceed its peak. -/
theorem consistent_of_evalCounted {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {a b : St Op Tst K}
    (h : evalCounted I W τ s ρ a = some b) (ha : a.cur ≤ a.peak) : b.cur ≤ b.peak := by
  have hc := (exec_within h).1
  have hh := map_addHistory_exec I W τ s ρ a 0 a.peak
  have he : St.addHistory 0 a.peak a = a := by simp [St.addHistory]
  rw [h, he, h, Option.map_some] at hh
  have hp := congrArg St.peak (Option.some.inj hh)
  change max a.peak b.peak = b.peak at hp
  rw [hc]
  exact ha.trans ((max_le_iff.mp hp.le).1)

/-- The sum of the independently specified charges of a bookkeeping list. -/
noncomputable def charges (ks : List Bookkeeping) : Count (Op ⊕ Bookkeeping) Tst :=
  (ks.map fun k => core k).sum

/-- An empty bookkeeping list has no charge. -/
theorem charges_nil : charges (Op := Op) (Tst := Tst) [] = 0 := rfl

/-- A bookkeeping list charges its head followed by its tail. -/
theorem charges_cons (k : Bookkeeping) (ks : List Bookkeeping) :
    charges (Op := Op) (Tst := Tst) (k :: ks) = core k + charges ks := rfl

/-- Concatenating bookkeeping lists adds their charges. -/
theorem charges_append (ks ls : List Bookkeeping) :
    charges (Op := Op) (Tst := Tst) (ks ++ ls) = charges ks + charges ls := by
  simp only [charges, List.map_append, List.sum_append]

/-- The instrumenter's index list agrees with the independent index charge. -/
theorem charges_index (e : IExp) :
    charges (Op := Op) (Tst := Tst) e.bookkeeping = index e := by
  induction e <;>
    simp only [IExp.bookkeeping, charges_append, charges_cons, charges_nil, add_zero,
      index, add_assoc, *]

/-- Dimension-list accounting agrees with the independent source charge. -/
theorem charges_dimensions (ds : List IExp) :
    charges (Op := Op) (Tst := Tst) (indexBookkeeping ds) = dimensions ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simpa [indexBookkeeping, List.flatMap_cons, charges_append, charges_index,
      dimensions] using congrArg (index d + ·) ih

/-- Address accounting agrees with the independent source charge. -/
theorem charges_operands (args : List Operand) :
    charges (Op := Op) (Tst := Tst) (operandBookkeeping args) = operands args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    change charges ((a.off.bookkeeping ++ [.operand]) ++ operandBookkeeping args) =
      index a.off + core .operand + operands args
    rw [charges_append, charges_append, charges_index, charges_cons, charges_nil, add_zero, ih]

/-- A bookkeeping tally adds exactly its charges without changing memory or scratch. -/
theorem eval_tally (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (ks : List Bookkeeping) (ρ : Env) (a : State Op Tst K) (ha : a.cur ≤ a.peak) :
    evalCounted I.instrument (instrumentWorkspace R.workspace) τ (tally ks) ρ a =
      some (charge (charges ks) a) := by
  induction ks generalizing a with
  | nil => simp [tally, evalCounted, charges, charge]
  | cons k ks ih =>
    let b := charge (core k) a
    have hb : b.cur ≤ b.peak := ha
    have hs : evalCounted I.instrument (instrumentWorkspace R.workspace) τ
        (.call (.inr k) [] [] []) ρ a = some b := by
      simp [evalCounted, IExp.evalList, Operand.evalList, Interp.callS_instrument_inr,
        instrumentWorkspace, Nat.max_eq_left ha, b, charge, core]
    change (evalCounted I.instrument (instrumentWorkspace R.workspace) τ
      (.call (.inr k) [] [] []) ρ a).bind
        (evalCounted I.instrument (instrumentWorkspace R.workspace) τ (tally ks) ρ) = _
    rw [hs, Option.bind_some]
    rw [ih b hb]
    simp only [b, charge, charges_cons, add_assoc]

/-- A source tally followed by another statement starts that statement at the charged state. -/
theorem eval_after_tally (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (ks : List Bookkeeping) (s : Stmt (Op ⊕ Bookkeeping) Tst) (ρ : Env)
    (a : State Op Tst K) (ha : a.cur ≤ a.peak) :
    evalCounted I.instrument (instrumentWorkspace R.workspace) τ (.seq (tally ks) s) ρ a =
      evalCounted I.instrument (instrumentWorkspace R.workspace) τ s ρ
        (charge (charges ks) a) := by
  rw [evalCounted, eval_tally I R τ ks ρ a ha, Option.bind_some]

/-- Charging consecutive instruction sets adds their counts. -/
theorem charge_charge (c d : Count (Op ⊕ Bookkeeping) Tst) (a : State Op Tst K) :
    charge c (charge d a) = charge (d + c) a := by
  simp [charge, add_assoc]

/-- The existing counted evaluator applied to an instrumented source tree. This abbreviation
is used only in the bridge proofs, not in the reference execution rules. -/
noncomputable abbrev instrumented (I : Interp Op Tst K) (R : ResourceModel Op Tst)
    (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (a : State Op Tst K) :=
  evalCounted I.instrument (instrumentWorkspace R.workspace) τ s.instrument ρ a

/-- Skip charges its one structural instruction. -/
theorem instrumented_skip (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (ρ : Env) (a : State Op Tst K) (ha : a.cur ≤ a.peak) :
    instrumented I R τ .skip ρ a = some (charge (core .skip) a) := by
  simpa only [instrumented, Stmt.instrument, charges_cons, charges_nil, add_zero] using
    eval_tally I R τ [.skip] ρ a ha

/-- Sequence enters the first statement with its sequence charge. -/
theorem instrumented_seq (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (s t : Stmt Op Tst) (ρ : Env) (a : State Op Tst K) (ha : a.cur ≤ a.peak) :
    instrumented I R τ (.seq s t) ρ a =
      (instrumented I R τ s ρ (charge (core .sequence) a)).bind
        (instrumented I R τ t ρ) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_cons, charges_nil, add_zero, evalCounted]

/-- An admitted call has its original memory effect, address charge and primitive workspace. -/
theorem instrumented_call (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (o : Op) (ds : List IExp) (ins outs : List Operand) (ρ : Env) (a : State Op Tst K)
    (ha : a.cur ≤ a.peak) {d : List ℕ} {xs ys : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (hx : Operand.evalList ρ ins = some xs)
    (hy : Operand.evalList ρ outs = some ys) :
    instrumented I R τ (.call o ds ins outs) ρ a =
      (I.callS o d xs ys τ a.mem).map fun m =>
        called R o d m (charge (dimensions ds + operands (ins ++ outs)) a) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_dimensions, charges_operands, evalCounted,
    hd, hx, hy, Option.bind_some, charge, Interp.callS_instrument_inl]
  rfl

/-- The branch charge and its actual query precede the selected statement. -/
theorem instrumented_ite (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (q : Tst) (ds : List IExp) (ins : List Operand) (s t : Stmt Op Tst) (ρ : Env)
    (a : State Op Tst K) (ha : a.cur ≤ a.peak) {d : List ℕ} {xs : List (ℕ × ℕ)} {v : Bool}
    (hd : IExp.evalList ρ.idx ds = some d) (hx : Operand.evalList ρ ins = some xs)
    (hq : I.test q d xs a.mem = some v) :
    instrumented I R τ (.ite q ds ins s t) ρ a =
      instrumented I R τ (if v then s else t) ρ
        (charge (dimensions ds + operands ins + core .branch + Count.test q d) a) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_dimensions, charges_operands, charges_cons,
    charges_nil, add_zero, evalCounted, hd, hx, Option.bind_some, charge,
    Interp.instrument, hq, St.tick, add_assoc]
  cases v <;> rfl

/-- A live frame runs its body at the evaluated dimensions and operands after its entry charge. -/
theorem instrumented_frame (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (ds : List IExp) (args : List Operand) (body : Stmt Op Tst) (ρ : Env)
    (a : State Op Tst K) (ha : a.cur ≤ a.peak) {d : List ℕ} {xs : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (hx : Operand.evalList ρ args = some xs)
    (hl : a.mem.Live xs) :
    instrumented I R τ (.frame ds args body) ρ a =
      instrumented I R τ body (Env.frame d xs)
        (charge (dimensions ds + operands args + core .frame) a) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_dimensions, charges_operands, charges_cons,
    charges_nil, add_zero, evalCounted, hd, hx, Option.bind_some, charge, if_pos hl]

/-- A bounded index query charges the conversion and enters its body at the returned index. -/
theorem instrumented_bindIdx (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (q : Tst) (ins : List Operand) (bound : IExp) (body : Stmt Op Tst) (ρ : Env)
    (a : State Op Tst K) (ha : a.cur ≤ a.peak) {xs : List (ℕ × ℕ)} {n v : ℕ}
    (hx : Operand.evalList ρ ins = some xs) (hn : bound.eval ρ.idx = some n)
    (hq : I.index q xs a.mem = some v) (hv : v ≤ n) :
    instrumented I R τ (.bindIdx q ins bound body) ρ a =
      instrumented I R τ body (ρ.pushIdx v)
        (charge (operands ins + index bound + core .bindIdx + Count.test q []) a) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_operands, charges_index, charges_cons,
    charges_nil, add_zero, evalCounted, hx, hn, Option.bind_some, charge,
    Interp.instrument, hq, if_pos hv, St.tick, add_assoc]

/-- A bookkeeping call at evaluated dimensions has its declared charge and no memory effect. -/
theorem eval_core (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (k : Bookkeeping) (ds : List IExp) (ρ : Env) (a : State Op Tst K)
    (ha : a.cur ≤ a.peak) {d : List ℕ} (hd : IExp.evalList ρ.idx ds = some d) :
    evalCounted I.instrument (instrumentWorkspace R.workspace) τ
      (.call (.inr k) ds [] []) ρ a = some (charge (core k d) a) := by
  simp [evalCounted, hd, Operand.evalList, Interp.callS_instrument_inr,
    instrumentWorkspace, Nat.max_eq_left ha, charge, core]

/-- Scoped allocation agrees with the source allocation and release states, including peak. -/
theorem instrumented_allocAs (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (fmt : StorageFormat) (len : IExp) (body : Stmt Op Tst) (ρ : Env)
    (a : State Op Tst K) (ha : a.cur ≤ a.peak) {n : ℕ} (hn : len.eval ρ.idx = some n) :
    instrumented I R τ (.allocAs fmt len body) ρ a =
      (instrumented I R τ body (ρ.pushBuf a.mem.store.length)
        (allocated fmt n (charge (index len) a))).map (released fmt n a.cur) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha, charges_index]
  change (evalCounted I.instrument (instrumentWorkspace R.workspace) τ
    (.call (.inr .allocate) [.const fmt.bytes, len] [] []) ρ (charge (index len) a)).bind _ = _
  rw [eval_core I R τ .allocate _ ρ (charge (index len) a) ha
    (d := [fmt.bytes, n]) (by simp [IExp.evalList, IExp.eval, hn]), Option.bind_some]
  let start := allocated fmt n (charge (index len) a)
  rw [evalCounted, evalCounted, hn, Option.bind_some]
  change ((evalCounted I.instrument (instrumentWorkspace R.workspace) τ
    body.instrument (ρ.pushBuf a.mem.store.length) start).map
      (fun b => (⟨⟨b.mem.store.pop, b.mem.pos⟩, b.cost, a.cur, b.peak⟩ : State Op Tst K))).bind
        (evalCounted I.instrument (instrumentWorkspace R.workspace) τ
          (.call (.inr .release) [.const fmt.bytes, len] [] []) ρ) = _
  cases hb : evalCounted I.instrument (instrumentWorkspace R.workspace) τ
      body.instrument (ρ.pushBuf a.mem.store.length) start with
  | none => rfl
  | some b =>
    have hstart : start.cur ≤ start.peak := Nat.le_max_right _ _
    have hcur := (exec_within hb).1
    have hp := consistent_of_evalCounted hb hstart
    have houter : a.cur ≤ b.peak := by
      rw [hcur] at hp
      exact (Nat.le_add_right a.cur _).trans hp
    simp only [Option.map_some, Option.bind_some]
    rw [eval_core I R τ .release _ ρ _ houter
      (d := [fmt.bytes, n]) (by simp [IExp.evalList, IExp.eval, hn])]
    rfl

/-- A counted loop enters its raw sequence of instrumented rounds after its entry charge. -/
theorem instrumented_loop (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (n : IExp) (body : Stmt Op Tst) (ρ : Env) (a : State Op Tst K)
    (ha : a.cur ≤ a.peak) {k : ℕ} (hn : n.eval ρ.idx = some k) :
    instrumented I R τ (.loop n body) ρ a =
      iter (fun i => evalCounted I.instrument (instrumentWorkspace R.workspace) τ
        (.seq (tally [.round]) body.instrument) (ρ.pushIdx i)) k
        (charge (index n + core .loop) a) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_index, charges_cons, charges_nil, add_zero,
    evalCounted, hn, Option.bind_some]

/-- Fuelled loops enter the counted query/body iteration after the fuel and entry charges. -/
theorem instrumented_whileFuel (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (fuel : IExp) (q : Tst) (ds : List IExp) (ins : List Operand)
    (body next : Stmt Op Tst) (ρ : Env) (a : State Op Tst K)
    (ha : a.cur ≤ a.peak) {n : ℕ} (hn : fuel.eval ρ.idx = some n) :
    instrumented I R τ (.whileFuel fuel q ds ins body next) ρ a =
      (whileIter (fun i => I.instrument.testSt q ds ins (ρ.pushIdx i))
        (fun i => evalCounted I.instrument (instrumentWorkspace R.workspace) τ
          (.seq (tally (indexBookkeeping ds ++ operandBookkeeping ins ++ [.round]))
            body.instrument) (ρ.pushIdx i)) n 0 (charge (index fuel + core .loop) a)).bind
        (fun jb => evalCounted I.instrument (instrumentWorkspace R.workspace) τ
          (.seq (tally (indexBookkeeping ds ++ operandBookkeeping ins ++ [.exit]))
            next.instrument) (ρ.pushIdx jb.1) jb.2) := by
  unfold instrumented
  rw [Stmt.instrument, eval_after_tally I R τ _ _ ρ a ha]
  simp only [charges_append, charges_index, charges_cons, charges_nil, add_zero,
    evalCounted, hn, Option.bind_some]

end NLAlib.Ops.Reference
