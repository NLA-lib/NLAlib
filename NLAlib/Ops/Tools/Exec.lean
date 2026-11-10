/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Static

/-!
# Tools: the counted run and the static count, computably

Outside the trusted base: nothing in `NLAlib.Ops` imports this file, and no theorem of the
library depends on it. It makes the evaluator of the core runnable by `#eval`.

`NLAlib.Ops.run` is computable as it stands. `NLAlib.Ops.exec` and `NLAlib.Ops.staticCost` are
not, because counts are finitely supported functions (`Finsupp`). This file gives a computable
twin of each and proves it equal to the core's definition; the core is not changed.

* `NLAlib.Ops.Tools.execC`: the counted run with the counts kept as a log of keys
  `(operation or query, dimensions)`. `NLAlib.Ops.Tools.map_toSt_execC`: mapped to a state of
  the core (`CSt.toSt`, the log summed into a `Count`), it is `exec`.
* `NLAlib.Ops.Tools.staticAt`: the static count at one key.
  `NLAlib.Ops.Tools.staticAt_eq`: it is `staticCost` evaluated at that key.
* `NLAlib.Ops.Tools.staticKeys`: the keys a tree can count (a list, possibly with repetitions);
  `NLAlib.Ops.Tools.staticAt_eq_zero`: every other key has static count zero.
-/

namespace NLAlib.Ops.Tools

open NLAlib.Ops

variable {Op Tst K : Type}

/-- A key of a count: an operation or a query, and the dimensions of its use. -/
abbrev Key (Op Tst : Type) := (Op ⊕ Tst) × List ℕ

/-- The count of a log of keys: one per entry. -/
noncomputable def logCount (l : List (Key Op Tst)) : Count Op Tst :=
  (l.map fun k => Finsupp.single k 1).sum

@[simp] theorem logCount_nil : logCount ([] : List (Key Op Tst)) = 0 := rfl

@[simp] theorem logCount_cons (k : Key Op Tst) (l : List (Key Op Tst)) :
    logCount (k :: l) = logCount l + Finsupp.single k 1 := by
  simp [logCount, add_comm]

/-- The state of the computable counted run: the counts are a log, most recent first. -/
structure CSt (Op Tst K : Type) where
  /-- The memory. -/
  mem : Mem K
  /-- The keys counted so far, most recent first. -/
  log : List (Key Op Tst)
  /-- The scratch cells now allocated. -/
  cur : ℕ
  /-- The peak of scratch cells. -/
  peak : ℕ

/-- The state of the core that a computable state stands for. -/
noncomputable def CSt.toSt (c : CSt Op Tst K) : St Op Tst K := ⟨c.mem, logCount c.log, c.cur, c.peak⟩

/-- The start of a run: no counts, no scratch. -/
def CSt.init (m : Mem K) : CSt Op Tst K := ⟨m, [], 0, 0⟩

theorem CSt.toSt_init (m : Mem K) : (CSt.init m : CSt Op Tst K).toSt = St.init m := rfl

/-- One use of the query `q` at `d`. -/
def CSt.tick (c : CSt Op Tst K) (q : Tst) (d : List ℕ) : CSt Op Tst K :=
  ⟨c.mem, (.inr q, d) :: c.log, c.cur, c.peak⟩

theorem CSt.toSt_tick (c : CSt Op Tst K) (q : Tst) (d : List ℕ) :
    (c.tick q d).toSt = c.toSt.tick q d := by
  simp [CSt.tick, CSt.toSt, St.tick, Count.test]

/-- The counted test of a loop round, computably. -/
def testC (I : Interp Op Tst K) (q : Tst) (ds : List IExp) (ins : List Operand) (ρ : Env)
    (c : CSt Op Tst K) : Option (Bool × CSt Op Tst K) :=
  (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
    (I.test q d a c.mem).map fun b => (b, c.tick q d)

/-- **The counted run, computably**: `exec` with the counts as a log. -/
def execC (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) :
    Stmt Op Tst → Env → CSt Op Tst K → Option (CSt Op Tst K)
  | .skip, _, st => some st
  | .abort, _, _ => none
  | .seq s t, ρ, st => (execC I W τ s ρ st).bind (execC I W τ t ρ)
  | .call o ds ins outs, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (Operand.evalList ρ outs).bind fun b => (I.callS o d a b τ st.mem).map fun m' =>
          ⟨m', (.inl o, d) :: st.log, st.cur, max st.peak (st.cur + W o d)⟩
  | .ite q ds ins t e, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ ins).bind fun a =>
        (I.test q d a st.mem).bind fun c =>
          if c then execC I W τ t ρ (st.tick q d) else execC I W τ e ρ (st.tick q d)
  | .whileFuel fuel q ds ins body k, ρ, st =>
      (fuel.eval ρ.idx).bind fun n =>
        (whileIter (fun i st => testC I q ds ins (ρ.pushIdx i) st)
          (fun i => execC I W τ body (ρ.pushIdx i)) n 0 st).bind fun jst =>
            execC I W τ k (ρ.pushIdx jst.1) jst.2
  | .bindIdx q ins bound body, ρ, st =>
      (Operand.evalList ρ ins).bind fun a => (bound.eval ρ.idx).bind fun B =>
        (I.index q a st.mem).bind fun v =>
          if v ≤ B then execC I W τ body (ρ.pushIdx v) (st.tick q []) else none
  | .alloc len body, ρ, st =>
      (len.eval ρ.idx).bind fun n =>
        (execC I W τ body (ρ.pushBuf st.mem.store.length)
          ⟨⟨st.mem.store.push n, st.mem.pos⟩, st.log, st.cur + n,
            max st.peak (st.cur + n)⟩).map fun st' =>
          ⟨⟨st'.mem.store.pop, st'.mem.pos⟩, st'.log, st.cur, st'.peak⟩
  | .loop n body, ρ, st =>
      (n.eval ρ.idx).bind fun k => iter (fun i st => execC I W τ body (ρ.pushIdx i) st) k st
  | .frame ds args body, ρ, st =>
      (IExp.evalList ρ.idx ds).bind fun d => (Operand.evalList ρ args).bind fun a =>
        if st.mem.Live a then execC I W τ body (Env.frame d a) st else none

theorem map_testC (I : Interp Op Tst K) (q : Tst) (ds : List IExp) (ins : List Operand) (ρ : Env)
    (c : CSt Op Tst K) :
    (testC I q ds ins ρ c).map (Prod.map id CSt.toSt) = I.testSt q ds ins ρ c.toSt := by
  simp only [testC, Interp.testSt]
  cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;> try rfl
  rename_i d a
  simp only [Option.bind_some, show c.toSt.mem = c.mem from rfl]
  cases I.test q d a c.mem <;> simp [CSt.toSt_tick]

/-- **The computable counted run is the counted run of the core.** -/
theorem map_toSt_execC (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K)
    (s : Stmt Op Tst) (ρ : Env) (c : CSt Op Tst K) :
    (execC I W τ s ρ c).map CSt.toSt = exec I W τ s ρ c.toSt := by
  induction s generalizing ρ c with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht =>
    simp only [execC, exec]
    rw [Option.map_bind_of_comm _ (fun a => iht ρ a), ihs]
  | call o ds ins outs =>
    simp only [execC, exec]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;>
      cases Operand.evalList ρ outs <;> simp [Option.map_map, Function.comp_def, CSt.toSt,
        Count.one]
  | ite q ds ins t e iht ihe =>
    simp only [execC, exec]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ ins <;> try rfl
    rename_i d a
    simp only [Option.bind_some, show c.toSt.mem = c.mem from rfl]
    cases I.test q d a c.mem with
    | none => rfl
    | some b => cases b <;> simp [iht, ihe, ← CSt.toSt_tick]
  | whileFuel fuel q ds ins body k ih ihk =>
    simp only [execC, exec]
    cases fuel.eval ρ.idx with
    | none => rfl
    | some n =>
      simp only [Option.bind_some]
      rw [Option.map_bind_of_comm (g := Prod.map id CSt.toSt)
        (f' := fun jst : ℕ × St Op Tst K => exec I W τ k (ρ.pushIdx jst.1) jst.2) _
        (fun a => ihk (ρ.pushIdx a.1) a.2)]
      rw [map_whileIter (fun i a => map_testC I q ds ins (ρ.pushIdx i) a)
        (fun i a => ih (ρ.pushIdx i) a)]
  | bindIdx q ins bound body ih =>
    simp only [execC, exec]
    cases Operand.evalList ρ ins <;> cases bound.eval ρ.idx <;> try rfl
    rename_i a B
    simp only [Option.bind_some, show c.toSt.mem = c.mem from rfl]
    cases I.index q a c.mem with
    | none => rfl
    | some v => by_cases hv : v ≤ B <;> simp [hv, ih, ← CSt.toSt_tick]
  | alloc len body ih =>
    simp only [execC, exec]
    cases len.eval ρ.idx with
    | none => rfl
    | some n =>
      have h := ih (ρ.pushBuf c.mem.store.length)
        ⟨⟨c.mem.store.push n, c.mem.pos⟩, c.log, c.cur + n, max c.peak (c.cur + n)⟩
      simp only [Option.bind_some]
      change _ = Option.map _ (exec I W τ body (ρ.pushBuf c.mem.store.length) (CSt.toSt
        ⟨⟨c.mem.store.push n, c.mem.pos⟩, c.log, c.cur + n, max c.peak (c.cur + n)⟩))
      rw [← h, Option.map_map, Option.map_map]
      rfl
  | loop n body ih =>
    simp only [execC, exec]
    cases n.eval ρ.idx with
    | none => rfl
    | some k => exact map_iter (fun i a => ih (ρ.pushIdx i) a) _ _
  | frame ds args body ih =>
    simp only [execC, exec]
    cases IExp.evalList ρ.idx ds <;> cases Operand.evalList ρ args <;> try rfl
    simp only [Option.bind_some, show c.toSt.mem = c.mem from rfl]
    split_ifs
    · exact ih _ _
    · rfl

/-- The computable counted run from the start state is `exec` from `St.init`. -/
theorem map_toSt_execC_init (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K)
    (s : Stmt Op Tst) (ρ : Env) (m : Mem K) :
    (execC I W τ s ρ (CSt.init m)).map CSt.toSt = exec I W τ s ρ (St.init m) :=
  map_toSt_execC I W τ s ρ (CSt.init m)

/-! ### The static count at a key -/

section Static

variable [DecidableEq Op] [DecidableEq Tst]

/-- The count at the key `k` of one use of `x` at the dimensions `ds`. -/
def useAt (x : Op ⊕ Tst) (ds : List IExp) (idx : List ℕ) (k : Key Op Tst) : ℕ :=
  match IExp.evalList idx ds with
  | some d => if (x, d) = k then 1 else 0
  | none => 0

/-- **The static count at the key `k`**, computably. -/
def staticAt : Stmt Op Tst → List ℕ → Key Op Tst → ℕ
  | .skip, _, _ => 0
  | .abort, _, _ => 0
  | .seq s t, idx, k => staticAt s idx k + staticAt t idx k
  | .call o ds _ _, idx, k => useAt (.inl o) ds idx k
  | .ite q ds _ t e, idx, k => useAt (.inr q) ds idx k + max (staticAt t idx k) (staticAt e idx k)
  | .whileFuel fuel q ds _ body c, idx, k =>
      ∑ i ∈ Finset.range ((fuel.eval idx).getD 0),
          (useAt (.inr q) ds (idx ++ [i]) k + staticAt body (idx ++ [i]) k) +
        (Finset.range ((fuel.eval idx).getD 0 + 1)).sup fun j => staticAt c (idx ++ [j]) k
  | .bindIdx q _ bound body, idx, k =>
      (if (.inr q, []) = k then 1 else 0) +
        (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v => staticAt body (idx ++ [v]) k
  | .alloc _ body, idx, k => staticAt body idx k
  | .loop n body, idx, k =>
      ∑ i ∈ Finset.range ((n.eval idx).getD 0), staticAt body (idx ++ [i]) k
  | .frame ds args body, idx, k =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => staticAt body (d ++ o) k
      | _, _ => 0

theorem useCost_apply (o : Op) (ds : List IExp) (idx : List ℕ) (k : Key Op Tst) :
    useCost o ds idx k = useAt (.inl o) ds idx k := by
  unfold useCost useAt
  cases IExp.evalList idx ds <;> simp [Count.one, Finsupp.single_apply]

theorem testCost_apply (q : Tst) (ds : List IExp) (idx : List ℕ) (k : Key Op Tst) :
    testCost (Op := Op) q ds idx k = useAt (.inr q) ds idx k := by
  unfold testCost useAt
  cases IExp.evalList idx ds <;> simp [Count.test, Finsupp.single_apply]

omit [DecidableEq Op] [DecidableEq Tst] in
theorem finsetSup_apply {ι : Type} (s : Finset ι) (f : ι → Count Op Tst) (k : Key Op Tst) :
    (s.sup f) k = s.sup fun i => f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s _ ih => rw [Finset.sup_insert, Finset.sup_insert, Finsupp.sup_apply, ih]

/-- **The computable static count is the static count of the core.** -/
theorem staticAt_eq (s : Stmt Op Tst) (idx : List ℕ) (k : Key Op Tst) :
    staticAt s idx k = staticCost s idx k := by
  induction s generalizing idx with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp [staticAt, staticCost, ihs, iht]
  | call o ds ins outs => simp [staticAt, staticCost, useCost_apply]
  | ite q ds ins t e iht ihe =>
    simp [staticAt, staticCost, iht, ihe, testCost_apply, Finsupp.sup_apply]
  | whileFuel fuel q ds ins body c ih ihc =>
    simp [staticAt, staticCost, ih, ihc, testCost_apply, finsetSup_apply]
  | bindIdx q ins bound body ih =>
    simp [staticAt, staticCost, ih, Count.test, Finsupp.single_apply, finsetSup_apply]
  | alloc len body ih => simp [staticAt, staticCost, ih]
  | loop n body ih => simp [staticAt, staticCost, ih, Finsupp.finsetSum_apply]
  | frame ds args body ih =>
    simp only [staticAt, staticCost]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;> simp [ih]

end Static

/-- The keys a use of `x` at the dimensions `ds` can count. -/
def useKeys (x : Op ⊕ Tst) (ds : List IExp) (idx : List ℕ) : List (Key Op Tst) :=
  match IExp.evalList idx ds with
  | some d => [(x, d)]
  | none => []

/-- **The keys of the static count**: every key with a nonzero static count is in this list. -/
def staticKeys : Stmt Op Tst → List ℕ → List (Key Op Tst)
  | .skip, _ => []
  | .abort, _ => []
  | .seq s t, idx => staticKeys s idx ++ staticKeys t idx
  | .call o ds _ _, idx => useKeys (.inl o) ds idx
  | .ite q ds _ t e, idx => useKeys (.inr q) ds idx ++ (staticKeys t idx ++ staticKeys e idx)
  | .whileFuel fuel q ds _ body c, idx =>
      ((List.range ((fuel.eval idx).getD 0)).flatMap fun i =>
          useKeys (.inr q) ds (idx ++ [i]) ++ staticKeys body (idx ++ [i])) ++
        (List.range ((fuel.eval idx).getD 0 + 1)).flatMap fun j => staticKeys c (idx ++ [j])
  | .bindIdx q _ bound body, idx =>
      (.inr q, []) :: (List.range ((bound.eval idx).getD 0 + 1)).flatMap fun v =>
        staticKeys body (idx ++ [v])
  | .alloc _ body, idx => staticKeys body idx
  | .loop n body, idx =>
      (List.range ((n.eval idx).getD 0)).flatMap fun i => staticKeys body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => staticKeys body (d ++ o)
      | _, _ => []

theorem useAt_eq_zero [DecidableEq Op] [DecidableEq Tst] {x : Op ⊕ Tst} {ds : List IExp}
    {idx : List ℕ} {k : Key Op Tst} (h : k ∉ useKeys x ds idx) : useAt x ds idx k = 0 := by
  unfold useAt
  unfold useKeys at h
  split
  · rename_i d hd
    rw [hd] at h
    exact if_neg fun e => h (by simp [← e])
  · rfl

/-- **Completeness of the keys**: a key outside `staticKeys` has static count zero. -/
theorem staticAt_eq_zero [DecidableEq Op] [DecidableEq Tst] (s : Stmt Op Tst) (idx : List ℕ)
    (k : Key Op Tst) (h : k ∉ staticKeys s idx) : staticAt s idx k = 0 := by
  induction s generalizing idx with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht =>
    simp only [staticKeys, List.mem_append, not_or] at h
    simp [staticAt, ihs _ h.1, iht _ h.2]
  | call o ds ins outs => exact useAt_eq_zero h
  | ite q ds ins t e iht ihe =>
    simp only [staticKeys, List.mem_append, not_or] at h
    simp [staticAt, useAt_eq_zero h.1, iht _ h.2.1, ihe _ h.2.2]
  | whileFuel fuel q ds ins body c ih ihc =>
    simp only [staticKeys, List.mem_append, List.mem_flatMap, List.mem_range, not_or,
      not_exists, not_and] at h
    simp only [staticAt]
    have h1 : ∀ i ∈ Finset.range ((fuel.eval idx).getD 0),
        useAt (.inr q) ds (idx ++ [i]) k + staticAt body (idx ++ [i]) k = 0 := fun i hi => by
      have := h.1 i (Finset.mem_range.mp hi)
      rw [useAt_eq_zero this.1, ih _ this.2]
    have h2 : ∀ j ∈ Finset.range ((fuel.eval idx).getD 0 + 1), staticAt c (idx ++ [j]) k ≤ 0 :=
      fun j hj => (ihc _ (h.2 j (Finset.mem_range.mp hj))).le
    rw [Finset.sum_eq_zero h1, Nat.eq_zero_of_le_zero (Finset.sup_le h2)]
  | bindIdx q ins bound body ih =>
    simp only [staticKeys, List.mem_cons, List.mem_flatMap, List.mem_range, not_or,
      not_exists, not_and] at h
    simp only [staticAt, if_neg (Ne.symm h.1), zero_add]
    exact Nat.eq_zero_of_le_zero
      (Finset.sup_le fun v hv => (ih _ (h.2 v (Finset.mem_range.mp hv))).le)
  | alloc len body ih => exact ih _ h
  | loop n body ih =>
    simp only [staticKeys, List.mem_flatMap, List.mem_range, not_exists, not_and] at h
    exact Finset.sum_eq_zero fun i hi => ih _ (h i (Finset.mem_range.mp hi))
  | frame ds args body ih =>
    simp only [staticKeys] at h
    simp only [staticAt]
    split <;> simp_all

end NLAlib.Ops.Tools
