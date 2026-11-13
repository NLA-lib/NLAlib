/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import NLAlib.Ops.Transfer

/-!
# Shared adapters for canonical algorithm certification

Supplied buffers remain explicit data. Their initial memory facts follow from their finite
indices, and total conditional program proofs supply total word-level preconditions. Original
operation counts can be projected out of the complete mandatory instrumented count without
losing the separate accounting guarantee on structural instructions.

## Main results

* `NLAlib.Ops.Problem.initial_readBlock`: a supplied initialized buffer can be read directly.
* `NLAlib.Ops.ConditionalRuns.wp`: total conditional execution supplies total program logic.
* `NLAlib.Ops.original_stmtCost_instrument`: structural instrumentation preserves raw counts.
* `NLAlib.Ops.Algorithm.ofWpActual`: actual-count resource proofs give total certificates.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- The initial stack has exactly the declared number of supplied buffers. -/
@[simp] theorem Problem.length_initial (d : Fin r → ℕ) (x : P.Input d) :
    (P.initial d x).store.length = b := by
  simp [Problem.initial]

/-- A supplied buffer retains its actual capacity in the initial memory. -/
@[simp] theorem Problem.initial_len (d : Fin r → ℕ) (x : P.Input d) (i : Fin b) :
    (P.initial d x).store.len i.val = (x.val.2 i).length := by
  simp [Problem.initial, Store.len]

/-- Initial reads address the supplied words, with no algorithm-dependent initializer. -/
@[simp] theorem Problem.initial_get (d : Fin r → ℕ) (x : P.Input d) (i : Fin b) (j : ℕ) :
    (P.initial d x).store.get i.val j = ((x.val.2 i)[j]?).join := by
  simp [Problem.initial, Store.get]

/-- A buffer supplied as initialized words reads back that very word list. -/
theorem Problem.initial_readBlock (d : Fin r → ℕ) (x : P.Input d) (i : Fin b)
    {xs : List K} (h : x.val.2 i = xs.map some) :
    (P.initial d x).store.readBlock i.val 0 xs.length = some xs := by
  refine Store.readBlock_eq_some_iff.mpr ⟨rfl, fun j hj => ?_⟩
  simp only [Nat.zero_add, Problem.initial_get, h, List.getElem?_map]
  cases xs[j]? <;> rfl

/-- Declared buffer capacities determine resident payload, including uninitialized slots. -/
theorem Problem.initialBytes_of_lengths (d : Fin r → ℕ) (x : P.Input d)
    (lens : Fin b → ℕ) (h : ∀ i, (x.val.2 i).length = lens i) :
    P.initialBytes d x = (List.ofFn fun i => (P.formats i).bytes * lens i).sum := by
  simp only [Problem.initialBytes, h]

/-- A successful conditional run provides total word-level logic. Raw count/workspace bounds
are not promoted here; canonical certification separately requires all instrumented bounds. -/
theorem ConditionalRuns.wp {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {c : Count Op Tst} {p : ℕ} {Q : Mem K → Prop}
    (h : ConditionalRuns I W τ s ρ m c p Q) : Wp .total I τ s ρ Q m := by
  obtain ⟨st, hr, _, _, hQ⟩ := h
  exact ⟨st.mem, run_of_exec hr, hQ⟩

/-- Original-operation projection preserves pointwise worst-case branch counts. -/
theorem Count.original_sup (c d : Count (Op ⊕ Bookkeeping) Tst) :
    Count.original (c ⊔ d) = Count.original c ⊔ Count.original d := by
  ext k
  simp only [Count.original_apply, Finsupp.sup_apply]

/-- Original-operation projection preserves finite worst-case loop bounds. -/
theorem Count.original_finset_sup {α : Type} (s : Finset α)
    (f : α → Count (Op ⊕ Bookkeeping) Tst) :
    Count.original (s.sup f) = s.sup (fun i => Count.original (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change Count.original (0 : Count (Op ⊕ Bookkeeping) Tst) = 0
    exact map_zero _
  | @insert a s ha ih => simp only [Finset.sup_insert, Count.original_sup, ih]

/-- Original calls retain their dimension-dependent static count. -/
theorem original_useCost (o : Op) (ds : List IExp) (idx : List ℕ) :
    Count.original (useCost (.inl o) ds idx : Count (Op ⊕ Bookkeeping) Tst) =
      useCost o ds idx := by
  unfold useCost
  cases IExp.evalList idx ds <;> simp

/-- A structural instruction has no original-operation count, even when dimensions fail. -/
theorem original_useCost_inr (o : Bookkeeping) (ds : List IExp) (idx : List ℕ) :
    Count.original (useCost (.inr o) ds idx : Count (Op ⊕ Bookkeeping) Tst) = 0 := by
  unfold useCost
  cases IExp.evalList idx ds <;> simp

/-- Query counts are preserved independently of structural instrumentation. -/
theorem original_testCost (q : Tst) (ds : List IExp) (idx : List ℕ) :
    Count.original (testCost q ds idx : Count (Op ⊕ Bookkeeping) Tst) =
      testCost q ds idx := by
  unfold testCost
  cases IExp.evalList idx ds <;> simp

/-- Bookkeeping-only syntax has no original calls or queries. -/
theorem original_stmtCost_tally (ks : List Bookkeeping) (idx : List ℕ) :
    Count.original (stmtCost (tally (Op := Op) (Tst := Tst) ks) idx) = 0 := by
  induction ks with
  | nil => simp [tally, stmtCost]
  | cons k ks ih => simp [tally, stmtCost, original_useCost_inr, ih]

/-- Structural instrumentation preserves the original operation/query static count exactly.
The unprojected static count still contains all structural and address-evaluation work. -/
theorem original_stmtCost_instrument (s : Stmt Op Tst) (idx : List ℕ) :
    Count.original (stmtCost s.instrument idx) = stmtCost s idx := by
  induction s generalizing idx with
  | skip => exact original_stmtCost_tally ..
  | abort => rfl
  | seq s t ihs iht =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ihs, iht]
  | call o ds ins outs =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, original_useCost]
  | ite q ds ins t e iht ihe =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_sup, iht, ihe,
      original_testCost]
  | whileFuel fuel q ds ins body k ih ihk =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_finset_sup,
      ih, ihk, original_testCost]
  | bindIdx q ins bound body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_finset_sup, ih]
  | allocAs fmt len body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ih,
      original_useCost_inr]
  | loop n body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ih]
  | frame ds args body ih =>
    simp only [Stmt.instrument, stmtCost, map_add, original_stmtCost_tally, zero_add]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;> simp [ih]

private def ProjectsOriginal (a : St (Op ⊕ Bookkeeping) Tst K) (b : St Op Tst K) : Prop :=
  a.mem = b.mem ∧ Count.original a.cost = b.cost

private theorem projectsOriginal_tick {a : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : ProjectsOriginal a b) (q : Tst) (ds : List ℕ) :
    ProjectsOriginal (a.tick q ds) (b.tick q ds) := by
  exact ⟨h.1, by simp only [St.tick, map_add, Count.original_test, h.2]⟩

private theorem projectsOriginal_bookkeeping {I : Interp Op Tst K}
    {W : Op → List ℕ → ℕ} {τ : Tape K} {ρ : Env} {k : Bookkeeping} {ds : List IExp}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ
      (.call (.inr k) ds [] []) ρ a = some a') (hab : ProjectsOriginal a b) :
    ProjectsOriginal a' b := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Operand.evalList, Option.bind_some, Interp.callS_instrument_inr,
    Option.map_some] at h
  cases h
  exact ⟨hab.1, by simp only [map_add, Count.original_bookkeeping, add_zero, hab.2]⟩

private theorem projectsOriginal_tally {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {ρ : Env} {ks : List Bookkeeping}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ (tally ks) ρ a = some a')
    (hab : ProjectsOriginal a b) : ProjectsOriginal a' b := by
  induction ks generalizing a with
  | nil => cases h; exact hab
  | cons k ks ih =>
    obtain ⟨a₁, ha, h⟩ := Option.bind_eq_some_iff.mp h
    exact ih h (projectsOriginal_bookkeeping ha hab)

private theorem after_tally {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {ρ : Env} {ks : List Bookkeeping} {s : Stmt (Op ⊕ Bookkeeping) Tst}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ (.seq (tally ks) s) ρ a = some a')
    (hab : ProjectsOriginal a b) :
    ∃ a₁, evalCounted I.instrument (instrumentWorkspace W) τ s ρ a₁ = some a' ∧
      ProjectsOriginal a₁ b := by
  obtain ⟨a₁, ha, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a₁, h, projectsOriginal_tally ha hab⟩

private theorem projectsOriginal_call {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {ρ : Env} {o : Op} {ds : List IExp} {ins outs : List Operand}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ
      (.call (.inl o) ds ins outs) ρ a = some a') (hab : ProjectsOriginal a b) :
    ∃ b', evalCounted I W τ (.call o ds ins outs) ρ b = some b' ∧
      ProjectsOriginal a' b' := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m', hm, h⟩ := Option.map_eq_some_iff.mp h
  cases h
  refine ⟨⟨m', b.cost + Count.one o d, b.cur, max b.peak (b.cur + W o d)⟩, ?_, ?_⟩
  · simp only [evalCounted, hd, hxs, hys, Option.bind_some]
    rw [← hab.1, ← Interp.callS_instrument_inl, hm]
    rfl
  · exact ⟨rfl, by simp only [map_add, Count.original_one, hab.2]⟩

private theorem projectsOriginal_test {I : Interp Op Tst K} {q : Tst}
    {ds : List IExp} {ins : List Operand} {ρ : Env}
    {a : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    {bs : Bool × St (Op ⊕ Bookkeeping) Tst K}
    (h : I.instrument.testSt q ds ins ρ a = some bs) (hab : ProjectsOriginal a b) :
    ∃ b', I.testSt q ds ins ρ b = some (bs.1, b') ∧ ProjectsOriginal bs.2 b' := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, h⟩ := Option.map_eq_some_iff.mp h
  cases h
  refine ⟨b.tick q d, ?_, projectsOriginal_tick hab q d⟩
  simp only [Interp.testSt, hd, hxs, Option.bind_some]
  rw [← hab.1, show I.test q d xs a.mem = some v from hv]
  rfl

private theorem projectsOriginal_alloc {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s : Stmt Op Tst}
    (ih : ∀ ρ a a' b, evalCounted I.instrument (instrumentWorkspace W) τ s.instrument ρ a =
      some a' → ProjectsOriginal a b →
        ∃ b', evalCounted I W τ s ρ b = some b' ∧ ProjectsOriginal a' b')
    {ρ : Env} {fmt : StorageFormat} {len : IExp}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ
      (Stmt.allocAs fmt len s).instrument ρ a = some a') (hab : ProjectsOriginal a b) :
    ∃ b', evalCounted I W τ (.allocAs fmt len s) ρ b = some b' ∧
      ProjectsOriginal a' b' := by
  obtain ⟨a₁, h, hab₁⟩ := after_tally h hab
  obtain ⟨a₂, ha₂, h⟩ := Option.bind_eq_some_iff.mp h
  have hab₂ := projectsOriginal_bookkeeping ha₂ hab₁
  obtain ⟨a₃, hbody, hrelease⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨n, hn, hbody⟩ := Option.bind_eq_some_iff.mp hbody
  obtain ⟨a₄, ha₄, hpop⟩ := Option.map_eq_some_iff.mp hbody
  cases hpop
  have hin : ProjectsOriginal
      ⟨⟨a₂.mem.store.push n, a₂.mem.pos⟩, a₂.cost, a₂.cur + fmt.bytes * n,
        max a₂.peak (a₂.cur + fmt.bytes * n)⟩
      ⟨⟨b.mem.store.push n, b.mem.pos⟩, b.cost, b.cur + fmt.bytes * n,
        max b.peak (b.cur + fmt.bytes * n)⟩ :=
    ⟨congrArg (fun m : Mem K => (⟨m.store.push n, m.pos⟩ : Mem K)) hab₂.1, hab₂.2⟩
  rw [show a₂.mem.store.length = b.mem.store.length from
    congrArg (fun m : Mem K => m.store.length) hab₂.1] at ha₄
  obtain ⟨b₄, hb₄, hab₄⟩ := ih _ _ _ _ ha₄ hin
  let b' : St Op Tst K := ⟨⟨b₄.mem.store.pop, b₄.mem.pos⟩, b₄.cost, b.cur, b₄.peak⟩
  have hpop : ProjectsOriginal ⟨⟨a₄.mem.store.pop, a₄.mem.pos⟩, a₄.cost, a₂.cur, a₄.peak⟩ b' :=
    ⟨congrArg (fun m : Mem K => (⟨m.store.pop, m.pos⟩ : Mem K)) hab₄.1, hab₄.2⟩
  refine ⟨b', ?_, projectsOriginal_bookkeeping hrelease hpop⟩
  simp only [evalCounted, hn, Option.bind_some, hb₄, Option.map_some]
  rfl

private theorem projectsOriginal_while {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s k : Stmt Op Tst}
    (ihs : ∀ ρ a a' b, evalCounted I.instrument (instrumentWorkspace W) τ s.instrument ρ a =
      some a' → ProjectsOriginal a b →
        ∃ b', evalCounted I W τ s ρ b = some b' ∧ ProjectsOriginal a' b')
    (ihk : ∀ ρ a a' b, evalCounted I.instrument (instrumentWorkspace W) τ k.instrument ρ a =
      some a' → ProjectsOriginal a b →
        ∃ b', evalCounted I W τ k ρ b = some b' ∧ ProjectsOriginal a' b')
    {ρ : Env} {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {a a' : St (Op ⊕ Bookkeeping) Tst K} {b : St Op Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ
      (Stmt.whileFuel fuel q ds ins s k).instrument ρ a = some a')
    (hab : ProjectsOriginal a b) :
    ∃ b', evalCounted I W τ (.whileFuel fuel q ds ins s k) ρ b = some b' ∧
      ProjectsOriginal a' b' := by
  obtain ⟨a₁, h, hab₁⟩ := after_tally h hab
  obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨js, hloop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b₁, hb₁, hab₁⟩ := whileIter_sim ProjectsOriginal
    (test := fun i st => I.instrument.testSt q ds ins (ρ.pushIdx i) st)
    (test' := fun i st => I.testSt q ds ins (ρ.pushIdx i) st)
    (body := fun i => evalCounted I.instrument (instrumentWorkspace W) τ
      (.seq (tally (indexBookkeeping ds ++ operandBookkeeping ins ++ [.round])) s.instrument)
        (ρ.pushIdx i))
    (body' := fun i => evalCounted I W τ s (ρ.pushIdx i))
    (fun _ _ _ _ hp ht => projectsOriginal_test ht hp)
    (fun i a a' b hp hbody => by
      obtain ⟨a₀, hbody, hp⟩ := after_tally hbody hp
      exact ihs (ρ.pushIdx i) a₀ a' b hbody hp) n 0 a₁ js b hab₁ hloop
  obtain ⟨a₂, h, hab₂⟩ := after_tally h hab₁
  obtain ⟨b', hb', hp⟩ := ihk _ _ _ _ h hab₂
  exact ⟨b', by simp only [evalCounted, hn, Option.bind_some, hb₁, hb'], hp⟩

private theorem projectsOriginal_instrument {I : Interp Op Tst K}
    {W : Op → List ℕ → ℕ} {τ : Tape K} (s : Stmt Op Tst) :
    ∀ ρ a a' b, evalCounted I.instrument (instrumentWorkspace W) τ s.instrument ρ a =
      some a' → ProjectsOriginal a b →
        ∃ b', evalCounted I W τ s ρ b = some b' ∧ ProjectsOriginal a' b' := by
  induction s with
  | skip =>
    intro ρ a a' b h hab
    exact ⟨b, rfl, projectsOriginal_tally h hab⟩
  | abort => intro ρ a a' b h hab; cases h
  | seq s t ihs iht =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b₁, hb₁, hab₁⟩ := ihs _ _ _ _ ha₁ hab
    obtain ⟨b', hb', hp⟩ := iht _ _ _ _ h hab₁
    exact ⟨b', by simp only [evalCounted, hb₁, Option.bind_some, hb'], hp⟩
  | call o ds ins outs =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    exact projectsOriginal_call h hab
  | ite q ds ins s t ihs iht =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    have hp := projectsOriginal_tick hab q d
    have hv' : I.test q d xs b.mem = some v := by rw [← hab.1]; exact hv
    cases v
    · obtain ⟨b', hb', hp⟩ := iht _ _ _ _ h hp
      exact ⟨b', by simp only [evalCounted, hd, hxs, hv', Option.bind_some, Bool.false_eq_true,
        ↓reduceIte, hb'], hp⟩
    · obtain ⟨b', hb', hp⟩ := ihs _ _ _ _ h hp
      exact ⟨b', by simp only [evalCounted, hd, hxs, hv', Option.bind_some, ↓reduceIte, hb'], hp⟩
  | whileFuel fuel q ds ins s k ihs ihk =>
    exact fun _ _ _ _ h hab => projectsOriginal_while ihs ihk h hab
  | bindIdx q ins bound s ih =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hvB
    obtain ⟨b', hb', hp⟩ := ih _ _ _ _ h (projectsOriginal_tick hab q [])
    refine ⟨b', ?_, hp⟩
    simp only [evalCounted, hxs, hB, Option.bind_some]
    rw [← hab.1, show I.index q xs a₀.mem = some v from hv, Option.bind_some, if_pos hvB, hb']
  | allocAs fmt len s ih => exact fun _ _ _ _ h hab => projectsOriginal_alloc ih h hab
  | loop n s ih =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb', hp⟩ := iter_sim ProjectsOriginal (fun i a a' b hp hbody => by
      obtain ⟨a₁, hbody, hp⟩ := after_tally hbody hp
      exact ih (ρ.pushIdx i) a₁ a' b hbody hp) k a₀ a' b hab h
    exact ⟨b', by simp only [evalCounted, hk, Option.bind_some, hb'], hp⟩
  | frame ds args s ih =>
    intro ρ a a' b h hab
    obtain ⟨a₀, h, hab⟩ := after_tally h hab
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hl
    obtain ⟨b', hb', hp⟩ := ih _ _ _ _ h hab
    exact ⟨b', by simp only [evalCounted, hd, hxs, Option.bind_some, ← hab.1,
      if_pos hl, hb'], hp⟩

/-- Projecting an actual instrumented run recovers exactly the source run's memory and
original operation/query counts. Structural counts remain present in the canonical run.
No equality of arbitrary initial or final workspace fields is asserted. -/
theorem evalCounted_original_instrument {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m : Mem K}
    {st : St (Op ⊕ Bookkeeping) Tst K}
    (h : evalCounted I.instrument (instrumentWorkspace W) τ s.instrument ρ (St.init m) =
      some st) :
    ∃ raw, evalCounted I W τ s ρ (St.init m) = some raw ∧
      raw.mem = st.mem ∧ raw.cost = Count.original st.cost := by
  obtain ⟨raw, hr, hm, hc⟩ := projectsOriginal_instrument s ρ _ st (St.init m) h
    ⟨rfl, map_zero _⟩
  exact ⟨raw, hr, hm.symm, hc.symm⟩

/-- Canonical execution exposes the actual source counted run with exactly its original
operation/query counts. Format validation and query-workspace reservation preserve that
memory and projection; structural instruction counts remain in the canonical result. -/
theorem exec_original_count {r b : ℕ} {p : Program Op Tst r b}
    {I : Interp Op Tst K} {R : ResourceModel Op Tst} {formats : Fin b → StorageFormat}
    {τ : Tape K} {d : Fin r → ℕ} {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (h : exec p I R formats τ d m = some st) :
    ∃ raw, evalCounted I R.workspace τ p.body (Program.environment (b := b) d)
      (St.init m) = some raw ∧ raw.mem = st.mem ∧ raw.cost = Count.original st.cost := by
  unfold exec at h
  split_ifs at h
  obtain ⟨counted, hcounted, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨raw, hr, hm, hc⟩ := evalCounted_original_instrument hcounted
  exact ⟨raw, hr, hm, hc⟩

namespace Algorithm

/-- Construct a total certificate using bounds on the actual canonical instruction count.
The total word-level proof supplies execution; the resource premise analyzes that same
execution. Work and span need not bound the weight of a conservative count manifest.
Scratch and resident memory retain their independent static bounds. -/
def ofWpActual {M : AccessModel Op Tst P} {S : Specification Op Tst P}
    (p : Program Op Tst r b) (ht : p.wellTyped M.resources P.formats = true)
    (hwp : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K),
      M.contracts d x I → ∀ τ, Wp .total I τ p.body (Program.environment (b := b) d)
        (fun m' => ∀ c, c ≤ S.budget d → S.good d x τ c m') (P.initial d x))
    (hActual : ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K),
      M.contracts d x I → ∀ τ st,
        exec p I M.resources P.formats τ d (P.initial d x) = some st →
        st.cost ≤ S.budget d ∧ M.resources.work st.cost ≤ S.work d ∧
          M.resources.span st.cost ≤ S.span d)
    (hspace : ∀ d, P.valid d → staticPeak M.resources p d ≤ S.scratch d)
    (hmemory : ∀ d, P.valid d → ∀ x : P.Input d,
      P.initialBytes d x + S.scratch d ≤ S.memory d) : Algorithm M S where
  program := p
  correct d hd x I hI τ := by
    obtain ⟨m', hr, hg⟩ := hwp d hd x I hI τ
    have hm : eval I.instrument τ p.body.instrument (Program.environment (b := b) d)
        (P.initial d x) = some m' := by rw [run_instrument]; exact hr
    obtain ⟨raw, he, -, -, hgood⟩ := ConditionalRuns.of_run
      (Q := fun m' => ∀ c, c ≤ S.budget d → S.good d x τ c m')
      hm hg (instrumentWorkspace M.resources.workspace)
    have hx := exec_of_evalCounted ht (by simp [Problem.initial]) he
    obtain ⟨hc, hw, hs⟩ := hActual d hd x I hI τ _ hx
    have hp := (exec_static hx).2.trans (hspace d hd)
    exact ⟨raw.reserveQueries M.resources, hx, hp, hc, hw, hs,
      (Nat.add_le_add_left hp _).trans (hmemory d hd x), hgood _ hc⟩

end Algorithm

end NLAlib.Ops
