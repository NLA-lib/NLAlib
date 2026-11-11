/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public import NLAlib.Ops.Blocks
public import NLAlib.Ops.Static

/-!
# A minimal program logic

Weakest preconditions by definition, since the run is deterministic:
`NLAlib.Ops.Wp md I τ s ρ Q m` says that the run of `s` from `m` satisfies `Q`, in the mode `md`.
One rule per constructor, each mode-generic; a call is replaced by its contract
(`NLAlib.Ops.wp_call`, and `NLAlib.Ops.wp_call_rel` in `NLAlib.Ops.Rules` for the contracts in
operand form); a loop needs an invariant (`NLAlib.Ops.wp_loop`, `NLAlib.Ops.wp_whileFuel`).

Frame: contracts state the memory after a call as an update of the memory before
(`NLAlib.Ops.Mem.upd`, `NLAlib.Ops.Mem.updBlock`), so what a call keeps is read off by the store
lemmas (`NLAlib.Ops.Store.get_upd_of_ne`, `NLAlib.Ops.Store.get_updBlock_of_buf_ne`,
`NLAlib.Ops.Store.get_append_of_lt` for scratch on top), and facts about one run are combined by
`NLAlib.Ops.Wp.and`.

This is the part of the logic the examples need; the full logic sits on the same definitions.

## Main results

* `NLAlib.Ops.wp_seq`, `NLAlib.Ops.wp_call`, `NLAlib.Ops.wp_loop`, `NLAlib.Ops.wp_alloc`,
  `NLAlib.Ops.wp_ite`, `NLAlib.Ops.wp_bindIdx`, `NLAlib.Ops.wp_frame`: the rules.
* `NLAlib.Ops.wp_whileFuel`: the loop with early exit, with an invariant indexed by the rounds
  done; the continuation is proved at the round of the exit and at the cap.
* `NLAlib.Ops.wp_ifZero`, `NLAlib.Ops.wp_ifPos`: branches on a size.
* `NLAlib.Ops.wp_abort_liberal`: in liberal mode a failing run satisfies everything.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

/-- **The weakest precondition**: the run of `s` from `m` satisfies `Q`, in the mode `md`. -/
def Wp (md : Mode) (I : Interp Op Tst K) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (Q : Mem K → Prop)
    (m : Mem K) : Prop :=
  md.Holds (eval I τ s ρ m) Q

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {Q Q' : Mem K → Prop} {m : Mem K}

theorem wp_total_iff {s : Stmt Op Tst} :
    Wp .total I τ s ρ Q m ↔ ∃ m', eval I τ s ρ m = some m' ∧ Q m' := Iff.rfl

theorem wp_liberal_iff {s : Stmt Op Tst} :
    Wp .liberal I τ s ρ Q m ↔ ConditionalRunsL I τ s ρ m Q := Iff.rfl

/-- A run equation is a total `Wp`, in every mode. -/
theorem wp_of_run {s : Stmt Op Tst} {m' : Mem K} (h : eval I τ s ρ m = some m') (hQ : Q m') :
    Wp md I τ s ρ Q m :=
  Mode.Holds.of_total ⟨m', h, hQ⟩

theorem run_of_wp {s : Stmt Op Tst} {m' : Mem K} (h : Wp .total I τ s ρ (· = m') m) :
    eval I τ s ρ m = some m' := by
  obtain ⟨m₁, h₁, rfl⟩ := h
  exact h₁

/-- Consequence. -/
theorem Wp.mono {s : Stmt Op Tst} (h : Wp md I τ s ρ Q m) (hQ : ∀ m', Q m' → Q' m') :
    Wp md I τ s ρ Q' m :=
  Mode.Holds.mono h hQ

/-- Two facts about one run. -/
theorem Wp.and {s : Stmt Op Tst} (h : Wp md I τ s ρ Q m) (h' : Wp md I τ s ρ Q' m) :
    Wp md I τ s ρ (fun m' => Q m' ∧ Q' m') m := by
  cases md
  · obtain ⟨a, ha, hq⟩ := h
    obtain ⟨a', ha', hq'⟩ := h'
    rw [ha] at ha'
    cases ha'
    exact ⟨a, ha, hq, hq'⟩
  · exact fun a ha => ⟨h a ha, h' a ha⟩

theorem wp_skip (h : Q m) : Wp md I τ .skip ρ Q m := Mode.holds_some h

/-- **In liberal mode a failing run satisfies every postcondition.** A liberal statement says
nothing of success: it is never a result by itself (`NLAlib.Ops.ConditionalRunsL`). -/
theorem wp_abort_liberal : Wp .liberal I τ .abort ρ Q m := fun _ h => by cases h

/-- Sequence. -/
theorem wp_seq {s t : Stmt Op Tst} (h : Wp md I τ s ρ (Wp md I τ t ρ Q) m) :
    Wp md I τ (.seq s t) ρ Q m :=
  Mode.holds_bind h

/-- **Call by contract.** The contract is given the window of the tape at the position. -/
theorem wp_call {o : Op} {C : Contract K} (hI : I.Meets md o C) {ds : List IExp}
    {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hpre : (C.on md d a b τ m).pre m)
    (hQ : ∀ m', (C.on md d a b τ m).post m m' → Q m') : Wp md I τ (.call o ds ins outs) ρ Q m := by
  simp only [Wp, eval, hd, ha, hb, Option.bind_some]
  exact (hI d a b τ m hpre).mono hQ

theorem holds_iter {σ : Type} {f : ℕ → σ → Option σ} {k : ℕ} (Inv : ℕ → σ → Prop)
    (hstep : ∀ i < k, ∀ s, Inv i s → md.Holds (f i s) (Inv (i + 1))) {s : σ} (h0 : Inv 0 s) :
    md.Holds (iter f k s) (Inv k) := by
  induction k with
  | zero => exact Mode.holds_some h0
  | succ k ih =>
    exact Mode.holds_bind ((ih fun i hi => hstep i (by omega)).mono fun a ha =>
      hstep k (by omega) a ha)

/-- **Loop**, with an invariant indexed by the number of iterations done. -/
theorem wp_loop {n : IExp} {body : Stmt Op Tst} {k : ℕ} (hn : n.eval ρ.idx = some k)
    (Inv : ℕ → Mem K → Prop) (h0 : Inv 0 m)
    (hstep : ∀ i < k, ∀ m, Inv i m → Wp md I τ body (ρ.pushIdx i) (Inv (i + 1)) m)
    (hQ : ∀ m, Inv k m → Q m) : Wp md I τ (.loop n body) ρ Q m := by
  simp only [Wp, eval, hn, Option.bind_some]
  exact (holds_iter Inv hstep h0).mono hQ

/-- Scratch buffer: the body runs with the new buffer on top, which is then popped. -/
theorem wp_alloc {format : StorageFormat} {len : IExp} {body : Stmt Op Tst} {n : ℕ} (hn : len.eval
  ρ.idx = some n)
    (h : Wp md I τ body (ρ.pushBuf m.store.length) (fun m' => Q ⟨m'.store.pop, m'.pos⟩)
      ⟨m.store.push n, m.pos⟩) : Wp md I τ (.allocAs format len body) ρ Q m := by
  simp only [Wp, eval, hn, Option.bind_some]
  exact Mode.holds_map h

/-- Procedure instance. -/
theorem wp_frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a) (hl : m.Live a)
    (h : Wp md I τ body (Env.frame d a) Q m) : Wp md I τ (.frame ds args body) ρ Q m := by
  simpa only [Wp, eval, hd, ha, Option.bind_some, if_pos hl] using h

/-- Branch, on the Boolean of the test. -/
theorem wp_ite {o : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} {c : Bool} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hc : I.test o d a m = some c)
    (h : Wp md I τ (if c then t else e) ρ Q m) : Wp md I τ (.ite o ds ins t e) ρ Q m := by
  simp only [Wp, eval, hd, ha, hc, Option.bind_some]
  cases c <;> simpa [Wp] using h

/-- Index binder, on the number returned, which must be within the bound. -/
theorem wp_bindIdx {o : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B v : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B) (hv : I.index o a m = some v) (hle : v ≤ B)
    (h : Wp md I τ body (ρ.pushIdx v) Q m) : Wp md I τ (.bindIdx o ins bound body) ρ Q m := by
  simpa only [Wp, eval, ha, hB, hv, Option.bind_some, if_pos hle] using h


theorem holds_whileIter {test : ℕ → Mem K → Option Bool} {body : ℕ → Mem K → Option (Mem K)}
    (Inv : ℕ → Mem K → Prop) {P : ℕ × Mem K → Prop} {n : ℕ}
    (hstep : ∀ i < n, ∀ m, Inv i m → md.Holds (test i m) fun c =>
      if c then md.Holds (body i m) (Inv (i + 1)) else P (i, m))
    (hcap : ∀ m, Inv n m → P (n, m)) :
    ∀ (r i : ℕ) (m : Mem K), i + r = n → Inv i m →
      md.Holds (whileIter (fun i m => (test i m).map fun b => (b, m)) body r i m) P := by
  intro r
  induction r with
  | zero =>
    intro i m hi hinv
    obtain rfl : i = n := by omega
    exact Mode.holds_some (hcap m hinv)
  | succ r ih =>
    intro i m hi hinv
    refine Mode.holds_bind (Mode.holds_map ((hstep i (by omega) m hinv).mono fun c hc => ?_))
    cases c with
    | false => exact Mode.holds_some (by simpa using hc)
    | true =>
      simp only [if_true] at hc ⊢
      exact Mode.holds_bind (hc.mono fun m₁ h₁ => ih (i + 1) m₁ (by omega) h₁)

/-- **The loop with early exit.** `Inv i` is an invariant of the memory after `i` rounds. At a
round below the cap the test is evaluated: if it holds the body keeps the invariant, otherwise
the continuation runs with the round index. At the cap the continuation runs without a test. -/
theorem wp_whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} {n : ℕ} (hn : fuel.eval ρ.idx = some n) (Inv : ℕ → Mem K → Prop)
    (h0 : Inv 0 m)
    (hstep : ∀ i < n, ∀ m, Inv i m → md.Holds (I.testAt q ds ins (ρ.pushIdx i) m) fun c =>
      if c then Wp md I τ body (ρ.pushIdx i) (Inv (i + 1)) m
      else Wp md I τ k (ρ.pushIdx i) Q m)
    (hcap : ∀ m, Inv n m → Wp md I τ k (ρ.pushIdx n) Q m) :
    Wp md I τ (.whileFuel fuel q ds ins body k) ρ Q m := by
  simp only [Wp, eval, hn, Option.bind_some]
  exact Mode.holds_bind (holds_whileIter (P := fun jm => Wp md I τ k (ρ.pushIdx jm.1) Q jm.2) Inv
    hstep hcap n 0 m (by omega) h0)

/-- A test whose Boolean is known. -/
theorem holds_testAt {q : Tst} {ds : List IExp} {ins : List Operand} {d : List ℕ}
    {a : List (ℕ × ℕ)} {c : Bool} {P : Bool → Prop} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hc : I.test q d a m = some c) (h : P c) :
    md.Holds (I.testAt q ds ins ρ m) P := by
  rw [Interp.testAt_eq hd ha, hc]
  exact Mode.holds_some h

/-! ### Branches on a size -/

/-- A branch on a size being zero. -/
theorem wp_ifZero {e : IExp} {body : Stmt Op Tst} {n : ℕ} (he : e.eval ρ.idx = some n)
    (h : if n = 0 then Wp md I τ body (ρ.pushIdx 0) Q m else Q m) :
    Wp md I τ (.ifZero e body) ρ Q m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl] at h
    simpa [Wp, Stmt.ifZero, eval, he, iter] using h
  · rw [if_neg (by omega)] at h
    have h1 : 1 - n = 0 := by omega
    simpa [Wp, Stmt.ifZero, eval, he, h1, iter] using Mode.holds_some (md := md) h

/-- A branch on a size being positive. -/
theorem wp_ifPos {e : IExp} {body : Stmt Op Tst} {n : ℕ} (he : e.eval ρ.idx = some n)
    (h : if 0 < n then Wp md I τ body (ρ.pushIdx 0) Q m else Q m) :
    Wp md I τ (.ifPos e body) ρ Q m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_neg (lt_irrefl 0)] at h
    simpa [Wp, Stmt.ifPos, eval, he, iter] using Mode.holds_some (md := md) h
  · rw [if_pos hn] at h
    have h1 : 1 - (1 - n) = 1 := by omega
    simpa [Wp, Stmt.ifPos, eval, he, h1, iter] using h

end Rules

end NLAlib.Ops
