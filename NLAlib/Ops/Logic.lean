/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public import NLAlib.Ops.Contract
public import NLAlib.Ops.Static

/-!
# A minimal program logic

Weakest preconditions by definition, since the run is deterministic:
`NLAlib.Ops.wp md I τ s ρ Q m` says that the run of `s` from `m` satisfies `Q`, in the mode `md`.
One rule per constructor; a call is replaced by its contract (`NLAlib.Ops.wp_call`) or, for a
functional operation, by an equation (`NLAlib.Ops.wp_call_fn`); a loop needs an invariant
(`NLAlib.Ops.wp_loop`). Every rule is mode-generic.

Frame: contracts state the memory after a call as an update of the memory before
(`NLAlib.Ops.Mem.upd`, `NLAlib.Ops.Mem.updBlock`), so what a call keeps is read off by the store
lemmas (`NLAlib.Ops.Store.get_upd_of_ne`, `NLAlib.Ops.Store.get_updBlock_of_buf_ne`,
`NLAlib.Ops.Store.get_append_of_lt` for scratch on top), and facts about one run are combined by
`NLAlib.Ops.wp.and`.

Grounding: `NLAlib.Ops.Interp.link_meets` and `NLAlib.Ops.Interp.link_isFn` reduce "the induced
interpretation meets the contract of `o`" to a `wp` statement, or a run equation, about the
implementation of `o`.

This is the part of the logic the examples need; the full logic sits on the same definitions.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ K : Type}

/-- **The weakest precondition**: the run of `s` from `m` satisfies `Q`, in the mode `md`. -/
def wp (md : Mode) (I : Interp Op K) (τ : ℕ → K) (s : Stmt Op) (ρ : Env) (Q : Mem K → Prop)
    (m : Mem K) : Prop :=
  md.holds (run I τ s ρ m) Q

section Rules

variable {md : Mode} {I : Interp Op K} {τ : ℕ → K} {ρ : Env} {Q Q' : Mem K → Prop} {m : Mem K}

theorem wp_total_iff {s : Stmt Op} :
    wp .total I τ s ρ Q m ↔ ∃ m', run I τ s ρ m = some m' ∧ Q m' := Iff.rfl

theorem wp_liberal_iff {s : Stmt Op} :
    wp .liberal I τ s ρ Q m ↔ RunsL I τ s ρ m Q := Iff.rfl

/-- A run equation is a total `wp`, in every mode. -/
theorem wp_of_run {s : Stmt Op} {m' : Mem K} (h : run I τ s ρ m = some m') (hQ : Q m') :
    wp md I τ s ρ Q m :=
  Mode.holds.of_total ⟨m', h, hQ⟩

theorem run_of_wp {s : Stmt Op} {m' : Mem K} (h : wp .total I τ s ρ (· = m') m) :
    run I τ s ρ m = some m' := by
  obtain ⟨m₁, h₁, rfl⟩ := h
  exact h₁

/-- Consequence. -/
theorem wp.mono {s : Stmt Op} (h : wp md I τ s ρ Q m) (hQ : ∀ m', Q m' → Q' m') :
    wp md I τ s ρ Q' m :=
  Mode.holds.mono h hQ

/-- Two facts about one run. -/
theorem wp.and {s : Stmt Op} (h : wp md I τ s ρ Q m) (h' : wp md I τ s ρ Q' m) :
    wp md I τ s ρ (fun m' => Q m' ∧ Q' m') m := by
  cases md
  · obtain ⟨a, ha, hq⟩ := h
    obtain ⟨a', ha', hq'⟩ := h'
    rw [ha] at ha'
    cases ha'
    exact ⟨a, ha, hq, hq'⟩
  · exact fun a ha => ⟨h a ha, h' a ha⟩

theorem wp_skip (h : Q m) : wp md I τ .skip ρ Q m := Mode.holds_some h

/-- Sequence. -/
theorem wp_seq {s t : Stmt Op} (h : wp md I τ s ρ (wp md I τ t ρ Q) m) :
    wp md I τ (.seq s t) ρ Q m :=
  Mode.holds_bind h

/-- **Call by contract.** -/
theorem wp_call {o : Op} {C : Contract K} (hI : I.Meets md o C) {ds : List IExp}
    {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hpre : (C md d a b τ).pre m)
    (hQ : ∀ m', (C md d a b τ).post m m' → Q m') : wp md I τ (.call o ds ins outs) ρ Q m := by
  simp only [wp, run, hd, ha, hb, Option.bind_some]
  exact (hI d a b τ m hpre).mono hQ

/-- **Call of a functional operation**: an equation. -/
theorem wp_call_fn {o : Op} {f : BlockFn K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.IsFn .total o f adm) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {a : List (ℕ × ℕ)} {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hadm : adm d a z) {m' : Mem K} (hf : f.apply d a z τ m = some m') (hQ : Q m') :
    wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_of_run (by simp only [run, hd, ha, hb, Option.bind_some, hI.callS_eq hadm hf]) hQ

/-- Call of a functional constant, on cells. -/
theorem wp_call_const {o : Op} {v : K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.IsFn .total o (.const v) adm) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some [])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm d [] z) (hz : z.2 < m.store.len z.1)
    (hQ : Q (m.upd z v)) : wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_const_eq_some_iff.mpr ⟨hz, rfl⟩) hQ

/-- Call of a functional operation of one cell, on cells. -/
theorem wp_call_un {o : Op} {g : K → Option K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.IsFn .total o (.un g) adm) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {x z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some [x]) (hb : Operand.evalList ρ outs = some [z])
    (hadm : adm d [x] z) {a v : K} (hx : m.store.get x.1 x.2 = some a) (hg : g a = some v)
    (hz : z.2 < m.store.len z.1) (hQ : Q (m.upd z v)) : wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_un_eq_some_iff.mpr ⟨a, v, hx, hg, hz, rfl⟩) hQ

/-- Call of a functional operation of two cells, on cells. -/
theorem wp_call_bin {o : Op} {g : K → K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (hI : I.IsFn .total o (.bin g) adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {x y z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some [x, y])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm d [x, y] z) {a b v : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hg : g a b = some v) (hz : z.2 < m.store.len z.1) (hQ : Q (m.upd z v)) :
    wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_bin_eq_some_iff.mpr ⟨a, b, v, hx, hy, hg, hz, rfl⟩)
    hQ

/-- Call of a functional operation of three cells, on cells. -/
theorem wp_call_tern {o : Op} {g : K → K → K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (hI : I.IsFn .total o (.tern g) adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {x y w z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some [x, y, w])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm d [x, y, w] z) {a b c v : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hw : m.store.get w.1 w.2 = some c) (hg : g a b c = some v) (hz : z.2 < m.store.len z.1)
    (hQ : Q (m.upd z v)) : wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm
    (BlockFn.apply_tern_eq_some_iff.mpr ⟨a, b, c, v, hx, hy, hw, hg, hz, rfl⟩) hQ

/-- A draw, on cells. -/
theorem wp_call_draw {o : Op} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.IsFn .total o .draw adm) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some [])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm d [] z) (hz : z.2 < m.store.len z.1)
    (hQ : Q ((m.upd z (τ m.pos)).advance 1)) : wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_draw_eq_some_iff.mpr ⟨hz, rfl⟩) hQ

theorem holds_iter {σ : Type} {f : ℕ → σ → Option σ} {k : ℕ} (Inv : ℕ → σ → Prop)
    (hstep : ∀ i < k, ∀ s, Inv i s → md.holds (f i s) (Inv (i + 1))) {s : σ} (h0 : Inv 0 s) :
    md.holds (iter f k s) (Inv k) := by
  induction k with
  | zero => exact Mode.holds_some h0
  | succ k ih =>
    exact Mode.holds_bind ((ih fun i hi => hstep i (by omega)).mono fun a ha =>
      hstep k (by omega) a ha)

/-- **Loop**, with an invariant indexed by the number of iterations done. -/
theorem wp_loop {n : IExp} {body : Stmt Op} {k : ℕ} (hn : n.eval ρ.idx = some k)
    (Inv : ℕ → Mem K → Prop) (h0 : Inv 0 m)
    (hstep : ∀ i < k, ∀ m, Inv i m → wp md I τ body (ρ.pushIdx i) (Inv (i + 1)) m)
    (hQ : ∀ m, Inv k m → Q m) : wp md I τ (.loop n body) ρ Q m := by
  simp only [wp, run, hn, Option.bind_some]
  exact (holds_iter Inv hstep h0).mono hQ

/-- Scratch buffer: the body runs with the new buffer on top, which is then popped. -/
theorem wp_alloc {len : IExp} {body : Stmt Op} {n : ℕ} (hn : len.eval ρ.idx = some n)
    (h : wp md I τ body (ρ.pushBuf m.store.length) (fun m' => Q ⟨m'.store.pop, m'.pos⟩)
      ⟨m.store.push n, m.pos⟩) : wp md I τ (.alloc len body) ρ Q m := by
  simp only [wp, run, hn, Option.bind_some]
  exact Mode.holds_map h

/-- Procedure instance. -/
theorem wp_frame {ds : List IExp} {args : List Operand} {body : Stmt Op} {d : List ℕ}
    {a : List (ℕ × ℕ)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a) (h : wp md I τ body (Env.frame d a) Q m) :
    wp md I τ (.frame ds args body) ρ Q m := by
  simpa only [wp, run, hd, ha, Option.bind_some] using h

/-- Branch, on the Boolean of the test. -/
theorem wp_ite {o : Op} {ds : List IExp} {ins : List Operand} {t e : Stmt Op} {d : List ℕ}
    {a : List (ℕ × ℕ)} {c : Bool} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hc : I.test o d a m = some c)
    (h : wp md I τ (if c then t else e) ρ Q m) : wp md I τ (.ite o ds ins t e) ρ Q m := by
  simp only [wp, run, hd, ha, hc, Option.bind_some]
  cases c <;> simpa [wp] using h

/-- Index binder, on the number returned, which must be within the bound. -/
theorem wp_bindIdx {o : Op} {ins : List Operand} {bound : IExp} {body : Stmt Op}
    {a : List (ℕ × ℕ)} {B v : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B) (hv : I.index o a m = some v) (hle : v ≤ B)
    (h : wp md I τ body (ρ.pushIdx v) Q m) : wp md I τ (.bindIdx o ins bound body) ρ Q m := by
  simpa only [wp, run, ha, hB, hv, Option.bind_some, if_pos hle] using h

end Rules

/-! ### Grounding: the induced interpretation meets a contract -/

/-- **Grounding a relational contract**: the induced interpretation meets the contract of an
implemented operation when the implementation satisfies it as a program. -/
theorem Interp.link_meets {I : Interp Op₂ K} {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) {md : Mode} {C : Contract K}
    (h : ∀ d ins outs τ m, (C md d ins outs τ).pre m →
      R.Fits d.length ins.length outs.length ∧
        wp md I τ R.body (Env.frame d (ins ++ outs)) ((C md d ins outs τ).post m) m) :
    (I.link T).Meets md o C := by
  intro d ins outs τ m hpre
  obtain ⟨hfit, hw⟩ := h d ins outs τ m hpre
  rw [Interp.link_callS_inl I hT, if_pos hfit]
  exact hw

/-- A kept operation meets the contracts it meets below. -/
theorem Interp.link_meets_kept {I : Interp Op₂ K} {T : Table Op₁ Op₂} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') {md : Mode} {C : Contract K} (h : I.Meets md o' C) :
    (I.link T).Meets md o C := by
  intro d ins outs τ m hpre
  rw [Interp.link_callS_inr I hT]
  exact h d ins outs τ m hpre

/-- **Grounding a functional contract** (the exact certificate): on admitted operands, where the
block function succeeds, the run of the implementation is the block function. -/
theorem Interp.link_isFn {I : Interp Op₂ K} {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) {f : BlockFn K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (h : ∀ d ins z τ m m', adm d ins z → f.apply d ins z τ m = some m' →
      R.Fits d.length ins.length 1 ∧ run I τ R.body (Env.frame d (ins ++ [z])) m = some m') :
    (I.link T).IsFn .total o f adm := by
  refine Interp.link_meets hT ?_
  rintro d ins outs τ m ⟨z, rfl, hadm, hn⟩
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp (hn rfl)
  obtain ⟨hfit, hr⟩ := h d ins z τ m m' hadm hm'
  exact ⟨hfit, m', hr, z, rfl, hm'⟩

end NLAlib.Ops
