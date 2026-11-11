/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Footprint

/-!
# Block specifications with footprints and named states

`NLAlib.Ops.Writes md I τ c ρ F P m`: the run of `c` from `m`, in the mode `md`, **writes only
the cells of `F`** (the store keeps its shape and every cell off `F`) and ends in a memory
satisfying `P`. It is `Wp` with a frame; every rule here is a rule of `Wp` with the frame
carried, so nothing is added to the trusted base.

The point is the form in which a proof continues after a step (`NLAlib.Ops.Writes.then_`):
the continuation receives a **fresh memory** `m'` with the frame `m.store.EqOff F m'.store` and
the postcondition, and never a chain of updates. That is a named state: what a later step needs
of `m'` is read off the frame (lengths by `Store.EqOff.len_eq`, kept blocks by
`Store.EqOff.keep`) and the postcondition (the blocks just written). Frames of consecutive steps
compose by `⊔` (`Store.EqOff.trans'`), and the footprint of a block is compared with the
declared one once, at the end (`fp_sub`).

Every rule is **mode-generic**: what is needed only for success (live handles, readable inputs,
room, a nonzero divisor) is under `md.Needs`, and a successful liberal run gives it back in the
postcondition. One proof gives the total statement and the refinement.

## Main results

* `NLAlib.Ops.Writes`, `NLAlib.Ops.Writes.then_` (the named step), `NLAlib.Ops.Writes.seq`,
  `NLAlib.Ops.Writes.mono`, `NLAlib.Ops.Writes.keep` (frame-carry of a bundle of facts).
* `NLAlib.Ops.writes_call`: **the call rule with a footprint**, in every mode, for any contract
  in operand form; `NLAlib.Ops.writes_call1`, `NLAlib.Ops.writes_call_cell`,
  `NLAlib.Ops.writes_call2`, `NLAlib.Ops.writes_call_bin`: shapes.
* `NLAlib.Ops.writes_alloc`, `NLAlib.Ops.writes_allocs`: scratch buffers as named states, with
  their handles and lengths; the frame after the pops is the caller's.
* `NLAlib.Ops.writes_ite`, `NLAlib.Ops.writes_bindIdx`, `NLAlib.Ops.writes_bindIdx_of_isIndex`.
* `NLAlib.Ops.Wp.named`: generalise a chain of updates into a fresh memory (checkpoint).
* `NLAlib.Ops.Impl.meets_of_writes`: **a certificate from a block specification**; the
  equation of the contract is built once, here.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **A block specification**: the run of `c` from `m`, in the mode `md`, writes only the cells
of `F` and ends in a memory satisfying `P`. -/
def Writes (md : Mode) (I : Interp Op Tst K) (τ : Tape K) (c : Stmt Op Tst) (ρ : Env) (F : Fp)
    (P : Mem K → Prop) (m : Mem K) : Prop :=
  Wp md I τ c ρ (fun m' => m.store.EqOff F m'.store ∧ P m') m

namespace Writes

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {c c' : Stmt Op Tst}
  {F G : Fp} {P P' : Mem K → Prop} {Q : Mem K → Prop} {m : Mem K}

/-- Consequence into `Wp`. -/
theorem wp (h : Writes md I τ c ρ F P m) (hQ : ∀ m', m.store.EqOff F m'.store → P m' → Q m') :
    Wp md I τ c ρ Q m :=
  Wp.mono h fun m' h' => hQ m' h'.1 h'.2

/-- **The named step**: after `c`, the proof goes on from a fresh memory `m'`, with the frame and
the postcondition of `c` as hypotheses. -/
theorem then_ (h : Writes md I τ c ρ F P m)
    (k : ∀ m', m.store.EqOff F m'.store → P m' → Wp md I τ c' ρ Q m') :
    Wp md I τ (.seq c c') ρ Q m :=
  wp_seq (h.wp k)

/-- Sequence: the footprints are joined. -/
theorem seq (h : Writes md I τ c ρ F P m)
    (h' : ∀ m', m.store.EqOff F m'.store → P m' → Writes md I τ c' ρ G P' m') :
    Writes md I τ (.seq c c') ρ (F ⊔ G) P' m :=
  wp_seq (Wp.mono h fun m' hm => Wp.mono (h' m' hm.1 hm.2) fun _ hm' => ⟨hm.1.trans' hm'.1, hm'.2⟩)

/-- Sequence against a declared footprint: the first part writes inside `F`, and the rest is
proved against `F` itself, so the footprint of the whole is the declared one (no `⊔` to
collapse at the end). -/
theorem seq_le (h : Writes md I τ c ρ G P m) (hG : G ≤ F)
    (h' : ∀ m', m.store.EqOff G m'.store → P m' → Writes md I τ c' ρ F P' m') :
    Writes md I τ (.seq c c') ρ F P' m :=
  wp_seq (Wp.mono h fun m' hm => Wp.mono (h' m' hm.1 hm.2) fun _ hm' =>
    ⟨(hm.1.mono hG).trans hm'.1, hm'.2⟩)

/-- Consequence: a larger footprint, a weaker postcondition (which may use the frame). -/
theorem mono (h : Writes md I τ c ρ F P m) (hF : F ≤ G)
    (hP : ∀ m', m.store.EqOff F m'.store → P m' → P' m') : Writes md I τ c ρ G P' m :=
  Wp.mono h fun m' hm => ⟨hm.1.mono hF, hP m' hm.1 hm.2⟩

/-- Two facts about one run. -/
theorem and (h : Writes md I τ c ρ F P m) (h' : Writes md I τ c ρ G P' m) :
    Writes md I τ c ρ F (fun m' => P m' ∧ P' m') m :=
  (Wp.and h h').mono fun _ hm => ⟨hm.1.1, hm.1.2, hm.2.2⟩

/-- **Frame-carry**: a fact about the store that reads only cells off the footprint is kept. -/
theorem keep (h : Writes md I τ c ρ F P m) {G : Fp} {P₀ : Store K → Prop}
    (hP : Store.ReadsOnly G P₀) (hD : Fp.Disj F G) (hp : P₀ m.store) :
    Writes md I τ c ρ F (fun m' => P m' ∧ P₀ m'.store) m :=
  Wp.mono h fun _ hm => ⟨hm.1, hm.2, hm.1.keep hP hD hp⟩

/-- Nothing is written. -/
theorem skip (h : P m) : Writes md I τ .skip ρ ⊥ P m := wp_skip ⟨Store.EqOff.refl _ _, h⟩

/-- A total specification holds in every mode. -/
theorem of_total (h : Writes .total I τ c ρ F P m) : Writes md I τ c ρ F P m :=
  Mode.Holds.of_total h

end Writes

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-! ### Calls -/

/-- **The call rule with a footprint**, in every mode, for a contract in operand form with any
number of output blocks: the call writes the output blocks and nothing else, the position
advances by the window, and the outputs are read back (they are pairwise disjoint), related to
the inputs read and to the window. Success needs live handles, readable inputs in the domain and
room, under `md.Needs`; a successful liberal call gives the inputs read. -/
theorem writes_call {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)} {k : ℕ}
    {ls : List ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hnd : d.length = R.nd) (hk : R.win d = k)
    (hls : R.outLens d = ls) (hadm : adm d a b) (hap : Fp.Apart b ls)
    (hpre : md.Needs (m.Live (a ++ b) ∧ (∃ xs, m.readBlocks a (R.inLens d) = some xs ∧
      R.dom d xs (τ.window R.stream m.pos k)) ∧ m.Room b ls)) :
    Writes md I τ (.call o ds ins outs) ρ (Fp.blocks b ls)
      (fun m' => m'.pos = m.pos + k ∧ ∃ xs ys, m.readBlocks a (R.inLens d) = some xs ∧
        m'.readBlocks b ls = some ys ∧ R.rel d xs (τ.window R.stream m.pos k) ys) m := by
  have key : ∀ xs ys, m.readBlocks a (R.inLens d) = some xs → m.Room b ls →
      ys.map List.length = ls → R.rel d xs (τ.window R.stream m.pos k) ys →
      m.store.EqOff (Fp.blocks b ls) ((m.updBlocks b ys).advance k).store ∧
        (((m.updBlocks b ys).advance k).pos = m.pos + k ∧ ∃ xs ys',
          m.readBlocks a (R.inLens d) = some xs ∧
          ((m.updBlocks b ys).advance k).readBlocks b ls = some ys' ∧
          R.rel d xs (τ.window R.stream m.pos k) ys') := by
    intro xs ys hr hz hl hrel
    subst hl
    refine ⟨Mem.eqOff_updBlocks (Store.EqOff.refl _ _) le_rfl, by simp, xs, ys, hr, ?_, hrel⟩
    rw [Mem.readBlocks_congr (m' := (m.updBlocks b ys).advance k) (m := m.updBlocks b ys) rfl]
    exact Mem.readBlocks_updBlocks hap hz
  cases md with
  | total =>
    obtain ⟨hl, ⟨xs, hr, hdom⟩, hz⟩ := hpre rfl
    exact wp_call_rel hI hd ha hb hnd hk hls hadm hl hr hdom hz fun ys hys hrel =>
      key xs ys hr hz hys hrel
  | liberal =>
    exact wp_call_rel_liberal hI hd ha hb hnd hk hls hadm fun xs ys _ hr hz hys hrel =>
      key xs ys hr hz hys hrel

/-- The call rule with a footprint for **one output block**: the block is read back. -/
theorem writes_call1 {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k l : ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z]) (hnd : d.length = R.nd) (hk : R.win d = k)
    (hls : R.outLens d = [l]) (hadm : adm d a [z])
    (hpre : md.Needs (m.Live (a ++ [z]) ∧ (∃ xs, m.readBlocks a (R.inLens d) = some xs ∧
      R.dom d xs (τ.window R.stream m.pos k)) ∧ z.2 + l ≤ m.store.len z.1)) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z.1 z.2 l)
      (fun m' => m'.pos = m.pos + k ∧ ∃ xs y, m.readBlocks a (R.inLens d) = some xs ∧
        m'.store.readBlock z.1 z.2 l = some y ∧ R.rel d xs (τ.window R.stream m.pos k) [y]) m := by
  refine (writes_call hI hd ha hb hnd hk hls hadm ⟨fun _ _ _ h => h, trivial⟩
    fun h => ⟨(hpre h).1, (hpre h).2.1, (hpre h).2.2, trivial⟩).mono
    (fun _ _ h => h.elim id False.elim) fun m' _ ⟨hpos, xs, ys, hxs, hys, hrel⟩ => ?_
  obtain ⟨y, ys', hy, hys', rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  obtain rfl : ys' = [] := by simpa [Mem.readBlocks] using hys'.symm
  exact ⟨hpos, xs, y, hxs, hy, hrel⟩

/-- The call rule with a footprint for **one output cell**. -/
theorem writes_call_cell {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k : ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z]) (hnd : d.length = R.nd) (hk : R.win d = k)
    (hls : R.outLens d = [1]) (hadm : adm d a [z])
    (hpre : md.Needs (m.Live (a ++ [z]) ∧ (∃ xs, m.readBlocks a (R.inLens d) = some xs ∧
      R.dom d xs (τ.window R.stream m.pos k)) ∧ z.2 < m.store.len z.1)) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos + k ∧ ∃ xs v, m.readBlocks a (R.inLens d) = some xs ∧
        m'.store.get z.1 z.2 = some v ∧ R.rel d xs (τ.window R.stream m.pos k) [[v]]) m := by
  refine (writes_call1 hI hd ha hb hnd hk hls hadm
    fun h => ⟨(hpre h).1, (hpre h).2.1, by have := (hpre h).2.2; omega⟩).mono le_rfl
    fun m' _ ⟨hpos, xs, y, hxs, hy, hrel⟩ => ?_
  obtain ⟨hl, hg⟩ := Store.readBlock_eq_some_iff.mp hy
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
  exact ⟨hpos, xs, v, hxs, by simpa using hg 0 (by omega), hrel⟩

/-- The call rule with a footprint for **two output blocks**, apart. -/
theorem writes_call2 {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z₁ z₂ : ℕ × ℕ}
    {k l₁ l₂ : ℕ} (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z₁, z₂]) (hnd : d.length = R.nd) (hk : R.win d = k)
    (hls : R.outLens d = [l₁, l₂]) (hadm : adm d a [z₁, z₂])
    (hap : Fp.Disj (Store.inBlock z₁.1 z₁.2 l₁) (Store.inBlock z₂.1 z₂.2 l₂))
    (hpre : md.Needs (m.Live (a ++ [z₁, z₂]) ∧ (∃ xs, m.readBlocks a (R.inLens d) = some xs ∧
      R.dom d xs (τ.window R.stream m.pos k)) ∧ z₁.2 + l₁ ≤ m.store.len z₁.1 ∧
      z₂.2 + l₂ ≤ m.store.len z₂.1)) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z₁.1 z₁.2 l₁ ⊔ Store.inBlock z₂.1 z₂.2 l₂)
      (fun m' => m'.pos = m.pos + k ∧ ∃ xs y₁ y₂, m.readBlocks a (R.inLens d) = some xs ∧
        m'.store.readBlock z₁.1 z₁.2 l₁ = some y₁ ∧ m'.store.readBlock z₂.1 z₂.2 l₂ = some y₂ ∧
        R.rel d xs (τ.window R.stream m.pos k) [y₁, y₂]) m := by
  refine (writes_call hI hd ha hb hnd hk hls hadm ⟨fun b i h₁ h₂ => ?_, ⟨fun _ _ _ h => h, trivial⟩⟩
    fun h => ⟨(hpre h).1, (hpre h).2.1, (hpre h).2.2.1, (hpre h).2.2.2, trivial⟩).mono
    (fun _ _ h => h.elim Or.inl fun h => h.elim Or.inr False.elim)
    fun m' _ ⟨hpos, xs, ys, hxs, hys, hrel⟩ => ?_
  · exact hap b i h₁ (h₂.elim id False.elim)
  obtain ⟨y₁, ys', hy₁, hys', rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  obtain ⟨y₂, ys'', hy₂, hys'', rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys'
  obtain rfl : ys'' = [] := by simpa [Mem.readBlocks] using hys''.symm
  exact ⟨hpos, xs, y₁, y₂, hxs, hy₁, hy₂, hrel⟩

/-- **A functional operation of two cells** (scalar arithmetic): the value is computed, and the
written cell holds it. -/
theorem writes_call_bin {o : Op} {g : K → K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn md o (.bin g) adm)
    {ins outs : List Operand} {x y z : ℕ × ℕ} {u v w : K}
    (ha : Operand.evalList ρ ins = some [x, y]) (hb : Operand.evalList ρ outs = some [z])
    (hadm : adm [] [x, y] [z]) (hx : m.store.get x.1 x.2 = some u)
    (hy : m.store.get y.1 y.2 = some v) (hg : g u v = some w)
    (hpre : md.Needs (m.Live [x, y, z] ∧ z.2 < m.store.len z.1)) :
    Writes md I τ (.call o [] ins outs) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some w) m := by
  have hr : m.readBlocks [x, y] [1, 1] = some [[u], [v]] := by
    simp [Mem.readBlocks, Store.readBlock, hx, hy]
  refine (writes_call_cell (R := (BlockFn.bin g).rel) hI rfl ha hb rfl rfl rfl hadm
    fun h => ⟨(hpre h).1, ⟨[[u], [v]], hr, [[w]], by simp [BlockFn.bin, hg], rfl⟩,
      (hpre h).2⟩).mono le_rfl fun m' _ ⟨hpos, xs, w', hxs, hw', hrel⟩ => ?_
  obtain rfl : xs = [[u], [v]] := Option.some.inj (hxs.symm.trans hr)
  have e : w = w' := by simpa [BlockFn.bin, hg] using hrel
  subst e
  exact ⟨by simpa using hpos, hw'⟩

/-! ### Scratch buffers -/

/-- **A scratch buffer as a named state.** The body is proved from every store `s₁` with one more
buffer, of length `n`, at the handle `L = m.store.length`, that agrees with the store below `L`;
its footprint may include the new buffer. The postcondition is asked of every store of length `L`
that agrees with the final one below `L` (the store after the pop is one), so no `pop` appears
in a goal, and a fact about the buffers below `L` transfers by `Store.Below.keep`. -/
theorem writes_alloc {len : IExp} {body : Stmt Op Tst} {n : ℕ} (hn : len.eval ρ.idx = some n)
    {F : Fp} {P : Mem K → Prop}
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + 1 → s₁.len m.store.length = n →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body (ρ.pushBuf m.store.length) (F ⊔ Store.inBuf m.store.length)
        (fun m' => ∀ s₂ : Store K, s₂.length = m.store.length →
          Store.Below m.store.length m'.store s₂ → P ⟨s₂, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (.alloc len body) ρ F P m := by
  refine wp_alloc hn (Wp.mono (h _ (by simp) (by simp) (Store.below_push _ _))
    fun m' ⟨hfr, hP⟩ => ⟨Store.EqOff.pop hfr, hP _ ?_ (Store.below_pop ?_)⟩)
  · rw [Store.length_pop, hfr.length_eq, Store.length_push]; rfl
  · rw [hfr.length_eq, Store.length_push]

/-- Nested scratch buffers of the lengths `lens`, the last innermost (the builder writes the
nested `.alloc`s, which are this by `rfl`). -/
def Stmt.allocs : List IExp → Stmt Op Tst → Stmt Op Tst
  | [], body => body
  | l :: ls, body => .alloc l (Stmt.allocs ls body)

/-- **An allocation chain**: `k` scratch buffers at the handles `L, L + 1, …, L + k - 1`
(`L = m.store.length`) with their lengths, as one named state; after the body they are all
freed. The rule for the blocks that allocate seven or eight buffers. -/
theorem writes_allocs {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    (hn : IExp.evalList ρ.idx lens = some ns) {F : Fp} {P : Mem K → Prop}
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (F ⊔ Fp.above m.store.length)
        (fun m' => ∀ s₂ : Store K, s₂.length = m.store.length →
          Store.Below m.store.length m'.store s₂ → P ⟨s₂, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ F P m := by
  induction lens generalizing m ρ ns F P with
  | nil =>
    simp only [IExp.evalList_nil, Option.some.injEq] at hn
    subst hn
    have h0 := h m.store (by simp) (fun i hi => absurd hi (by simp)) (Store.Below.refl _ _)
    have e : (⟨ρ.idx, ρ.buf ++ (List.range ([] : List ℕ).length).map (m.store.length + ·)⟩ :
        Env) = ρ := by
      cases ρ; simp
    rw [e] at h0
    exact Wp.mono h0 fun m' ⟨hfr, hP⟩ =>
      ⟨hfr.of_above, hP m'.store hfr.length_eq (Store.Below.refl _ _)⟩
  | cons l ls ih =>
    rw [IExp.evalList_cons] at hn
    obtain ⟨n, hl, hn⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨ns', hns', rfl⟩ := Option.map_eq_some_iff.mp hn
    refine writes_alloc hl fun s₁ hs₁ hs₁L hs₁B => ?_
    refine ih (m := ⟨s₁, m.pos⟩) (ρ := ρ.pushBuf m.store.length) (by simpa using hns')
      fun s₂ hs₂ hlens hB => ?_
    simp only at hs₂ hlens hB ⊢
    have h₂ := h s₂ (by simp [hs₂, hs₁]; omega) (fun i hi => ?_)
      (hs₁B.trans (hB.mono (by omega)))
    · have e : (⟨ρ.idx, ρ.buf ++ (List.range (n :: ns').length).map (m.store.length + ·)⟩ : Env) =
          ⟨(ρ.pushBuf m.store.length).idx,
            (ρ.pushBuf m.store.length).buf ++ (List.range ns'.length).map (s₁.length + ·)⟩ := by
        simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
          Env.idx_pushBuf, Env.buf_pushBuf, hs₁, List.append_assoc, List.singleton_append,
          Nat.add_zero]
        congr 3
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply]
        omega
      rw [e] at h₂
      refine Writes.mono h₂ (fun b i hb => ?_) fun m' _ hP s₃ hs₃ hB₃ s₄ hs₄ hB₄ =>
        hP s₄ hs₄ ((hB₃.mono (by omega)).trans hB₄)
      rcases hb with hb | hb
      · exact Or.inl (Or.inl hb)
      · by_cases hbL : b = m.store.length
        · exact Or.inl (Or.inr hbL)
        · exact Or.inr (show s₁.length ≤ b by simp only [Fp.above] at hb; omega)
    · rcases i with _ | i
      · simpa [(hB m.store.length (by omega)).1] using hs₁L
      · have := hlens i (by simpa using hi)
        simpa [hs₁, Nat.add_assoc, Nat.add_comm 1 i] using this

/-! ### Branches and indices -/

/-- Branch, on the Boolean of the test. -/
theorem writes_ite {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst}
    {d : List ℕ} {a : List (ℕ × ℕ)} {c : Bool} {F : Fp} {P : Mem K → Prop}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hc : I.test q d a m = some c) (h : Writes md I τ (if c then t else e) ρ F P m) :
    Writes md I τ (.ite q ds ins t e) ρ F P m := wp_ite hd ha hc h

/-- Branch, in the form of a liberal proof: the test is evaluated under `md.Holds` (a liberal
proof does not have to show that it succeeds). -/
theorem writes_ite_holds {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst}
    {F : Fp} {P : Mem K → Prop}
    (h : md.Holds (I.testAt q ds ins ρ m) fun c => Writes md I τ (if c then t else e) ρ F P m) :
    Writes md I τ (.ite q ds ins t e) ρ F P m := by
  have e : run I τ (.ite q ds ins t e) ρ m =
      (I.testAt q ds ins ρ m).bind fun c => if c then run I τ t ρ m else run I τ e ρ m := by
    simp only [run, Interp.testAt, Option.bind_assoc]
  unfold Writes Wp
  rw [e]
  exact Mode.holds_bind (h.mono fun c hc => by cases c <;> simpa [Writes, Wp] using hc)

/-- Index binder, on the number returned, within the bound. -/
theorem writes_bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B v : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B)
    (hv : I.index q a m = some v) (hle : v ≤ B) (h : Writes md I τ body (ρ.pushIdx v) F P m) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m := wp_bindIdx ha hB hv hle h

/-- Index binder, in the form of a liberal proof: the number is read under `md.Holds`; the body
is proved at it, and success needs it within the bound. -/
theorem writes_bindIdx_holds {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B)
    (h : md.Holds (I.index q a m) fun v =>
      md.Needs (v ≤ B) ∧ (v ≤ B → Writes md I τ body (ρ.pushIdx v) F P m)) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m := by
  unfold Writes Wp
  simp only [run, ha, hB, Option.bind_some]
  refine Mode.holds_bind (h.mono fun v hv => ?_)
  by_cases hle : v ≤ B
  · rw [if_pos hle]
    exact hv.2 hle
  · rw [if_neg hle]
    cases md with
    | total => exact absurd (hv.1 rfl) hle
    | liberal => exact fun _ h => by cases h

/-- A procedure instance: the body runs in the environment of its dimensions and operands. -/
theorem writes_frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} {F : Fp} {P : Mem K → Prop} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a) (hl : m.Live a)
    (h : Writes md I τ body (Env.frame d a) F P m) :
    Writes md I τ (.frame ds args body) ρ F P m := wp_frame hd ha hl h

/-- **Index binder from the access model**: the number is the conversion `f` of the cells read
(`Interp.IsIndex`); the body is proved at that number. -/
theorem writes_bindIdx_of_isIndex {q : Tst} {f : List K → Option ℕ} (hI : I.IsIndex q f)
    {ins : List Operand} {bound : IExp} {body : Stmt Op Tst} {a : List (ℕ × ℕ)}
    {xs : List (List K)} {B v : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B)
    (hr : m.readBlocks a (a.map fun _ => 1) = some xs) (hf : f xs.flatten = some v)
    (hle : v ≤ B) (h : Writes md I τ body (ρ.pushIdx v) F P m) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m :=
  writes_bindIdx ha hB ((hI a m xs hr).trans hf) hle h

/-! ### Named states for chains -/

/-- **Checkpoint**: generalise the current memory, a chain of updates, into a fresh memory with
the facts `P` proved about the chain. The tactic `checkpoint` proves `P` (frame by `frame`, reads
by `store_simp`) and introduces the name. -/
theorem Wp.named {c : Stmt Op Tst} {Q : Mem K → Prop} (P : Mem K → Prop) (hP : P m)
    (h : ∀ m', P m' → Wp md I τ c ρ Q m') : Wp md I τ c ρ Q m := h m hP

end Rules

/-! ### Certificates from block specifications -/

/-- **A certificate from a block specification.** On admitted, live operands with the inputs
`xs` read and room for the outputs, the body writes only the output blocks, advances the
position by the window, and the output blocks are read back related to the inputs: then the
implementation meets the contract. The output blocks must be pairwise disjoint (the admitted
operands say so); the equation `m' = (m.updBlocks outs ys).advance _` is built here, once
(`Mem.eq_updBlocks_of_eqOff`). -/
theorem Impl.meets_of_writes {R : Impl Op Tst} {I : Interp Op Tst K} {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : ∀ (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) (xs : List (List K)),
      d.length = B.nd → adm d ins outs → m.Live (ins ++ outs) →
      m.readBlocks ins (B.inLens d) = some xs →
      B.dom d xs (τ.window B.stream m.pos (B.win d)) → m.Room outs (B.outLens d) →
      R.Fits d.length ins.length outs.length ∧
        Writes .total I τ R.body (Env.frame d (ins ++ outs)) (Fp.blocks outs (B.outLens d))
          (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys, m'.readBlocks outs (B.outLens d) = some ys ∧
            B.rel d xs (τ.window B.stream m.pos (B.win d)) ys) m) :
    R.Meets I .total (B.spec adm) := by
  refine Impl.meets_rel fun d ins outs τ m xs hnd hadm hl hr hdom hz => ?_
  obtain ⟨hfit, hw⟩ := h d ins outs τ m xs hnd hadm hl hr hdom hz
  refine ⟨hfit, Wp.mono hw fun m' ⟨hfr, hpos, ys, hys, hrel⟩ =>
    ⟨ys, Mem.map_length_of_readBlocks hys, hrel, ?_⟩⟩
  rw [← Mem.updBlocks_advance]
  exact Mem.eq_updBlocks_of_eqOff (m := m.advance (B.win d)) hfr hys hpos

/-- A certified implementation writes only the output blocks of its contract. Its body can be
used by a larger proof with the same contract postcondition and a frame on all other cells. -/
theorem Impl.Meets.writes {R : Impl Op Tst} {I : Interp Op Tst K} {md : Mode} {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : R.Meets I md (B.spec adm)) {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {τ : Tape K} {m : Mem K} (hpre : ((B.spec adm).on md d ins outs τ m).pre m)
    (hlive : m.Live (ins ++ outs)) :
    Writes md I τ R.body (Env.frame d (ins ++ outs)) (Fp.blocks outs (B.outLens d))
      (((B.spec adm).on md d ins outs τ m).post m) m := by
  refine Wp.mono ((h d ins outs τ m hpre).2 hlive).2 fun m' hpost => ?_
  obtain ⟨xs, hr, hroom, ys, hlen, hrel, rfl⟩ := hpost
  exact ⟨Mem.eqOff_updBlocks (Store.EqOff.refl _ _) (by rw [hlen]), xs, hr, hroom,
    ys, hlen, hrel, rfl⟩

end NLAlib.Ops
