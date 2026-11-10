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

**Phase A**: statements only (`sorry`).

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
    Writes md I τ (.seq c c') ρ (F ⊔ G) P' m := by sorry

/-- Consequence: a larger footprint, a weaker postcondition (which may use the frame). -/
theorem mono (h : Writes md I τ c ρ F P m) (hF : F ≤ G)
    (hP : ∀ m', m.store.EqOff F m'.store → P m' → P' m') : Writes md I τ c ρ G P' m := by sorry

/-- Two facts about one run. -/
theorem and (h : Writes md I τ c ρ F P m) (h' : Writes md I τ c ρ G P' m) :
    Writes md I τ c ρ F (fun m' => P m' ∧ P' m') m := by sorry

/-- **Frame-carry**: a fact about the store that reads only cells off the footprint is kept. -/
theorem keep (h : Writes md I τ c ρ F P m) {G : Fp} {P₀ : Store K → Prop}
    (hP : Store.ReadsOnly G P₀) (hD : Fp.Disj F G) (hp : P₀ m.store) :
    Writes md I τ c ρ F (fun m' => P m' ∧ P₀ m'.store) m := by sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-! ### Scratch buffers -/

/-- **A scratch buffer as a named state.** The body is proved from every store `s₁` with one more
buffer, of length `n`, at the handle `m.store.length`, that agrees with the store below it; its
footprint may include the new buffer, which is gone after the pop. -/
theorem writes_alloc {len : IExp} {body : Stmt Op Tst} {n : ℕ} (hn : len.eval ρ.idx = some n)
    {F : Fp} {P : Mem K → Prop}
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + 1 → s₁.len m.store.length = n →
      (∀ b, b < m.store.length → s₁.len b = m.store.len b) →
      (∀ b off k, b < m.store.length → s₁.readBlock b off k = m.store.readBlock b off k) →
      Writes md I τ body (ρ.pushBuf m.store.length) (F ⊔ Store.inBuf m.store.length)
        (fun m' => P ⟨m'.store.pop, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (.alloc len body) ρ F P m := by sorry

/-- Nested scratch buffers of the lengths `lens`, the last innermost. -/
def Stmt.allocs : List IExp → Stmt Op Tst → Stmt Op Tst
  | [], body => body
  | l :: ls, body => .alloc l (Stmt.allocs ls body)

/-- The buffers from the handle `L` on. -/
def Fp.above (L : ℕ) : Fp := fun b _ => L ≤ b

/-- **An allocation chain**: `k` scratch buffers at the handles `L, L + 1, …, L + k - 1`
(`L = m.store.length`) with their lengths, as one named state; after the body they are all
freed. This is the rule for the blocks that allocate seven or eight buffers. -/
theorem writes_allocs {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    (hn : IExp.evalList ρ.idx lens = some ns) {F : Fp} {P : Mem K → Prop}
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      (∀ b, b < m.store.length → s₁.len b = m.store.len b) →
      (∀ b off k, b < m.store.length → s₁.readBlock b off k = m.store.readBlock b off k) →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (F ⊔ Fp.above m.store.length)
        (fun m' => P ⟨m'.store.take m.store.length, m'.pos⟩) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ F P m := by sorry

/-! ### Branches and indices -/

/-- Branch, on the Boolean of the test. -/
theorem writes_ite {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst}
    {d : List ℕ} {a : List (ℕ × ℕ)} {c : Bool} {F : Fp} {P : Mem K → Prop}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hc : I.test q d a m = some c) (h : Writes md I τ (if c then t else e) ρ F P m) :
    Writes md I τ (.ite q ds ins t e) ρ F P m := by sorry

/-- Index binder, on the number returned, within the bound. -/
theorem writes_bindIdx {q : Tst} {ins : List Operand} {bound : IExp} {body : Stmt Op Tst}
    {a : List (ℕ × ℕ)} {B v : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B)
    (hv : I.index q a m = some v) (hle : v ≤ B) (h : Writes md I τ body (ρ.pushIdx v) F P m) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m := by sorry

/-- **Index binder from the access model**: the number is the conversion `f` of the cells read
(`Interp.IsIndex`); the body is proved at that number. -/
theorem writes_bindIdx_of_isIndex {q : Tst} {f : List K → Option ℕ} (hI : I.IsIndex q f)
    {ins : List Operand} {bound : IExp} {body : Stmt Op Tst} {a : List (ℕ × ℕ)}
    {xs : List (List K)} {B v : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B)
    (hr : m.readBlocks a (a.map fun _ => 1) = some xs) (hf : f xs.flatten = some v)
    (hle : v ≤ B) (h : Writes md I τ body (ρ.pushIdx v) F P m) :
    Writes md I τ (.bindIdx q ins bound body) ρ F P m := by sorry

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
      R.Fits d.length ins.length outs.length ∧ Fp.Apart outs (B.outLens d) ∧
        Writes .total I τ R.body (Env.frame d (ins ++ outs)) (Fp.blocks outs (B.outLens d))
          (fun m' => m'.pos = m.pos + B.win d ∧ ∃ ys, m'.readBlocks outs (B.outLens d) = some ys ∧
            B.rel d xs (τ.window B.stream m.pos (B.win d)) ys) m) :
    R.Meets I .total (B.spec adm) := by sorry

end NLAlib.Ops
