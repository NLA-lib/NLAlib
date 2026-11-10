/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Frame
public import NLAlib.Ops.StoreSimp
public import NLAlib.Ops.Rules
public import NLAlib.Ops.Tape

/-!
# Operations with a tape window: draws and hidden randomness

A `NLAlib.Ops.WinRel` is a relational contract in operand form for an operation that reads a
window of the tape: the output block is related to the input blocks **and to the entries of the
window**, and the position advances by the length of the window. The operation takes no random
operand. Two uses:

* **visible randomness**: `NLAlib.Ops.drawRel s`, a vector draw; the output block *is* the
  window, so the values are in the store of the algorithm that called it;
* **hidden randomness**: the output is some function of the inputs and of the window (a noisy
  product, a stochastically rounded sum). The algorithm holds no cell with the window entries
  and no operation hands them out, so it cannot compute with them.

The statement about the law is separate and is mathematics: with the law of the tape
(`NLAlib.Ops.IsTapeLaw`), the window of a call at the position `p` is independent of the past of
`p`, with the product law (`NLAlib.Ops.IsTapeLaw.integral_window`). So a contract of this form
is a contract **conditional on the history**: for inputs that are any function of the past, the
output has the law that the relation gives it from a fresh window.

## Main results

* `NLAlib.Ops.wp_call_win`: the call rule.
* `NLAlib.Ops.Interp.link_meets_win`: grounding, from an implementation that draws into its own
  scratch (`NLAlib.Ops.Impl.MeetsWin`).
* `NLAlib.Ops.Interp.IsFn.meets_drawRel`: the vector draw of the model meets `drawRel`.
* `NLAlib.Ops.wp_loop_fill`: the loop that fills a block cell by cell.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

/-- **A block relation with a tape window.** At `nd` dimensions `d`, the call reads input blocks
of the lengths `inLens d` and the window of `win d` entries of the stream `stream` at the
position, writes one output block `ys` of the length `outLen d` with `rel d xs w ys`, and
advances the position by `win d`. -/
structure WinRel (K : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The stream of the tape that is read. -/
  stream : ℕ
  /-- The length of the window. -/
  win : List ℕ → ℕ
  /-- The lengths of the input blocks. -/
  inLens : List ℕ → List ℕ
  /-- The length of the output block. -/
  outLen : List ℕ → ℕ
  /-- The relation between the input blocks, the window and the output block. -/
  rel : List ℕ → List (List K) → List K → List K → Prop

/-- **The contract of a block relation with a window** on the admitted operands `adm`. It reads
the operand blocks and the window at the position, and nothing else. -/
def WinRel.spec (R : WinRel K) (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Contract K :=
  fun md d ins outs τ =>
    { pre := fun m => ∃ z, outs = [z] ∧ d.length = R.nd ∧ adm d ins z ∧
        md.Needs (m.Live (ins ++ [z]) ∧ (m.readBlocks ins (R.inLens d)).isSome ∧
          z.2 + R.outLen d ≤ m.store.len z.1)
      post := fun m m' => ∃ z xs ys, outs = [z] ∧ m.readBlocks ins (R.inLens d) = some xs ∧
        ys.length = R.outLen d ∧ R.rel d xs (τ.window R.stream m.pos (R.win d)) ys ∧
        m' = (m.updBlock z ys).advance (R.win d) }

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {Q : Mem K → Prop} {m : Mem K}

/-- **Call of an operation with a window, on given operands**: the input blocks `xs` are read,
the output block `ys` is related to them and to the window at the position, which advances. The
lengths `k` of the window and `l` of the output are handed over reduced. -/
theorem wp_call_win {o : Op} {R : WinRel K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.Meets md o (R.spec adm)) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {a : List (ℕ × ℕ)} {z : ℕ × ℕ} {k l : ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hl : R.outLen d = l) (hadm : adm d a z)
    (hlive : m.Live (a ++ [z])) {xs : List (List K)}
    (hr : m.readBlocks a (R.inLens d) = some xs) (hz : z.2 + l ≤ m.store.len z.1)
    (hQ : ∀ ys, ys.length = l → R.rel d xs (τ.window R.stream m.pos k) ys →
      Q ((m.updBlock z ys).advance k)) : Wp md I τ (.call o ds ins outs) ρ Q m := by
  subst hk hl
  refine wp_call hI hd ha hb ⟨z, rfl, hnd, hadm, fun _ => ⟨hlive, by simp [hr], hz⟩⟩ ?_
  rintro m' ⟨z', xs', ys, hz', hr', hl', hrel, rfl⟩
  cases hz'
  rw [hr] at hr'
  cases hr'
  exact hQ ys hl' hrel

/-- **The loop that fills a block cell by cell**: round `i` writes the value `v i` in the cell
`o + i` of the buffer `b` and moves the position from `pos i` to `pos (i + 1)`; it may read the
cells already written and everything outside the block. -/
theorem wp_loop_fill {n : IExp} {body : Stmt Op Tst} {N b o : ℕ} {S : Store K} (v : ℕ → K)
    (pos : ℕ → ℕ) (hn : n.eval ρ.idx = some N)
    (hstep : ∀ i < N, ∀ s', S.EqOff (Store.inBlock b o i) s' →
      s'.readBlock b o i = some ((List.range i).map v) →
      Wp md I τ body (ρ.pushIdx i) (· = ⟨s'.upd b (o + i) (v i), pos (i + 1)⟩) ⟨s', pos i⟩)
    (hlen : o + N ≤ S.len b)
    (hQ : ∀ s', S.EqOff (Store.inBlock b o N) s' →
      s'.readBlock b o N = some ((List.range N).map v) → Q ⟨s', pos N⟩) :
    Wp md I τ (.loop n body) ρ Q ⟨S, pos 0⟩ := by
  refine wp_loop hn (fun i m' => ∃ s', m' = ⟨s', pos i⟩ ∧ S.EqOff (Store.inBlock b o i) s' ∧
    s'.readBlock b o i = some ((List.range i).map v)) ⟨S, rfl, by
      simpa using Store.EqOff.refl _ _, by simp⟩ ?_ fun m' ⟨s', h1, h2, h3⟩ => h1 ▸ hQ s' h2 h3
  rintro i hi m' ⟨s', rfl, hfr, hr⟩
  refine (hstep i hi s' hfr hr).mono ?_
  rintro m' rfl
  refine ⟨_, rfl, (hfr.mono fun b' q h => ⟨h.1, h.2.1, by have := h.2.2; omega⟩).upd
    ⟨rfl, by omega, by omega⟩ _, ?_⟩
  rw [List.range_succ, List.map_append]
  have := Store.readBlock_upd_concat hr (by rw [hfr.len_eq]; omega) (v i)
  simpa using this

end Rules

/-! ### Grounding -/

/-- **The implementation `R` meets the contract with a window `B`** over the interpretation `I`:
on admitted, live operands, with the input blocks `xs` read and room for the output, it fits and
its run writes an output block related to `xs` and to the window at the position, advances the
position by the window, and changes nothing else. Whatever the implementation draws into its
scratch is gone at the end of its run. -/
def Impl.MeetsWin (R : Impl Op Tst) (I : Interp Op Tst K) (B : WinRel K)
    (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Prop :=
  ∀ (d : List ℕ) (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : Tape K) (m : Mem K) (xs : List (List K)),
    d.length = B.nd → adm d ins z → m.Live (ins ++ [z]) →
    m.readBlocks ins (B.inLens d) = some xs → z.2 + B.outLen d ≤ m.store.len z.1 →
    R.Fits d.length ins.length 1 ∧ Wp .total I τ R.body (Env.frame d (ins ++ [z]))
      (fun m' => ∃ ys, ys.length = B.outLen d ∧
        B.rel d xs (τ.window B.stream m.pos (B.win d)) ys ∧
        m' = (m.updBlock z ys).advance (B.win d)) m

/-- **Grounding a contract with a window**: the induced interpretation meets the contract of an
operation whose implementation meets it. -/
theorem Interp.link_meets_win {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {R : Impl Op₂ Tst} (hT : T o = .inl R) {B : WinRel K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : R.MeetsWin I B adm) :
    (I.link T).Meets .total o (B.spec adm) := by
  refine Interp.link_meets hT ?_
  rintro d ins outs τ m ⟨z, rfl, hnd, hadm, hn⟩
  obtain ⟨hl, hr, hz⟩ := hn rfl
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨hfit, hw⟩ := h d ins z τ m xs hnd hadm hl hxs hz
  exact ⟨fun _ => hl, fun _ => ⟨hfit, hw.mono fun m' ⟨ys, h1, h2, h3⟩ =>
    ⟨z, xs, ys, rfl, hxs, h1, h2, h3⟩⟩⟩

/-! ### Visible randomness: the vector draw -/

/-- **The vector draw** `draw [n] [] [g]` of the stream `s`: the block `g` receives the window of
`n` entries. The values drawn are in the store of the caller. -/
def drawRel (s : ℕ) : WinRel K where
  nd := 1
  stream := s
  win d := d.headD 0
  inLens _ := []
  outLen d := d.headD 0
  rel _ _ w ys := ys = w

@[storeNF] theorem drawRel_win (s : ℕ) (d : List ℕ) :
    (drawRel (K := K) s).win d = d.headD 0 := rfl

@[storeNF] theorem drawRel_inLens (s : ℕ) (d : List ℕ) : (drawRel (K := K) s).inLens d = [] := rfl

@[storeNF] theorem drawRel_outLen (s : ℕ) (d : List ℕ) :
    (drawRel (K := K) s).outLen d = d.headD 0 := rfl

/-- The vector draw of the model meets the contract of the vector draw. -/
theorem Interp.IsFn.meets_drawRel {I : Interp Op Tst K} {o : Op} {s : ℕ}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : I.IsFn .total o (.drawVec s) adm) :
    I.Meets .total o ((drawRel s).spec adm) := by
  rintro d ins outs τ m ⟨z, rfl, hnd, hadm, hn⟩
  obtain ⟨hl, hr, hz⟩ := hn rfl
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain rfl : ins = [] := by
    rcases ins with _ | ⟨a, ins⟩
    · rfl
    · simp [drawRel, Mem.readBlocks] at hr
  have ha : (BlockFn.drawVec s : BlockFn K).apply [n] [] z τ m =
      some ((m.updBlock z (τ.window s m.pos n)).advance n) :=
    BlockFn.apply_eq_some_iff.mpr
      ⟨hl, [], τ.window s m.pos n, rfl, rfl, by simpa [drawRel] using hz, rfl⟩
  exact ⟨_, h.callS_eq hadm ha, z, [], τ.window s m.pos n, rfl, rfl, by simp [drawRel], rfl, rfl⟩

end NLAlib.Ops
