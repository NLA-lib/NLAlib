/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic

/-!
# The call rule

One rule for a call of an operation under a contract in operand form (`NLAlib.Ops.BlockRel`),
whatever the contract: relational, functional, with a window, with any number of input and
output blocks.

## Main results

* `NLAlib.Ops.wp_call_rel`, **the** rule, in every mode: from the input blocks that are read,
  the continuation receives output blocks of the declared lengths, related to the inputs and to
  the window, written at the output operands, and the position advanced by the window.
* `NLAlib.Ops.wp_call_rel_liberal`: partial correctness, with nothing to prove about the memory;
  the continuation also receives that the inputs were read and that there was room.

Everything else here is a corollary for a shape of the outputs or of the contract, so that the
continuation is stated on blocks and cells instead of lists of blocks:

* one output block, one output cell, two output blocks: `NLAlib.Ops.wp_call_rel1`,
  `NLAlib.Ops.wp_call_rel_cell`, `NLAlib.Ops.wp_call_rel2`;
* a functional contract, where the call is an equation: `NLAlib.Ops.wp_call_fn`,
  `NLAlib.Ops.wp_call_fn_liberal`, and on cells `NLAlib.Ops.wp_call_const`, `wp_call_un`,
  `wp_call_bin`, `wp_call_tern`, `wp_call_draw`.

The tactic `wp_call` (`NLAlib.Ops.Tactic`) applies the right one and discharges the side goals.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {Q : Mem K → Prop} {m : Mem K}

/-- **The call rule**: a call under a contract in operand form, on given operands. The input
blocks `xs` are read and are in the domain; the output blocks `ys` have the declared lengths `ls`
and are related to `xs` and to the window of `k` entries at the position, which advances. The
lengths `k` and `ls` are handed over reduced. -/
theorem wp_call_rel {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)} {k : ℕ}
    {ls : List ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some b)
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = ls) (hadm : adm d a b)
    (hlive : m.Live (a ++ b)) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz : m.Room b ls)
    (hQ : ∀ ys, ys.map List.length = ls → R.rel d xs (τ.window R.stream m.pos k) ys →
      Q ((m.updBlocks b ys).advance k)) : Wp md I τ (.call o ds ins outs) ρ Q m := by
  subst hk hls
  refine wp_call hI hd ha hb ⟨hnd, hadm, fun _ => ⟨hlive, ⟨xs, hr, hdom⟩, hz⟩⟩ ?_
  rintro m' ⟨xs', hr', -, ys, hlen, hrel, rfl⟩
  have e : xs' = xs := Option.some.inj (hr'.symm.trans hr)
  subst e
  exact hQ ys hlen hrel

/-- **The call rule, partial correctness**: nothing is proved about the memory; a successful call
had live operands, read its inputs and had room for its outputs. -/
theorem wp_call_rel_liberal {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets .liberal o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)} {k : ℕ}
    {ls : List ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some b)
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = ls) (hadm : adm d a b)
    (hQ : ∀ xs ys, m.Live (a ++ b) → m.readBlocks a (R.inLens d) = some xs → m.Room b ls →
      ys.map List.length = ls → R.rel d xs (τ.window R.stream m.pos k) ys →
      Q ((m.updBlocks b ys).advance k)) : Wp .liberal I τ (.call o ds ins outs) ρ Q m := by
  subst hk hls
  intro m' hrun
  simp only [run, hd, ha, hb, Option.bind_some] at hrun
  obtain ⟨xs, hr, hroom, ys, hlen, hrel, rfl⟩ := hI d a b τ m ⟨hnd, hadm, by simp⟩ m' hrun
  exact hQ xs ys (Interp.live_of_callS hrun) hr hroom hlen hrel

/-- The call rule for **one output block**. -/
theorem wp_call_rel1 {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k l : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [l]) (hadm : adm d a [z])
    (hlive : m.Live (a ++ [z])) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz : z.2 + l ≤ m.store.len z.1)
    (hQ : ∀ ys, ys.length = l → R.rel d xs (τ.window R.stream m.pos k) [ys] →
      Q ((m.updBlock z ys).advance k)) : Wp md I τ (.call o ds ins outs) ρ Q m := by
  refine wp_call_rel hI hd ha hb hnd hk hls hadm hlive hr hdom ⟨hz, trivial⟩ fun ys hlen hrel => ?_
  obtain ⟨y, rfl, hy⟩ := map_length_eq_one hlen
  exact hQ y hy hrel

/-- The call rule for **one output cell**. -/
theorem wp_call_rel_cell {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {k : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [1]) (hadm : adm d a [z])
    (hlive : m.Live (a ++ [z])) (hr : m.readBlocks a (R.inLens d) = some xs)
    (hdom : R.dom d xs (τ.window R.stream m.pos k)) (hz : z.2 < m.store.len z.1)
    (hQ : ∀ v, R.rel d xs (τ.window R.stream m.pos k) [[v]] → Q ((m.upd z v).advance k)) :
    Wp md I τ (.call o ds ins outs) ρ Q m := by
  refine wp_call_rel1 hI hd ha hb hnd hk hls hadm hlive hr hdom (by omega) fun ys hys hrel => ?_
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hys
  exact hQ v hrel

/-- The call rule for **two output blocks** (a factorization, a rotation of two vectors). -/
theorem wp_call_rel2 {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z₁ z₂ : ℕ × ℕ}
    {k l₁ l₂ : ℕ} {xs : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z₁, z₂])
    (hnd : d.length = R.nd) (hk : R.win d = k) (hls : R.outLens d = [l₁, l₂])
    (hadm : adm d a [z₁, z₂]) (hlive : m.Live (a ++ [z₁, z₂]))
    (hr : m.readBlocks a (R.inLens d) = some xs) (hdom : R.dom d xs (τ.window R.stream m.pos k))
    (hz₁ : z₁.2 + l₁ ≤ m.store.len z₁.1) (hz₂ : z₂.2 + l₂ ≤ m.store.len z₂.1)
    (hQ : ∀ y₁ y₂, y₁.length = l₁ → y₂.length = l₂ →
      R.rel d xs (τ.window R.stream m.pos k) [y₁, y₂] →
      Q (((m.updBlock z₁ y₁).updBlock z₂ y₂).advance k)) :
    Wp md I τ (.call o ds ins outs) ρ Q m := by
  refine wp_call_rel hI hd ha hb hnd hk hls hadm hlive hr hdom ⟨hz₁, hz₂, trivial⟩
    fun ys hlen hrel => ?_
  obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := map_length_eq_two hlen
  exact hQ y₁ y₂ h₁ h₂ hrel

/-! ### Functional contracts: the call is an equation -/

/-- **Call of a functional operation**: an equation. -/
theorem wp_call_fn {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn .total o f adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hadm : adm d a b) {m' : Mem K}
    (hf : f.apply d a b τ m = some m') (hQ : Q m') : Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_of_run (by simp only [run, hd, ha, hb, Option.bind_some, hI.callS_eq hadm hf]) hQ

/-- **Call of a functional operation, partial correctness**: if the call succeeds, it is the
block function. -/
theorem wp_call_fn_liberal {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn .liberal o f adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hnd : d.length = f.nd) (hadm : adm d a b)
    (hQ : ∀ m', f.apply d a b τ m = some m' → Q m') :
    Wp .liberal I τ (.call o ds ins outs) ρ Q m := by
  intro m' hrun
  simp only [run, hd, ha, hb, Option.bind_some] at hrun
  exact hQ m' (hI.apply_of_callS hnd hadm hrun)

/-- Call of a functional constant, on cells. -/
theorem wp_call_const {o : Op} {v : K} {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (hI : I.IsFn .total o (.const v) adm) {ds : List IExp} {ins outs : List Operand}
    {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some []) (ha : Operand.evalList ρ ins = some [])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm [] [] [z]) (hz : z.2 < m.store.len z.1)
    (hQ : Q (m.upd z v)) : Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_const_eq_some_iff.mpr ⟨hz, rfl⟩) hQ

/-- Call of a functional operation of one cell, on cells. -/
theorem wp_call_un {o : Op} {g : K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn .total o (.un g) adm)
    {ds : List IExp} {ins outs : List Operand} {x z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some []) (ha : Operand.evalList ρ ins = some [x])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm [] [x] [z]) {a v : K}
    (hx : m.store.get x.1 x.2 = some a) (hg : g a = some v) (hz : z.2 < m.store.len z.1)
    (hQ : Q (m.upd z v)) : Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_un_eq_some_iff.mpr ⟨a, v, hx, hg, hz, rfl⟩) hQ

/-- Call of a functional operation of two cells, on cells. -/
theorem wp_call_bin {o : Op} {g : K → K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn .total o (.bin g) adm)
    {ds : List IExp} {ins outs : List Operand} {x y z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some []) (ha : Operand.evalList ρ ins = some [x, y])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm [] [x, y] [z]) {a b v : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hg : g a b = some v) (hz : z.2 < m.store.len z.1) (hQ : Q (m.upd z v)) :
    Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_bin_eq_some_iff.mpr ⟨a, b, v, hx, hy, hg, hz, rfl⟩)
    hQ

/-- Call of a functional operation of three cells, on cells. -/
theorem wp_call_tern {o : Op} {g : K → K → K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn .total o (.tern g) adm)
    {ds : List IExp} {ins outs : List Operand} {x y w z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some []) (ha : Operand.evalList ρ ins = some [x, y, w])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm [] [x, y, w] [z]) {a b c v : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b)
    (hw : m.store.get w.1 w.2 = some c) (hg : g a b c = some v) (hz : z.2 < m.store.len z.1)
    (hQ : Q (m.upd z v)) : Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm
    (BlockFn.apply_tern_eq_some_iff.mpr ⟨a, b, c, v, hx, hy, hw, hg, hz, rfl⟩) hQ

/-- A draw, on cells. -/
theorem wp_call_draw {o : Op} {st : ℕ} {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (hI : I.IsFn .total o (.draw st) adm) {ds : List IExp} {ins outs : List Operand}
    {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some []) (ha : Operand.evalList ρ ins = some [])
    (hb : Operand.evalList ρ outs = some [z]) (hadm : adm [] [] [z]) (hz : z.2 < m.store.len z.1)
    (hQ : Q ((m.upd z (τ m.pos st)).advance 1)) : Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_draw_eq_some_iff.mpr ⟨hz, rfl⟩) hQ

end Rules

end NLAlib.Ops
