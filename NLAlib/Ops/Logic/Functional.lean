/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blocks
public import NLAlib.Ops.Logic.Writes

/-!
# Functional calls with exact output blocks

Functional operation proofs supply the mathematical output once. The shared call rule returns
those exact blocks, their frame, and the tape position without exposing the graph relation or
asking each caller to recover equal outputs from determinism.

## Main results

* `NLAlib.Ops.writes_call_fn`: any number of exact output blocks from a functional primitive.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
  {ρ : Env} {m : Mem K}

/-- A functional call writes its known mathematical outputs and preserves every other cell.
The input and output blocks may overlap: all inputs are read before the writes. Only the
output blocks must be mutually disjoint so that every output can be read back. -/
theorem writes_call_fn {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn md o f adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a b : List (ℕ × ℕ)}
    {xs ys : List (List K)} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some b)
    (hnd : d.length = f.nd) (hadm : adm d a b) (hap : Fp.Apart b (f.outLens d))
    (hl : m.Live (a ++ b)) (hr : m.readBlocks a (f.inLens d) = some xs)
    (hfn : f.fn d (τ.window f.stream m.pos (f.win d)) xs = some ys)
    (hys : ys.map List.length = f.outLens d) (hz : m.Room b (f.outLens d)) :
    Writes md I τ (.call o ds ins outs) ρ (Fp.blocks b (f.outLens d))
      (fun m' => m'.pos = m.pos + f.win d ∧ m'.readBlocks b (f.outLens d) = some ys) m := by
  refine (writes_call hI hd ha hb hnd rfl rfl hadm hap
    (fun _ => ⟨hl, ⟨xs, hr, ys, hfn, hys⟩, hz⟩)).mono le_rfl ?_
  intro m' _ ⟨hp, xs', ys', hr', hy', hf'⟩
  obtain rfl : xs' = xs := Option.some.inj (hr'.symm.trans hr)
  obtain rfl : ys' = ys := Option.some.inj (hf'.symm.trans hfn)
  exact ⟨hp, hy'⟩

/-- A functional operation with one known output block, in the form used by matrix kernels. -/
theorem writes_call_fn1 {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn md o f adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)}
    {z : ℕ × ℕ} {xs : List (List K)} {y : List K} {l : ℕ}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z]) (hnd : d.length = f.nd)
    (hls : f.outLens d = [l]) (hadm : adm d a [z]) (hl : m.Live (a ++ [z]))
    (hr : m.readBlocks a (f.inLens d) = some xs)
    (hfn : f.fn d (τ.window f.stream m.pos (f.win d)) xs = some [y])
    (hy : y.length = l) (hz : z.2 + l ≤ m.store.len z.1) :
    Writes md I τ (.call o ds ins outs) ρ (Store.inBlock z.1 z.2 l)
      (fun m' => m'.pos = m.pos + f.win d ∧ m'.store.readBlock z.1 z.2 l = some y) m := by
  refine (writes_call_fn hI hd ha hb hnd hadm (by simp [hls, Fp.Apart]) hl hr hfn
    (by simp [hy, hls]) (by simpa [hls, Mem.Room] using hz)).mono ?_ ?_
  · simp [hls, Fp.blocks]
  · intro m' _ ⟨hp, hr⟩
    rw [hls] at hr
    obtain ⟨y', ys', hy', _, he⟩ := Mem.readBlocks_cons_eq_some.mp hr
    obtain ⟨rfl, _⟩ := List.cons.inj he
    exact ⟨hp, hy'⟩

/-- A functional operation with two known output blocks, preserving both outputs explicitly. -/
theorem writes_call_fn2 {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (hI : I.IsFn md o f adm)
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)}
    {z₁ z₂ : ℕ × ℕ} {xs : List (List K)} {y₁ y₂ : List K} {l₁ l₂ : ℕ}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z₁, z₂]) (hnd : d.length = f.nd)
    (hls : f.outLens d = [l₁, l₂]) (hadm : adm d a [z₁, z₂])
    (hap : Fp.Disj (Store.inBlock z₁.1 z₁.2 l₁) (Store.inBlock z₂.1 z₂.2 l₂))
    (hl : m.Live (a ++ [z₁, z₂])) (hr : m.readBlocks a (f.inLens d) = some xs)
    (hfn : f.fn d (τ.window f.stream m.pos (f.win d)) xs = some [y₁, y₂])
    (hy₁ : y₁.length = l₁) (hy₂ : y₂.length = l₂)
    (hz₁ : z₁.2 + l₁ ≤ m.store.len z₁.1) (hz₂ : z₂.2 + l₂ ≤ m.store.len z₂.1) :
    Writes md I τ (.call o ds ins outs) ρ
      (Store.inBlock z₁.1 z₁.2 l₁ ⊔ Store.inBlock z₂.1 z₂.2 l₂)
      (fun m' => m'.pos = m.pos + f.win d ∧
        m'.store.readBlock z₁.1 z₁.2 l₁ = some y₁ ∧
        m'.store.readBlock z₂.1 z₂.2 l₂ = some y₂) m := by
  refine (writes_call_fn hI hd ha hb hnd hadm
    (by simpa [hls, Fp.Apart, Fp.blocks] using hap) hl hr hfn
    (by simp [hy₁, hy₂, hls]) (by simpa [hls, Mem.Room] using And.intro hz₁ hz₂)).mono ?_ ?_
  · simp [hls, Fp.blocks]
  · intro m' _ ⟨hp, hr⟩
    rw [hls] at hr
    obtain ⟨y₁', ys', hy₁', hr', he⟩ := Mem.readBlocks_cons_eq_some.mp hr
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    obtain ⟨y₂', ys'', hy₂', _, he'⟩ := Mem.readBlocks_cons_eq_some.mp hr'
    obtain ⟨rfl, _⟩ := List.cons.inj he'
    exact ⟨hp, hy₁', hy₂'⟩

/-- A constant-valued scalar call writes its cell with the ordinary frame and unchanged tape
position. The output needs capacity but no prior initialization. -/
theorem writes_call_const {o : Op} {v : K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (hI : I.IsFn .total o (BlockFn.const v) adm) {out : Operand} {z : ℕ × ℕ}
    (hout : out.eval ρ = some z) (hadm : adm [] [] [z])
    (hz : z.2 < m.store.len z.1) :
    Writes md I τ (.call o [] [] [out]) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some v) m := by
  apply wp_call_const hI rfl rfl (by simp [Operand.evalList, hout]) hadm hz
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, rfl,
    Store.get_upd_self hz _⟩

/-- A unary scalar call returns its known word with the ordinary cell footprint. Input and
output may alias exactly; output capacity and the actual input read imply their liveness. -/
theorem writes_call_un {o : Op} {g : K → Option K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (hI : I.IsFn .total o (.un g) adm) {ins outs : List Operand} {x z : ℕ × ℕ}
    (ha : Operand.evalList ρ ins = some [x]) (hb : Operand.evalList ρ outs = some [z])
    (hadm : adm [] [x] [z]) {a v : K} (hx : m.store.get x.1 x.2 = some a)
    (hg : g a = some v) (hz : z.2 < m.store.len z.1) :
    Writes md I τ (.call o [] ins outs) ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some v) m := by
  apply wp_call_un hI rfl ha hb hadm hx hg hz
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, rfl,
    Store.get_upd_self hz _⟩

/-- A framed scalar result is an exact mathematical memory update. Algorithms can continue
from that update without reproving cell extensionality or unfolding execution. -/
theorem Writes.wp_eq_upd {c : Stmt Op Tst} {z : ℕ × ℕ} {v : K}
    (h : Writes md I τ c ρ (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some v) m) :
    Wp md I τ c ρ (fun m' => m' = m.upd z v) m := by
  refine h.wp fun m' hfr ⟨hp, hg⟩ => ?_
  have hfr' : m.store.EqOff (Fp.blocks [z] [1]) m'.store := by
    simpa [Fp.blocks] using hfr
  have hr := BlockFn.readBlocks_cells_one.mpr ⟨v, hg, rfl⟩
  have he := Mem.eq_updBlocks_of_eqOff hfr' hr hp
  simpa [Mem.updBlocks, Mem.updBlock, Store.updBlock, Mem.upd] using he

end NLAlib.Ops
