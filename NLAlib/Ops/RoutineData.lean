/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.Logic.IsolatedLink
public import NLAlib.Ops.Logic.BlockSequence
public import NLAlib.Ops.Logic.Footprint

/-!
# A routine on stored data

A routine written against an operation that only an oracle provides (a product with a matrix)
becomes a routine on stored data by forwarding the data to every call of that operation: the
data blocks are new leading operands, isolated, and each call of the operation is replaced by an
implementation that reads them (`NLAlib.Ops.Stmt.linkContext`). `NLAlib.Ops.Routine.withData`
is that routine, and `NLAlib.Ops.Routine.Meets.withData` gives its judgment from the judgment of
the matrix-free routine under the interpretation in which the operation reads the stored words
(`NLAlib.Ops.Interp.withData`). No other proof about the tree is needed.

## Main definitions

* `NLAlib.Ops.Routine.withData`: a routine with its data forwarded to a context table.
* `NLAlib.Ops.Interp.withData`: the interpretation of the matrix-free operations on the data.
* `NLAlib.Ops.Routine.Spec.onData`: the specification of a routine on stored data.

## Main results

* `NLAlib.Ops.Routine.Meets.withData`: the judgment of a routine on stored data.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Lo Tst : Type}

/-- The environment of a frame whose leading operands are context is the frame of the others
with the context forwarded after the dimensions. -/
theorem Env.frame_append_eq_withContext (d : List ℕ) (ctx e : List (ℕ × ℕ)) :
    Env.frame d (ctx ++ e) = (Env.frame d e).withContext ctx d.length := by
  simp only [Env.frame, Env.withContext, List.map_append, List.take_left', List.drop_left',
    List.append_assoc]

/-- Reading leading blocks and then the others. -/
theorem Mem.readBlocks_append_eq_some {m : Mem K} :
    ∀ {zs ws : List (ℕ × ℕ)} {ls ns : List ℕ} {X : List (List K)}, zs.length = ls.length →
      m.readBlocks (zs ++ ws) (ls ++ ns) = some X →
        ∃ xs ys, m.readBlocks zs ls = some xs ∧ m.readBlocks ws ns = some ys ∧ X = xs ++ ys
  | [], _, [], _, _, _, h => ⟨[], _, rfl, h, rfl⟩
  | z :: zs, ws, l :: ls, ns, X, hl, h => by
    obtain ⟨x, xs, hx, hxs, rfl⟩ := readBlocks_cons_eq_some.mp h
    obtain ⟨xs₁, ys, h₁, h₂, rfl⟩ :=
      Mem.readBlocks_append_eq_some (by simpa using hl) hxs
    exact ⟨x :: xs₁, ys, readBlocks_cons_eq_some.mpr ⟨x, xs₁, hx, h₁, rfl⟩, h₂, rfl⟩

/-- Reading blocks gives one block per operand. -/
theorem Mem.length_readBlocks {m : Mem K} :
    ∀ {zs : List (ℕ × ℕ)} {ls : List ℕ} {X : List (List K)},
      m.readBlocks zs ls = some X → X.length = zs.length
  | [], [], _, h => by cases h; rfl
  | _ :: _, _ :: _, _, h => by
    obtain ⟨_, _, _, hxs, rfl⟩ := readBlocks_cons_eq_some.mp h
    simp [Mem.length_readBlocks hxs]
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- **The interpretation of matrix-free operations on stored data**: the operations of the
table are those of `I`, with the context blocks `ctx` forwarded; it is guarded by the contracts
`rel`/`adm` and by the condition that the context buffers hold their words in `reference`. A
proof device: the program that runs is the linked tree. -/
noncomputable def Interp.withData (I : Interp Lo Tst K) (T : ContextTable Op Lo Tst)
    (ctx : List (ℕ × ℕ)) (reference : Store K) (rel : Op → BlockRel K)
    (adm : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) (fallback : Interp Op Tst K) :
    Interp Op Tst K :=
  (I.linkContext T ctx).guardIsolated (fun o => (rel o).spec (adm o))
    (Mem.Isolated (· ∈ ctx.map Prod.fst) reference) (· ∈ ctx.map Prod.fst) fallback

/-- **The specification of a routine on stored data**: the first `c` blocks read are the data;
they satisfy `P`, and the routine meets the specification `S₀ d data` of the matrix-free
routine on the other blocks. -/
def Routine.Spec.onData (c : ℕ) (P : List ℕ → List (List K) → Prop)
    (S₀ : List ℕ → List (List K) → Routine.Spec K) : Routine.Spec K where
  pre d ω X := P d (X.take c) ∧ (S₀ d (X.take c)).pre d ω (X.drop c)
  post d ω X Y := (S₀ d (X.take c)).post d ω (X.drop c) Y

namespace Routine

/-- **A routine on stored data**: the data blocks, one per length of `lens`, are new leading
operands, isolated; the tree is the tree of `R` with the data forwarded to the operations that
`T` implements. The dimensions, draws and remaining operands are those of `R`. -/
def withData (R : Routine Op Tst) (lens : List (List ℕ → ℕ)) (T : ContextTable Op Lo Tst) :
    Routine Lo Tst where
  nd := R.nd
  ports := lens.map Port.isolated ++ R.ports
  draws := R.draws
  body := R.body.linkContext lens.length R.nd T
  binds := R.binds.map fun l => List.range lens.length ++ l.map (· + lens.length)
  sep := .buffers

variable {R : Routine Op Tst} {lens : List (List ℕ → ℕ)} {T : ContextTable Op Lo Tst}

private theorem filter_isolated {α : Type} (P : Port × α → Bool) (b : Bool)
    (hP : ∀ l x, P (Port.isolated l, x) = b) :
    ∀ (lens : List (List ℕ → ℕ)) (xs : List α), lens.length = xs.length →
      (((lens.map Port.isolated).zip xs).filter P).map Prod.snd = if b then xs else []
  | [], [], _ => by split <;> rfl
  | l :: ls, x :: xs, h => by
    have ih := filter_isolated P b hP ls xs (by simpa using h)
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons, hP]
    cases b <;> simpa using ih
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The operands of the routine on data selected by their access: the data blocks if the access
of an isolated operand is selected, then those of `R`. -/
theorem withData_sel {α : Type} (p : Access → Bool) {ctx rest : List α}
    (hc : ctx.length = lens.length) :
    (R.withData lens T).sel p (ctx ++ rest) =
      (if p .isolated then ctx else []) ++ R.sel p rest := by
  unfold sel withData
  rw [List.zip_append (by simp [hc]), List.filter_append, List.map_append,
    filter_isolated _ (p .isolated) (fun _ _ => rfl) lens ctx hc.symm]

/-- The reported operands of the routine on data are those of `R`: data is never written. -/
theorem withData_outs {α : Type} {ctx rest : List α} (hc : ctx.length = lens.length) :
    (R.withData lens T).outs (ctx ++ rest) = R.outs rest := by
  unfold outs withData
  rw [List.zip_append (by simp [hc]), List.filter_append, List.map_append,
    filter_isolated _ false (fun _ _ => rfl) lens ctx hc.symm]
  rfl

/-- The lengths of the operands of the routine on data. -/
theorem withData_lens (d : List ℕ) :
    (R.withData lens T).lens d = lens.map (· d) ++ R.lens d := by
  simp [Routine.lens, withData]

/-- No operand of the routine on data continues another if none of `R` does. -/
theorem withData_flat : (R.withData lens T).flat = R.flat := by
  simp [flat, withData, Port.flat, List.all_append, Port.isolated]

private theorem filterMap_range_getElem? {α : Type} (l : List α) :
    ∀ n, n ≤ l.length → (List.range n).filterMap (fun i => l[i]?) = l.take n
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.filterMap_append, filterMap_range_getElem? l n (by omega),
      List.take_add_one]
    simp [List.getElem?_eq_getElem (show n < l.length by omega)]

/-- The buffer variables of the routine on data: the data blocks, then those of `R`. -/
theorem withData_env {ctx rest : List (ℕ × ℕ)} (hc : ctx.length = lens.length) :
    (R.withData lens T).env (ctx ++ rest) = ctx ++ R.env rest := by
  unfold env withData
  cases R.binds with
  | none => rfl
  | some l =>
    simp only [Option.map_some, List.filterMap_append, List.filterMap_map]
    rw [← hc, filterMap_range_getElem? _ _ (by simp), List.take_left' rfl]
    congr 1
    refine List.filterMap_congr fun i _ => ?_
    simp [List.getElem?_append_right]

/-- Separation by buffer of the operands of the routine on data: that of `R` on its operands,
and every data buffer apart from every other operand. -/
theorem withData_separated {ctx rest : List (ℕ × ℕ)} (hc : ctx.length = lens.length)
    (hr : rest.length = R.ports.length) (h : (R.withData lens T).Separated (ctx ++ rest)) :
    R.Separated rest ∧ ∀ a ∈ ctx, ∀ z ∈ rest, a.1 ≠ z.1 := by
  rw [separated_iff_pairwise] at h
  rw [separated_iff_pairwise]
  change ((lens.map Port.isolated ++ R.ports).zip (ctx ++ rest)).Pairwise _ at h
  rw [List.zip_append (by simp [hc]), List.pairwise_append] at h
  obtain ⟨-, h₂, h₃⟩ := h
  refine ⟨h₂, fun a ha z hz => ?_⟩
  have ha' : a ∈ ((lens.map Port.isolated).zip ctx).map Prod.snd := by
    rw [List.map_snd_zip (by simp [hc])]
    exact ha
  have hz' : z ∈ (R.ports.zip rest).map Prod.snd := by
    rw [List.map_snd_zip (by omega)]
    exact hz
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz'
  refine h₃ u hu v hv ?_
  obtain ⟨l, -, hl⟩ := List.mem_map.mp (List.of_mem_zip hu).1
  rw [← hl]
  cases v.1.access <;> rfl

/-- The judgment of a routine on stored data, from the judgment of the matrix-free routine
under the interpretation in which the operations read the stored words. At each call the data
operands `ctx` hold blocks `raws`; when they satisfy `P`, the matrix-free routine meets the
specification `S₀ d raws` under `Interp.withData`, whose contracts `rel`/`adm` then hold
(`hsat`).
The routine on stored data then meets `Spec.onData lens.length P S₀`.

`R` is separated by buffer and has no continuing operand, as the linking of stored data needs
the data buffers apart from every other buffer. -/
theorem Meets.withData {I : Interp Lo Tst K} (P : List ℕ → List (List K) → Prop)
    (S₀ : List ℕ → List (List K) → Spec K) (rel : List ℕ → List (List K) → Op → BlockRel K)
    (adm : List ℕ → Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (fallback : List ℕ → List (List K) → Interp Op Tst K)
    (hflat : R.flat = true) (hsepR : R.sep = .buffers)
    (hsat : ∀ d (ctx : List (ℕ × ℕ)) (m : Mem K) raws, ctx.length = lens.length →
      m.readBlocks ctx (lens.map (· d)) = some raws → P d raws → ∀ o,
        (I.withData T ctx m.store (rel d raws) (adm d) (fallback d raws)).Satisfies .total o
          ((rel d raws o).spec (adm d o)))
    (hmeets : ∀ d (ctx : List (ℕ × ℕ)) (m : Mem K) raws, ctx.length = lens.length →
      m.readBlocks ctx (lens.map (· d)) = some raws → P d raws →
        R.Meets (I.withData T ctx m.store (rel d raws) (adm d) (fallback d raws)) (S₀ d raws)) :
    (R.withData lens T).Meets I (Spec.onData lens.length P S₀) := by
  intro d args τ m X hnd hlen hl hsep hr hpreS hroom
  have hflat' : (R.withData lens T).flat = true := withData_flat.trans hflat
  rw [arity_of_flat hflat'] at hlen
  rw [operands_of_flat hflat' d hlen] at hr hroom ⊢
  have hlen' : args.length = lens.length + R.ports.length := by
    rw [hlen]
    change (lens.map Port.isolated ++ R.ports).length = _
    simp
  obtain ⟨ctx, rest, rfl, hc, hrest⟩ : ∃ ctx rest, args = ctx ++ rest ∧
      ctx.length = lens.length ∧ rest.length = R.ports.length :=
    ⟨args.take lens.length, args.drop lens.length, (List.take_append_drop _ _).symm,
      by simp; omega, by simp; omega⟩
  have hsep' : (R.withData lens T).Separated (ctx ++ rest) := by
    have h := hsep
    unfold SeparatedAt at h
    rwa [Routine.regions_of_flat hflat'] at h
  obtain ⟨hsepR', hapart⟩ := withData_separated hc hrest hsep'
  dsimp only [readArgs, readLens] at hr
  rw [withData_sel _ hc, withData_lens, withData_sel _ (by simp)] at hr
  simp only [Access.readable, if_true] at hr
  obtain ⟨raws, xs, hraws, hxs, rfl⟩ :=
    Mem.readBlocks_append_eq_some (by simp [hc]) hr
  have hrl : raws.length = lens.length := (Mem.length_readBlocks hraws).trans hc
  have htake : (raws ++ xs).take lens.length = raws := by rw [← hrl, List.take_left' rfl]
  have hdrop : (raws ++ xs).drop lens.length = xs := by rw [← hrl, List.drop_left' rfl]
  obtain ⟨hP, hpre₀⟩ := hpreS
  rw [htake, hdrop] at hpre₀
  rw [htake] at hP
  dsimp only [writeArgs, writeLens] at hroom
  rw [withData_sel _ hc, withData_lens, withData_sel _ (by simp)] at hroom
  simp only [Access.writable, Bool.false_eq_true, if_false, List.nil_append] at hroom
  have hlrest : m.Live rest := fun z hz => hl z (List.mem_append_right _ hz)
  have hnd' : d.length = R.nd := hnd
  have hW := hmeets d ctx m raws hc hraws hP d rest τ m xs hnd'
    (by rw [arity_of_flat hflat]; exact hrest) hlrest
    (by unfold SeparatedAt; rw [hsepR, Routine.regions_of_flat hflat]; exact hsepR')
    (by rw [operands_of_flat hflat d hrest]; exact hxs)
    hpre₀ (by rw [operands_of_flat hflat d hrest]; exact hroom)
  rw [operands_of_flat hflat d hrest] at hW
  have hcut : ∀ h, h ∈ ctx.map Prod.fst → h < m.store.length := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hh
    exact hl z (List.mem_append_left _ hz)
  have havoid : ∀ z ∈ R.env rest, ¬ z.1 ∈ ctx.map Prod.fst := by
    intro z hz hmem
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    exact hapart a ha z (mem_of_mem_env hz) he
  have hlink := Wp.linkContext_of_isolated I T ctx (rel d raws) (adm d) (fallback d raws)
    (· ∈ ctx.map Prod.fst) m.store (hsat d ctx m raws hc hraws hP) (slot := d.length)
    (ρ := Env.frame d (R.env rest)) (by simp) (Mem.Isolated.refl hcut)
    (Env.Avoids.frame havoid d) (fun z hz => List.mem_map_of_mem hz) hW
  rw [withData_env hc, Env.frame_append_eq_withContext]
  change Wp .total I τ (R.body.linkContext lens.length R.nd T) _ _ m
  rw [← hc, ← hnd']
  dsimp only [writeArgs, writeLens, outArgs, outLens]
  rw [withData_sel _ hc, withData_lens, withData_sel _ (by simp), withData_outs hc,
    withData_outs (by simp)]
  simp only [Access.writable, Bool.false_eq_true, if_false, List.nil_append]
  refine Wp.mono hlink fun m' ⟨hfr, hadv, ys, hys, hp⟩ => ⟨hfr, hadv, ys, hys, ?_⟩
  change (S₀ d ((raws ++ xs).take ctx.length)).post d _ ((raws ++ xs).drop ctx.length) ys
  rw [hc, htake, hdrop]
  exact hp

end Routine

end NLAlib.Ops
