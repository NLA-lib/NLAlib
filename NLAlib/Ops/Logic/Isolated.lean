/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Contract
public import NLAlib.Ops.ContextRun
public import NLAlib.Ops.Logic.Allocation

/-!
# Isolated buffers: context snapshots without a buffer order

The isolated buffers are those satisfying an arbitrary predicate `C` on handles: the ordinary
capabilities of a tree avoid `C`, and the buffers in `C` keep their lengths and cells. A stored
operand can then be in any buffer different from the buffers the tree may write.

## Main definitions

* `NLAlib.Ops.Env.Avoids`: no buffer capability of the environment is isolated.
* `NLAlib.Ops.Store.On`: two stores agree on the isolated buffers.
* `NLAlib.Ops.Mem.Isolated`: the isolated buffers are live and hold the reference words.
* `NLAlib.Ops.Interp.guardIsolated`: the guarded source interpretation.

## Main results

* `NLAlib.Ops.BlockRel.isolated_of_post`: a local post with non-isolated outputs keeps the
  isolated buffers.
* `NLAlib.Ops.Interp.satisfies_guardIsolated`: global source laws from local primitive contracts.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- No buffer capability of the environment is isolated. -/
def Env.Avoids (C : ℕ → Prop) (ρ : Env) : Prop := ∀ b ∈ ρ.buf, ¬ C b

/-- The isolated buffers have the same lengths and cells in `s` and `s'`. -/
def Store.On (C : ℕ → Prop) (s s' : Store K) : Prop :=
  ∀ b, C b → s'.len b = s.len b ∧ ∀ i, s'.get b i = s.get b i

/-- The isolated buffers are live and retain exactly their reference lengths and cells. -/
def Mem.Isolated (C : ℕ → Prop) (reference : Store K) (m : Mem K) : Prop :=
  (∀ b, C b → b < m.store.length) ∧ Store.On C reference m.store

theorem Store.On.refl (C : ℕ → Prop) (s : Store K) : Store.On C s s :=
  fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem Store.On.trans {C : ℕ → Prop} {s s' s'' : Store K} (h : Store.On C s s')
    (h' : Store.On C s' s'') : Store.On C s s'' :=
  fun b hb => ⟨(h' b hb).1.trans (h b hb).1, fun i => ((h' b hb).2 i).trans ((h b hb).2 i)⟩

/-- A block of an isolated buffer is read back unchanged. -/
theorem Store.On.readBlock {C : ℕ → Prop} {s s' : Store K} (h : Store.On C s s') {b : ℕ}
    (hb : C b) (o n : ℕ) : s'.readBlock b o n = s.readBlock b o n :=
  Store.readBlock_congr fun _ _ => (h b hb).2 _

/-- Writes confined to non-isolated buffers keep every isolated length and cell. -/
theorem Store.EqOff.on_of_avoids {C : ℕ → Prop} {F : Fp} {s s' : Store K}
    (h : Store.EqOff F s s') (hF : ∀ b i, F b i → ¬ C b) : Store.On C s s' :=
  fun b hb => ⟨h.len_eq b, fun i => h.get_eq fun hf => hF b i hf hb⟩

/-- The blocks at non-isolated operands contain no isolated cell. -/
theorem Fp.blocks_avoids {C : ℕ → Prop} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (hz : ∀ z ∈ zs, ¬ C z.1) : ∀ b i, Fp.blocks zs ls b i → ¬ C b := by
  induction zs generalizing ls with
  | nil => intro b i h; cases ls <;> exact False.elim h
  | cons z zs ih =>
    cases ls with
    | nil => intro b i h; exact False.elim h
    | cons l ls =>
      rintro b i (⟨rfl, _, _⟩ | h)
      · exact hz z (by simp)
      · exact ih (fun z hz' => hz z (by simp [hz'])) b i h

/-- Appending an index does not introduce a buffer capability. -/
theorem Env.Avoids.pushIdx {C : ℕ → Prop} {ρ : Env} (h : ρ.Avoids C) (i : ℕ) :
    (ρ.pushIdx i).Avoids C := h

/-- A fresh non-isolated buffer keeps the environment off the isolated buffers. -/
theorem Env.Avoids.pushBuf {C : ℕ → Prop} {b : ℕ} {ρ : Env} (h : ρ.Avoids C) (hb : ¬ C b) :
    (ρ.pushBuf b).Avoids C := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact (List.mem_singleton.mp hx) ▸ hb

/-- Every successfully evaluated operand names an non-isolated buffer. -/
theorem Operand.avoids_of_eval {C : ℕ → Prop} {ρ : Env} {a : Operand} {z : ℕ × ℕ}
    (h : ρ.Avoids C) (ha : a.eval ρ = some z) : ¬ C z.1 := by
  simp only [Operand.eval] at ha
  cases hb : ρ.buf[a.buf]? with
  | none => simp only [hb] at ha; cases ha
  | some b =>
    cases ho : a.off.eval ρ.idx with
    | none => simp only [hb, ho] at ha; cases ha
    | some off =>
      simp only [hb, ho] at ha
      cases ha
      exact h b (List.mem_of_getElem? hb)

/-- Every member of an evaluated operand tuple names an non-isolated buffer. -/
theorem Operand.avoids_of_evalList {C : ℕ → Prop} {ρ : Env} {as : List Operand}
    {zs : List (ℕ × ℕ)} (h : ρ.Avoids C) (ha : evalList ρ as = some zs) :
    ∀ z ∈ zs, ¬ C z.1 := by
  induction as generalizing zs with
  | nil => cases ha; simp
  | cons a as ih =>
    rw [evalList_cons] at ha
    obtain ⟨z, hz, htail⟩ := Option.bind_eq_some_iff.mp ha
    obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp htail
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact avoids_of_eval h hz
    · exact ih ht y hy

/-- Passing non-isolated operands to a procedure keeps its environment off the isolated
buffers. -/
theorem Env.Avoids.frame {C : ℕ → Prop} {as : List (ℕ × ℕ)} (h : ∀ z ∈ as, ¬ C z.1)
    (d : List ℕ) : (Env.frame d as).Avoids C := by
  intro b hb
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
  exact h z hz

/-- A memory in which the isolated buffers are live is isolated in its own store. -/
theorem Mem.Isolated.refl {C : ℕ → Prop} {m : Mem K} (h : ∀ b, C b → b < m.store.length) :
    m.Isolated C m.store := ⟨h, Store.On.refl _ _⟩

/-- A new scratch buffer leaves the isolated buffers untouched. -/
theorem Mem.Isolated.push {C : ℕ → Prop} {reference : Store K} {m : Mem K}
    (h : m.Isolated C reference) (n : ℕ) :
    (Mem.mk (m.store.push n) m.pos).Isolated C reference :=
  ⟨fun b hb => by rw [Store.length_push]; exact Nat.lt_succ_of_lt (h.1 b hb),
    fun b hb => ⟨(Store.len_push_of_lt (h.1 b hb) n).trans (h.2 b hb).1,
      fun i => (Store.get_push_of_lt (h.1 b hb) n i).trans ((h.2 b hb).2 i)⟩⟩

/-- Removing a scratch buffer above every isolated buffer keeps them. -/
theorem Mem.Isolated.pop {C : ℕ → Prop} {reference : Store K} {m : Mem K}
    (h : m.Isolated C reference) {L : ℕ} (hC : ∀ b, C b → b < L)
    (hL : m.store.length = L + 1) : (Mem.mk m.store.pop m.pos).Isolated C reference := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have := hC b hb
    simp only [Store.length_pop]
    omega
  · have hlt : b + 1 < m.store.length := by
      have := hC b hb
      omega
    exact ⟨(Store.len_pop_of_lt hlt).trans (h.2 b hb).1,
      fun i => (Store.get_pop_of_lt hlt i).trans ((h.2 b hb).2 i)⟩

/-- Every declared context capability in an isolated buffer remains live. -/
theorem Mem.Isolated.live {C : ℕ → Prop} {reference : Store K} {m : Mem K}
    (h : m.Isolated C reference) {context : List (ℕ × ℕ)}
    (hc : ∀ z ∈ context, C z.1) : m.Live context :=
  fun z hz => h.1 z.1 (hc z hz)

/-- Declared local outputs in non-isolated buffers keep the isolated buffers. -/
theorem BlockRel.isolated_of_post {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {C : ℕ → Prop} {reference : Store K} {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {w : List K} {m m' : Mem K} (h : m.Isolated C reference)
    (ho : ∀ z ∈ outs, ¬ C z.1) (hp : ((R.spec adm).spec .total d ins outs w).post m m') :
    m'.Isolated C reference := by
  obtain ⟨xs, _, _, ys, _, _, rfl⟩ := hp
  have hf : m.store.EqOff (Fp.blocks outs (ys.map List.length))
      ((m.updBlocks outs ys).advance (R.win d)).store :=
    Mem.eqOff_updBlocks (Store.EqOff.refl _ _) le_rfl
  exact ⟨fun b hb => (h.1 b hb).trans_eq hf.length_eq.symm,
    h.2.trans (hf.on_of_avoids (Fp.blocks_avoids ho))⟩

/-! ### The guarded source interpretation -/

/-- Guard delegation by the source primitive precondition and the isolated-buffer regime.
Queries retain the active interpretation and receive no additional context operands. -/
noncomputable def Interp.guardIsolated (active : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (C : ℕ → Prop)
    (fallback : Interp Op Tst K) : Interp Op Tst K := by
  classical
  exact {
    call := fun o d ins outs τ m =>
      if good m ∧ ∀ z ∈ outs, ¬ C z.1 then
        if ((contracts o).on .total d ins outs τ m).pre m then
          active.call o d ins outs τ m
        else none
      else fallback.call o d ins outs τ m
    test := active.test
    index := active.index }

open scoped Classical in
/-- The ordinary core liveness and shape checks commute with the proof-side guard. -/
theorem Interp.callS_guardIsolated (active fallback : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (C : ℕ → Prop)
    (o : Op) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) :
    (active.guardIsolated contracts good C fallback).callS o d ins outs τ m =
      if good m ∧ ∀ z ∈ outs, ¬ C z.1 then
        if ((contracts o).on .total d ins outs τ m).pre m then
          active.callS o d ins outs τ m
        else none
      else fallback.callS o d ins outs τ m := by
  classical
  by_cases hg : good m ∧ ∀ z ∈ outs, ¬ C z.1
  · by_cases hp : ((contracts o).on .total d ins outs τ m).pre m
    · simp only [Interp.callS, Interp.guardIsolated, if_pos hg, if_pos hp]
    · simp only [Interp.callS, Interp.guardIsolated, if_pos hg, if_neg hp, Option.bind_none]
      split_ifs <;> rfl
  · simp only [Interp.callS, Interp.guardIsolated, if_neg hg]

/-- Local correctness of delegated primitive calls and a valid fallback give a globally
valid source contract. No algorithm execution is included in either premise. -/
theorem Interp.satisfies_guardIsolated (active fallback : Interp Op Tst K)
    (contracts : Op → Contract K) (good : Mem K → Prop) (C : ℕ → Prop) (o : Op)
    (hFallback : fallback.Satisfies .total o (contracts o))
    (hActive : ∀ d ins outs τ m, good m → (∀ z ∈ outs, ¬ C z.1) →
      ((contracts o).on .total d ins outs τ m).pre m →
      Mode.total.Holds (active.callS o d ins outs τ m)
        (((contracts o).on .total d ins outs τ m).post m)) :
    (active.guardIsolated contracts good C fallback).Satisfies .total o (contracts o) := by
  classical
  refine Interp.Satisfies.of_callS ?_
  intro d ins outs τ m hp
  rw [Interp.callS_guardIsolated]
  by_cases hg : good m ∧ ∀ z ∈ outs, ¬ C z.1
  · rw [if_pos hg, if_pos hp]
    exact hActive d ins outs τ m hg.1 hg.2 hp
  · rw [if_neg hg]
    exact hFallback.callS d ins outs τ m hp

/-- A successful guarded call within the isolated regime uses the actual delegated call
and satisfies the source primitive precondition. -/
theorem Interp.callS_guardIsolated_of_good {active fallback : Interp Op Tst K}
    {contracts : Op → Contract K} {good : Mem K → Prop} {C : ℕ → Prop}
    {o : Op} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K}
    (hg : good m) (ho : ∀ z ∈ outs, ¬ C z.1)
    (hr : (active.guardIsolated contracts good C fallback).callS o d ins outs τ m = some m') :
    ((contracts o).on .total d ins outs τ m).pre m ∧
      active.callS o d ins outs τ m = some m' := by
  classical
  rw [Interp.callS_guardIsolated, if_pos ⟨hg, ho⟩] at hr
  split_ifs at hr with hp
  exact ⟨hp, hr⟩

end NLAlib.Ops
