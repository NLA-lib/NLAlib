/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ContextGuard
public import NLAlib.Ops.ContextRun
public import NLAlib.Ops.Logic.Allocation

/-!
# Protected raw context snapshots

Ordinary source capabilities lie above a fixed buffer boundary. The context occupies
surviving buffers below that boundary. Local block-relation posts preserve every context
cell, and scoped allocation preserves the same snapshot without exposing a global handle.

## Main results

* `NLAlib.Ops.Mem.ContextSnapshot`: live protected prefix and its stored words.
* `NLAlib.Ops.BlockRel.contextSnapshot_of_post`: local output framing protects that prefix.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- Every ordinary buffer capability lies outside the protected context prefix. -/
def Env.Above (cutoff : ℕ) (ρ : Env) : Prop := ∀ b ∈ ρ.buf, cutoff ≤ b

/-- A declared raw prefix remains live and retains exactly its original lengths and cells. -/
def Mem.ContextSnapshot (cutoff : ℕ) (reference : Store K) (m : Mem K) : Prop :=
  cutoff ≤ m.store.length ∧ Store.Below cutoff reference m.store

/-- Appending an index does not introduce a buffer capability. -/
theorem Env.Above.pushIdx {cutoff : ℕ} {ρ : Env} (h : ρ.Above cutoff) (i : ℕ) :
    (ρ.pushIdx i).Above cutoff := h

/-- Fresh allocation adds only a capability above the protected prefix. -/
theorem Env.Above.pushBuf {cutoff b : ℕ} {ρ : Env} (h : ρ.Above cutoff) (hb : cutoff ≤ b) :
    (ρ.pushBuf b).Above cutoff := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · simpa using (List.mem_singleton.mp hx) ▸ hb

/-- Every successfully evaluated ordinary operand names an ordinary source capability. -/
theorem Operand.above_of_eval {cutoff : ℕ} {ρ : Env} {a : Operand} {z : ℕ × ℕ}
    (h : ρ.Above cutoff) (ha : a.eval ρ = some z) : cutoff ≤ z.1 := by
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

/-- Every member of an evaluated operand tuple stays outside the protected prefix. -/
theorem Operand.above_of_evalList {cutoff : ℕ} {ρ : Env} {as : List Operand}
    {zs : List (ℕ × ℕ)} (h : ρ.Above cutoff) (ha : evalList ρ as = some zs) :
    ∀ z ∈ zs, cutoff ≤ z.1 := by
  induction as generalizing zs with
  | nil => cases ha; simp
  | cons a as ih =>
    rw [evalList_cons] at ha
    obtain ⟨z, hz, htail⟩ := Option.bind_eq_some_iff.mp ha
    obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp htail
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact above_of_eval h hz
    · exact ih ht y hy

/-- Passing ordinary operands to a procedure retains capability separation. -/
theorem Env.Above.frame {cutoff : ℕ} {as : List (ℕ × ℕ)} (h : ∀ z ∈ as, cutoff ≤ z.1)
    (d : List ℕ) : (Env.frame d as).Above cutoff := by
  intro b hb
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
  exact h z hz

/-- The initial raw context is its own snapshot. -/
theorem Mem.ContextSnapshot.refl {cutoff : ℕ} {m : Mem K} (h : cutoff ≤ m.store.length) :
    m.ContextSnapshot cutoff m.store := ⟨h, Store.Below.refl _ _⟩

/-- A new scratch buffer leaves the protected prefix untouched. -/
theorem Mem.ContextSnapshot.push {cutoff : ℕ} {reference : Store K} {m : Mem K}
    (h : m.ContextSnapshot cutoff reference) (n : ℕ) :
    (Mem.mk (m.store.push n) m.pos).ContextSnapshot cutoff reference :=
  ⟨by simpa using h.1.trans (Nat.le_succ _), h.2.trans ((Store.below_push _ _).mono h.1)⟩

/-- Removing a scratch buffer strictly above the protected prefix preserves the snapshot. -/
theorem Mem.ContextSnapshot.pop {cutoff : ℕ} {reference : Store K} {m : Mem K}
    (h : m.ContextSnapshot cutoff reference) (hAbove : cutoff < m.store.length) :
    (Mem.mk m.store.pop m.pos).ContextSnapshot cutoff reference := by
  have hp := Store.below_pop (s := m.store) (L := m.store.length - 1) (by omega)
  exact ⟨by simp only [Store.length_pop]; omega, h.2.trans (hp.mono (by omega))⟩

/-- Every declared context capability below the boundary remains live. -/
theorem Mem.ContextSnapshot.live {cutoff : ℕ} {reference : Store K} {m : Mem K}
    (h : m.ContextSnapshot cutoff reference) {context : List (ℕ × ℕ)}
    (hc : ∀ z ∈ context, z.1 < cutoff) : m.Live context :=
  fun z hz => (hc z hz).trans_le h.1

/-- A local block-relation post writes only its declared ordinary output buffers. -/
theorem BlockRel.eqOff_above_of_post {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {cutoff : ℕ} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {w : List K} {m m' : Mem K}
    (ho : ∀ z ∈ outs, cutoff ≤ z.1) (hp : ((R.spec adm).spec .total d ins outs w).post m m') :
    m.store.EqOff (Fp.above cutoff) m'.store := by
  obtain ⟨xs, _, _, ys, _, _, rfl⟩ := hp
  exact Mem.eqOff_updBlocks (Store.EqOff.refl _ _) (Fp.blocks_le_above ho)

/-- Declared local outputs above the boundary preserve the entire context snapshot. -/
theorem BlockRel.contextSnapshot_of_post {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {cutoff : ℕ} {reference : Store K} {d : List ℕ} {ins outs : List (ℕ × ℕ)}
    {w : List K} {m m' : Mem K} (h : m.ContextSnapshot cutoff reference)
    (ho : ∀ z ∈ outs, cutoff ≤ z.1) (hp : ((R.spec adm).spec .total d ins outs w).post m m') :
    m'.ContextSnapshot cutoff reference := by
  have hf := BlockRel.eqOff_above_of_post (R := R) ho hp
  exact ⟨by rw [hf.length_eq]; exact h.1,
    h.2.trans (hf.below_of_above (fun _ _ hb => hb))⟩

end NLAlib.Ops
