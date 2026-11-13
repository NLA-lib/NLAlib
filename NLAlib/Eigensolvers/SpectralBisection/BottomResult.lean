/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.BlockSequence
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# The stored recursion-boundary result

The boundary initializes identity and zero eigenvalue words. The mathematical identity uses
actual machine literals; no exact-real arithmetic hypothesis is required.

## Main results

* `NLAlib.SpectralBisection.BottomOutput`: the mathematical identity and zero output.
* `NLAlib.SpectralBisection.writes_bottomResult`: total initialization from disjoint capacity.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The stored identity and zero eigenvalues, without any metadata obligation. -/
def BottomOutput {K : Type} (M : Machine K) (k : ℕ) (u e : ℕ × ℕ) (s : Store K) : Prop :=
  s.HoldsEntries (EntryCodec.pair K) ⟨u.1, u.2, k, k, k⟩
    (fun i j => (if i = j then M.lit 1 else M.lit 0, M.lit 0)) ∧
  s.HoldsVec e.1 e.2 k (fun _ => M.lit 0)

/-- The boundary predicate exposes the two actual packed mathematical output blocks. -/
theorem BottomOutput.readBlocks {K : Type} {M : Machine K} {k : ℕ} {u e : ℕ × ℕ}
    {s : Store K} (h : BottomOutput M k u e s) (pos : ℕ) :
    (Mem.mk s pos).readBlocks [u, e] [2 * (k * k), k] =
      some [(EntryCodec.pair K).packFinMatrix (Matrix.of fun (i j : Fin k) =>
        (if i = j then M.lit 1 else M.lit 0, M.lit 0)), List.replicate k (M.lit 0)] := by
  have hu := h.1.readBlock_packFinMatrix rfl
  have he := Store.holdsVec_iff_readBlock.mp h.2
  have hu' : s.readBlock u.1 u.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix (Matrix.of fun (i j : Fin k) =>
        (if i = j then M.lit 1 else M.lit 0, M.lit 0))) := by
    simpa only [Nat.mul_comm, EntryCodec.pair, Fin.val_inj] using hu
  have he' : s.readBlock e.1 e.2 k = some (List.replicate k (M.lit 0)) := by
    simpa using he
  simp [Mem.readBlocks, hu', he']

/-- The recursion-boundary output reads only its matrix and eigenvalue regions. -/
theorem readsOnly_bottomOutput {K : Type} (M : Machine K) (k : ℕ) (u e : ℕ × ℕ) :
    Store.ReadsOnly (Store.inBlock u.1 u.2 (2 * (k * k)) ⊔ Store.inBlock e.1 e.2 k)
      (BottomOutput M k u e) := by
  intro s s' h ⟨hU, hE⟩
  exact ⟨Store.readsOnly_holdsEntries (EntryCodec.pair K) _ _ le_rfl
      s s' (fun b i hi => h b i (Or.inl hi)) hU,
    Store.readsOnly_holdsVec _ _ _ _ s s' (fun b i hi => h b i (Or.inr hi)) hE⟩

/-- Literal identity and zero eigenvalues are initialized from output capacity alone. -/
theorem writes_bottomResult {K Op Tst : Type} [Has ScalarOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K}
    {m : Mem K} {k : ℕ} {u e : ℕ × ℕ} (hl : m.Live [u, e])
    (hu : u.2 + 2 * (k * k) ≤ m.store.len u.1) (he : e.2 + k ≤ m.store.len e.1)
    (hdis : Fp.Disj (Store.inBlock u.1 u.2 (2 * (k * k))) (Store.inBlock e.1 e.2 k)) :
    Writes .total I τ (bottomResultImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [k] [u, e])
      (Store.inBlock u.1 u.2 (2 * (k * k)) ⊔ Store.inBlock e.1 e.2 k)
      (fun m' => m'.pos = m.pos ∧ BottomOutput M k u e m'.store) m := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  refine (writes_frame rfl rfl (by room) (PairMatrix.writes_identity hS hu)).seq
    fun m₁ hfr ⟨hU, hp⟩ => ?_
  have hU' := PairMatrix.holdsEntries_of_holdsVec hU
  have hz : e.2 + k ≤ m₁.store.len e.1 := by rw [hfr.len_eq]; exact he
  have hfill := writes_fill (n := .var 0) (N := k) (b := e.1) (o := e.2)
    (md := .total) (m := m₁) (τ := τ) (ρ := Env.frame [k] [u, e])
    (body := .call (Has.inj (ScalarOp.lit 0)) [] [] [⟨1, .var 2 + .var 3⟩])
    rfl (fun _ => M.lit 0) (fun _ => m₁.pos) rfl
    (fun i hi m' hfr' _ hpos => by
      have hc : e.2 + i < m'.store.len e.1 := by rw [hfr'.len_eq]; omega
      refine wp_call_const (hS (.lit 0)) rfl rfl rfl trivial hc ?_
      exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
        Store.get_upd_self hc _, hpos⟩)
  refine (hfill.keep (Store.readsOnly_holdsEntries (EntryCodec.pair K) _ _ le_rfl)
    hdis.symm hU').mono le_rfl ?_
  rintro m' _ ⟨⟨hE, hp'⟩, hU''⟩
  exact ⟨hp'.trans hp, hU'', hE⟩

end NLAlib.SpectralBisection
