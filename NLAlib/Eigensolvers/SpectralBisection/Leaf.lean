/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Total output guarantees for spectral bisection leaves

Leaves use the actual machine literals and stored diagonal words. Their execution needs readable
input and writable, disjoint output blocks, with the functional scalar and dimension-literal
contracts. No spectral assumption, rounding estimate or successful-execution premise is needed.

## Main results

* `NLAlib.SpectralBisection.writes_leafValues`: stored real diagonal words or literal zeros.
* `NLAlib.SpectralBisection.writes_leaf`: complete stored identity, eigenvalues and node kind.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst K : Type} [Has ScalarOp Op]

/-- A leaf's eigenvalues are copied from its stored real diagonal or initialized to literal
zero. A readable source and disjoint output capacity suffice for total execution. -/
theorem writes_leafValues {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    (diagonal : Bool) {τ : Tape K} {m : Mem K} {n : ℕ} {a e : ℕ × ℕ} {v : ℕ → K}
    (ha : m.store.HoldsVec a.1 a.2 (2 * (n * n)) v)
    (he : e.2 + n ≤ m.store.len e.1)
    (hdisj : Fp.Disj (Store.inBlock e.1 e.2 n) (Store.inBlock a.1 a.2 (2 * (n * n)))) :
    Writes .total I τ (leafValues (Op := Op) (Tst := Tst) diagonal)
      (Env.frame [n] [a, e]) (Store.inBlock e.1 e.2 n)
      (fun m' => m'.store.HoldsVec e.1 e.2 n
        (fun i => if diagonal then v (2 * (i * n + i)) else M.lit 0) ∧ m'.pos = m.pos) m := by
  cases diagonal with
  | true => exact PairMatrix.writes_diagonalReal hI ha he hdisj
  | false =>
    refine writes_fill rfl (fun _ => M.lit 0) (fun _ => m.pos) rfl
      fun i hi m' hfr _ hpos => ?_
    have hz : e.2 + i < m'.store.len e.1 := by rw [hfr.len_eq]; omega
    refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial hz ?_
    exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
      Store.get_upd_self hz _, hpos⟩

/-- Every leaf writes its complete identity, its eigenvalue vector and the literal leaf kind.
The pairwise apartness includes the source matrix and all three outputs. These are total
functional guarantees for actual machine words, with no arithmetic-accuracy hypothesis. -/
theorem writes_leaf [Has IndexOp Op] {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    (hL : IsIndexLit M I) (diagonal : Bool) {τ : Tape K} {m : Mem K} {n : ℕ}
    {a u e kind : ℕ × ℕ} {v : ℕ → K} (hl : m.Live [a, u, e, kind])
    (ha : m.store.HoldsVec a.1 a.2 (2 * (n * n)) v)
    (hu : u.2 + 2 * (n * n) ≤ m.store.len u.1) (he : e.2 + n ≤ m.store.len e.1)
    (hk : kind.2 < m.store.len kind.1)
    (hap : Fp.Apart [u, e, kind, a] [2 * (n * n), n, 1, 2 * (n * n)]) :
    Writes .total I τ (leaf (Op := Op) (Tst := Tst) diagonal)
      (Env.frame [n] [a, u, e, kind])
      (Store.inBlock u.1 u.2 (2 * (n * n)) ⊔
        (Store.inBlock e.1 e.2 n ⊔ Store.inBlock kind.1 kind.2 1))
      (fun m' => m'.store.HoldsVec u.1 u.2 (2 * (n * n))
          (fun q => if ∃ j < n, q = 2 * (j * n + j) then M.lit 1 else M.lit 0) ∧
        m'.store.HoldsVec e.1 e.2 n
          (fun i => if diagonal then v (2 * (i * n + i)) else M.lit 0) ∧
        m'.store.get kind.1 kind.2 = some (M.lit 1) ∧ m'.pos = m.pos) m := by
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
    Fp.disj_bot_right, and_true] at hap
  obtain ⟨⟨hUE, hUK, hUA⟩, ⟨hEK, hEA⟩, -⟩ := hap
  have hU := writes_frame (τ := τ) (ρ := Env.frame [n] [a, u, e, kind])
    (ds := [.var 0]) (args := [⟨1, .var 2⟩]) rfl rfl (show m.Live [u] from fun z hz => hl z (by
      obtain rfl := List.mem_singleton.mp hz
      simp))
    (PairMatrix.writes_identity hI hu)
  refine hU.seq fun m₁ hfr₁ ⟨hU₁, hp₁⟩ => ?_
  have hA₁ := hfr₁.keep (Store.readsOnly_holdsVec a.1 a.2 (2 * (n * n)) v) hUA ha
  have hE := writes_frame (τ := τ) (ρ := Env.frame [n] [a, u, e, kind])
    (ds := [.var 0]) (args := [⟨0, .var 1⟩, ⟨2, .var 3⟩]) rfl rfl
    (show m₁.Live [a, e] from (fun z hz => by
      rw [hfr₁.length_eq]
      exact hl z (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with rfl | rfl <;> simp)))
    (writes_leafValues hI diagonal hA₁ (by rwa [hfr₁.len_eq]) hEA)
  refine (hE.keep (Store.readsOnly_holdsVec u.1 u.2 (2 * (n * n)) _) hUE.symm hU₁).seq
    fun m₂ hfr₂ ⟨⟨hE₂, hp₂⟩, hU₂⟩ => ?_
  have hK := writes_indexLit (τ := τ) (ρ := Env.frame [n] [a, u, e, kind])
    (e := .const 1) (out := ⟨3, .var 4⟩) hL (n := 1) rfl rfl (by
    rw [hfr₂.len_eq, hfr₁.len_eq]
    exact hk)
  refine ((hK.keep (Store.readsOnly_holdsVec u.1 u.2 (2 * (n * n)) _) hUK.symm hU₂).keep
    (Store.readsOnly_holdsVec e.1 e.2 n _) hEK.symm hE₂).mono le_rfl ?_
  intro m₃ _ ⟨⟨⟨hp₃, hK₃⟩, hU₃⟩, hE₃⟩
  exact ⟨hU₃, hE₃, hK₃, hp₃.trans (hp₂.trans hp₁)⟩

end NLAlib.SpectralBisection
