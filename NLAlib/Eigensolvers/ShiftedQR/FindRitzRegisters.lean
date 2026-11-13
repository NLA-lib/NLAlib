/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzAlg
public import NLAlib.Eigensolvers.ShiftedQR.FindRitzMath

/-!
# Exact natural search indices in actual scalar words

The first three workspace cells hold the window start, natural half length and exponent.
Each update is an ordinary dimension-literal operation, read back by the standard bounded
index query. Exact arithmetic supplies its natural-literal decoding law.

## Main results

* `NLAlib.ShiftedQR.SearchWords`: the three actual readable index words.
* `NLAlib.ShiftedQR.findRitzInitialize_writes`: initialization of the search indices.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The actual window start, half length and exponent in the first three workspace words. -/
def SearchWords (r : ℕ × ℕ) (a h e : ℕ) (s : Store ℝ) : Prop :=
  s.get r.1 r.2 = some (a : ℝ) ∧ s.get r.1 (r.2 + 1) = some (h : ℝ) ∧
    s.get r.1 (r.2 + 2) = some (e : ℝ)

/-- Search index words read only their three-cell prefix. -/
theorem readsOnly_searchWords (r : ℕ × ℕ) (a h e : ℕ) :
    Store.ReadsOnly (Store.inBlock r.1 r.2 3) (SearchWords r a h e) := by
  exact ((Store.readsOnly_get r.1 r.2 (a : ℝ)).and
    ((Store.readsOnly_get r.1 (r.2 + 1) (h : ℝ)).and
      (Store.readsOnly_get r.1 (r.2 + 2) (e : ℝ)))).mono (by fp_sub)

variable {Op Tst : Type} [Has IndexOp Op]

/-- An actual dimension-literal operation stores the natural as an exact real word. -/
theorem writes_indexNat {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ} {ρ : Env}
    {e : IExp} {out : Operand} {n : ℕ} {z : ℕ × ℕ}
    (he : e.eval ρ.idx = some n) (ho : out.eval ρ = some z)
    (hz : z.2 < m.store.len z.1) :
    Writes .total I τ (.call (Has.inj IndexOp.lit) [e] [] [out]) ρ
      (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (n : ℝ)) m := by
  have hlit : M.lit (n : ℚ) = (n : ℝ) := by simpa using hE.lit (n : ℚ)
  exact (writes_indexLit hL he ho hz).mono le_rfl
    (fun _ _ h => ⟨h.1, by simpa only [hlit] using h.2⟩)

/-- Actual index literal calls initialize the first window, natural half length and exponent.
The remaining three workspace cells need not be initialized. -/
theorem findRitzInitialize_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {k : ℕ} {r : ℕ × ℕ} (hr : r.2 + 3 ≤ m.store.len r.1) :
    Writes .total I τ findRitzInitialize.body (Env.frame [k] [r, r])
      (Store.inBlock r.1 r.2 3)
      (fun m' => m'.pos = m.pos ∧ SearchWords r 0 (k / 2) 1 m'.store) m := by
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (writes_indexNat hL hE rfl rfl (by change r.2 < m.store.len r.1; omega))
    (by fp_sub) fun m' hfr ⟨hp, hzero⟩ => ?_
  refine Writes.seq_le (writes_indexNat hL hE rfl rfl (by
    change r.2 + 1 < m'.store.len r.1
    rw [hfr.len_eq]
    omega))
    (by fp_sub) fun m'' hfr' ⟨hp', hhalf⟩ => ?_
  have hzero' := hfr'.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hzero
  refine (writes_indexNat hL hE rfl rfl (by
    change r.2 + 2 < m''.store.len r.1
    rw [hfr'.len_eq, hfr.len_eq]
    omega)).mono
    (by fp_sub) ?_
  intro m''' hfr'' ⟨hp'', hone⟩
  refine ⟨hp''.trans (hp'.trans hp), ?_⟩
  exact ⟨hfr''.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_inBlock_of_le (by omega)).symm hzero',
    hfr''.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hhalf, hone⟩

end NLAlib.ShiftedQR
