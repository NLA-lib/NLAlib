/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Storage

/-!
# Read footprints of stored mathematical levels

Stored levels depend on their matrix region, actual size words and parameter pair. The size
region retains the root size word for an empty problem by using `max n 1` words.

## Main results

* `NLAlib.SpectralBisection.levelInputFp`: the complete input read footprint.
* `NLAlib.SpectralBisection.StoresLevel.of_eqOff_input`: preserve a level through disjoint writes.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A level's matrix, size and parameter reads, including the empty-root size word. -/
def levelInputFp (n d : ℕ) (ma sz lv : ℕ × ℕ) : Fp :=
  Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d) (2 * (n * n)) ⊔
    (Store.inBlock sz.1 (sz.2 + n * d) (max n 1) ⊔
      Store.inBlock lv.1 (lv.2 + 2 * d) 2)

/-- A complete canonical-root level reads only its declared matrix, size and parameter words. -/
theorem readsOnly_storesLevel_input {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (n fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : ℕ) (ma sz lv : ℕ × ℕ) (pos : ℕ) :
    Store.ReadsOnly (levelInputFp n d ma sz lv)
      (fun s => StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv ⟨s, pos⟩) := by
  intro s s' heq h
  refine ⟨?_, ?_, ?_⟩
  · intro a lo x ha hx
    have hb := add_k_le_and_of_eighLoc hx
    have hlo : lo < max n 1 := by
      by_cases hn : n = 0
      · omega
      · have hp := hb.2 (by omega); omega
    have hm := Nat.mul_le_mul_left (2 * x.k) (show x.k ≤ n by omega)
    have hs := Nat.mul_le_mul_left (2 * n) hb.1
    have hMat : Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
        (2 * (x.k * x.k)) ≤ Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d) (2 * (n * n)) := by
      apply Fp.inBlock_le_inBlock (by omega)
      nlinarith
    have hr := h.1 a lo x ha hx
    refine ⟨(heq sz.1 _ (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩))).trans hr.1, ?_⟩
    apply (Store.readBlock_congr ?_).trans hr.2
    intro j hj
    exact heq ma.1 _ (Or.inl (hMat _ _ ⟨rfl, by omega, by omega⟩))
  · intro lo hlo ha
    exact (heq sz.1 _ (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩))).trans (h.2.1 lo hlo ha)
  · apply (Store.readBlock_congr ?_).trans h.2.2
    intro j hj
    exact heq lv.1 _ (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩))

/-- A disjoint write preserves every actual input word of a stored mathematical level. -/
theorem StoresLevel.of_eqOff_input {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d : ℕ} {R0 eps beta : K} {ell : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {ma sz lv : ℕ × ℕ}
    {m m' : Mem K} {G : Fp} (hfr : m.store.EqOff G m'.store)
    (hdis : Fp.Disj G (levelInputFp n d ma sz lv))
    (h : StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv m) :
    StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv m' :=
  hfr.keep (readsOnly_storesLevel_input M F n fuel R0 eps beta ell A d ma sz lv m.pos) hdis h

end NLAlib.SpectralBisection
