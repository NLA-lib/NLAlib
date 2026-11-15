/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FinishSearch

/-!
# Exact three-phase candidate search from initialized registers

A zero flag starts the actual stored Ritz loop. The completed prefix state then feeds the
promising/grid/fallback computation. Registers and trial matrix are implementation-owned
fresh scratch of the enclosing iteration; the input matrix is retained throughout the search.

## Main results

* `NLAlib.ShiftedQR.completeSearchWith_writes`: exact scalar strategy search and fallback.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- All three search phases return the defined mathematical shifted-step matrix. Raw test
words are initialized before the call, while the matrix output may be entirely uninitialized.
The statement covers a rejected full candidate list by computing its genuine fallback. -/
theorem completeSearchWith_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {F : Impl O Q} (hF : RitzSearchContract F I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m D : ℕ} {w ss c r z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B θ α γ : ℝ} {shifts : List ℂ}
    (hHess : IsUpperHessenberg H) (hlen : shifts.length = 2 ^ m) (hk : 2 ^ m ≤ n)
    (hτ : 0 ≤ τ) (hDp : 0 < D)
    (hD : D = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hH : HoldsMatrix w H μ.store) (hSS : HoldsMatrix ss (shiftColumn shifts) μ.store)
    (hThreshold : μ.store.get c.1 c.2 = some (τ ^ 2))
    (hTarget : μ.store.get r.1 (r.2 + 1) =
      some ((1 - γ) ^ (2 * (2 ^ m)) * subdiagNormSqProd (2 ^ m) H))
    (hRadius : μ.store.get r.1 (r.2 + 2) =
      some (exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H)))
    (hFlag : μ.store.get r.1 (r.2 + 3) = some 0)
    (hl : μ.Live [w, ss, c, r, z]) (hr : r.2 + 8 ≤ μ.store.len r.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len z.1)
    (hFreshR : r.1 ≠ w.1 ∧ r.1 ≠ ss.1 ∧ r.1 ≠ c.1 ∧ r.1 ≠ z.1)
    (hFreshZ : z.1 ≠ w.1 ∧ z.1 ≠ ss.1 ∧ z.1 ≠ c.1) :
    Writes .total I tape (completeSearchWith F).body
      (Env.frame [n + 1, m, 2 ^ m, D] [w, ss, c, r, z, r])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 8)
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix z (shqrAcceptStep τ B θ α γ m H shifts) μ'.store) μ := by
  rcases hFreshR with ⟨hrw, hrss, hrc, hrz⟩
  rcases hFreshZ with ⟨hzw, hzss, hzc⟩
  have hwl := hl w (by simp)
  have hssl := hl ss (by simp)
  have hcl := hl c (by simp)
  have hrl := hl r (by simp)
  have hzl := hl z (by simp)
  have hStart : CandidateHolds τ γ (2 ^ m) H [] z (r.1, r.2 + 3) μ.store := hFlag
  have hStored := searchStoredWithScratch_writes (τp := tape) (m := μ) (before := [])
    (a := w) (ss := ss) (t := c) (target := (r.1, r.2 + 1))
    (s := (r.1, r.2 + 6)) (z := z) (f := (r.1, r.2 + 3))
    hS hE hL hC hk hτ hH hSS hThreshold hTarget hStart (by room)
    (by dsimp only; omega) hz (by dsimp only; omega) (by disjoint) (by disjoint)
  unfold completeSearchWith
  refine hStored.frame_seq_le (by rw [hlen]; rfl) rfl (by room) (by fp_sub) ?_
  intro μ₁ hfr ⟨hp, hState⟩
  have hH₁ := hH.of_eqOff hfr (by disjoint)
  have hSS₁ := hSS.of_eqOff hfr (by disjoint)
  have hT₁ := hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hThreshold
  have hTarget₁ := hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hTarget
  have hRadius₁ := hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hRadius
  have hFinish := finishRitzSearchWith_writes (tape := tape) (μ := μ₁) hS hE hL hC hF
    hHess hlen hk hτ hDp hD hH₁ hSS₁ hT₁ hTarget₁ hRadius₁
    (by simpa only [List.nil_append] using hState) (hl.congr hfr.length_eq)
    (by rw [hfr.len_eq]; exact hr) (by rw [hfr.len_eq]; exact hz)
    ⟨hrw, hrss, hrc, hrz⟩ ⟨hzw, hzss, hzc⟩
  refine (hFinish.in_frame rfl rfl (by room)).mono le_rfl ?_
  intro μ₂ _ ⟨hp', hZ⟩
  exact ⟨hp'.trans hp, hZ⟩

end NLAlib.ShiftedQR
