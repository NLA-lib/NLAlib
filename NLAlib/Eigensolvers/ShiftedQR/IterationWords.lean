/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.PrepareIteration
public import NLAlib.Eigensolvers.ShiftedQR.CompleteSearch

/-!
# Total word proof for a scalar strategy iteration

Preparation, exact three-phase search and copy-back compose through ordinary output blocks.
The two matrices, Ritz column and eight registers are actual scoped word storage. The
promising-search tree enters through its proved local implementation law; closed decoupling
substitutes the concrete scalar binary search.

## Main results

* `NLAlib.ShiftedQR.searchAndCopyWith_writes`: selected/default matrix copied back.
* `NLAlib.ShiftedQR.iterationWith_writes`: the complete scoped exact strategy iteration.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has CmpTst Q]

omit [Has EigenvalueKernelOp O] in
/-- Prepared search and actual copy-back return the exact mathematical strategy step. The
registers and trial matrix are fresh implementation workspace, not user input restrictions. -/
theorem searchAndCopyWith_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {F : Impl O Q} (hF : RitzSearchContract F I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m D : ℕ} {w ss c r z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B θ α γ : ℝ} {shifts : List ℂ}
    (hHess : IsUpperHessenberg H) (hlen : shifts.length = 2 ^ m) (hk : 2 ^ m ≤ n)
    (hτ : 0 ≤ τ) (hDp : 0 < D)
    (hD : D = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hH : HoldsMatrix w H μ.store) (hSS : HoldsMatrix ss (shiftColumn shifts) μ.store)
    (hCst : μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))])
    (hRegs : μ.store.readBlock r.1 r.2 4 = some [subdiagNormSqProd (2 ^ m) H,
      (1 - γ) ^ (2 * (2 ^ m)) * subdiagNormSqProd (2 ^ m) H,
      exceptionalRadius (2 ^ m) B θ α (hessenbergPotential (2 ^ m) H), 0])
    (hl : μ.Live [w, ss, c, r, z]) (hr : r.2 + 8 ≤ μ.store.len r.1)
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len z.1)
    (hFreshR : r.1 ≠ w.1 ∧ r.1 ≠ ss.1 ∧ r.1 ≠ c.1 ∧ r.1 ≠ z.1)
    (hFreshZ : z.1 ≠ w.1 ∧ z.1 ≠ ss.1 ∧ z.1 ≠ c.1) :
    Writes .total I tape (searchAndCopyWith F).body
      (Env.frame [n + 1, m, 2 ^ m, D] [w, ss, c, r, z, w, z, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 8)
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix w (shqrAcceptStep τ B θ α γ m H shifts) μ'.store) μ := by
  rcases hFreshR with ⟨hrw, hrss, hrc, hrz⟩
  rcases hFreshZ with ⟨hzw, hzss, hzc⟩
  have hwl := hl w (by simp)
  have hssl := hl ss (by simp)
  have hcl := hl c (by simp)
  have hrl := hl r (by simp)
  have hzl := hl z (by simp)
  have hComplete := completeSearchWith_writes (tape := tape) (μ := μ) hS hE hL hC hF
    hHess hlen hk hτ hDp hD hH hSS
    (by simpa using Store.get_of_readBlock hCst (j := 0) (by simp) (0 : ℝ))
    (by simpa using Store.get_of_readBlock hRegs (j := 1) (by simp) (0 : ℝ))
    (by simpa using Store.get_of_readBlock hRegs (j := 2) (by simp) (0 : ℝ))
    (by simpa using Store.get_of_readBlock hRegs (j := 3) (by simp) (0 : ℝ)) hl hr hz
    ⟨hrw, hrss, hrc, hrz⟩ ⟨hzw, hzss, hzc⟩
  unfold searchAndCopyWith
  refine hComplete.frame_seq_le rfl rfl (by room) (by fp_sub) ?_
  intro μ₁ hfr ⟨hp, hZ⟩
  have hw := Store.le_len_of_readBlock hH (by positivity)
  have hCopy := copyMatrix_writes (τ := tape) hS hZ
    (by rw [hfr.len_eq]; exact hw) (by disjoint)
  refine (hCopy.in_frame rfl rfl (by room)).mono (by fp_sub) ?_
  intro μ₂ _ ⟨hp', hW⟩
  exact ⟨hp'.trans hp, hW⟩

/-- The actual scalar iteration computes the mathematical three-phase shifted step of its
local Ritz routine, including fallback. All workspace is scoped; the raw matrix, parameter
and constant words are the only supplied data. -/
theorem iterationWith_writes {M : Machine ℝ} {I : Interp O Q ℝ} {eta : ℝ}
    {K : KernelRoutines eta} (hS : IsScalar M I) (hE : ExactModel id M)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (hK : IsEigenvalueKernels K I)
    {F : Impl O Q} (hF : RitzSearchContract F I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m D : ℕ} {w p c : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B θ α γ : ℝ}
    (hHess : IsUpperHessenberg H) (hk : 2 ^ m ≤ n) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hDp : 0 < D)
    (hD : D = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hH : HoldsMatrix w H μ.store)
    (hP : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hCst : μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))])
    (hl : μ.Live [w, p, c, w]) :
    Writes .total I tape (iterationWith F).body (Env.frame [n + 1, m, 2 ^ m, D] [w, p, c, w])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix w
        (shqrAcceptStep τ B θ α γ m H (K.ritz (n + 1) (2 ^ m) H)) μ'.store) μ := by
  have hwl := hl w (by simp)
  have hpl := hl p (by simp)
  have hcl := hl c (by simp)
  change Writes .total I tape (Stmt.allocs
    [.const 2 * .var 2, .const 8, .const 2 * (.var 0 * .var 0)] _) _ _ _ μ
  refine writes_allocs_preserving_post
    (ns := [2 * (2 ^ m), 8, 2 * ((n + 1) * (n + 1))]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hwl⟩) ?_
  intro store hlen hlens hBelow
  let ss : ℕ × ℕ := (μ.store.length, 0)
  let r : ℕ × ℕ := (μ.store.length + 1, 0)
  let z : ℕ × ℕ := (μ.store.length + 2, 0)
  have hSSlen : store.len ss.1 = 2 * (2 ^ m) := by simpa [ss] using hlens 0 (by simp)
  have hRlen : store.len r.1 = 8 := by simpa [r] using hlens 1 (by simp)
  have hZlen : store.len z.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [z] using hlens 2 (by simp)
  have hPrep := prepareIteration_writes (tape := tape) (μ := ⟨store, μ.pos⟩)
    (w := w) (p := p) (c := c) (ss := ss) (r := r) hS hE hL hK rfl hk hB
    (by simp [Mem.Live, ss, r, hlen]; omega) (hH.of_below hBelow hwl)
    (hBelow.readBlock_of hpl hP) (hBelow.readBlock_of hcl hCst)
    (by dsimp [ss]; simpa only [Nat.zero_add] using hSSlen.ge)
    (by dsimp [r]; rw [hRlen]; omega) (by dsimp [ss, r]; disjoint)
    (by dsimp [ss, r]; disjoint)
  refine hPrep.frame_seq_le rfl rfl (by simp [Mem.Live, ss, r, hlen]; omega)
    (sup_le (Fp.inBlock_le_sup_above le_rfl)
      (Fp.inBlock_le_sup_above (by dsimp [r]; omega))) ?_
  intro μ₁ hfr₁ ⟨hp₁, hSS, hRegs⟩
  have hH₁ := (hH.of_below hBelow hwl).of_eqOff hfr₁ (by dsimp [ss, r]; disjoint)
  have hC₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
    (by dsimp [ss, r]; disjoint) (hBelow.readBlock_of hcl hCst)
  have hSearch := searchAndCopyWith_writes (tape := tape) (μ := μ₁)
    (w := w) (ss := ss) (c := c) (r := r) (z := z) (n := n) (m := m) (D := D)
    (τ := τ) (B := B) (θ := θ) (α := α) (γ := γ) hS hE hL hC hF
    hHess (K.length_ritz _ _ _) hk hτ hDp hD hH₁ hSS hC₁ hRegs
    (by simp [Mem.Live, ss, r, z, hfr₁.length_eq, hlen]; omega)
    (by rw [hfr₁.len_eq]; dsimp [r]; simpa only [Nat.zero_add] using hRlen.ge)
    (by rw [hfr₁.len_eq]; dsimp [z]; simpa only [Nat.zero_add] using hZlen.ge)
    (by dsimp [ss, r, z]; omega) (by dsimp [ss, r, z]; omega)
  refine (hSearch.in_frame rfl rfl
    (by simp [Mem.Live, ss, r, z, hfr₁.length_eq, hlen]; omega)).mono
    (sup_le (sup_le le_sup_left (Fp.inBlock_le_sup_above (by dsimp [z]; omega)))
      (Fp.inBlock_le_sup_above (by dsimp [r]; omega))) ?_
  intro μ₂ _ ⟨hp₂, hW⟩
  exact ⟨hp₂.trans hp₁, hW⟩

end NLAlib.ShiftedQR
