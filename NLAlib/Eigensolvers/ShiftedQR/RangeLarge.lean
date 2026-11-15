/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RangeSplit

/-!
# Decoupling and splitting a large active range

The quantitative assumptions of the global input imply rapid-decoupling hypotheses for the
actual active block. A fixed scalar implementation supplies the local decoupling word theorem;
the actual stored scan index is bounded-read before committing and splitting that block.

## Main results

* `NLAlib.ShiftedQR.processLarge_writes`: one large range advances the full invariant.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has IdxTst Q]

/-- Global raw spectral assumptions imply the local quantitative hypotheses before any
execution of the supplied decoupling implementation. -/
private theorem block_rapidDecouplingHyps {n d lo : ℕ}
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {τ ε B θ α γ δ g : ℝ} {m F : ℕ}
    (hInv : DeflationInv H ε ((lo, d + 1) :: rest) done A roots)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hε : ε = (((((lo, d + 1) :: rest) ++ done).length - 1 : ℕ) : ℝ) * τ) :
    RapidDecouplingHyps (subBlock A (lo, d + 1)) τ B θ α γ (δ / 2) m F := by
  have he : ((((lo, d + 1) :: rest) ++ done).length - 1) = rest.length + done.length := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [hτ]
  exact hInv.rapidDecouplingHyps hGlobal (by rw [hε, he, hτ])

/-- The actual large-range program decouples its raw block, binds the returned small-entry
index, and commits the resulting two children. The global assumptions concern the input
matrix and parameters; the decoupling proof is local to one fixed scalar implementation. -/
theorem processLarge_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I) (hQ : IsToNat id I)
    {θ : ℝ} (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n d lo j m F M : ℕ} {a p stack out w r : ℕ × ℕ}
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {τ ε B α γ δ g : ℝ} {rest done : List (ℕ × ℕ)}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hInv : DeflationInv H ε ((lo, d + 1) :: rest) done A roots)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hkn : 2 ^ m ≤ d) (hA : HoldsMatrix a A μ.store)
    (hW : HoldsMatrix w (subBlock A (lo, d + 1)) μ.store)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hOut : FinishedHolds out done roots μ.store) (hSt : StackHolds stack rest.reverse μ.store)
    (hε : ε = (((((lo, d + 1) :: rest) ++ done).length - 1 : ℕ) : ℝ) * τ)
    (hj : 2 * done.length + ((lo, d + 1) :: rest).length = j + 1) :
    Writes .total I tape (processLarge D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M, lo, d + 1] [a, p, stack, out, w, r])
      (worklistFp (n + 1) a stack out w r)
      (fun μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out (j + 1) μ') μ := by
  have hRapid := block_rapidDecouplingHyps hInv hGlobal hτ hε
  have hτ0 : 0 ≤ τ := by
    rcases hRapid with ⟨_, _, _, _, _, _, _, hδ, hδτ, _⟩
    exact (mul_nonneg hδ.le (specNorm_nonneg _)).trans hδτ
  have hMpos : 0 < M := by
    have hB := hRapid.one_le
    rcases hRapid with ⟨_, _, hθ, hα, _, _, hγ, _⟩
    have hb := one_le_ceil_sqrt_two_div_exceptionalSpacing hB hθ hα hγ m
    rw [← hM] at hb
    omega
  have hr := hInv.active_block (r := (lo, d + 1)) List.mem_cons_self
  have hd : d + 1 ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hscratch := hG.disj_scratch.mono
    (by fp_sub : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔
      Store.inBlock r.1 r.2 5 ≤ _) le_rfl
  have hWR : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))))
      (Store.inBlock r.1 r.2 5) := by
    have hfull : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock r.1 r.2 5) := by simpa using hG.disj 4 5 (by omega)
    exact hfull.mono (by fp_sub) le_rfl
  have hP : Fp.Disj (Store.inBlock p.1 p.2 5)
      (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock r.1 r.2 5) :=
    (hscratch.mono le_rfl (by fp_sub)).symm
  have hLiveD : μ.Live [w, p, w, r] := by
    simpa [Mem.Live] using (And.intro (hG.live w (by simp))
      (And.intro (hG.live p (by simp))
        (And.intro (hG.live w (by simp)) (hG.live r (by simp)))))
  have hw := hD (tape := tape) (subBlock A (lo, d + 1)) hr.2.2 hRapid hkn hτ0 hM hMpos
    hW hParams hLiveD
    (by have hw := hG.room.2.2.2.2.1; omega) hG.room.2.2.2.2.2.1 hWR hP
  unfold processLarge
  refine hw.frame_seq_le rfl rfl hLiveD
    (by fp_sub [worklistFp]) ?_
  intro μ₁ hfr₁ ⟨hp₁, U, H', hU, hH', hHess, hdec, hW₁, hScan⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hA₁ := hA.of_eqOff hfr₁ (hscratch.mono le_rfl (by fp_sub))
  have hrest : rest.length ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hSt₁ := hSt.of_eqOff hfr₁ (hscratch.mono le_rfl (by
    simp only [List.length_reverse]; fp_sub))
  have hOut₁ := hOut.of_eqOff hfr₁ (hscratch.mono le_rfl ((finishedFp_le
    (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)).trans (by fp_sub)))
  obtain ⟨i, hiWord, hiSmall⟩ := hScan.index_of_isDecoupledAbs hτ0 hdec
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hiWord rfl (by have := i.isLt; omega) ?_
  have hsplit := writeAndSplit_writes (tape := tape) hS hE hL hQ hG₁ hInv hA₁ hW₁
    hOut₁ hSt₁ hU hH' hHess hiSmall hε hj
  refine (hsplit.in_frame rfl rfl
    (by simpa [Mem.Live] using (And.intro (hG₁.live a (by simp))
      (And.intro (hG₁.live stack (by simp)) (hG₁.live w (by simp)))))).mono
    (by fp_sub [worklistFp]) ?_
  intro _ _ ⟨hp₂, hInv₂⟩
  exact ⟨hp₂.trans hp₁, hInv₂⟩

end NLAlib.ShiftedQR
