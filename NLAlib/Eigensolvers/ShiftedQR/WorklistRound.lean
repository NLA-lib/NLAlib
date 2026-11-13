/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RangeProcess

/-!
# Popping and processing the actual active range

A positive stored count supplies a nonempty mathematical worklist. The program copies its top
pair, bounded-reads both actual natural words, and calls the proven size-selected range
processor. Its total proof advances the full invariant without a successful-execution premise.

## Main results

* `NLAlib.ShiftedQR.worklistRound_writes`: one actual range pop and processing visit.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has IdxTst Q]

/-- The actual top range is bounded-read and processed under the global input hypotheses.
Persistent geometry supplies capacity for the stack, output and scratch before execution. -/
theorem worklistRound_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I) (hQ : IsToNat id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n j count m F M : ℕ} {a p stack out w r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ B α γ δ g : ℝ}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hInv : WorklistInv H τ a stack out j μ)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hCount : μ.store.get stack.1 stack.2 = some (count : ℝ)) (hpos : 0 < count) :
    Writes .total I tape (worklistRound D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [a, p, stack, out, w, r])
      (worklistFp (n + 1) a stack out w r)
      (fun μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out (j + 1) μ') μ := by
  obtain ⟨active, done, A, roots, ε, hDefl, hA, hOut, hStack, hε, hj⟩ := hInv
  cases active with
  | nil =>
    have hc0 : μ.store.get stack.1 stack.2 = some (0 : ℝ) := by simpa using hStack.1
    have he : count = 0 := by exact_mod_cast Option.some.inj (hCount.symm.trans hc0)
    omega
  | cons range rest =>
    rcases range with ⟨lo, d⟩
    have hbounds := hDefl.active_block (r := (lo, d)) List.mem_cons_self
    have hlo : lo ≤ n + 1 := by have := hbounds.2.1; omega
    have hd : d ≤ n + 1 := by have := hbounds.2.1; omega
    have hcap : rest.length + 1 ≤ n + 1 := by
      have hb := hDefl.length_le
      simp only [List.length_append, List.length_cons] at hb
      omega
    have htop : StackHolds stack (rest.reverse ++ [(lo, d)]) μ.store := by
      simpa only [List.reverse_cons] using hStack
    have hRS : Fp.Disj (Store.inBlock r.1 r.2 2)
        (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1))) := by
      have hfull : Fp.Disj (Store.inBlock r.1 r.2 5)
          (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1))) := by
        simpa using hG.disj 5 2 (by omega)
      exact hfull.mono (by fp_sub) le_rfl
    have hw := rangePop_writes (τ := tape) hS hL hQ hE htop
      (by simpa using hcap) (by simpa only [Nat.add_assoc] using hG.room.2.2.1)
      (by have hb := hG.room.2.2.2.2.2.1; omega)
      (by simpa [Mem.Live] using And.intro (hG.live stack (by simp)) (hG.live r (by simp))) hRS
    unfold worklistRound
    refine hw.frame_seq_le rfl rfl
      (by simpa [Mem.Live] using And.intro (hG.live stack (by simp)) (hG.live r (by simp)))
      (by fp_sub [worklistFp]) ?_
    intro μ₁ hfr₁ ⟨hp₁, hSt₁, hRange⟩
    have hG₁ := hG.of_eqOff hfr₁
    have hprotect := hG.disj_pop.mono
      (by fp_sub : Store.inBlock stack.1 stack.2 1 ⊔ Store.inBlock r.1 r.2 2 ≤ _) le_rfl
    have hA₁ := hA.of_eqOff hfr₁ (hprotect.mono le_rfl (by fp_sub))
    have hParams₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
      (hprotect.mono le_rfl (by fp_sub)) hParams
    have hOut₁ := hOut.of_eqOff hfr₁ (hprotect.mono le_rfl ((finishedFp_le
      (fun q hq => (hDefl.partition.2.1 q (List.mem_append_right _ hq)).2)).trans (by fp_sub)))
    have hLo : μ₁.store.get r.1 r.2 = some (lo : ℝ) := by
      simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
    have hSize : μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ) := by
      simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hLo rfl hlo ?_
    refine writes_bindIdx_of_decode_nat hQ rfl rfl hSize rfl hd ?_
    have hprocess := processRange_writes (tape := tape) hS hE hL hQ hK D hD hG₁ hDefl
      hGlobal hτ hM hA₁ hParams₁ hOut₁ hSt₁ hε hj
    refine (hprocess.in_frame rfl rfl hG₁.live).mono le_rfl ?_
    intro _ _ ⟨hp₂, hInv₂⟩
    exact ⟨hp₂.trans hp₁, hInv₂⟩

end NLAlib.ShiftedQR
