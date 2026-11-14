/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RangeFinish
public import NLAlib.Eigensolvers.ShiftedQR.RangeLarge

/-!
# Total processing of an active range

The actual diagonal block is copied into workspace before either branch. Its runtime size
selects finishing by the local eigenvalue kernel or scalar decoupling followed by a split.
The two proven branches advance the same deflation, stored-stack and partial-output invariant.

## Main results

* `NLAlib.ShiftedQR.processRange_writes`: total range processing from raw global assumptions.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has IdxTst Q]

/-- The actual range processor copies the active diagonal block and advances the complete
invariant through the size-selected branch. The only substituted proof concerns the fixed
scalar decoupling implementation on one local matrix, under raw quantitative hypotheses. -/
theorem processRange_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I) (hQ : IsToNat id I)
    {θ : ℝ} {K : KernelRoutines θ} (hK : IsEigenvalueKernels K I)
    (D : Impl O Q) (hD : DecouplingContract θ D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n d lo j m F M : ℕ} {a p stack out w r : ℕ × ℕ}
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {τ ε B α γ δ g : ℝ} {rest done : List (ℕ × ℕ)}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hInv : DeflationInv H ε ((lo, d) :: rest) done A roots)
    (hGlobal : ShiftedQRHyps H B θ α γ δ g m F) (hτ : τ = δ * frobNorm H)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hA : HoldsMatrix a A μ.store)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hOut : FinishedHolds out done roots μ.store) (hSt : StackHolds stack rest.reverse μ.store)
    (hε : ε = (((((lo, d) :: rest) ++ done).length - 1 : ℕ) : ℝ) * τ)
    (hj : 2 * done.length + ((lo, d) :: rest).length = j + 1) :
    Writes .total I tape (processRange D).body
      (Env.frame [n + 1, m, 2 ^ m, F, M, lo, d] [a, p, stack, out, w, r])
      (worklistFp (n + 1) a stack out w r)
      (fun μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out (j + 1) μ') μ := by
  have hr := hInv.active_block (r := (lo, d)) List.mem_cons_self
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hAW : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * (d * d))) := by
    have hfull : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa using hG.disj 0 4 (by omega)
    exact hfull.mono le_rfl (by fp_sub)
  have hc := copyToWork_writes (τ := tape) (lo := lo) (d := d) hS
    (by simpa [Mem.Live] using And.intro (hG.live a (by simp)) (hG.live w (by simp)))
    hA hr.2.1 (by have hw := hG.room.2.2.2.2.1; omega) hAW
  unfold processRange
  refine hc.frame_seq_le rfl rfl
    (by simpa [Mem.Live] using And.intro (hG.live a (by simp)) (hG.live w (by simp)))
    (by fp_sub [worklistFp]) ?_
  intro μ₁ hfr₁ ⟨hp₁, hW₁⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hprotect := hG.disj_scratch.mono
    (by fp_sub : Store.inBlock w.1 w.2 (2 * (d * d)) ≤ _) le_rfl
  have hA₁ := hA.of_eqOff hfr₁ (hprotect.mono le_rfl (by fp_sub))
  have hParams₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
    (hprotect.mono le_rfl (by fp_sub)) hParams
  have hrest : rest.length ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hSt₁ := hSt.of_eqOff hfr₁ (hprotect.mono le_rfl (by
    simp only [List.length_reverse]; fp_sub))
  have hOut₁ := hOut.of_eqOff hfr₁ (hprotect.mono le_rfl ((finishedFp_le
    (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)).trans (by fp_sub)))
  by_cases hs : d ≤ 2 ^ m
  · have hfinish := finishActive_writes (tape := tape) hK hG₁ hInv hA₁ hW₁ hOut₁ hSt₁ hε hj
    refine (writes_ifPos
      (P := fun μ₂ => μ₂.pos = μ₁.pos ∧ WorklistInv H τ a stack out (j + 1) μ₂)
      (n := 2 ^ m + 1 - d) rfl ?_).seq_le le_rfl ?_
    · rw [if_pos (by omega)]
      exact (hfinish.in_frame rfl rfl
        (by simpa [Mem.Live] using (And.intro (hG₁.live w (by simp))
          (hG₁.live out (by simp))))).mono (by fp_sub [worklistFp]) (fun _ _ hp => hp)
    · intro μ₂ _ ⟨hp₂, hInv₂⟩
      refine writes_ifPos (n := d - 2 ^ m) rfl ?_
      rw [if_neg (by omega)]
      exact ⟨hp₂.trans hp₁, hInv₂⟩
  · refine (writes_ifPos (F := ⊥) (P := fun μ₂ => μ₂ = μ₁)
      (n := 2 ^ m + 1 - d) rfl (by rw [if_neg (by omega)])).seq_le bot_le ?_
    intro μ₂ _ he
    subst μ₂
    cases d with
    | zero => omega
    | succ d =>
      have hlarge := processLarge_writes (tape := tape) hS hE hL hQ D hD hG₁ hInv
        hGlobal hτ hM (by omega) hA₁ hW₁ hParams₁ hOut₁ hSt₁ hε hj
      refine writes_ifPos (n := d + 1 - 2 ^ m) rfl ?_
      rw [if_pos (by omega)]
      refine (hlarge.in_frame rfl rfl hG₁.live).mono le_rfl ?_
      intro _ _ ⟨hp₂, hInv₂⟩
      exact ⟨hp₂.trans hp₁, hInv₂⟩

end NLAlib.ShiftedQR
