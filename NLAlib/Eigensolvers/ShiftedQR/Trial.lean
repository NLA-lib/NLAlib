/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.MultiStep
public import NLAlib.Eigensolvers.ShiftedQR.Acceptance

/-!
# Exact scalar trial of one candidate shift

The trial copies the original matrix, executes the prescribed number of actual single-shift
steps on the copy, and evaluates acceptance from its actual entries. The original matrix and
parameters survive for subsequent candidates. Trial output capacity starts uninitialized.

## Main results

* `NLAlib.ShiftedQR.trial`: one candidate's actual scalar computation.
* `NLAlib.ShiftedQR.trial_writes`: the computed matrix and exact mathematical acceptance flag.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Copy the input matrix, apply the same stored shift `k` times and test the resulting matrix.
The input threshold is τ² and the input target is the precomputed product-contraction target. -/
def trial : Impl Op Tst := opsImpl% [n, k] (A, S, Threshold, Target) → (Z, Flag) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (A, Z);
  run repeatedStep.body [n, k] (Z, S, Z);
  run acceptTrial.body [n, k] (Z, Threshold, Target, Flag)
}

open Classical in
/-- Every candidate trial returns its exact repeated-shift matrix and its zero/one acceptance
classification. A candidate is allowed to fail the acceptance test; total execution does not
require an invertible shifted matrix or a successful candidate. -/
theorem trial_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s t target z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} {τ γ : ℝ}
    (hk : k ≤ n) (hτ : 0 ≤ τ) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some ((1 - γ) ^ (2 * k) * subdiagNormSqProd k H))
    (hl : m.Live [a, s, t, target, z, f])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hf : f.2 < m.store.len f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock f.1 f.2 1))
    (hsep : Fp.Disj
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 2 ⊔ Store.inBlock t.1 t.2 1 ⊔
        Store.inBlock target.1 target.2 1)) :
    Writes .total I τp trial.body (Env.frame [n + 1, k] [a, s, t, target, z, f])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix z (multiShiftedQRStep H (List.replicate k shift)) m'.store ∧
        m'.store.get f.1 f.2 = some (if IsShiftAccept τ γ k H shift then (1 : ℝ) else 0)) m := by
  classical
  unfold trial
  have hcopy := copyMatrix_writes (τ := τp) hS hH hz
    (hsep.symm.mono (by fp_sub) le_sup_left)
  refine hcopy.frame_seq_le rfl rfl
    (by simpa [Mem.Live] using And.intro (hl a (by simp)) (hl z (by simp)))
    le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hZ₁⟩
  have hS₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
    (hsep.mono le_sup_left (by fp_sub)) hs
  have hT₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    (hsep.mono le_sup_left (by fp_sub)) ht
  have hTarget₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    (hsep.mono le_sup_left (by fp_sub)) hTarget
  have hstep := repeatedStep_writes (τ := τp) (m := m₁) (k := k) hS hE hC
    (by simpa [Mem.Live, hfr₁.length_eq] using
      And.intro (hl z (by simp)) (And.intro (hl s (by simp)) (hl z (by simp)))) hZ₁ hS₁
    (hsep.symm.mono (by fp_sub) le_sup_left)
  refine hstep.frame_seq_le rfl rfl
    (by simpa [Mem.Live, hfr₁.length_eq] using
      And.intro (hl z (by simp)) (And.intro (hl s (by simp)) (hl z (by simp)))) le_sup_left ?_
  intro m₂ hfr₂ ⟨hp₂, hZ₂⟩
  have hT₂ := hfr₂.keep (Store.readsOnly_get _ _ _)
    (hsep.mono le_sup_left (by fp_sub)) hT₁
  have hTarget₂ := hfr₂.keep (Store.readsOnly_get _ _ _)
    (hsep.mono le_sup_left (by fp_sub)) hTarget₁
  have haccept := acceptTrial_writes (τp := τp) (m := m₂) (f := f) hS hE hL hC
    hk hτ hZ₂ hT₂ hTarget₂ (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hf)
    (Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨hzf.symm, hsep.mono le_sup_right (by fp_sub)⟩,
        hsep.mono le_sup_right (by fp_sub)⟩)
  refine (haccept.in_frame rfl rfl
    (by simpa [Mem.Live, hfr₂.length_eq, hfr₁.length_eq] using
      And.intro (hl z (by simp)) (And.intro (hl t (by simp))
        (And.intro (hl target (by simp)) (hl f (by simp)))))).mono
    le_sup_right ?_
  intro m₃ hfr₃ ⟨hp₃, hFlag₃⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hZ₂.of_eqOff hfr₃ hzf.symm,
    by
      by_cases ha : IsShiftAccept τ γ k H shift
      · have ha' : IsDecoupledAbs τ (multiShiftedQRStep H (List.replicate k shift)) ∨
            subdiagNormSqProd k (multiShiftedQRStep H (List.replicate k shift)) ≤
              (1 - γ) ^ (2 * k) * subdiagNormSqProd k H := ha
        simpa only [if_pos ha, if_pos ha'] using hFlag₃
      · have ha' : ¬(IsDecoupledAbs τ (multiShiftedQRStep H (List.replicate k shift)) ∨
            subdiagNormSqProd k (multiShiftedQRStep H (List.replicate k shift)) ≤
              (1 - γ) ^ (2 * k) * subdiagNormSqProd k H) := ha
        simpa only [if_neg ha, if_neg ha'] using hFlag₃⟩

end NLAlib.ShiftedQR
