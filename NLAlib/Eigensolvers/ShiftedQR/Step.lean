/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Sweep

/-!
# Total exact scalar shifted QR step

Initialization and the Givens sweep compute the existing mathematical shifted step. The
working matrix and coefficient arena are allocated by the program and released on return.
The input matrix and shift are arbitrary actual words; singular shifts and vanishing working
columns do not require a successful-execution hypothesis.

## Main results

* `NLAlib.ShiftedQR.shiftedStep_writes_of_sweep`: the step on any machine, from its sweep.
* `NLAlib.ShiftedQR.shiftedStep_writes`: exact output in surviving supplied storage.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- The frame of the scalar step on any machine: initialization stores the machine shift
(`NLAlib.ShiftedQR.machineShiftedPrefix`) in a fresh working matrix and the raw matrix in the
output, and allocates the coefficient arena. If every run of the sweep from such a state ends
with the output holding a matrix with the property `P`, so does the step. Its output is supplied
uninitialized capacity; all temporary buffers are scoped. -/
theorem shiftedStep_writes_of_sweep {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop}
    (hl : m.Live [a, s, z]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsweep : ∀ (m₁ : Mem ℝ) (w cf : ℕ × ℕ),
      HoldsMatrix w (machineShiftedPrefix M H shift (n + 1)) m₁.store →
      HoldsMatrix z H m₁.store → cf.2 + 4 ≤ m₁.store.len cf.1 →
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) →
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock cf.1 cf.2 4) →
      Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock cf.1 cf.2 4) →
      m₁.Live [w, z, cf, w, z] →
      Writes .total I τ sweep.body (Env.frame [n + 1] [w, z, cf, w, z])
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock cf.1 cf.2 4)
        (fun m' => m'.pos = m₁.pos ∧ ∃ H', P H' ∧ HoldsMatrix z H' m'.store) m₁) :
    Writes .total I τ shiftedStep.body (Env.frame [n + 1] [a, s, z])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => m'.pos = m.pos ∧ ∃ H', P H' ∧ HoldsMatrix z H' m'.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ z.1 < m.store.length := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 4] _)
    _ _ _ m
  refine writes_allocs_preserving_post (ns := [2 * ((n + 1) * (n + 1)), 4]) rfl
    (fun hBelow ⟨hp, H', hP, hH'⟩ => ⟨hp, H', hP, hH'.of_below hBelow hlive.2.2⟩) ?_
  intro store hlen hlens hBelow
  let w : ℕ × ℕ := (m.store.length, 0)
  let cf : ℕ × ℕ := (m.store.length + 1, 0)
  have hw : store.len w.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [w] using hlens 0 (by simp)
  have hcf : store.len cf.1 = 4 := by
    simpa [cf] using hlens 1 (by simp)
  have haw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hsw : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [w]; omega)
  have hwc : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne (by dsimp [w, cf]; omega)
  have hzc : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock cf.1 cf.2 4) :=
    Fp.disj_inBlock_of_ne (by dsimp [cf]; omega)
  have hinit := initializeState_writes_word (τ := τ) (m := ⟨store, m.pos⟩)
    (a := a) (s := s) (w := w) (z := z) hS
    (by simp [Mem.Live, w, hlen]; omega) (hH.of_below hBelow hlive.1)
    ((hBelow.readBlock hlive.2.1 _ _).trans hs)
    (by dsimp [w]; simpa only [Nat.zero_add] using hw.ge)
    (by rw [(hBelow z.1 hlive.2.2).1]; exact hz) haw haz hsw hsz hwz
  refine hinit.frame_seq_le rfl rfl
    (by simp [Mem.Live, w, hlen]; omega)
    (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left) ?_
  intro m₁ hfr₁ ⟨hp₁, hW₁, hZ₁⟩
  have hsw := hsweep m₁ w cf hW₁ hZ₁
    (by rw [hfr₁.len_eq]; dsimp [cf]; simpa only [Nat.zero_add] using hcf.ge)
    hwz hwc hzc (by simp [Mem.Live, w, cf, hfr₁.length_eq, hlen]; omega)
  refine (hsw.in_frame rfl rfl
    (by simp [Mem.Live, w, cf, hfr₁.length_eq, hlen]; omega)).mono
    (sup_le (sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left)
      (Fp.inBlock_le_sup_above (by dsimp [cf]; omega))) ?_
  intro m₂ _ ⟨hp₂, hZ₂⟩
  exact ⟨hp₂.trans hp₁, hZ₂⟩

/-- The exact scalar program returns the shifted QR step of the actual raw matrix and shift.
Its output is supplied uninitialized capacity. All temporary buffers are scoped; no safe-run
or nonzero-pivot assumption is needed. -/
theorem shiftedStep_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, z]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ shiftedStep.body (Env.frame [n + 1] [a, s, z])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix z (shiftedQRStep H shift) m'.store) m := by
  refine (shiftedStep_writes_of_sweep (P := (· = shiftedQRStep H shift)) hS hl hH hs hz haz hsz
    fun m₁ w cf hW hZ hc hwz hwc hzc hl₁ => ?_).mono le_rfl
    fun _ _ ⟨hp, _, rfl, hZ⟩ => ⟨hp, hZ⟩
  rw [machineShiftedPrefix_eq hE, shiftedPrefix_all] at hW
  refine (sweep_writes (τ := τ) hS hE hCmp hW hZ hc hwz hwc hzc hl₁).mono le_rfl
    fun _ _ ⟨hp, _, hZ'⟩ => ⟨hp, _, ?_, hZ'⟩
  rw [shiftedQRStep_eq_conj_givensHessenbergState, Nat.add_sub_cancel]

end NLAlib.ShiftedQR
