/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Potential
public import NLAlib.Eigensolvers.ShiftedQR.Scan

/-!
# Exact acceptance test for a trial shifted QR matrix

A trial is accepted when it is decoupled or its squared-potential product is below the stored
target. Both tests inspect the actual trial matrix. The implementation uses the scalar scan
and scalar product loops, then compares their actual output words.

## Main results

* `NLAlib.ShiftedQR.ScanHolds.flag_eq`: exact zero/one interpretation of a completed scan.
* `NLAlib.ShiftedQR.acceptTrialWithScratch`: scalar implementation of the disjunction.
* `NLAlib.ShiftedQR.acceptTrialWithScratch_writes`: total exact acceptance classification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

open Classical in
/-- A completed scan stores the exact zero/one flag of mathematical absolute decoupling. -/
theorem ScanHolds.flag_eq {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ : ℝ} {r : ℕ × ℕ} {st : Store ℝ} (h : ScanHolds H (τ ^ 2) n r st) (hτ : 0 ≤ τ) :
    st.get r.1 (r.2 + 3) = some (if IsDecoupledAbs τ H then (1 : ℝ) else 0) := by
  classical
  rw [h.1]
  by_cases hd : IsDecoupledAbs τ H
  · have hs := (scanPrefix_isSome_iff_isDecoupledAbs H hτ).mpr hd
    simp only [hs, hd, if_true]
  · have hs := mt (scanPrefix_isSome_iff_isDecoupledAbs H hτ).mp hd
    simp [hs, hd]

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Inspect a trial matrix, calculate its squared-potential product and write its exact
acceptance flag. R has five caller-owned scan words and P one caller-owned product word. -/
def acceptTrialWithScratch : Impl Op Tst := opsImpl% [n, k] (A, Threshold, Target, R, P) → (Flag) {
  run scan.body [n] (A, Threshold, R);
  run subdiagProduct.body [n, k] (A, P);
  call (Has.inj ScalarOp.copy) [] (R[3]) → (Flag);
  if (Has.inj CmpTst.le) [] (P, Target) {
    call (Has.inj (ScalarOp.lit 1)) [] () → (Flag)
  } else { skip }
}

open Classical in
/-- Total acceptance classification from the actual supplied trial matrix and stored threshold
and target. Scratch, output and input separation concern real word regions, including views
of one arena. No assumption about which trial will pass is made. -/
theorem acceptTrialWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a t target r p f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ T : ℝ}
    (hk : k ≤ n) (hτ : 0 ≤ τ) (hH : HoldsMatrix a H m.store)
    (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some T)
    (hl : m.Live [a, t, target, r, p, f])
    (hr : r.2 + 5 ≤ m.store.len r.1) (hp : p.2 < m.store.len p.1)
    (hf : f.2 < m.store.len f.1)
    (hapart : Fp.Apart [r, p, f] [5, 1, 1])
    (hsep : Fp.Disj (Fp.blocks [r, p, f] [5, 1, 1])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 1 ⊔ Store.inBlock target.1 target.2 1)) :
    Writes .total I τp acceptTrialWithScratch.body
      (Env.frame [n + 1, k] [a, t, target, r, p, f]) (Fp.blocks [r, p, f] [5, 1, 1])
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 =
        some (if IsDecoupledAbs τ H ∨ subdiagNormSqProd k H ≤ T then (1 : ℝ) else 0)) m := by
  classical
  have hlscan : m.Live [a, t, r] := by
    simpa [Mem.Live] using
      And.intro (hl a (by simp)) (And.intro (hl t (by simp)) (hl r (by simp)))
  have hlprod : m.Live [a, p] := by
    simpa [Mem.Live] using And.intro (hl a (by simp)) (hl p (by simp))
  have hrp : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock p.1 p.2 1) := by
    simpa using hapart.disj_getD_of_lt (i := 0) (j := 1) (by decide) (by simp)
  have hpf : Fp.Disj (Store.inBlock p.1 p.2 1) (Store.inBlock f.1 f.2 1) := by
    simpa using hapart.disj_getD_of_lt (i := 1) (j := 2) (by decide) (by simp)
  have hscan := scan_writes (τ := τp) (m := m) (r := r) hS hE hL hC hH ht
    hlscan hr
    (hsep.mono (by fp_sub) (by fp_sub)) (hsep.mono (by fp_sub) (by fp_sub))
  unfold acceptTrialWithScratch
  refine hscan.frame_seq_le rfl rfl
    hlscan (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hScan⟩
  have hH₁ := hH.of_eqOff hfr₁ (hsep.mono (by fp_sub) (by fp_sub))
  have hT₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) hTarget
  have hFlag₁ := hScan.flag_eq hτ
  have hprod := subdiagProduct_writes (τ := τp) (m := m₁) (p := p) hS hE hk hH₁
    (by rw [hfr₁.len_eq]; exact hp) (hsep.symm.mono (by fp_sub) (by fp_sub))
  refine hprod.frame_seq_le rfl rfl
    (hlprod.congr hfr₁.length_eq)
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hP₂⟩
  have hFlag₂ := hfr₂.keep (Store.readsOnly_get _ _ _)
    (hrp.symm.mono le_rfl (by fp_sub)) hFlag₁
  have hT₂ := hfr₂.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) hT₁
  refine (writes_call_un (hS .copy) rfl rfl trivial hFlag₂ rfl
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hf)).seq_le (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hF₃⟩
  have hP₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hpf.symm hP₂
  have hT₃ := hfr₃.keep (Store.readsOnly_get _ _ _)
    (hsep.mono (by fp_sub) (by fp_sub)) hT₂
  refine writes_ite rfl rfl (hC.test_le (d := []) hP₃ hT₃) ?_
  simp only [id_eq, decide_eq_true_eq]
  by_cases hsmall : subdiagNormSqProd k H ≤ T
  · rw [if_pos hsmall]
    refine (writes_call_const (hS (.lit 1)) rfl trivial
      (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hf)).mono (by fp_sub) ?_
    intro m₄ _ ⟨hp₄, hF₄⟩
    have hone : M.lit 1 = (1 : ℝ) := by simpa using hE.lit 1
    exact ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), by simpa [hsmall, hone] using hF₄⟩
  · rw [if_neg hsmall]
    exact (Writes.skip (I := I) (τ := τp)
      ⟨hp₃.trans (hp₂.trans hp₁), by simpa only [hsmall, or_false] using hF₃⟩).mono
      bot_le (fun _ _ h => h)

/-- Scope five scan words and one product word, returning only the persistent acceptance flag. -/
def acceptTrial : Impl Op Tst := opsImpl% [n, k] (A, Threshold, Target) → (Flag) {
  let R ← alloc 5;
  let P ← alloc 1;
  run acceptTrialWithScratch.body [n, k] (A, Threshold, Target, R, P, Flag)
}

open Classical in
/-- The scoped acceptance test writes the exact zero/one result and removes all temporary
scan/product storage. Only the actual matrix, threshold and target words are consumed. -/
theorem acceptTrial_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {τp : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a t target f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {τ T : ℝ}
    (hk : k ≤ n) (hτ : 0 ≤ τ) (hH : HoldsMatrix a H m.store)
    (ht : m.store.get t.1 t.2 = some (τ ^ 2))
    (hTarget : m.store.get target.1 target.2 = some T)
    (hf : f.2 < m.store.len f.1)
    (hsep : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 1 ⊔ Store.inBlock target.1 target.2 1)) :
    Writes .total I τp acceptTrial.body (Env.frame [n + 1, k] [a, t, target, f])
      (Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 =
        some (if IsDecoupledAbs τ H ∨ subdiagNormSqProd k H ≤ T then (1 : ℝ) else 0)) m := by
  classical
  have hal := Store.lt_length_of_get (hH.get_re 0 0)
  have htl := Store.lt_length_of_get ht
  have htargetl := Store.lt_length_of_get hTarget
  have hfl := Store.lt_length_of_lt_len hf
  change Writes .total I τp (Stmt.allocs [.const 5, .const 1] _) _ _ _ m
  refine writes_allocs_preserving_post (ns := [5, 1]) rfl
    (fun hBelow hp => ⟨hp.1, ((hBelow f.1 hfl).2 f.2).trans hp.2⟩) ?_
  intro store hlen hlens hBelow
  let r : ℕ × ℕ := (m.store.length, 0)
  let p : ℕ × ℕ := (m.store.length + 1, 0)
  have hr : store.len r.1 = 5 := by simpa [r] using hlens 0 (by simp)
  have hp : store.len p.1 = 1 := by simpa [p] using hlens 1 (by simp)
  have hapart : Fp.Apart [r, p, f] [5, 1, 1] := by
    dsimp only [r, p]
    disjoint
  have hscratch : Fp.Disj (Store.inBlock r.1 r.2 5 ⊔ Store.inBlock p.1 p.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 1 ⊔ Store.inBlock target.1 target.2 1) := by
    dsimp only [r, p]
    disjoint
  have hall : Fp.Disj (Fp.blocks [r, p, f] [5, 1, 1])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 1 ⊔ Store.inBlock target.1 target.2 1) := by
    simpa only [Fp.blocks, sup_bot_eq, ← sup_assoc] using
      Fp.disj_sup_left.mpr ⟨hscratch, hsep⟩
  have hbody := acceptTrialWithScratch_writes (τp := τp) (m := ⟨store, m.pos⟩)
    (r := r) (p := p) (f := f) hS hE hL hC hk hτ (hH.of_below hBelow hal)
    (((hBelow t.1 htl).2 t.2).trans ht)
    (((hBelow target.1 htargetl).2 target.2).trans hTarget)
    (by simp [Mem.Live, r, p, hlen]; omega)
    (by dsimp [r]; simpa only [Nat.zero_add] using hr.ge)
    (by dsimp [p]; rw [hp]; omega) (by rw [(hBelow f.1 hfl).1]; exact hf)
    hapart hall
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, r, p, hlen]; omega)).mono
    (by
      simp only [Fp.blocks, sup_bot_eq]
      exact sup_le (Fp.inBlock_le_sup_above le_rfl)
        (sup_le (Fp.inBlock_le_sup_above (by dsimp [p]; omega)) le_sup_left))
    (fun _ _ h => h)

end NLAlib.ShiftedQR
