/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveHalfFinish

/-!
# Total inverse-polynomial half norms from actual scalar row solves

The routine initializes the last basis row, executes the selected shifts for the requested
number of rounds, then computes its squared Euclidean norm. A zero pivot produces an actual
singular-shift certificate and a defined zero placeholder. Unused shifts are not tested.

## Main results

* `NLAlib.ShiftedQR.halfNorm`: the scoped scalar half-norm implementation.
* `NLAlib.ShiftedQR.halfNorm_writes`: total norm-or-singularity correctness.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Evaluate and finish the half from an initialized row and clear report. -/
def halfNormAfterInit : Impl Op Tst := opsImpl% [n, k, a, h, e] (H, SS, V, T, Flag) → (Norm, Flag) {
  run halfRounds.body [n, k, a, h, e] (H, SS, V, Flag, V, Flag);
  run finishHalfNorm.body [n] (V, T, Flag, Norm, Flag)
}

/-- The initialized inverse-row fold and actual final branch give the full half-norm result.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfNormAfterInit_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss v t z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hl : m.Live [b, ss, v, t, f, z, f])
    (hV : HoldsVector v (Pi.single (Fin.last n) 1) m.store)
    (hf0 : m.store.get f.1 f.2 = some 0) (htv : t.1 ≠ v.1) (htf : t.1 ≠ f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock f.1 f.2 1))
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 1 ≤ m.store.len z.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ halfNormAfterInit.body
      (Env.frame [n + 1, k, a, h, e] [b, ss, v, t, f, z, f])
      (Fp.blocks [v, t, z, f] [2 * (n + 1), 3, 1, 1])
      (fun m' => m'.pos = m.pos ∧ HalfNormResult z f H (halfSegment shifts a h) e m'.store) m := by
  have hlRound : m.Live [b, ss, v, f, v, f] := by
    intro x hx
    apply hl x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have hw := halfRounds_writes hS hE hCmp (τ := τ) (e := e) hH hB hSS hak hal hSep hlRound hf
    (Or.inr ⟨hf0, hV⟩)
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlRound) (by fp_sub)
    fun m' hfr ⟨hp, _, _, hstate⟩ => ?_
  have hn := finishHalfNorm_writes hS hE hCmp (τ := τ) hstate htv htf hzf
    (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hz)
  have hlFinish : m.Live [v, t, f, z, f] := by
    intro x hx
    apply hl x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  exact (hn.in_frame rfl rfl (hlFinish.congr hfr.length_eq)).mono (by fp_sub)
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- Clear the report before evaluating an initialized basis row. -/
def halfNormAfterVector : Impl Op Tst := opsImpl% [n, k, a, h, e] (H, SS, V, T) → (Norm, Flag) {
  run clearRowSolveFlag.body [] (Flag, Flag);
  run halfNormAfterInit.body [n, k, a, h, e] (H, SS, V, T, Flag, Norm, Flag)
}

/-- The half-norm evaluator initializes its report and preserves the given last basis row.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfNormAfterVector_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss v t z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hl : m.Live [b, ss, v, t, z, f])
    (hV : HoldsVector v (Pi.single (Fin.last n) 1) m.store)
    (htv : t.1 ≠ v.1) (htf : t.1 ≠ f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock f.1 f.2 1))
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 1 ≤ m.store.len z.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ halfNormAfterVector.body
      (Env.frame [n + 1, k, a, h, e] [b, ss, v, t, z, f])
      (Fp.blocks [v, t, z, f] [2 * (n + 1), 3, 1, 1])
      (fun m' => m'.pos = m.pos ∧ HalfNormResult z f H (halfSegment shifts a h) e m'.store) m := by
  have hlFlag : m.Live [f, f] := by
    intro x hx
    apply hl x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have hw := clearRowSolveFlag_writes hS hE (τ := τ) hf
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlFlag) (by fp_sub) fun m' hfr ⟨hp, hflag⟩ => ?_
  have hB' := hB.of_eqOff hfr hSep.fa
  have hSS' := hfr.keep (readsOnly_holdsVector ss (fun i : Fin k => shifts.getD i 0)) hSep.fs hSS
  have hV' : HoldsVector v (Pi.single (Fin.last n) 1) m'.store :=
    hfr.keep (readsOnly_holdsVector v _) (Fp.disj_inBlock_of_ne hSep.fv) hV
  have hlInit : m.Live [b, ss, v, t, f, z, f] := by
    intro x hx
    apply hl x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have hn := halfNormAfterInit_writes hS hE hCmp (τ := τ) (e := e) hH hB' hSS' hak hal hSep
    (hlInit.congr hfr.length_eq) hV' hflag htv htf hzf
    (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hz)
    (by rw [hfr.len_eq]; exact hf)
  exact (hn.in_frame rfl rfl (hlInit.congr hfr.length_eq)).mono le_rfl
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- Initialize the last basis row from capacity, then evaluate the requested half. -/
def halfNormWithScratch : Impl Op Tst := opsImpl% [n, k, a, h, e] (H, SS, V, T) → (Norm, Flag) {
  run lastBasisVector.body [n] (V);
  run halfNormAfterVector.body [n, k, a, h, e] (H, SS, V, T, Norm, Flag)
}

/-- The caller-scratch half norm initializes every needed vector component and output word.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfNormWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss v t z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hl : m.Live [b, ss, v, t, z, f])
    (htv : t.1 ≠ v.1) (htf : t.1 ≠ f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock f.1 f.2 1))
    (hv : v.2 + 2 * (n + 1) ≤ m.store.len v.1)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 1 ≤ m.store.len z.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ halfNormWithScratch.body
      (Env.frame [n + 1, k, a, h, e] [b, ss, v, t, z, f])
      (Fp.blocks [v, t, z, f] [2 * (n + 1), 3, 1, 1])
      (fun m' => m'.pos = m.pos ∧ HalfNormResult z f H (halfSegment shifts a h) e m'.store) m := by
  have hlVector : m.Live [v] := by
    intro x hx
    apply hl x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have hw := lastBasisVector_writes hS hE (τ := τ) hv
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlVector) (by fp_sub) fun m' hfr ⟨hp, hV⟩ => ?_
  have hB' := hB.of_eqOff hfr (Fp.disj_inBlock_of_ne hSep.va)
  have hSS' := hfr.keep (readsOnly_holdsVector ss (fun i : Fin k => shifts.getD i 0))
    (Fp.disj_inBlock_of_ne hSep.vs) hSS
  have hn := halfNormAfterVector_writes hS hE hCmp (τ := τ) (e := e) hH hB' hSS' hak hal hSep
    (hl.congr hfr.length_eq) hV htv htf hzf
    (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hz)
    (by rw [hfr.len_eq]; exact hf)
  exact (hn.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- The half norm scopes its initialized vector and three scalar norm scratch words.
Algorithm: shifted-qr (run model) -/
def halfNorm : Impl Op Tst := opsImpl% [n, k, a, h, e] (H, SS) → (Norm, Flag) {
  let V ← alloc (2 * n);
  let T ← alloc 3;
  run halfNormWithScratch.body [n, k, a, h, e] (H, SS, V, T, Norm, Flag)
}

/-- The scalar half-norm routine is total without any assumption excluding eigenvalue shifts.
It returns the exact norm or an initialized zero placeholder and a genuine singularity witness.
The selected segment lies inside both the stored block and the supplied mathematical list.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfNorm_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hak : a + h ≤ k)
    (hal : a + h ≤ shifts.length) (hl : m.Live [b, ss, z, f])
    (hfa : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock b.1 b.2 (2 * ((n + 1) * (n + 1)))))
    (hfs : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock ss.1 ss.2 (2 * k)))
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock f.1 f.2 1))
    (hz : z.2 + 1 ≤ m.store.len z.1) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ halfNorm.body (Env.frame [n + 1, k, a, h, e] [b, ss, z, f])
      (Store.inBlock z.1 z.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ HalfNormResult z f H (halfSegment shifts a h) e m'.store) m := by
  have hLive : b.1 < m.store.length ∧ ss.1 < m.store.length ∧
      z.1 < m.store.length ∧ f.1 < m.store.length := by simpa [Mem.Live] using hl
  apply writes_allocs_preserving_post (lens := [.const 2 * .var 0, .const 3])
    (ns := [2 * (n + 1), 3]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hLive.2.2.1 hLive.2.2.2⟩)
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 2 := by simpa using hlen
  let v : ℕ × ℕ := (m.store.length, 0)
  let t : ℕ × ℕ := (m.store.length + 1, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have hv : v.2 + 2 * (n + 1) ≤ store.len v.1 := by
    simpa [v] using (hlens 0 (by simp)).ge
  have ht : t.2 + 3 ≤ store.len t.1 := by simpa [t] using (hlens 1 (by simp)).ge
  have hSep : HalfSolveSeparate (n + 1) k b ss v f := by
    constructor
    · dsimp [v]; omega
    · dsimp [v]; omega
    · dsimp [v]; omega
    · exact hfa
    · exact hfs
  have hl' : m₁.Live [b, ss, v, t, z, f] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
    all_goals change _ < store.length
    all_goals try dsimp only [v, t, Prod.fst]
    all_goals omega
  have hw := halfNormWithScratch_writes hS hE hCmp (τ := τ) (e := e) (m := m₁)
    hH (hB.of_below hBelow hLive.1) (hSS.of_below hBelow hLive.2.1) hak hal hSep hl'
    (by dsimp [v, t]; omega) (by dsimp [t]; omega) hzf hv ht
    (by change z.2 + 1 ≤ store.len z.1; rw [(hBelow z.1 hLive.2.2.1).1]; exact hz)
    (by change f.2 + 1 ≤ store.len f.1; rw [(hBelow f.1 hLive.2.2.2).1]; exact hf)
  exact (hw.in_frame rfl rfl hl').mono (by fp_sub [v, t]) (fun _ _ h => h)

end NLAlib.ShiftedQR
