/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolve

/-!
# Checked row solves at an actual stored shift

The shift is subtracted from a fresh matrix copy before the scalar Givens row solver runs.
The raw matrix and shift remain source data. Singularity is reported for the actual shifted
matrix, so an eigenvalue candidate never forces a zero-denominator division.

## Main results

* `NLAlib.ShiftedQR.shiftedRowSolve`: the actual shifted row solver.
* `NLAlib.ShiftedQR.shiftedRowSolve_writes`: total singularity-or-inverse correctness.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Subtract the supplied shift from a working matrix, then solve its row system. -/
def solveShiftedWorking : Impl Op Tst := opsImpl% [n] (R, S, V) → (V, Flag) {
  run shiftDiagonal.body [n] (R, S, R);
  run rowSolve.body [n] (R, V, V, Flag)
}

/-- The working-copy path computes the shifted inverse row or reports actual singularity.
[GolubVanLoan2013, §5.2.5]. -/
theorem solveShiftedWorking_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {r s v f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} {w : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hR : HoldsMatrix r H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hV : HoldsVector v w m.store) (hrv : r.1 ≠ v.1) (hfv : f.1 ≠ v.1)
    (hrs : Fp.Disj (Store.inBlock r.1 r.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 2)) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ solveShiftedWorking.body (Env.frame [n + 1] [r, s, v, v, f])
      (Store.inBlock r.1 r.2 (2 * ((n + 1) * (n + 1))) ⊔
        (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1))
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f (H - shift • 1) w m'.store) m := by
  have hrl := Store.lt_length_of_get (hR.get_re (0 : Fin (n + 1)) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by omega) (0 : ℝ))
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
  have hfl : f.1 < m.store.length := Store.lt_length_of_lt_len (by omega : f.2 < _)
  have hl : m.Live [r, s, r] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  have hw := shiftDiagonal_writes hS hE (τ := τ) hl hR hs hrs
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hl) le_sup_left fun m' hfr ⟨hp, hR'⟩ => ?_
  have hV' : HoldsVector v w m'.store :=
    hfr.keep (readsOnly_holdsVector v w) (Fp.disj_inBlock_of_ne hrv) hV
  have hr := rowSolve_writes hS hE hCmp (τ := τ) (hH.sub_smul_one shift) hR' hV' hfv
    (by rw [hfr.len_eq]; exact hf)
  have hl' : m'.Live [r, v, v, f] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> rw [hfr.length_eq] <;> assumption
  exact (hr.in_frame rfl rfl hl').mono le_sup_right (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- A fresh working copy leaves the raw matrix and stored shift available to the caller.
Algorithm: shifted-qr (run model) -/
def shiftedRowSolve : Impl Op Tst := opsImpl% [n] (H, S, V) → (V, Flag) {
  let R ← alloc (2 * (n * n));
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (H, R);
  run solveShiftedWorking.body [n] (R, S, V, V, Flag)
}

/-- The actual stored shift yields either a certified singular shifted matrix or its exact
inverse row, without any assumption that the shift avoids the spectrum. All scratch is scoped.
[GolubVanLoan2013, §5.2.5]. -/
theorem shiftedRowSolve_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s v f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} {w : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hV : HoldsVector v w m.store) (hfv : f.1 ≠ v.1) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ shiftedRowSolve.body (Env.frame [n + 1] [a, s, v, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f (H - shift • 1) w m'.store) m := by
  have hal := Store.lt_length_of_get (hA.get_re (0 : Fin (n + 1)) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by omega) (0 : ℝ))
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
  have hfl : f.1 < m.store.length := Store.lt_length_of_lt_len (by omega : f.2 < _)
  apply writes_allocs_preserving_post (lens := [.const 2 * (.var 0 * .var 0)])
    (ns := [2 * ((n + 1) * (n + 1))]) rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hvl hfl⟩)
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 1 := by simpa using hlen
  let r : ℕ × ℕ := (m.store.length, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have hr : r.2 + 2 * ((n + 1) * (n + 1)) ≤ store.len r.1 := by
    simpa [r] using (hlens 0 (by simp)).ge
  have hA' := hA.of_below hBelow hal
  have hV' := hV.of_below hBelow hvl
  have hs' := (hBelow.readBlock hsl _ _).trans hs
  have hf' : f.2 + 1 ≤ store.len f.1 := by rw [(hBelow f.1 hfl).1]; exact hf
  have hrv : r.1 ≠ v.1 := by dsimp [r]; omega
  have hrs : r.1 ≠ s.1 := by dsimp [r]; omega
  have hw := copyMatrix_writes hS (τ := τ) (m := m₁) (a := a) (b := r) hA' hr
    (Fp.disj_inBlock_of_ne (by dsimp [r]; omega))
  have hl : m₁.Live [a, r] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb <;> subst b
    · change a.1 < store.length
      omega
    · change m.store.length < store.length
      omega
  change Writes .total I τ (.seq _ _) _ _ _ m₁
  refine Writes.seq_le (hw.in_frame rfl rfl hl) (by fp_sub [r]) fun m' hfr ⟨hp, hR⟩ => ?_
  have hV'' : HoldsVector v w m'.store :=
    hfr.keep (readsOnly_holdsVector v w) (Fp.disj_inBlock_of_ne hrv) hV'
  have hs'' := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
    (Fp.disj_inBlock_of_ne hrs) hs'
  have hc := solveShiftedWorking_writes hS hE hCmp (τ := τ) hH hR hs'' hV'' hrv hfv
    (Fp.disj_inBlock_of_ne hrs) (by rw [hfr.len_eq]; exact hf')
  have hl' : m'.Live [r, s, v, v, f] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb | hb | hb <;> subst b <;> rw [hfr.length_eq]
    all_goals change _ < store.length
    all_goals first | exact (by dsimp [r]; omega) | omega
  exact (hc.in_frame rfl rfl hl').mono (by fp_sub [r])
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

end NLAlib.ShiftedQR
