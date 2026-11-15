/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveFinish

/-!
# The checked scalar Givens row-solve core

The core factors a working copy, initializes its flag, solves the triangular row using actual
pivot branches, and applies the saved rotations when all pivots were nonzero. All numerical
steps use scalar arithmetic; singularity is a computed outcome.

## Main results

* `NLAlib.ShiftedQR.rowSolveAfterFlag`: checked substitution and final rotations.
* `NLAlib.ShiftedQR.rowSolveAfterFlag_writes`: singularity or the exact inverse row.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Solve an already factored matrix with an initially clear singularity flag. -/
def rowSolveAfterFlag : Impl Op Tst := opsImpl% [n] (R, V, Cf, Acc, T, Flag) → (V, Flag) {
  run substitutionLoop.body [n] (R, V, Acc, T, Flag, V, Flag);
  run finishRowSolve.body [n] (V, Cf, T, Flag, V, Flag)
}

/-- Checked triangular substitution and saved reverse rotations return a genuine singularity
certificate or the exact inverse row. The determinant is not assumed nonzero.
[GolubVanLoan2013, §5.2.5]. -/
theorem rowSolveAfterFlag_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a v cf z t f : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hD : IsUpperHessenberg D) (hR : HoldsMatrix a (givensHessenbergR D) m.store)
    (hV : HoldsVector v w m.store) (hCf : HoldsCoefficients cf D n m.store)
    (hSep : RowSolveSeparate a v cf z t f) (hf0 : m.store.get f.1 f.2 = some 0)
    (hc : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 10 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ rowSolveAfterFlag.body (Env.frame [n + 1] [a, v, cf, z, t, f, v, f])
      (rowSolveFp (n + 1) a v cf z t f)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f D w m'.store) m := by
  have hl := rowSolve_live hR hV hc hz ht hf
  have hlSub : m.Live [a, v, z, t, f, v, f] := by
    intro b hb
    apply hl b
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    tauto
  have hs := substitutionLoop_writes hS hE hCmp (τ := τ) (by omega : 0 < n + 1) hR hV
    hSep.va hSep.za hSep.zv hSep.ta hSep.tv hSep.tz hSep.fa hSep.fv hSep.fz hSep.ft hf0
    hz (by omega) hf
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hs.in_frame rfl rfl hlSub) (by fp_sub [rowSolveFp])
    fun m' hfr ⟨hp, _, hcase⟩ => ?_
  have hCf' := hfr.keep (readsOnly_holdsCoefficients cf D n)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hSep.fc,
      Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
        ⟨Fp.disj_inBlock_of_ne hSep.tc, Fp.disj_inBlock_of_ne hSep.zc⟩,
          Fp.disj_inBlock_of_ne hSep.cv.symm⟩⟩) hCf
  have hw := finishRowSolve_writes hS hE hCmp (τ := τ) hD hCf' hcase
    hSep.cv.symm hSep.tv hSep.tc hSep.fv hSep.ft
    (by rw [hfr.len_eq]; exact hc) (by rw [hfr.len_eq]; exact ht)
  have hlFinish : m.Live [v, cf, t, f, v, f] := by
    intro b hb
    apply hl b
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    tauto
  exact (hw.in_frame rfl rfl (hlFinish.congr hfr.length_eq)).mono
    (by fp_sub [rowSolveFp]) (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- Initialize the singularity report with an actual scalar zero literal. -/
def clearRowSolveFlag : Impl Op Tst := opsImpl% [] (Flag) → (Flag) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (Flag)
}

omit [Has CmpTst Tst] in
/-- Clearing the report writes one actual word and does not consume tape. -/
theorem clearRowSolveFlag_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ} {f : ℕ × ℕ}
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ clearRowSolveFlag.body (Env.frame [] [f, f]) (Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get f.1 f.2 = some 0) m := by
  have hw : Wp .total I τ clearRowSolveFlag.body (Env.frame [] [f, f])
      (fun m' => m' = m.updBlock f [M.lit 0]) m := by
    refine wp_call_const (hS (.lit 0)) (z := f) rfl rfl rfl trivial (by omega) ?_
    simp [Mem.updBlock, Store.updBlock, Mem.upd]
  refine (Writes.of_wp_eq_updBlock hw).mono le_rfl ?_
  rintro m' _ rfl
  have hzero : M.lit 0 = 0 := by simpa using hE.lit 0
  refine ⟨rfl, ?_⟩
  simpa [Mem.store_updBlock, Store.updBlock, hzero] using
    Store.get_upd_self (s := m.store) (b := f.1) (i := f.2) (by omega) (0 : ℝ)

/-- Initialize the report and solve an already factored row using its saved coefficients. -/
def rowSolveTriangular : Impl Op Tst := opsImpl% [n] (R, V, Cf, Acc, T, Flag) → (V, Flag) {
  run clearRowSolveFlag.body [] (Flag, Flag);
  run rowSolveAfterFlag.body [n] (R, V, Cf, Acc, T, Flag, V, Flag)
}

/-- The complete checked triangular and reverse-rotation phase initializes its own report.
Singular inputs return their certificate, while nonsingular inputs return the inverse row.
[GolubVanLoan2013, §5.2.5]. -/
theorem rowSolveTriangular_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a v cf z t f : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hD : IsUpperHessenberg D) (hR : HoldsMatrix a (givensHessenbergR D) m.store)
    (hV : HoldsVector v w m.store) (hCf : HoldsCoefficients cf D n m.store)
    (hSep : RowSolveSeparate a v cf z t f)
    (hc : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 10 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ rowSolveTriangular.body (Env.frame [n + 1] [a, v, cf, z, t, f, v, f])
      (rowSolveFp (n + 1) a v cf z t f)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f D w m'.store) m := by
  have hfl : f.1 < m.store.length := Store.lt_length_of_lt_len (by omega : f.2 < _)
  have hl : m.Live [f, f] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact hfl
  have hw := clearRowSolveFlag_writes hS hE (τ := τ) hf
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hl) (by fp_sub [rowSolveFp])
    fun m' hfr ⟨hp, hflag⟩ => ?_
  have hR' := hR.of_eqOff hfr (Fp.disj_inBlock_of_ne hSep.fa)
  have hV' : HoldsVector v w m'.store :=
    hfr.keep (readsOnly_holdsVector v w) (Fp.disj_inBlock_of_ne hSep.fv) hV
  have hCf' := hfr.keep (readsOnly_holdsCoefficients cf D n)
    (Fp.disj_inBlock_of_ne hSep.fc) hCf
  have hc' : cf.2 + 4 * (n + 1) ≤ m'.store.len cf.1 := by rw [hfr.len_eq]; exact hc
  have hz' : z.2 + 2 ≤ m'.store.len z.1 := by rw [hfr.len_eq]; exact hz
  have ht' : t.2 + 10 ≤ m'.store.len t.1 := by rw [hfr.len_eq]; exact ht
  have hf' : f.2 + 1 ≤ m'.store.len f.1 := by rw [hfr.len_eq]; exact hf
  have hs := rowSolveAfterFlag_writes hS hE hCmp (τ := τ) hD hR' hV' hCf' hSep hflag
    hc' hz' ht' hf'
  exact (hs.in_frame rfl rfl (rowSolve_live hR' hV' hc' hz' ht' hf')).mono le_rfl
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

/-- Factor the working matrix, then execute the checked triangular solve and rotations. -/
def rowSolveCore : Impl Op Tst := opsImpl% [n] (R, V, Cf, Acc, T, Flag) → (V, Flag) {
  run factorRows.body [n] (R, Cf, R, Cf);
  run rowSolveTriangular.body [n] (R, V, Cf, Acc, T, Flag, V, Flag)
}

/-- The concrete scalar row-solve core is total on every upper Hessenberg input, reporting
singularity or returning the original row multiplied by the inverse.
[GolubVanLoan2013, §5.2.5]. -/
theorem rowSolveCore_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a v cf z t f : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hD : IsUpperHessenberg D) (hR : HoldsMatrix a D m.store) (hV : HoldsVector v w m.store)
    (hSep : RowSolveSeparate a v cf z t f)
    (hc : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 10 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ rowSolveCore.body (Env.frame [n + 1] [a, v, cf, z, t, f, v, f])
      (rowSolveFp (n + 1) a v cf z t f)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f D w m'.store) m := by
  have hl0 := rowSolve_live hR hV hc hz ht hf
  have hl : m.Live [a, cf, a, cf] := by
    intro b hb
    apply hl0 b
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    tauto
  have hw := factorRows_writes hS hE hCmp (τ := τ) hSep.ac hR hc
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hl) (by fp_sub [rowSolveFp])
    fun m' hfr ⟨hp, hR', hCf⟩ => ?_
  have hV' : HoldsVector v w m'.store := hfr.keep (readsOnly_holdsVector v w)
    (Fp.disj_sup_left.mpr
      ⟨Fp.disj_inBlock_of_ne hSep.va.symm, Fp.disj_inBlock_of_ne hSep.cv⟩) hV
  have hc' : cf.2 + 4 * (n + 1) ≤ m'.store.len cf.1 := by rw [hfr.len_eq]; exact hc
  have hz' : z.2 + 2 ≤ m'.store.len z.1 := by rw [hfr.len_eq]; exact hz
  have ht' : t.2 + 10 ≤ m'.store.len t.1 := by rw [hfr.len_eq]; exact ht
  have hf' : f.2 + 1 ≤ m'.store.len f.1 := by rw [hfr.len_eq]; exact hf
  have hs := rowSolveTriangular_writes hS hE hCmp (τ := τ) hD hR' hV' hCf hSep hc' hz' ht' hf'
  exact (hs.in_frame rfl rfl (rowSolve_live hR' hV' hc' hz' ht' hf')).mono le_rfl
    (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

end NLAlib.ShiftedQR
