/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveShifted
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveHalfMath

/-!
# Checked inverse-row candidates in a half norm

Each candidate uses its actual stored shift and the total shifted row solver. A singularity
report skips all later candidate arithmetic. The source matrix and complete shift list are
retained throughout the inverse-polynomial fold.

## Main results

* `NLAlib.ShiftedQR.halfSolveCandidate`: one checked stored shift.
* `NLAlib.ShiftedQR.HalfVectorState`: a singularity witness or the exact current inverse row.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- A stored shift list is a vector in the ordinary pair-codec representation. -/
abbrev HoldsShifts {k : ℕ} (a : ℕ × ℕ) (ss : List ℂ) (s : Store ℝ) : Prop :=
  HoldsVector a (fun i : Fin k => ss.getD i 0) s

/-- The temporary vector and report preserve the source matrix and stored shift list. -/
structure HalfSolveSeparate (n k : ℕ) (a ss v f : ℕ × ℕ) : Prop where
  /-- The scoped vector has a different buffer from the source matrix. -/
  va : v.1 ≠ a.1
  /-- The scoped vector has a different buffer from the shifts. -/
  vs : v.1 ≠ ss.1
  /-- The report has a different buffer from the scoped vector. -/
  fv : f.1 ≠ v.1
  /-- The report word is disjoint from the source matrix. -/
  fa : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * (n * n)))
  /-- The report word is disjoint from the stored shifts. -/
  fs : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock ss.1 ss.2 (2 * k))

/-- The current inverse row, or a genuine singular shifted matrix in the selected segment. -/
def HalfVectorState {n : ℕ} (v f : ℕ × ℕ) (H : Matrix (Fin n) (Fin n) ℂ)
    (ss : List ℂ) (w : Fin n → ℂ) (s : Store ℝ) : Prop :=
  (s.get f.1 f.2 = some 1 ∧ ∃ shift ∈ ss, (H - shift • 1).det = 0) ∨
    (s.get f.1 f.2 = some 0 ∧ HoldsVector v w s)

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Solve at the selected actual stored shift only while the singularity flag is clear. -/
def halfSolveCandidate : Impl Op Tst := opsImpl% [n, k, a, i] (H, SS, V, Flag) → (V, Flag) {
  if (Has.inj CmpTst.isZero) [] (Flag) {
    run shiftedRowSolve.body [n] (H, SS[2 * (a + i)], V, V, Flag)
  } else {
    skip
  }
}

/-- A previously reported singularity skips a candidate without reading its shift. -/
theorem halfSolveCandidate_singular {I : Interp Op Tst ℝ} (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a i : ℕ} {b ss v f : ℕ × ℕ}
    (hf : m.store.get f.1 f.2 = some 1) :
    Writes .total I τ halfSolveCandidate.body (Env.frame [n, k, a, i] [b, ss, v, f, v, f]) ⊥
      (fun m' => m' = m) m := by
  have ht := hCmp.test_isZero (d := []) (m := m) (x := f) hf
  simp only [id_eq, one_ne_zero, decide_false] at ht
  exact writes_ite rfl rfl ht (Writes.skip rfl)

/-- A clear candidate reports singularity or computes its exact inverse row, retaining both
source blocks. The shift need not avoid the spectrum. [BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem halfSolveCandidate_clear {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a i : ℕ} {b ss v f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ} {w : Fin (n + 1) → ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hV : HoldsVector v w m.store)
    (hi : a + i < k) (hSep : HalfSolveSeparate (n + 1) k b ss v f)
    (hf0 : m.store.get f.1 f.2 = some 0) (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ halfSolveCandidate.body
      (Env.frame [n + 1, k, a, i] [b, ss, v, f, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧
        RowSolveResult v f (H - shifts.getD (a + i) 0 • 1) w m'.store) m := by
  have ht := hCmp.test_isZero (d := []) (m := m) (x := f) hf0
  simp only [id_eq, decide_true] at ht
  refine writes_ite rfl rfl ht ?_
  let s : ℕ × ℕ := (ss.1, ss.2 + 2 * (a + i))
  have hshift := HoldsVector.read_entry hSS (⟨a + i, hi⟩ : Fin k)
  have hw := shiftedRowSolve_writes hS hE hCmp (τ := τ) (s := s)
    hH hB hshift hV hSep.fv hf
  have hbl := Store.lt_length_of_get (hB.get_re (0 : Fin (n + 1)) 0)
  have hsl := Store.lt_length_of_get (HoldsVector.get_re hSS ⟨a + i, hi⟩)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
  have hfl := Store.lt_length_of_get hf0
  have hl : m.Live [b, s, v, v, f] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  refine (hw.in_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
    IExp.eval, s]) hl).mono le_rfl ?_
  intro m' hfr h
  exact ⟨h.1, hB.of_eqOff hfr
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hSep.va, hSep.fa⟩),
    hfr.keep (readsOnly_holdsVector ss (fun j : Fin k => shifts.getD j 0))
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hSep.vs, hSep.fs⟩) hSS, h.2⟩

end NLAlib.ShiftedQR
