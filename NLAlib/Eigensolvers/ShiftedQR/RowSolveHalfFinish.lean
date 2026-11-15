/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveHalfLoops
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveNorm

/-!
# The final squared norm or singularity report of a half

A clear flag computes the actual vector's squared Euclidean norm. A set flag writes a zero
placeholder norm and retains its singular-shift witness. Both output words are initialized.

## Main results

* `NLAlib.ShiftedQR.HalfNormResult`: a total numeric result or singularity certificate.
* `NLAlib.ShiftedQR.finishHalfNorm`: the actual final flag branch and scalar norm computation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- A half norm is either the exact inverse-polynomial squared norm or an actual singular
shift certificate, accompanied by a defined zero placeholder norm. -/
def HalfNormResult {n : ℕ} (z f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) (e : ℕ) (s : Store ℝ) : Prop :=
  (s.get f.1 f.2 = some 1 ∧ s.get z.1 z.2 = some 0 ∧
    ∃ shift ∈ ss, (H - shift • 1).det = 0) ∨
  (s.get f.1 f.2 = some 0 ∧ s.get z.1 z.2 =
    some (‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly ss))⁻¹ ^ e) (Fin.last n))‖ ^ 2))

/-- Half-norm outputs survive release of their scoped vector and arithmetic workspace. -/
theorem HalfNormResult.of_below {n L : ℕ} {z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} {e : ℕ} {s s' : Store ℝ}
    (h : HalfNormResult z f H ss e s) (hBelow : Store.Below L s s')
    (hz : z.1 < L) (hf : f.1 < L) : HalfNormResult z f H ss e s' := by
  rcases h with ⟨hflag, hnorm, hsing⟩ | ⟨hflag, hnorm⟩
  · exact Or.inl ⟨((hBelow f.1 hf).2 _).trans hflag, ((hBelow z.1 hz).2 _).trans hnorm, hsing⟩
  · exact Or.inr ⟨((hBelow f.1 hf).2 _).trans hflag, ((hBelow z.1 hz).2 _).trans hnorm⟩

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute the clear branch's squared norm; initialize its placeholder on a singular branch. -/
def finishHalfNorm : Impl Op Tst := opsImpl% [n] (V, T, Flag) → (Norm, Flag) {
  if (Has.inj CmpTst.isZero) [] (Flag) {
    run vectorNormSquared.body [n] (V, T, Norm)
  } else {
    run clearRowSolveFlag.body [] (Norm, Norm)
  }
}

/-- The actual flag branch gives an initialized norm and exact classification, without
assuming every candidate shift is nonsingular. [BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem finishHalfNorm_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n e : ℕ} {v t z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    (hstate : HalfVectorState v f H ss (halfSolvePrefix H ss e) m.store)
    (htv : t.1 ≠ v.1) (htf : t.1 ≠ f.1)
    (hzf : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock f.1 f.2 1))
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 1 ≤ m.store.len z.1) :
    Writes .total I τ finishHalfNorm.body (Env.frame [n + 1] [v, t, f, z, f])
      (Store.inBlock t.1 t.2 3 ⊔ Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ HalfNormResult z f H ss e m'.store) m := by
  rcases hstate with ⟨hf, shift, hmem, hdet⟩ | ⟨hf, hV⟩
  · have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf
    simp only [id_eq, one_ne_zero, decide_false] at htest
    refine writes_ite rfl rfl htest ?_
    have hw := clearRowSolveFlag_writes hS hE (τ := τ) hz
    have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
    have hl : m.Live [z, z] := by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact hzl
    refine (hw.in_frame rfl rfl hl).mono le_sup_right ?_
    intro m' hfr h
    exact ⟨h.1, Or.inl ⟨hfr.keep (Store.readsOnly_get _ _ _) hzf hf,
      h.2, shift, hmem, hdet⟩⟩
  · have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf
    simp only [id_eq, decide_true] at htest
    refine writes_ite rfl rfl htest ?_
    have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
    have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
    have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
    have hl : m.Live [v, t, z] := by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> assumption
    have hw := vectorNormSquared_writes hS hE (τ := τ) hl hV htv ht hz
    refine (hw.in_frame rfl rfl hl).mono le_rfl ?_
    intro m' hfr h
    refine ⟨h.1, Or.inr ⟨hfr.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne htf, hzf⟩) hf, ?_⟩⟩
    simpa only [halfSolvePrefix_eq_power H ss e] using h.2

end NLAlib.ShiftedQR
