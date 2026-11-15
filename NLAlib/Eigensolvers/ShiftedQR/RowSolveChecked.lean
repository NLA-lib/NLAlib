/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveSubst

/-!
# Actual zero-pivot branches of triangular substitution

The singularity flag starts at zero. A column first checks its actual complex pivot; a zero
pivot sets the flag and skips the division. Once set, the flag makes all later columns skip.
A nonzero pivot takes the already verified scalar substitution path.

## Main results

* `NLAlib.ShiftedQR.checkedSubstituteColumn`: the actual checked column program.
* `NLAlib.ShiftedQR.checkedSubstituteColumn_singular`: a singularity flag skips the column.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- A substitution column preserves a disjoint zero flag during its arithmetic update. -/
theorem substituteColumn_keepFlag_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a v z t f : ℕ × ℕ} {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (j : Fin n) (hR : HoldsMatrix a R m.store) (hV : HoldsVector v (solvePrefix R w j) m.store)
    (hpivot : R j j ≠ 0) (hva : v.1 ≠ a.1) (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1)
    (hta : t.1 ≠ a.1) (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hfv : f.1 ≠ v.1) (hfz : f.1 ≠ z.1) (hft : f.1 ≠ t.1)
    (hf0 : m.store.get f.1 f.2 = some 0)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 4 ≤ m.store.len t.1) :
    Writes .total I τ substituteColumn.body (Env.frame [n, j] [a, v, z, t, v])
      ((Store.inBlock t.1 t.2 4 ⊔ Store.inBlock z.1 z.2 2) ⊔
        Store.inBlock v.1 (v.2 + 2 * j) 2)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a R m'.store ∧
        m'.store.get f.1 f.2 = some 0 ∧ HoldsVector v (solvePrefix R w (j + 1)) m'.store) m := by
  refine (substituteColumn_writes hS hE j hR hV hpivot hva hza hzv hta htv htz hz ht).mono
    le_rfl ?_
  intro m' hfr ⟨hp, hR', hV'⟩
  exact ⟨hp, hR', hfr.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr
      ⟨Fp.disj_inBlock_of_ne hft.symm, Fp.disj_inBlock_of_ne hfz.symm⟩,
        Fp.disj_inBlock_of_ne hfv.symm⟩) hf0, hV'⟩

variable [Has CmpTst Tst]

/-- A set singularity flag skips every subsequent column. Otherwise the actual pivot is
checked before the verified substitution routine is entered. -/
def checkedSubstituteColumn : Impl Op Tst := opsImpl% [n, j] (R, V, Acc, T, Flag) → (V, Flag) {
  if (Has.inj CmpTst.isZero) [] (Flag) {
    run checkComplexPivot.body [] (R[2 * (j * n + j)], Flag, Flag);
    if (Has.inj CmpTst.isZero) [] (Flag) {
      run substituteColumn.body [n, j] (R, V, Acc, T, V)
    } else {
      skip
    }
  } else {
    skip
  }
}

/-- An existing singularity report causes no further arithmetic or memory changes. -/
theorem checkedSubstituteColumn_singular {I : Interp Op Tst ℝ} (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n j : ℕ} {a v z t f : ℕ × ℕ}
    (hf : m.store.get f.1 f.2 = some 1) :
    Writes .total I τ checkedSubstituteColumn.body (Env.frame [n, j] [a, v, z, t, f, v, f]) ⊥
      (fun m' => m' = m) m := by
  have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf
  simp only [id_eq, one_ne_zero, decide_false] at htest
  exact writes_ite rfl rfl htest (Writes.skip rfl)

/-- A previously clear flag either reports an actual zero diagonal or completes the next
coordinate using its nonzero pivot. No assumption rules out singular matrices.
[GolubVanLoan2013, §3.1.2]. -/
theorem checkedSubstituteColumn_clear {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a v z t f : ℕ × ℕ}
    {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (j : Fin n) (hR : HoldsMatrix a R m.store) (hV : HoldsVector v (solvePrefix R w j) m.store)
    (hva : v.1 ≠ a.1) (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1)
    (hta : t.1 ≠ a.1) (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hfa : f.1 ≠ a.1) (hfv : f.1 ≠ v.1) (hfz : f.1 ≠ z.1) (hft : f.1 ≠ t.1)
    (hf0 : m.store.get f.1 f.2 = some 0)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 4 ≤ m.store.len t.1)
    (hf : f.2 + 1 ≤ m.store.len f.1) :
    Writes .total I τ checkedSubstituteColumn.body (Env.frame [n, j] [a, v, z, t, f, v, f])
      (Store.inBlock f.1 f.2 1 ⊔ ((Store.inBlock t.1 t.2 4 ⊔ Store.inBlock z.1 z.2 2) ⊔
        Store.inBlock v.1 (v.2 + 2 * j) 2))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a R m'.store ∧
        ((m'.store.get f.1 f.2 = some 1 ∧ R j j = 0) ∨
          (m'.store.get f.1 f.2 = some 0 ∧ R j j ≠ 0 ∧
            HoldsVector v (solvePrefix R w (j + 1)) m'.store))) m := by
  have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf0
  simp only [id_eq, decide_true] at htest
  refine writes_ite rfl rfl htest ?_
  let y : ℕ × ℕ := (a.1, a.2 + 2 * (j * n + j))
  have hp := checkComplexPivot_writes hS hE hCmp (τ := τ) (y := y)
    (hR.get_re j j) (hR.get_im j j) hf0 hf
  have hal := Store.lt_length_of_get (hR.get_re j j)
  have hfl := Store.lt_length_of_get hf0
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV j)
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  have hl : m.Live [y, f, f] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  refine Writes.seq_le (hp.in_frame rfl (by simp [Operand.evalList, Operand.eval,
    Env.frame, IExp.eval, y]) hl) le_sup_left fun m' hfr ⟨hp', hcase⟩ => ?_
  have hR' := hR.of_eqOff hfr (Fp.disj_inBlock_of_ne hfa)
  have hV' : HoldsVector v (solvePrefix R w j) m'.store :=
    hfr.keep (readsOnly_holdsVector v (solvePrefix R w j)) (Fp.disj_inBlock_of_ne hfv) hV
  rcases hcase with ⟨hzero, hne⟩ | ⟨hone, heq⟩
  · have htst := hCmp.test_isZero (d := []) (m := m') (x := f) hzero
    simp only [id_eq, decide_true] at htst
    refine writes_ite rfl rfl htst ?_
    have hw := substituteColumn_keepFlag_writes hS hE (τ := τ) j hR' hV' hne
      hva hza hzv hta htv htz hfv hfz hft hzero
      (by rw [hfr.len_eq]; exact hz) (by rw [hfr.len_eq]; exact ht)
    have hl' : m'.Live [a, v, z, t, v] := by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> rw [hfr.length_eq] <;> assumption
    exact (hw.in_frame rfl rfl hl').mono le_sup_right
      (fun _ _ h => ⟨h.1.trans hp', h.2.1, Or.inr ⟨h.2.2.1, hne, h.2.2.2⟩⟩)
  · have htst := hCmp.test_isZero (d := []) (m := m') (x := f) hone
    simp only [id_eq, one_ne_zero, decide_false] at htst
    refine writes_ite rfl rfl htst ?_
    exact (Writes.skip ⟨hp', hR', Or.inl ⟨hone, heq⟩⟩).mono bot_le (fun _ _ h => h)

end NLAlib.ShiftedQR
