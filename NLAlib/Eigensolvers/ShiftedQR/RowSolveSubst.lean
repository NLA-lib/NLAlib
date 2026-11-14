/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveResidual
public import NLAlib.Eigensolvers.ShiftedQR.Division
public import NLAlib.Eigensolvers.ShiftedQR.Pivot

/-!
# Pivot-guarded forward substitution of a complex row

A column residual is computed by scalar multiply-subtract operations and divided by the
actual diagonal pair. The checked column contract requires its mathematical pivot to be
nonzero; the complete substitution program obtains this fact from the actual pivot test and
reports a zero pivot through its singularity flag.

## Main results

* `NLAlib.ShiftedQR.substituteColumn`: residual accumulation followed by complex division.
* `NLAlib.ShiftedQR.substituteColumn_writes`: one exact forward-substitution coordinate.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Solve one triangular column once its nonzero pivot has been established. -/
def substituteColumn : Impl Op Tst := opsImpl% [n, j] (R, V, Acc, T) → (V) {
  run columnResidual.body [n, j] (R, V, Acc, T, Acc);
  run complexDivideWithScratch.body [] (Acc, R[2 * (j * n + j)], T, V[2 * j])
}

/-- A nonzero triangular pivot makes the actual residual and scalar divisions compute the
next coordinate of the established mathematical forward substitution. [GolubVanLoan2013, §3.1.2]. -/
theorem substituteColumn_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a v z t : ℕ × ℕ} {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (j : Fin n) (hR : HoldsMatrix a R m.store) (hV : HoldsVector v (solvePrefix R w j) m.store)
    (hpivot : R j j ≠ 0) (hva : v.1 ≠ a.1) (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1)
    (hta : t.1 ≠ a.1) (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 4 ≤ m.store.len t.1) :
    Writes .total I τ substituteColumn.body (Env.frame [n, j] [a, v, z, t, v])
      ((Store.inBlock t.1 t.2 4 ⊔ Store.inBlock z.1 z.2 2) ⊔
        Store.inBlock v.1 (v.2 + 2 * j) 2)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a R m'.store ∧
        HoldsVector v (solvePrefix R w (j + 1)) m'.store) m := by
  have hal := Store.lt_length_of_get (hR.get_re j j)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV j)
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  have hl : m.Live [a, v, z, t, z] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hr := columnResidual_writes hS hE (τ := τ) j hR hV hza hzv hta htv htz hz (by omega)
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hr.in_frame rfl rfl hl)
    ((sup_le_sup (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl).trans le_sup_left)
    fun m' hfr ⟨hp, hacc⟩ => ?_
  have hR' := hR.of_eqOff hfr
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hta, Fp.disj_inBlock_of_ne hza⟩)
  have hV' : HoldsVector v (solvePrefix R w j) m'.store :=
    hfr.keep (readsOnly_holdsVector v (solvePrefix R w j))
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne htv, Fp.disj_inBlock_of_ne hzv⟩) hV
  let y : ℕ × ℕ := (a.1, a.2 + 2 * (j * n + j))
  let out : ℕ × ℕ := (v.1, v.2 + 2 * j)
  have hg0 := Store.get_of_readBlock hacc (j := 0) (by omega) (0 : ℝ)
  have hg1 := Store.get_of_readBlock hacc (j := 1) (by omega) (0 : ℝ)
  have hout := Store.lt_len_of_get (HoldsVector.get_im hV' j)
  have hd := complexDivideWithScratch_writes hS hE (τ := τ) (x := z) (y := y) (z := out)
    htz hta htv hpivot (by simpa using hg0) (by simpa using hg1)
    (hR'.get_re j j) (hR'.get_im j j) (by rw [hfr.len_eq]; exact ht) hout
  have hl' : m'.Live [z, y, t, out] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb | hb <;> subst b <;> rw [hfr.length_eq]
    all_goals first | exact hzl | exact hal | exact htl | exact hvl
  refine (hd.in_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
    IExp.eval, y, out]) hl').mono ?_ ?_
  · simp only [Fp.blocks, sup_bot_eq]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · intro m'' hfr' ⟨hp', hquot⟩
    have hframe : m'.store.EqOff (Store.inBlock t.1 t.2 4 ⊔
        Store.inBlock out.1 out.2 2) m''.store := by
      simpa only [Fp.blocks, sup_bot_eq] using hfr'
    have hv := HoldsVector.update_scratch hV' j _ hframe (Fp.disj_inBlock_of_ne htv)
      (by simpa using Store.get_of_readBlock hquot (j := 0) (by omega) (0 : ℝ))
      (by simpa using Store.get_of_readBlock hquot (j := 1) (by omega) (0 : ℝ))
    refine ⟨hp'.trans hp, hR'.of_eqOff hframe
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hta, Fp.disj_inBlock_of_ne hva⟩), ?_⟩
    simpa only [← solvePrefix_residual R w j] using hv

end NLAlib.ShiftedQR
