/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveForward
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveSpace
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveVector

/-!
# Completing a checked Givens row solve

A clear flag applies the stored rotations to the solved triangular row. A set flag returns
the zero-diagonal singularity certificate without inspecting a partially solved row.

## Main results

* `NLAlib.ShiftedQR.finishRowSolve`: the actual final flag branch and reverse rotations.
* `NLAlib.ShiftedQR.finishRowSolve_writes`: singularity or the exact inverse row.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Apply the saved rotations only when every checked triangular pivot was nonzero. -/
def finishRowSolve : Impl Op Tst := opsImpl% [n] (V, Cf, T, Flag) → (V, Flag) {
  if (Has.inj CmpTst.isZero) [] (Flag) {
    run reverseVectorRotations.body [n] (V, Cf, T, V)
  } else {
    skip
  }
}

/-- The actual final flag branch returns either a genuine singularity certificate or the
row multiplied by the original matrix inverse. No determinant premise is assumed.
[GolubVanLoan2013, §5.2.5]. -/
theorem finishRowSolve_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v cf t f : ℕ × ℕ}
    {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {w : Fin (n + 1) → ℂ}
    (hD : IsUpperHessenberg D) (hCf : HoldsCoefficients cf D n m.store)
    (hcase : (m.store.get f.1 f.2 = some 1 ∧ ∃ i, givensHessenbergR D i i = 0) ∨
      (m.store.get f.1 f.2 = some 0 ∧ HoldsVector v (rowForwardSubst (givensHessenbergR D) w)
        m.store ∧ ∀ i, givensHessenbergR D i i ≠ 0))
    (hvc : v.1 ≠ cf.1) (htv : t.1 ≠ v.1) (htc : t.1 ≠ cf.1)
    (hfv : f.1 ≠ v.1) (hft : f.1 ≠ t.1)
    (hc : cf.2 + 4 * (n + 1) ≤ m.store.len cf.1)
    (ht : t.2 + 10 ≤ m.store.len t.1) :
    Writes .total I τ finishRowSolve.body (Env.frame [n + 1] [v, cf, t, f, v, f])
      (Store.inBlock v.1 v.2 (2 * (n + 1)) ⊔ Store.inBlock t.1 t.2 10)
      (fun m' => m'.pos = m.pos ∧ RowSolveResult v f D w m'.store) m := by
  rcases hcase with ⟨hf, i, hi⟩ | ⟨hf, hV, hdiag⟩
  · have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf
    simp only [id_eq, one_ne_zero, decide_false] at htest
    refine writes_ite rfl rfl htest ?_
    exact (Writes.skip ⟨rfl, Or.inl ⟨hf, factor_singular_of_zero_diagonal hD i hi⟩⟩).mono
      bot_le (fun _ _ h => h)
  · have htest := hCmp.test_isZero (d := []) (m := m) (x := f) hf
    simp only [id_eq, decide_true] at htest
    refine writes_ite rfl rfl htest ?_
    have hw := reverseVectorRotations_writes hS hE (τ := τ) hV hCf hvc htv htc ht
    have hvl := Store.lt_length_of_get (HoldsVector.get_re hV (0 : Fin (n + 1)))
    have hcl : cf.1 < m.store.length := Store.lt_length_of_lt_len (by omega : cf.2 < _)
    have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
    have hl : m.Live [v, cf, t, v] := by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    refine (hw.in_frame rfl rfl hl).mono le_rfl ?_
    intro m' hfr ⟨hp, hV'⟩
    refine ⟨hp, Or.inr ⟨hfr.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hfv.symm,
        Fp.disj_inBlock_of_ne hft.symm⟩) hf, ?_⟩⟩
    simpa only [Nat.add_sub_cancel, reverseRotations_solve_of_diagonal D hD hdiag w] using hV'

end NLAlib.ShiftedQR
