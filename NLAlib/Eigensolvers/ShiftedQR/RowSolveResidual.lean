/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RowSolveStorage
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveMath
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveUpdate
public import NLAlib.Ops.Blas.HermitianEntry
public import NLAlib.Ops.Logic.Loop

/-!
# The scalar residual loop of triangular row substitution

The current right-hand-side coordinate is copied into an accumulator. Earlier solved
coordinates then subtract their complex products with the triangular column. The vector and
matrix remain readable throughout; only the accumulator and reusable arithmetic scratch change.

## Main results

* `NLAlib.ShiftedQR.columnResidual`: the actual column-residual program.
* `NLAlib.ShiftedQR.residualTerms_writes`: the multiply-subtract loop computes its finite sum.
* `NLAlib.ShiftedQR.columnResidual_writes`: initialization and the complete residual.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Subtract the first $j$ complex products from the supplied accumulator. -/
def residualTerms : Impl Op Tst := opsImpl% [n, j] (R, V, Acc, T) → (Acc) {
  for i < j {
    run subtractProductWithScratch.body [] (V[2 * i], R[2 * (j * n + i)], T, Acc, Acc)
  }
}

/-- Copy the current right-hand side and accumulate the triangular column residual. -/
def columnResidual : Impl Op Tst := opsImpl% [n, j] (R, V, Acc, T) → (Acc) {
  run Hermitian.copyPair.body [] (V[2 * j], Acc);
  run residualTerms.body [n, j] (R, V, Acc, T, Acc)
}

/-- The scalar product loop computes the exact residual of a triangular column. Its three
scratch words and the accumulator are separate from the matrix and vector buffers.
[GolubVanLoan2013, §3.1.2]. -/
theorem residualTerms_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a v z t : ℕ × ℕ} {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (j : Fin n) (hR : HoldsMatrix a R m.store) (hV : HoldsVector v w m.store)
    (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1) (hta : t.1 ≠ a.1)
    (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hacc : m.store.readBlock z.1 z.2 2 = some [(w j).re, (w j).im])
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 3 ≤ m.store.len t.1) :
    Writes .total I τ residualTerms.body (Env.frame [n, j] [a, v, z, t, z])
      (Store.inBlock t.1 t.2 3 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(residualPrefix R w j j).re, (residualPrefix R w j j).im]) m := by
  let F := Store.inBlock t.1 t.2 3 ⊔ Store.inBlock z.1 z.2 2
  change Writes .total I τ (.loop _ _) _ _ _ m
  refine writes_loop (N := (j : ℕ)) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
      some [(residualPrefix R w j k).re, (residualPrefix R w j k).im])
    ⟨rfl, by simpa only [residualPrefix, columnProductSum_zero, sub_zero] using hacc⟩ ?_
  intro k hk m' hfr ⟨hp, hacc'⟩
  let i : Fin n := ⟨k, by have := j.isLt; omega⟩
  let x : ℕ × ℕ := (v.1, v.2 + 2 * k)
  let y : ℕ × ℕ := (a.1, a.2 + 2 * (j * n + k))
  have hR' := hR.of_eqOff hfr
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hta, Fp.disj_inBlock_of_ne hza⟩)
  have hV' : HoldsVector v w m'.store := hfr.keep (readsOnly_holdsVector v w)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne htv, Fp.disj_inBlock_of_ne hzv⟩) hV
  have hg0 := Store.get_of_readBlock hacc' (j := 0) (by omega) (0 : ℝ)
  have hg1 := Store.get_of_readBlock hacc' (j := 1) (by omega) (0 : ℝ)
  have hz' : z.2 + 2 ≤ m'.store.len z.1 := by rw [hfr.len_eq]; exact hz
  have ht' : t.2 + 3 ≤ m'.store.len t.1 := by rw [hfr.len_eq]; exact ht
  have hw := subtractProductWithScratch_writes hS hE (τ := τ) (x := x) (y := y)
    htv hta htz (HoldsVector.get_re hV' i) (HoldsVector.get_im hV' i)
    (hR'.get_re i j) (hR'.get_im i j) (by simpa using hg0) (by simpa using hg1) ht' hz'
  have hxl := Store.lt_length_of_get (HoldsVector.get_re hV' i)
  have hyl := Store.lt_length_of_get (hR'.get_re i j)
  have hzl : z.1 < m'.store.length := Store.lt_length_of_get (by simpa using hg0)
  have htl : t.1 < m'.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  have hl : m'.Live [x, y, t, z, z] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb | hb | hb <;> subst b
    all_goals first | exact hxl | exact hyl | exact htl | exact hzl
  refine (hw.in_frame rfl (by simp [Operand.evalList, Operand.eval, Env.frame,
    Env.pushIdx, IExp.eval, x, y]) hl).mono (by simp only [Fp.blocks, sup_bot_eq]; exact le_rfl) ?_
  intro m'' _ h
  refine ⟨h.1.trans hp, ?_⟩
  simpa only [residualPrefix_succ R w j (t := k) (by have := j.isLt; omega)] using h.2

/-- The column-residual routine starts from the current vector entry and computes the exact
sum required by triangular substitution. The source matrix and vector remain untouched.
[GolubVanLoan2013, §3.1.2]. -/
theorem columnResidual_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a v z t : ℕ × ℕ} {R : Matrix (Fin n) (Fin n) ℂ} {w : Fin n → ℂ}
    (j : Fin n) (hR : HoldsMatrix a R m.store) (hV : HoldsVector v w m.store)
    (hza : z.1 ≠ a.1) (hzv : z.1 ≠ v.1) (hta : t.1 ≠ a.1)
    (htv : t.1 ≠ v.1) (htz : t.1 ≠ z.1)
    (hz : z.2 + 2 ≤ m.store.len z.1) (ht : t.2 + 3 ≤ m.store.len t.1) :
    Writes .total I τ columnResidual.body (Env.frame [n, j] [a, v, z, t, z])
      (Store.inBlock t.1 t.2 3 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(residualPrefix R w j j).re, (residualPrefix R w j j).im]) m := by
  let x : ℕ × ℕ := (v.1, v.2 + 2 * j)
  have hcopy := Writes.of_wp_eq_updBlock
    (Hermitian.wp_copyPair_of_disj (md := .total) (τ := τ) (x := x) hS
      (Fp.disj_inBlock_of_ne hzv.symm) (HoldsVector.get_re hV j)
      (HoldsVector.get_im hV j) hz rfl)
  have hw : Writes .total I τ Hermitian.copyPair.body (Env.frame [] [x, z])
      (Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(w j).re, (w j).im]) m := by
    refine hcopy.mono le_rfl ?_
    rintro m' _ rfl
    exact ⟨rfl, Store.readBlock_updBlock_self (by simpa using hz)⟩
  have hal := Store.lt_length_of_get (hR.get_re j j)
  have hvl := Store.lt_length_of_get (HoldsVector.get_re hV j)
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have htl : t.1 < m.store.length := Store.lt_length_of_lt_len (by omega : t.2 < _)
  have hl : m.Live [x, z] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hvl
    · exact hzl
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl (by simp [Operand.evalList, Operand.eval,
    Env.frame, IExp.eval, x]) hl) le_sup_right fun m' hfr ⟨hp, hacc⟩ => ?_
  have hR' := hR.of_eqOff hfr (Fp.disj_inBlock_of_ne hza)
  have hV' : HoldsVector v w m'.store := hfr.keep (readsOnly_holdsVector v w)
    (Fp.disj_inBlock_of_ne hzv) hV
  have hr := residualTerms_writes hS hE (τ := τ) j hR' hV' hza hzv hta htv htz hacc
    (by rw [hfr.len_eq]; exact hz) (by rw [hfr.len_eq]; exact ht)
  have hl' : m'.Live [a, v, z, t, z] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rw [hfr.length_eq] <;> assumption
  exact (hr.in_frame rfl rfl hl').mono le_rfl (fun _ _ h => ⟨h.1.trans hp, h.2⟩)

end NLAlib.ShiftedQR
