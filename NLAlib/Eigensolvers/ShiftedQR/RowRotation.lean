/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Rotation

/-!
# Complex row-vector Givens rotation

The actual scalar kernel forms the two entries of a row vector multiplied by the Givens
matrix. Both outputs are retained in scratch before their exactly aliased sources change.

## Main results

* `NLAlib.ShiftedQR.rotateRowWithScratch`: actual scalar computation of row-vector times Givens.
* `NLAlib.ShiftedQR.writes_rotateRowWithScratch`: total exact mathematical pair output.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Actual scalar instructions for row-vector multiplication by the Givens matrix. -/
def rowInstructions : List (ScalarIns ScalarOp) :=
  [⟨.neg, [⟨1, .var 1⟩], scratchWord 4⟩,
   ⟨.copy, [⟨1, .var 1 + .const 1⟩], scratchWord 5⟩,
   ⟨.copy, [⟨0, .var 0⟩], scratchWord 6⟩,
   ⟨.neg, [⟨0, .var 0 + .const 1⟩], scratchWord 7⟩] ++
  Pair.linearInstructions ⟨0, .var 0⟩ (scratchWord 4) ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 0) ++
  Pair.linearInstructions ⟨1, .var 1⟩ (scratchWord 6) ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 2) ++
  [⟨.copy, [scratchWord 0], ⟨5, .var 5⟩⟩,
   ⟨.copy, [scratchWord 1], ⟨5, .var 5 + .const 1⟩⟩,
   ⟨.copy, [scratchWord 2], ⟨6, .var 6⟩⟩,
   ⟨.copy, [scratchWord 3], ⟨6, .var 6 + .const 1⟩⟩]

/-- Rotate a stored complex row-vector by the Givens matrix using ten scratch words. -/
def rotateRowWithScratch : Impl Op Tst :=
  ⟨0, 5, 2, .scalarBlock (rowInstructions.map ScalarIns.lift)⟩

private def rowPrefix (M : Machine ℝ) (t _x _y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  [((t.1, t.2 + 4), M.neg s.1), ((t.1, t.2 + 5), s.2),
   ((t.1, t.2 + 6), c.1), ((t.1, t.2 + 7), M.neg c.2)] ++
  Pair.linearTrace M (t.1, t.2 + 8) t c (M.neg s.1, s.2) u v ++
  Pair.linearTrace M (t.1, t.2 + 8) (t.1, t.2 + 2)
    s (c.1, M.neg c.2) u v

private def rowTrace (M : Machine ℝ) (t x y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  let p := Pair.linearWords M c (M.neg s.1, s.2) u v
  let q := Pair.linearWords M s (c.1, M.neg c.2) u v
  rowPrefix M t x y c s u v ++
  [(x, p.1), ((x.1, x.2 + 1), p.2), (y, q.1), ((y.1, y.2 + 1), q.2)]

private theorem eval_row {M : Machine ℝ} {m : Mem ℝ} {c s x y t : ℕ × ℕ}
    {cv sv xv yv : ℝ × ℝ}
    (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1) (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1)
    (hc0 : m.store.get c.1 c.2 = some cv.1)
    (hc1 : m.store.get c.1 (c.2 + 1) = some cv.2)
    (hs0 : m.store.get s.1 s.2 = some sv.1)
    (hs1 : m.store.get s.1 (s.2 + 1) = some sv.2)
    (hx0 : m.store.get x.1 x.2 = some xv.1)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.2)
    (hy0 : m.store.get y.1 y.2 = some yv.1)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.2) :
    ScalarIns.evalBlock M.eval (Env.frame [] [c, s, x, y, t, x, y]) rowInstructions
      m.store.cellFn = some (rowTrace M t x y cv sv xv yv) := by
  have hct := Ne.symm htc
  have hst := Ne.symm hts
  have hxt := Ne.symm htx
  have hyt := Ne.symm hty
  rcases c with ⟨cb, co⟩
  rcases s with ⟨sb, so⟩
  rcases x with ⟨xb, xo⟩
  rcases y with ⟨yb, yo⟩
  rcases t with ⟨tb, toff⟩
  have hupd (g : ℕ × ℕ → Option ℝ) (u w : ℕ × ℕ) (v : Option ℝ) :
      Function.update g u v w = if w = u then v else g w := Function.update_apply ..
  have hpair := @Prod.mk.injEq ℕ ℕ
  dsimp only [rowInstructions, scratchWord, Pair.linearInstructions, rowTrace, rowPrefix,
    Pair.linearTrace, Pair.linearWords, Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      Nat.add_assoc, Nat.add_zero, Nat.reduceAdd, and_false, false_and, if_true, if_false,
      Nat.add_left_cancel_iff, Nat.add_eq_left, Nat.left_eq_add, Nat.reduceEqDiff, *]


/-- The actual row-vector scalar rotation always terminates under the exact scalar model and
stores the two mathematical Givens outputs. Input/output views are exactly aliased.
[GolubVanLoan2013, §5.1.8]. -/
theorem writes_rotateRowWithScratch {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hI : IsScalar M I) (hM : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {c s x y t : ℕ × ℕ} {cv sv xv yv : ℂ}
    (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1) (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock y.1 y.2 2))
    (hc0 : m.store.get c.1 c.2 = some cv.re)
    (hc1 : m.store.get c.1 (c.2 + 1) = some cv.im)
    (hs0 : m.store.get s.1 s.2 = some sv.re)
    (hs1 : m.store.get s.1 (s.2 + 1) = some sv.im)
    (hx0 : m.store.get x.1 x.2 = some xv.re)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.im)
    (hy0 : m.store.get y.1 y.2 = some yv.re)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.im)
    (ht : t.2 + 10 ≤ m.store.len t.1)
    (hx : x.2 + 2 ≤ m.store.len x.1) (hy : y.2 + 2 ≤ m.store.len y.1) :
    Writes .total I τ rotateRowWithScratch.body (Env.frame [] [c, s, x, y, t, x, y])
      (Fp.blocks [t, x, y] [10, 2, 2])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [x, y] [2, 2] =
        some [[(xv*cv-yv*star sv).re, (xv*cv-yv*star sv).im],
          [(xv*sv+yv*star cv).re, (xv*sv+yv*star cv).im]]) m := by
  let ws := rowTrace M t x y (cv.re, cv.im) (sv.re, sv.im) (xv.re, xv.im) (yv.re, yv.im)
  have hev := eval_row (M := M) (m := m)
    (cv := (cv.re, cv.im)) (sv := (sv.re, sv.im))
    (xv := (xv.re, xv.im)) (yv := (yv.re, yv.im)) htc hts htx hty hc0 hc1 hs0 hs1 hx0 hx1 hy0 hy1
  have hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, rowTrace, rowPrefix, Pair.linearTrace, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have hwrite := writes_machineScalarBlock (τ := τ) hI hev hroom
  change Writes .total I τ rotateRowWithScratch.body _ _ _ m at hwrite
  refine hwrite.mono ?_ ?_
  · intro b i hi
    simp only [rowTrace, rowPrefix, Pair.linearTrace, List.map_append, List.map_cons,
      List.map_nil, Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq, or_assoc] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h <;> obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    have hneg (r : ℝ) : M.neg r = -r := hM.neg r
    have hs : decodeComplex id (M.neg sv.re, sv.im) = -star sv := by
      apply Complex.ext <;> simp [decodeComplex, hneg]
    have hc : decodeComplex id (cv.re, M.neg cv.im) = star cv := by
      apply Complex.ext <;> simp [decodeComplex, hneg]
    have hp := decode_linearWords hM (cv.re, cv.im) (M.neg sv.re, sv.im)
      (xv.re, xv.im) (yv.re, yv.im)
    have hq := decode_linearWords hM (sv.re, sv.im) (cv.re, M.neg cv.im)
      (xv.re, xv.im) (yv.re, yv.im)
    rw [hs] at hp
    rw [hc] at hq
    simp only [decodeComplex, id_eq, Complex.eta] at hp hq
    have hpr := congrArg Complex.re hp
    have hpi := congrArg Complex.im hp
    have hqr := congrArg Complex.re hq
    have hqi := congrArg Complex.im hq
    dsimp only at hpr hpi hqr hqi
    have hout := Pair.readBlocks_updCells_pairs (m := m)
      (prior := rowPrefix M t x y (cv.re, cv.im) (sv.re, sv.im)
        (xv.re, xv.im) (yv.re, yv.im))
      (u := Pair.linearWords M (cv.re, cv.im) (M.neg sv.re, sv.im)
        (xv.re, xv.im) (yv.re, yv.im))
      (v := Pair.linearWords M (sv.re, sv.im) (cv.re, M.neg cv.im)
        (xv.re, xv.im) (yv.re, yv.im)) hxy hx hy
    refine ⟨rfl, ?_⟩
    simpa only [rowTrace, hpr, hpi, hqr, hqi, mul_comm, mul_neg, neg_mul, sub_eq_add_neg]
      using hout



end NLAlib.ShiftedQR
