/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.Machine
public import NLAlib.Matrix.Factorizations.Givens

/-!
# Stored complex Givens rotations over real scalar arithmetic

The pair kernels compute both output entries in caller-owned scratch before overwriting
either input. Every multiplication, addition and conjugation component is an explicit
real scalar call. Input/output aliasing is exactly the in-place pair update.

## Main results

* `NLAlib.ShiftedQR.decode_linearWords`: exact real arithmetic gives complex linear algebra.
* `NLAlib.ShiftedQR.linearComplex`: the computed complex linear combination on any machine.
* `NLAlib.ShiftedQR.writes_rotateLeftWithScratch_word`,
  `NLAlib.ShiftedQR.writes_rotateRightWithScratch_word`: the pair updates on any machine; the
  exact theorems are their corollaries.
* `NLAlib.ShiftedQR.rotateLeftWithScratch`: the left Givens pair update.
* `NLAlib.ShiftedQR.rotateRightWithScratch`: the right adjoint Givens pair update.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Exact scalar word arithmetic makes the pair linear combination the corresponding
complex linear combination. [GolubVanLoan2013, §5.1.8]. -/
theorem decode_linearWords {K : Type} {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) (a b x y : K × K) :
    decodeComplex dec (Pair.linearWords M a b x y) =
      decodeComplex dec a * decodeComplex dec x + decodeComplex dec b * decodeComplex dec y := by
  apply Complex.ext <;>
    simp [decodeComplex, Pair.linearWords, hM.add, hM.sub, hM.mul]

/-- The complex number stored by `NLAlib.Ops.Pair.linearWords` on the machine `M` from the
components of $a, b, x, y$: the computed $a x + b y$. -/
def linearComplex (M : Machine ℝ) (a b x y : ℂ) : ℂ :=
  ⟨(Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).1,
    (Pair.linearWords M (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)).2⟩

/-- In exact arithmetic the stored linear combination is $a x + b y$. -/
theorem linearComplex_eq {M : Machine ℝ} (hM : ExactModel id M) (a b x y : ℂ) :
    linearComplex M a b x y = a * x + b * y := by
  have h := decode_linearWords hM (a.re, a.im) (b.re, b.im) (x.re, x.im) (y.re, y.im)
  simp only [decodeComplex, id] at h
  exact h

variable {Op Tst : Type} [Has ScalarOp Op]


/-- Address of one caller-owned scalar scratch word. -/
def scratchWord (i : ℕ) : Operand := ⟨4, .var 4 + .const i⟩

/-- Actual scalar instructions for the left in-place pair rotation. -/
def leftInstructions : List (ScalarIns ScalarOp) :=
  [⟨.neg, [⟨1, .var 1⟩], scratchWord 4⟩,
   ⟨.copy, [⟨1, .var 1 + .const 1⟩], scratchWord 5⟩,
   ⟨.copy, [⟨0, .var 0⟩], scratchWord 6⟩,
   ⟨.neg, [⟨0, .var 0 + .const 1⟩], scratchWord 7⟩] ++
  Pair.linearInstructions ⟨0, .var 0⟩ ⟨1, .var 1⟩ ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 0) ++
  Pair.linearInstructions (scratchWord 4) (scratchWord 6) ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 2) ++
  [⟨.copy, [scratchWord 0], ⟨5, .var 5⟩⟩,
   ⟨.copy, [scratchWord 1], ⟨5, .var 5 + .const 1⟩⟩,
   ⟨.copy, [scratchWord 2], ⟨6, .var 6⟩⟩,
   ⟨.copy, [scratchWord 3], ⟨6, .var 6 + .const 1⟩⟩]

/-- Actual scalar instructions for the right in-place pair rotation. -/
def rightInstructions : List (ScalarIns ScalarOp) :=
  [⟨.copy, [⟨0, .var 0⟩], scratchWord 4⟩,
   ⟨.neg, [⟨0, .var 0 + .const 1⟩], scratchWord 5⟩,
   ⟨.copy, [⟨1, .var 1⟩], scratchWord 6⟩,
   ⟨.neg, [⟨1, .var 1 + .const 1⟩], scratchWord 7⟩] ++
  Pair.linearInstructions (scratchWord 4) (scratchWord 6) ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 0) ++
  [⟨.neg, [⟨1, .var 1⟩], scratchWord 4⟩,
   ⟨.neg, [⟨1, .var 1 + .const 1⟩], scratchWord 5⟩] ++
  Pair.linearInstructions (scratchWord 4) ⟨0, .var 0⟩ ⟨2, .var 2⟩ ⟨3, .var 3⟩
    (scratchWord 8) (scratchWord 2) ++
  [⟨.copy, [scratchWord 0], ⟨5, .var 5⟩⟩,
   ⟨.copy, [scratchWord 1], ⟨5, .var 5 + .const 1⟩⟩,
   ⟨.copy, [scratchWord 2], ⟨6, .var 6⟩⟩,
   ⟨.copy, [scratchWord 3], ⟨6, .var 6 + .const 1⟩⟩]

/-- The left Givens update computes both outputs before overwriting either source pair.
Its scalar instruction list uses the shared complex linear-combination kernel. -/
def rotateLeftWithScratch : Impl Op Tst :=
  ⟨0, 5, 2, .scalarBlock (leftInstructions.map ScalarIns.lift)⟩

/-- The right adjoint Givens update computes both outputs in ten scratch words before
copying them back to the exactly aliased input/output views. -/
def rotateRightWithScratch : Impl Op Tst :=
  ⟨0, 5, 2, .scalarBlock (rightInstructions.map ScalarIns.lift)⟩

private def leftPrefix (M : Machine ℝ) (t _x _y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  [((t.1, t.2 + 4), M.neg s.1), ((t.1, t.2 + 5), s.2),
   ((t.1, t.2 + 6), c.1), ((t.1, t.2 + 7), M.neg c.2)] ++
  Pair.linearTrace M (t.1, t.2 + 8) t c s u v ++
  Pair.linearTrace M (t.1, t.2 + 8) (t.1, t.2 + 2)
    (M.neg s.1, s.2) (c.1, M.neg c.2) u v

private def leftTrace (M : Machine ℝ) (t x y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  let p := Pair.linearWords M c s u v
  let q := Pair.linearWords M (M.neg s.1, s.2) (c.1, M.neg c.2) u v
  leftPrefix M t x y c s u v ++
  [(x, p.1), ((x.1, x.2 + 1), p.2), (y, q.1), ((y.1, y.2 + 1), q.2)]

private theorem eval_left {M : Machine ℝ} {m : Mem ℝ} {c s x y t : ℕ × ℕ}
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
    ScalarIns.evalBlock M.eval (Env.frame [] [c, s, x, y, t, x, y]) leftInstructions
      m.store.cellFn = some (leftTrace M t x y cv sv xv yv) := by
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
  dsimp only [leftInstructions, scratchWord, Pair.linearInstructions, leftTrace, leftPrefix,
    Pair.linearTrace, Pair.linearWords, Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      Nat.add_assoc, Nat.add_zero, Nat.reduceAdd, and_false, false_and, if_true, if_false,
      Nat.add_left_cancel_iff, Nat.add_eq_left, Nat.left_eq_add, Nat.reduceEqDiff, *]


private def rightPrefix (M : Machine ℝ) (t _x _y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  [((t.1, t.2 + 4), c.1), ((t.1, t.2 + 5), M.neg c.2),
   ((t.1, t.2 + 6), s.1), ((t.1, t.2 + 7), M.neg s.2)] ++
  Pair.linearTrace M (t.1, t.2 + 8) t (c.1, M.neg c.2) (s.1, M.neg s.2) u v ++
  [((t.1, t.2 + 4), M.neg s.1), ((t.1, t.2 + 5), M.neg s.2)] ++
  Pair.linearTrace M (t.1, t.2 + 8) (t.1, t.2 + 2) (M.neg s.1, M.neg s.2) c u v

private def rightTrace (M : Machine ℝ) (t x y : ℕ × ℕ) (c s u v : ℝ × ℝ) :=
  let p := Pair.linearWords M (c.1, M.neg c.2) (s.1, M.neg s.2) u v
  let q := Pair.linearWords M (M.neg s.1, M.neg s.2) c u v
  rightPrefix M t x y c s u v ++
  [(x, p.1), ((x.1, x.2 + 1), p.2), (y, q.1), ((y.1, y.2 + 1), q.2)]

private theorem eval_right {M : Machine ℝ} {m : Mem ℝ} {c s x y t : ℕ × ℕ}
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
    ScalarIns.evalBlock M.eval (Env.frame [] [c, s, x, y, t, x, y]) rightInstructions
      m.store.cellFn = some (rightTrace M t x y cv sv xv yv) := by
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
  dsimp only [rightInstructions, scratchWord, Pair.linearInstructions, rightTrace, rightPrefix,
    Pair.linearTrace, Pair.linearWords, Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      Nat.add_assoc, Nat.add_zero, Nat.reduceAdd, and_false, false_and, if_true, if_false,
      Nat.add_left_cancel_iff, Nat.add_eq_left, Nat.left_eq_add, Nat.reduceEqDiff, *]


/-- The actual left scalar rotation on any machine always terminates and stores the two
computed versions of $c x + s y$ and $-\bar s x + \bar c y$. Conjugations use the machine's
negation operation. Input/output views are exactly aliased. [GolubVanLoan2013, §5.1.8]. -/
theorem writes_rotateLeftWithScratch_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hI : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
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
    Writes .total I τ rotateLeftWithScratch.body (Env.frame [] [c, s, x, y, t, x, y])
      (Fp.blocks [t, x, y] [10, 2, 2])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [x, y] [2, 2] =
        some [[(linearComplex M cv sv xv yv).re, (linearComplex M cv sv xv yv).im],
          [(linearComplex M ⟨M.neg sv.re, sv.im⟩ ⟨cv.re, M.neg cv.im⟩ xv yv).re,
            (linearComplex M ⟨M.neg sv.re, sv.im⟩ ⟨cv.re, M.neg cv.im⟩ xv yv).im]]) m := by
  let ws := leftTrace M t x y (cv.re, cv.im) (sv.re, sv.im) (xv.re, xv.im) (yv.re, yv.im)
  have hev := eval_left (M := M) (m := m)
    (cv := (cv.re, cv.im)) (sv := (sv.re, sv.im))
    (xv := (xv.re, xv.im)) (yv := (yv.re, yv.im)) htc hts htx hty hc0 hc1 hs0 hs1 hx0 hx1 hy0 hy1
  have hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, leftTrace, leftPrefix, Pair.linearTrace, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have hwrite := writes_machineScalarBlock (τ := τ) hI hev hroom
  change Writes .total I τ rotateLeftWithScratch.body _ _ _ m at hwrite
  refine hwrite.mono ?_ ?_
  · intro b i hi
    simp only [leftTrace, leftPrefix, Pair.linearTrace, List.map_append, List.map_cons,
      List.map_nil, Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq, or_assoc] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h <;> obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    refine ⟨rfl, ?_⟩
    exact Pair.readBlocks_updCells_pairs (m := m)
      (prior := leftPrefix M t x y (cv.re, cv.im) (sv.re, sv.im)
        (xv.re, xv.im) (yv.re, yv.im))
      (u := Pair.linearWords M (cv.re, cv.im) (sv.re, sv.im) (xv.re, xv.im) (yv.re, yv.im))
      (v := Pair.linearWords M (M.neg sv.re, sv.im) (cv.re, M.neg cv.im)
        (xv.re, xv.im) (yv.re, yv.im)) hxy hx hy

/-- The actual left scalar rotation always terminates under the exact scalar model and
stores the two mathematical Givens outputs. Input/output views are exactly aliased.
[GolubVanLoan2013, §5.1.8]. -/
theorem writes_rotateLeftWithScratch {M : Machine ℝ} {I : Interp Op Tst ℝ}
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
    Writes .total I τ rotateLeftWithScratch.body (Env.frame [] [c, s, x, y, t, x, y])
      (Fp.blocks [t, x, y] [10, 2, 2])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [x, y] [2, 2] =
        some [[(cv*xv+sv*yv).re, (cv*xv+sv*yv).im],
          [(-star sv*xv+star cv*yv).re, (-star sv*xv+star cv*yv).im]]) m := by
  refine (writes_rotateLeftWithScratch_word hI htc hts htx hty hxy hc0 hc1 hs0 hs1 hx0 hx1
    hy0 hy1 ht hx hy).mono le_rfl ?_
  rintro μ _ ⟨hp, hr⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  have hs : (⟨M.neg sv.re, sv.im⟩ : ℂ) = -star sv := by
    apply Complex.ext <;> simp [hneg]
  have hc : (⟨cv.re, M.neg cv.im⟩ : ℂ) = star cv := by
    apply Complex.ext <;> simp [hneg]
  rw [hs, hc, linearComplex_eq hM, linearComplex_eq hM] at hr
  exact ⟨hp, hr⟩


/-- The actual right adjoint scalar rotation on any machine always terminates and stores the
two computed outputs $\bar c x + \bar s y$ and $-s x + c y$, the conjugations by exact negation
of the words. Input/output views are exactly aliased. [GolubVanLoan2013, §5.1.8]. -/
theorem writes_rotateRightWithScratch_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hI : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
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
    Writes .total I τ rotateRightWithScratch.body (Env.frame [] [c, s, x, y, t, x, y])
      (Fp.blocks [t, x, y] [10, 2, 2])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [x, y] [2, 2] =
        some [[(linearComplex M ⟨cv.re, M.neg cv.im⟩ ⟨sv.re, M.neg sv.im⟩ xv yv).re,
            (linearComplex M ⟨cv.re, M.neg cv.im⟩ ⟨sv.re, M.neg sv.im⟩ xv yv).im],
          [(linearComplex M ⟨M.neg sv.re, M.neg sv.im⟩ cv xv yv).re,
            (linearComplex M ⟨M.neg sv.re, M.neg sv.im⟩ cv xv yv).im]]) m := by
  let ws := rightTrace M t x y (cv.re, cv.im) (sv.re, sv.im) (xv.re, xv.im) (yv.re, yv.im)
  have hev := eval_right (M := M) (m := m)
    (cv := (cv.re, cv.im)) (sv := (sv.re, sv.im))
    (xv := (xv.re, xv.im)) (yv := (yv.re, yv.im)) htc hts htx hty hc0 hc1 hs0 hs1 hx0 hx1 hy0 hy1
  have hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, rightTrace, rightPrefix, Pair.linearTrace, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have hwrite := writes_machineScalarBlock (τ := τ) hI hev hroom
  change Writes .total I τ rotateRightWithScratch.body _ _ _ m at hwrite
  refine hwrite.mono ?_ ?_
  · intro b i hi
    simp only [rightTrace, rightPrefix, Pair.linearTrace, List.map_append, List.map_cons,
      List.map_nil, Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq, or_assoc] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h <;> obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    refine ⟨rfl, ?_⟩
    exact Pair.readBlocks_updCells_pairs (m := m)
      (prior := rightPrefix M t x y (cv.re, cv.im) (sv.re, sv.im)
        (xv.re, xv.im) (yv.re, yv.im))
      (u := Pair.linearWords M (cv.re, M.neg cv.im) (sv.re, M.neg sv.im)
        (xv.re, xv.im) (yv.re, yv.im))
      (v := Pair.linearWords M (M.neg sv.re, M.neg sv.im) (cv.re, cv.im)
        (xv.re, xv.im) (yv.re, yv.im)) hxy hx hy

/-- The actual right adjoint scalar rotation always terminates under the exact scalar model and
stores the two mathematical Givens outputs. Input/output views are exactly aliased.
[GolubVanLoan2013, §5.1.8]. -/
theorem writes_rotateRightWithScratch {M : Machine ℝ} {I : Interp Op Tst ℝ}
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
    Writes .total I τ rotateRightWithScratch.body (Env.frame [] [c, s, x, y, t, x, y])
      (Fp.blocks [t, x, y] [10, 2, 2])
      (fun μ => μ.pos = m.pos ∧ μ.readBlocks [x, y] [2, 2] =
        some [[(xv*star cv+yv*star sv).re, (xv*star cv+yv*star sv).im],
          [(-xv*sv+yv*cv).re, (-xv*sv+yv*cv).im]]) m := by
  refine (writes_rotateRightWithScratch_word hI htc hts htx hty hxy hc0 hc1 hs0 hs1 hx0 hx1
    hy0 hy1 ht hx hy).mono le_rfl ?_
  rintro μ _ ⟨hp, hr⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  have hc : (⟨cv.re, M.neg cv.im⟩ : ℂ) = star cv := by
    apply Complex.ext <;> simp [hneg]
  have hs : (⟨sv.re, M.neg sv.im⟩ : ℂ) = star sv := by
    apply Complex.ext <;> simp [hneg]
  have hn : (⟨M.neg sv.re, M.neg sv.im⟩ : ℂ) = -sv := by
    apply Complex.ext <;> simp [hneg]
  rw [hc, hs, hn, linearComplex_eq hM, linearComplex_eq hM] at hr
  refine ⟨hp, ?_⟩
  rw [hr]
  simp only [mul_comm, mul_neg]

end NLAlib.ShiftedQR
