/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.Machine

/-!
# Complex division by actual scalar operations

The denominator is its sum of two real squares. Both numerators are computed before either
output word is overwritten, permitting exact aliases with either input pair. A nonzero
complex denominator is the mathematical hypothesis ensuring the real divisions are valid.

## Main results

* `NLAlib.ShiftedQR.complexDivideWithScratch`: eleven scalar instructions and four scratch words.
* `NLAlib.ShiftedQR.complexDivideWithScratch_writes`: exact quotient under the exact scalar model.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The actual eleven scalar instructions for complex division. -/
def divisionInstructions : List (ScalarIns ScalarOp) :=
  [⟨.mul, [⟨1, .var 1⟩, ⟨1, .var 1⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨1, .var 1 + .const 1⟩, ⟨1, .var 1 + .const 1⟩],
     ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.add, [⟨2, .var 2⟩, ⟨2, .var 2 + .const 3⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1⟩], ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1 + .const 1⟩],
     ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2 + .const 3⟩],
     ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1⟩], ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1 + .const 1⟩], ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.sub, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2 + .const 3⟩],
     ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2⟩], ⟨3, .var 3⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2⟩], ⟨3, .var 3 + .const 1⟩⟩]

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Compute a complex quotient with four caller-owned scratch words. -/
def complexDivideWithScratch : Impl Op Tst :=
  ⟨0, 3, 1, .scalarBlock (divisionInstructions.map ScalarIns.lift)⟩

private def divisionPrefix (M : Machine ℝ) (t : ℕ × ℕ) (x y : ℝ × ℝ) :=
  let d₀ := M.mul y.1 y.1
  let d₁ := M.mul y.2 y.2
  let r₀ := M.mul x.1 y.1
  let r₁ := M.mul x.2 y.2
  let i₀ := M.mul x.2 y.1
  let i₁ := M.mul x.1 y.2
  [(t, d₀), ((t.1, t.2 + 3), d₁), (t, M.add d₀ d₁),
   ((t.1, t.2 + 1), r₀), ((t.1, t.2 + 3), r₁), ((t.1, t.2 + 1), M.add r₀ r₁),
   ((t.1, t.2 + 2), i₀), ((t.1, t.2 + 3), i₁), ((t.1, t.2 + 2), M.sub i₀ i₁)]

private def divisionWords (M : Machine ℝ) (x y : ℝ × ℝ) : ℝ × ℝ :=
  let d := M.add (M.mul y.1 y.1) (M.mul y.2 y.2)
  (M.div (M.add (M.mul x.1 y.1) (M.mul x.2 y.2)) d,
    M.div (M.sub (M.mul x.2 y.1) (M.mul x.1 y.2)) d)

private def divisionTrace (M : Machine ℝ) (t z : ℕ × ℕ) (x y : ℝ × ℝ) :=
  divisionPrefix M t x y ++
    [(z, (divisionWords M x y).1), ((z.1, z.2 + 1), (divisionWords M x y).2)]

private theorem eval_division {M : Machine ℝ} {m : Mem ℝ} {x y t z : ℕ × ℕ}
    {xv yv : ℝ × ℝ} (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1) (htz : t.1 ≠ z.1)
    (hx0 : m.store.get x.1 x.2 = some xv.1)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.2)
    (hy0 : m.store.get y.1 y.2 = some yv.1)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.2) :
    ScalarIns.evalBlock M.eval (Env.frame [] [x, y, t, z]) divisionInstructions
      m.store.cellFn = some (divisionTrace M t z xv yv) := by
  have hxt := Ne.symm htx
  have hyt := Ne.symm hty
  have hzt := Ne.symm htz
  rcases x with ⟨xb, xo⟩
  rcases y with ⟨yb, yo⟩
  rcases t with ⟨tb, toff⟩
  rcases z with ⟨zb, zo⟩
  have hupd (g : ℕ × ℕ → Option ℝ) (u w : ℕ × ℕ) (v : Option ℝ) :
      Function.update g u v w = if w = u then v else g w := Function.update_apply ..
  have hpair := @Prod.mk.injEq ℕ ℕ
  dsimp only [divisionInstructions, divisionTrace, divisionPrefix, divisionWords,
    Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      and_false, false_and, if_true, if_false,
      Nat.add_left_cancel_iff, Nat.add_eq_left, Nat.left_eq_add, Nat.reduceEqDiff, *]

private theorem decode_divisionWords {M : Machine ℝ} (hM : ExactModel id M)
    (x y : ℂ) (hy : y ≠ 0) :
    decodeComplex id (divisionWords M (x.re, x.im) (y.re, y.im)) = x / y := by
  have hadd (a b : ℝ) : M.add a b = a + b := hM.add a b
  have hsub (a b : ℝ) : M.sub a b = a - b := hM.sub a b
  have hmul (a b : ℝ) : M.mul a b = a * b := hM.mul a b
  have hd : M.add (M.mul y.re y.re) (M.mul y.im y.im) = Complex.normSq y := by
    simp only [hadd, hmul, Complex.normSq_apply]
  have hne : Complex.normSq y ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hy)
  have hdiv (a : ℝ) : M.div a (M.add (M.mul y.re y.re) (M.mul y.im y.im)) =
      a / Complex.normSq y := by
    simpa only [hd, id_eq] using hM.div a _ (by simpa only [hd, id_eq] using hne)
  apply Complex.ext
  · dsimp only [decodeComplex, divisionWords, id_eq]
    rw [hdiv]
    simp only [hadd, hmul, Complex.div_re, add_div]
  · dsimp only [decodeComplex, divisionWords, id_eq]
    rw [hdiv]
    simp only [hsub, hmul, Complex.div_im, sub_div]

/-- Eleven actual scalar instructions compute the exact quotient whenever the complex
input denominator is nonzero. Both inputs may exactly alias the output pair, since the
numerators are retained before either output is written. [GolubVanLoan2013, §1.1.3]. -/
theorem complexDivideWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hI : IsScalar M I) (hM : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {x y t z : ℕ × ℕ} {xv yv : ℂ}
    (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1) (htz : t.1 ≠ z.1) (hyv : yv ≠ 0)
    (hx0 : m.store.get x.1 x.2 = some xv.re)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.im)
    (hy0 : m.store.get y.1 y.2 = some yv.re)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.im)
    (ht : t.2 + 4 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ complexDivideWithScratch.body (Env.frame [] [x, y, t, z])
      (Fp.blocks [t, z] [4, 2])
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock z.1 z.2 2 =
        some [(xv / yv).re, (xv / yv).im]) m := by
  have hev := eval_division (M := M) (m := m) (xv := (xv.re, xv.im))
    (yv := (yv.re, yv.im)) htx hty htz hx0 hx1 hy0 hy1
  have hroom : ∀ w ∈ divisionTrace M t z (xv.re, xv.im) (yv.re, yv.im),
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [divisionTrace, divisionPrefix, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp <;> omega
  have hwrite := writes_machineScalarBlock (τ := τ) hI hev hroom
  change Writes .total I τ complexDivideWithScratch.body _ _ _ m at hwrite
  refine hwrite.mono ?_ ?_
  · intro b i hi
    simp only [divisionTrace, divisionPrefix, List.map_append, List.map_cons, List.map_nil,
      Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      or_assoc] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h <;>
      obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    have he := decode_divisionWords hM xv yv hyv
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp only [decodeComplex, id_eq] at hr hi
    have hout := Pair.readBlock_updCells_pair (m := m)
      (prior := divisionPrefix M t (xv.re, xv.im) (yv.re, yv.im))
      (v := divisionWords M (xv.re, xv.im) (yv.re, yv.im)) hz
    exact ⟨rfl, by simpa only [divisionTrace, hr, hi] using hout⟩


end NLAlib.ShiftedQR
