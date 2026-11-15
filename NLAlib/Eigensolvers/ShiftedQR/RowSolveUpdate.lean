/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Matrix.FinitePrecision.Machine

/-!
# Scalar multiply-subtract for forward substitution

The accumulator pair is updated by subtracting a complex product. All six product operations
finish in three scratch words before either accumulator component is overwritten.

## Main results

* `NLAlib.ShiftedQR.subtractProductWithScratch`: eight real scalar operations.
* `NLAlib.ShiftedQR.subtractProductWithScratch_writes`: the exact complex accumulator update.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Real scalar instructions for the complex update $z \leftarrow z-xy$. -/
def subtractProductInstructions : List (ScalarIns ScalarOp) :=
  [⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1 + .const 1⟩],
     ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.sub, [⟨2, .var 2⟩, ⟨2, .var 2 + .const 1⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1 + .const 1⟩], ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1⟩], ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2 + .const 2⟩],
     ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.sub, [⟨3, .var 3⟩, ⟨2, .var 2⟩], ⟨3, .var 3⟩⟩,
   ⟨.sub, [⟨3, .var 3 + .const 1⟩, ⟨2, .var 2 + .const 1⟩],
     ⟨3, .var 3 + .const 1⟩⟩]

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Subtract a complex product from an accumulator, reusing three scratch words. -/
def subtractProductWithScratch : Impl Op Tst :=
  ⟨0, 4, 1, .scalarBlock (subtractProductInstructions.map ScalarIns.lift)⟩

private def subtractProductWords (M : Machine ℝ) (x y z : ℝ × ℝ) : ℝ × ℝ :=
  (M.sub z.1 (M.sub (M.mul x.1 y.1) (M.mul x.2 y.2)),
    M.sub z.2 (M.add (M.mul x.1 y.2) (M.mul x.2 y.1)))

private def subtractProductPrefix (M : Machine ℝ) (t : ℕ × ℕ) (x y : ℝ × ℝ) :=
  [(t, M.mul x.1 y.1), ((t.1, t.2 + 1), M.mul x.2 y.2),
   (t, M.sub (M.mul x.1 y.1) (M.mul x.2 y.2)),
   ((t.1, t.2 + 1), M.mul x.1 y.2), ((t.1, t.2 + 2), M.mul x.2 y.1),
   ((t.1, t.2 + 1), M.add (M.mul x.1 y.2) (M.mul x.2 y.1))]

private def subtractProductTrace (M : Machine ℝ) (t z : ℕ × ℕ) (x y w : ℝ × ℝ) :=
  subtractProductPrefix M t x y ++
    [(z, (subtractProductWords M x y w).1),
      ((z.1, z.2 + 1), (subtractProductWords M x y w).2)]

private theorem eval_subtractProduct {M : Machine ℝ} {m : Mem ℝ}
    {x y t z : ℕ × ℕ} {xv yv zv : ℝ × ℝ}
    (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1) (htz : t.1 ≠ z.1)
    (hx0 : m.store.get x.1 x.2 = some xv.1)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.2)
    (hy0 : m.store.get y.1 y.2 = some yv.1)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.2)
    (hz0 : m.store.get z.1 z.2 = some zv.1)
    (hz1 : m.store.get z.1 (z.2 + 1) = some zv.2) :
    ScalarIns.evalBlock M.eval (Env.frame [] [x, y, t, z, z]) subtractProductInstructions
      m.store.cellFn = some (subtractProductTrace M t z xv yv zv) := by
  have hxt := htx.symm
  have hyt := hty.symm
  have hzt := htz.symm
  rcases x with ⟨xb, xo⟩
  rcases y with ⟨yb, yo⟩
  rcases t with ⟨tb, toff⟩
  rcases z with ⟨zb, zo⟩
  have hupd (g : ℕ × ℕ → Option ℝ) (u w : ℕ × ℕ) (v : Option ℝ) :
      Function.update g u v w = if w = u then v else g w := Function.update_apply ..
  have hpair (x₁ x₂ y₁ y₂ : ℕ) :
      ((x₁, x₂) = (y₁, y₂)) = (x₁ = y₁ ∧ x₂ = y₂) := Prod.mk.injEq ..
  simp only [subtractProductInstructions, subtractProductTrace, subtractProductPrefix,
    subtractProductWords, List.cons_append, List.nil_append]
  dsimp only [Env.frame]
  repeat' first
    | rw [ScalarIns.evalBlock.eq_def]
      dsimp only [Machine.eval, Operand.evalList, Operand.eval, IExp.eval]
      simp only [Store.cellFn, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero,
        List.nil_append, Nat.reduceLT, List.getElem_cons_succ, Option.bind_some,
        List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, false_and,
        and_false, if_true, if_false, Nat.add_left_cancel_iff, Nat.add_eq_left,
        Nat.left_eq_add, Nat.reduceEqDiff, *]
  rfl

/-- The actual scalar program subtracts a complex product from the accumulator. Inputs and
accumulator may overlap because both product components are captured before the output writes.
The scratch buffer is separate. [GolubVanLoan2013, §3.1.2]. -/
theorem subtractProductWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {x y t z : ℕ × ℕ} {xv yv zv : ℂ}
    (htx : t.1 ≠ x.1) (hty : t.1 ≠ y.1) (htz : t.1 ≠ z.1)
    (hx0 : m.store.get x.1 x.2 = some xv.re)
    (hx1 : m.store.get x.1 (x.2 + 1) = some xv.im)
    (hy0 : m.store.get y.1 y.2 = some yv.re)
    (hy1 : m.store.get y.1 (y.2 + 1) = some yv.im)
    (hz0 : m.store.get z.1 z.2 = some zv.re)
    (hz1 : m.store.get z.1 (z.2 + 1) = some zv.im)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ subtractProductWithScratch.body (Env.frame [] [x, y, t, z, z])
      (Fp.blocks [t, z] [3, 2])
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(zv - xv * yv).re, (zv - xv * yv).im]) m := by
  have hev := eval_subtractProduct (M := M) (m := m) (xv := (xv.re, xv.im))
    (yv := (yv.re, yv.im)) (zv := (zv.re, zv.im)) htx hty htz hx0 hx1 hy0 hy1 hz0 hz1
  have hroom : ∀ w ∈ subtractProductTrace M t z (xv.re, xv.im) (yv.re, yv.im) (zv.re, zv.im),
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [subtractProductTrace, subtractProductPrefix, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have hw := writes_machineScalarBlock (τ := τ) hS hev hroom
  change Writes .total I τ subtractProductWithScratch.body _ _ _ m at hw
  refine hw.mono ?_ ?_
  · intro b i hi
    simp only [subtractProductTrace, subtractProductPrefix, List.map_append, List.map_cons,
      List.map_nil, Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq, or_assoc] at hi
    rcases hi with h | h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl⟩ := h
    all_goals simp only [Fp.blocks, sup_bot_eq]
    all_goals
      first
      | exact Or.inl ⟨rfl, by omega, by omega⟩
      | exact Or.inr ⟨rfl, by omega, by omega⟩
  · rintro m' _ rfl
    refine ⟨rfl, ?_⟩
    have h := Pair.readBlock_updCells_pair (m := m)
      (prior := subtractProductPrefix M t (xv.re, xv.im) (yv.re, yv.im))
      (v := subtractProductWords M (xv.re, xv.im) (yv.re, yv.im) (zv.re, zv.im)) hz
    have hsub : ∀ x y, M.sub x y = x - y := hE.sub
    have hmul : ∀ x y, M.mul x y = x * y := hE.mul
    have hadd : ∀ x y, M.add x y = x + y := hE.add
    simpa only [subtractProductTrace, subtractProductWords, hsub, hmul, hadd,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] using h

end NLAlib.ShiftedQR
