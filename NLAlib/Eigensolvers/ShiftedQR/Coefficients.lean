/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.ScalarOutput
public import NLAlib.Ops.Logic.SpatialScalar
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Matrix.Factorizations.Givens

/-!
# Givens coefficients computed from real scalar words

Complex inputs use two adjacent real words. The program copies their four components into
scratch, computes the radius by four real squares and a square root, and branches on its
actual computed zero test. The zero branch returns the identity rotation. The other branch
divides conjugated components by the positive radius. No rotation operation is a primitive.

## Main results

* `NLAlib.ShiftedQR.coefficientsWithScratch` is the scalar coefficient program.
* `NLAlib.ShiftedQR.coefficients` scopes its seven scratch cells.
* `NLAlib.ShiftedQR.coefficientsWithScratch_writes` proves the caller-scratch routine total.
* `NLAlib.ShiftedQR.coefficients_writes` proves the scoped routine computes `givensCoeffs`.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Capture the four input words and compute their Euclidean radius in scratch cell four.
Scratch cells five and six are reused while accumulating the four squares. -/
def coefficientPrefix : List (ScalarIns ScalarOp) :=
  [⟨.copy, [⟨0, .var 0⟩], ⟨2, .var 2⟩⟩,
   ⟨.copy, [⟨0, .var 0 + .const 1⟩], ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.copy, [⟨1, .var 1⟩], ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.copy, [⟨1, .var 1 + .const 1⟩], ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.mul, [⟨2, .var 2⟩, ⟨2, .var 2⟩], ⟨2, .var 2 + .const 4⟩⟩,
   ⟨.mul, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2 + .const 1⟩], ⟨2, .var 2 + .const 5⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 4⟩, ⟨2, .var 2 + .const 5⟩], ⟨2, .var 2 + .const 4⟩⟩,
   ⟨.mul, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2 + .const 2⟩], ⟨2, .var 2 + .const 5⟩⟩,
   ⟨.mul, [⟨2, .var 2 + .const 3⟩, ⟨2, .var 2 + .const 3⟩], ⟨2, .var 2 + .const 6⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 5⟩, ⟨2, .var 2 + .const 6⟩], ⟨2, .var 2 + .const 5⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 4⟩, ⟨2, .var 2 + .const 5⟩], ⟨2, .var 2 + .const 4⟩⟩,
   ⟨.sqrt, [⟨2, .var 2 + .const 4⟩], ⟨2, .var 2 + .const 4⟩⟩]

/-- The zero-pair branch writes the identity rotation's two complex coefficients. -/
def coefficientZero : List (ScalarIns ScalarOp) :=
  [⟨.lit 1, [], ⟨3, .var 3⟩⟩, ⟨.lit 0, [], ⟨3, .var 3 + .const 1⟩⟩,
   ⟨.lit 0, [], ⟨4, .var 4⟩⟩, ⟨.lit 0, [], ⟨4, .var 4 + .const 1⟩⟩]

/-- The nonzero branch divides the conjugated input components by the captured radius. -/
def coefficientDivide : List (ScalarIns ScalarOp) :=
  [⟨.neg, [⟨2, .var 2 + .const 1⟩], ⟨2, .var 2 + .const 5⟩⟩,
   ⟨.neg, [⟨2, .var 2 + .const 3⟩], ⟨2, .var 2 + .const 6⟩⟩,
   ⟨.div, [⟨2, .var 2⟩, ⟨2, .var 2 + .const 4⟩], ⟨3, .var 3⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 5⟩, ⟨2, .var 2 + .const 4⟩], ⟨3, .var 3 + .const 1⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2 + .const 4⟩], ⟨4, .var 4⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 6⟩, ⟨2, .var 2 + .const 4⟩], ⟨4, .var 4 + .const 1⟩⟩]

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Compute the two Givens coefficients using seven caller-owned scratch cells. Inputs and
outputs are two-word complex views; the captured inputs permit exact output/input aliasing. -/
def coefficientsWithScratch : Impl Op Tst := ⟨0, 3, 2,
  .seq (.scalarBlock (coefficientPrefix.map ScalarIns.lift))
    (.ite (Has.inj CmpTst.isZero) [] [⟨2, .var 2 + .const 4⟩]
      (.scalarBlock (coefficientZero.map ScalarIns.lift))
      (.scalarBlock (coefficientDivide.map ScalarIns.lift)))⟩

/-- The coefficient routine with one scoped scratch buffer of seven real words. -/
def coefficients : Impl Op Tst := ⟨0, 2, 2,
  .alloc (.const 7) (.frame []
    [⟨0, .var 0⟩, ⟨1, .var 1⟩, ⟨4, .const 0⟩, ⟨2, .var 2⟩, ⟨3, .var 3⟩]
    coefficientsWithScratch.body)⟩

/-- The component squares equal the complex squared norms used by the mathematical rotation. -/
theorem coefficient_radius_eq (u v : ℂ) :
    Real.sqrt ((u.re * u.re + u.im * u.im) + (v.re * v.re + v.im * v.im)) =
      Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]


/-- The actual ordered writes of the coefficient prefix under exact arithmetic. -/
private noncomputable def coefficientPrefixWrites (t : ℕ × ℕ) (u v : ℂ) :
    List ((ℕ × ℕ) × ℝ) :=
  [((t.1, t.2), u.re), ((t.1, t.2 + 1), u.im),
   ((t.1, t.2 + 2), v.re), ((t.1, t.2 + 3), v.im),
   ((t.1, t.2 + 4), u.re * u.re), ((t.1, t.2 + 5), u.im * u.im),
   ((t.1, t.2 + 4), u.re * u.re + u.im * u.im),
   ((t.1, t.2 + 5), v.re * v.re), ((t.1, t.2 + 6), v.im * v.im),
   ((t.1, t.2 + 5), v.re * v.re + v.im * v.im),
   ((t.1, t.2 + 4), (u.re * u.re + u.im * u.im) + (v.re * v.re + v.im * v.im)),
   ((t.1, t.2 + 4), Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2))]

/-- Pure scalar evaluation captures the inputs and computes the exact radius. -/
private theorem eval_coefficientPrefix {M : Machine ℝ} (hE : ExactModel id M)
    {a b t c s : ℕ × ℕ} {u v : ℂ} {f : ℕ × ℕ → Option ℝ}
    (hta : t.1 ≠ a.1) (htb : t.1 ≠ b.1)
    (hu0 : f a = some u.re) (hu1 : f (a.1, a.2 + 1) = some u.im)
    (hv0 : f b = some v.re) (hv1 : f (b.1, b.2 + 1) = some v.im) :
    ScalarIns.evalBlock M.eval (Env.frame [] [a, b, t, c, s]) coefficientPrefix f =
      some (coefficientPrefixWrites t u v) := by
  have hadd : ∀ x y, M.add x y = x + y := hE.add
  have hmul : ∀ x y, M.mul x y = x * y := hE.mul
  have hsqrt : M.sqrt ((u.re * u.re + u.im * u.im) +
      (v.re * v.re + v.im * v.im)) = Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have hn : 0 ≤ (u.re * u.re + u.im * u.im) + (v.re * v.re + v.im * v.im) :=
      add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
        (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    exact (show M.sqrt _ = Real.sqrt _ from hE.sqrt _ hn).trans (coefficient_radius_eq u v)
  rcases a with ⟨ab, ao⟩
  rcases b with ⟨bb, bo⟩
  rcases t with ⟨tb, toff⟩
  rcases c with ⟨cb, co⟩
  rcases s with ⟨sb, so⟩
  dsimp only at hta htb hu1 hv1
  have hat : ab ≠ tb := hta.symm
  have hbt : bb ≠ tb := htb.symm
  have hupd (g : ℕ × ℕ → Option ℝ) (x y : ℕ × ℕ) (w : Option ℝ) :
      Function.update g x w y = if y = x then w else g y := Function.update_apply g x w y
  have hpair (x₁ x₂ y₁ y₂ : ℕ) :
      ((x₁, x₂) = (y₁, y₂)) = (x₁ = y₁ ∧ x₂ = y₂) := Prod.mk.injEq x₁ x₂ y₁ y₂
  simp only [coefficientPrefix, coefficientPrefixWrites]
  dsimp only [Env.frame]
  repeat' first
    | rw [ScalarIns.evalBlock.eq_def]
      dsimp only [Machine.eval, Operand.evalList, Operand.eval, IExp.eval]
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero,
        List.nil_append, Nat.reduceLT, List.getElem_cons_succ, Option.bind_some,
        List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, false_and, and_false,
        if_true, if_false, Nat.add_left_cancel_iff, Nat.add_eq_left, Nat.left_eq_add,
        Nat.reduceEqDiff, *]
  rfl


/-- The captured words and radius after the actual scalar prefix. -/
private theorem coefficientPrefix_reads {m : Mem ℝ} {t : ℕ × ℕ} (u v : ℂ)
    (ht : t.2 + 7 ≤ m.store.len t.1) :
    let m' := m.updCells (coefficientPrefixWrites t u v)
    m'.store.get t.1 t.2 = some u.re ∧
    m'.store.get t.1 (t.2 + 1) = some u.im ∧
    m'.store.get t.1 (t.2 + 2) = some v.re ∧
    m'.store.get t.1 (t.2 + 3) = some v.im ∧
    m'.store.get t.1 (t.2 + 4) = some (Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
  dsimp only [coefficientPrefixWrites, Mem.updCells]
  constructor
  · store_simp
  constructor
  · store_simp
  constructor
  · store_simp
  constructor <;> store_simp

omit [Has CmpTst Tst] in
/-- The prefix writes only the seven scratch cells and returns its captured values. -/
private theorem coefficientPrefix_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {a b t c s : ℕ × ℕ} {u v : ℂ}
    (hta : t.1 ≠ a.1) (htb : t.1 ≠ b.1)
    (hu0 : m.store.get a.1 a.2 = some u.re)
    (hu1 : m.store.get a.1 (a.2 + 1) = some u.im)
    (hv0 : m.store.get b.1 b.2 = some v.re)
    (hv1 : m.store.get b.1 (b.2 + 1) = some v.im)
    (ht : t.2 + 7 ≤ m.store.len t.1) :
    Writes .total I τ (.scalarBlock (coefficientPrefix.map ScalarIns.lift))
      (Env.frame [] [a, b, t, c, s]) (Store.inBlock t.1 t.2 7)
      (fun m' => m'.pos = m.pos ∧ m'.store.get t.1 t.2 = some u.re ∧
        m'.store.get t.1 (t.2 + 1) = some u.im ∧
        m'.store.get t.1 (t.2 + 2) = some v.re ∧
        m'.store.get t.1 (t.2 + 3) = some v.im ∧
        m'.store.get t.1 (t.2 + 4) = some (Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2))) m := by
  have hreg : ∀ w ∈ coefficientPrefixWrites t u v,
      Store.inBlock t.1 t.2 7 w.1.1 w.1.2 := by
    intro w hw
    simp only [coefficientPrefixWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      dsimp only [Store.inBlock]
      exact ⟨rfl, by omega, by omega⟩
  have hroom : ∀ w ∈ coefficientPrefixWrites t u v,
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    obtain ⟨hbuf, hlo, hhi⟩ := hreg w hw
    rw [hbuf]
    omega
  refine (writes_machineScalarBlock hS
    (eval_coefficientPrefix hE hta htb hu0 hu1 hv0 hv1) hroom).mono ?_ ?_
  · intro q i h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    simpa only [he] using hreg w hw
  · intro m' _ he
    subst m'
    exact ⟨rfl, coefficientPrefix_reads u v ht⟩

/-- The actual four writes of the identity-rotation branch. -/
private def coefficientZeroWrites (c s : ℕ × ℕ) : List ((ℕ × ℕ) × ℝ) :=
  [((c.1, c.2), 1), ((c.1, c.2 + 1), 0), ((s.1, s.2), 0), ((s.1, s.2 + 1), 0)]

/-- The literal branch is independent of all input and scratch contents. -/
private theorem eval_coefficientZero {M : Machine ℝ} (hE : ExactModel id M)
    (a b t c s : ℕ × ℕ) (f : ℕ × ℕ → Option ℝ) :
    ScalarIns.evalBlock M.eval (Env.frame [] [a, b, t, c, s]) coefficientZero f =
      some (coefficientZeroWrites c s) := by
  have h1 : M.lit 1 = 1 := by simpa using hE.lit 1
  have h0 : M.lit 0 = 0 := by simpa using hE.lit 0
  simp [coefficientZero, ScalarIns.evalBlock, Machine.eval, Env.frame, Operand.evalList,
    Operand.eval, IExp.eval, coefficientZeroWrites, h1, h0]

omit [Has CmpTst Tst] in
/-- The zero branch writes its two packed output blocks, including spatially separate
views in a single caller buffer. -/
private theorem coefficientZero_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {a b t c s : ℕ × ℕ}
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2))
    (hc : c.2 + 2 ≤ m.store.len c.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ (.scalarBlock (coefficientZero.map ScalarIns.lift))
      (Env.frame [] [a, b, t, c, s]) (Fp.blocks [c, s] [2, 2])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [c, s] [2, 2] =
        some [[1, 0], [0, 0]]) m := by
  have hroom : ∀ w ∈ coefficientZeroWrites c s, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [coefficientZeroWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    all_goals dsimp only; omega
  refine (writes_machineScalarBlock hS (eval_coefficientZero hE a b t c s m.store.cellFn)
    hroom).mono ?_ ?_
  · intro q i h
    simp only [Fp.cells, coefficientZeroWrites, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, le_rfl, by omega⟩
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨rfl, le_rfl, by omega⟩)
    · exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
  · intro m' _ he
    subst m'
    have heq : m.updCells (coefficientZeroWrites c s) =
        m.updBlocks [c, s] [[1, 0], [0, 0]] := rfl
    rw [heq]
    refine ⟨rfl, Mem.readBlocks_updBlocks ?_ ⟨hc, hs, trivial⟩⟩
    refine ⟨?_, ⟨?_, trivial⟩⟩
    · simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      Fp.blocks, sup_bot_eq] using hcs
    · simp [Fp.blocks, Fp.Disj]

/-- The ordered writes of the nonzero-radius branch. -/
private noncomputable def coefficientDivideWrites (t c s : ℕ × ℕ) (u v : ℂ) (r : ℝ) :
    List ((ℕ × ℕ) × ℝ) :=
  [((t.1, t.2 + 5), -u.im), ((t.1, t.2 + 6), -v.im),
   ((c.1, c.2), u.re / r), ((c.1, c.2 + 1), -u.im / r),
   ((s.1, s.2), v.re / r), ((s.1, s.2 + 1), -v.im / r)]

/-- Pure evaluation divides only by the supplied nonzero captured radius. -/
private theorem eval_coefficientDivide {M : Machine ℝ} (hE : ExactModel id M)
    {a b t c s : ℕ × ℕ} {u v : ℂ} {r : ℝ} {f : ℕ × ℕ → Option ℝ}
    (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1) (hr : r ≠ 0)
    (h0 : f (t.1, t.2) = some u.re) (h1 : f (t.1, t.2 + 1) = some u.im)
    (h2 : f (t.1, t.2 + 2) = some v.re) (h3 : f (t.1, t.2 + 3) = some v.im)
    (h4 : f (t.1, t.2 + 4) = some r) :
    ScalarIns.evalBlock M.eval (Env.frame [] [a, b, t, c, s]) coefficientDivide f =
      some (coefficientDivideWrites t c s u v r) := by
  have hneg : ∀ x, M.neg x = -x := hE.neg
  have hdiv : ∀ x, M.div x r = x / r := fun x => hE.div x r hr
  rcases a with ⟨ab, ao⟩
  rcases b with ⟨bb, bo⟩
  rcases t with ⟨tb, toff⟩
  rcases c with ⟨cb, co⟩
  rcases s with ⟨sb, so⟩
  dsimp only at htc hts h0 h1 h2 h3 h4
  have hct : cb ≠ tb := htc.symm
  have hst : sb ≠ tb := hts.symm
  have hupd (g : ℕ × ℕ → Option ℝ) (x y : ℕ × ℕ) (w : Option ℝ) :
      Function.update g x w y = if y = x then w else g y := Function.update_apply g x w y
  have hpair (x₁ x₂ y₁ y₂ : ℕ) :
      ((x₁, x₂) = (y₁, y₂)) = (x₁ = y₁ ∧ x₂ = y₂) := Prod.mk.injEq x₁ x₂ y₁ y₂
  simp only [coefficientDivide, coefficientDivideWrites]
  dsimp only [Env.frame]
  repeat' first
    | rw [ScalarIns.evalBlock.eq_def]
      dsimp only [Machine.eval, Operand.evalList, Operand.eval, IExp.eval]
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, getElem?_pos, List.getElem_cons_zero,
        List.nil_append, Nat.reduceLT, List.getElem_cons_succ, Option.bind_some,
        List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, false_and, and_false,
        if_true, if_false, Nat.add_left_cancel_iff, Nat.left_eq_add,
        Nat.reduceEqDiff, *]
  rfl

omit [Has CmpTst Tst] in
/-- A nonzero radius branch writes the conjugated component quotients. -/
private theorem coefficientDivide_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {a b t c s : ℕ × ℕ} {u v : ℂ} {r : ℝ}
    (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2)) (hr : r ≠ 0)
    (h0 : m.store.get t.1 t.2 = some u.re)
    (h1 : m.store.get t.1 (t.2 + 1) = some u.im)
    (h2 : m.store.get t.1 (t.2 + 2) = some v.re)
    (h3 : m.store.get t.1 (t.2 + 3) = some v.im)
    (h4 : m.store.get t.1 (t.2 + 4) = some r)
    (ht : t.2 + 7 ≤ m.store.len t.1)
    (hc : c.2 + 2 ≤ m.store.len c.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ (.scalarBlock (coefficientDivide.map ScalarIns.lift))
      (Env.frame [] [a, b, t, c, s]) (Fp.blocks [t, c, s] [7, 2, 2])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [c, s] [2, 2] =
        some [[u.re / r, -u.im / r], [v.re / r, -v.im / r]]) m := by
  have hroom : ∀ w ∈ coefficientDivideWrites t c s u v r,
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [coefficientDivideWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only; omega
  refine (writes_machineScalarBlock hS
    (eval_coefficientDivide hE htc hts hr h0 h1 h2 h3 h4) hroom).mono ?_ ?_
  · intro q i h
    simp only [Fp.cells, coefficientDivideWrites, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨rfl, le_rfl, by omega⟩)
    · exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩))
  · intro m' _ he
    subst m'
    have heq : m.updCells (coefficientDivideWrites t c s u v r) =
        ((m.upd (t.1, t.2 + 5) (-u.im)).upd (t.1, t.2 + 6) (-v.im)).updBlocks
          [c, s] [[u.re / r, -u.im / r], [v.re / r, -v.im / r]] := rfl
    rw [heq]
    refine ⟨rfl, Mem.readBlocks_updBlocks ?_ ?_⟩
    · refine ⟨?_, ⟨?_, trivial⟩⟩
      · simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
          Fp.blocks, sup_bot_eq] using hcs
      · simp [Fp.blocks, Fp.Disj]
    · change c.2 + 2 ≤ ((m.upd (t.1, t.2 + 5) (-u.im)).upd
        (t.1, t.2 + 6) (-v.im)).store.len c.1 ∧
        s.2 + 2 ≤ ((m.upd (t.1, t.2 + 5) (-u.im)).upd
        (t.1, t.2 + 6) (-v.im)).store.len s.1 ∧ True
      simpa only [Mem.store_upd, Store.len_upd] using And.intro hc (And.intro hs trivial)

/-- Exact scalar arithmetic and the actual zero test compute the mathematical Givens
coefficients for every pair, including the zero pair. The scratch buffer is separate from
all inputs and outputs; the two output views are spatially disjoint and may share a buffer.
Outputs may coincide with the original inputs because their components are captured first.
[GolubVanLoan2013, Algorithm 5.1.3]. -/
theorem coefficientsWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {a b t c s : ℕ × ℕ} {u v : ℂ}
    (hta : t.1 ≠ a.1) (htb : t.1 ≠ b.1) (htc : t.1 ≠ c.1) (hts : t.1 ≠ s.1)
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2))
    (hu0 : m.store.get a.1 a.2 = some u.re)
    (hu1 : m.store.get a.1 (a.2 + 1) = some u.im)
    (hv0 : m.store.get b.1 b.2 = some v.re)
    (hv1 : m.store.get b.1 (b.2 + 1) = some v.im)
    (ht : t.2 + 7 ≤ m.store.len t.1)
    (hc : c.2 + 2 ≤ m.store.len c.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ coefficientsWithScratch.body (Env.frame [] [a, b, t, c, s])
      (Fp.blocks [t, c, s] [7, 2, 2])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [c, s] [2, 2] =
        some [[(givensCoeffs u v).1.re, (givensCoeffs u v).1.im],
          [(givensCoeffs u v).2.re, (givensCoeffs u v).2.im]]) m := by
  classical
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (coefficientPrefix_writes hS hE hta htb hu0 hu1 hv0 hv1 ht)
    le_sup_left fun m' hfr ⟨hpos, h0, h1, h2, h3, h4⟩ => ?_
  have ht' : t.2 + 7 ≤ m'.store.len t.1 := by rw [hfr.len_eq]; exact ht
  have hc' : c.2 + 2 ≤ m'.store.len c.1 := by rw [hfr.len_eq]; exact hc
  have hs' : s.2 + 2 ≤ m'.store.len s.1 := by rw [hfr.len_eq]; exact hs
  by_cases hz : Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) = 0
  · have htest := hCmp.test_isZero (d := []) (m := m') (x := (t.1, t.2 + 4)) h4
    simp only [id_eq, hz, decide_true] at htest
    refine writes_ite rfl rfl htest ?_
    refine (coefficientZero_writes hS hE hcs hc' hs').mono le_sup_right ?_
    rintro m'' _ ⟨hpos', hread⟩
    refine ⟨hpos'.trans hpos, ?_⟩
    simpa only [givensCoeffs, hz, if_pos, Prod.fst, Prod.snd, Complex.one_re,
      Complex.one_im, Complex.zero_re, Complex.zero_im] using hread
  · have htest := hCmp.test_isZero (d := []) (m := m') (x := (t.1, t.2 + 4)) h4
    simp only [id_eq, hz, decide_false] at htest
    refine writes_ite rfl rfl htest ?_
    refine (coefficientDivide_writes hS hE htc hts hcs hz h0 h1 h2 h3 h4 ht' hc' hs').mono
      le_rfl ?_
    rintro m'' _ ⟨hpos', hread⟩
    refine ⟨hpos'.trans hpos, ?_⟩
    simpa [givensCoeffs, hz, RCLike.star_def, Complex.div_ofReal_re,
      Complex.div_ofReal_im] using hread

/-- Scoped coefficient computation returns the exact complex Givens coefficients and
releases all scratch. Input and output views may overlap; the two output views are apart.
The actual radius test covers the zero pair without a division by zero.
[GolubVanLoan2013, Algorithm 5.1.3]. -/
theorem coefficients_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {a b c s : ℕ × ℕ} {u v : ℂ}
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2))
    (hu0 : m.store.get a.1 a.2 = some u.re)
    (hu1 : m.store.get a.1 (a.2 + 1) = some u.im)
    (hv0 : m.store.get b.1 b.2 = some v.re)
    (hv1 : m.store.get b.1 (b.2 + 1) = some v.im)
    (hc : c.2 + 2 ≤ m.store.len c.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ coefficients.body (Env.frame [] [a, b, c, s])
      (Fp.blocks [c, s] [2, 2])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks [c, s] [2, 2] =
        some [[(givensCoeffs u v).1.re, (givensCoeffs u v).1.im],
          [(givensCoeffs u v).2.re, (givensCoeffs u v).2.im]]) m := by
  have hal : a.1 < m.store.length := Store.lt_length_of_get hu0
  have hbl : b.1 < m.store.length := Store.lt_length_of_get hv0
  have hcl : c.1 < m.store.length := Store.lt_length_of_lt_len (by omega : c.2 < _)
  have hsl : s.1 < m.store.length := Store.lt_length_of_lt_len (by omega : s.2 < _)
  have hl : m.Live [c, s] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> assumption
  apply writes_allocs_readBlocks (lens := [.const 7]) (ns := [7]) rfl hl
  intro store hlen hlens hBelow
  have hlen' : store.length = m.store.length + 1 := by simpa using hlen
  let t : ℕ × ℕ := (m.store.length, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have ht : t.2 + 7 ≤ store.len t.1 := by
    have h := hlens 0 (by simp)
    simpa [t] using h.ge
  have hl' : m₁.Live [a, b, t, c, s] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz | hz <;> subst z
    · change a.1 < store.length
      omega
    · change b.1 < store.length
      omega
    · change m.store.length < store.length
      omega
    · change c.1 < store.length
      omega
    · change s.1 < store.length
      omega
  refine (writes_frame rfl rfl hl'
    (coefficientsWithScratch_writes hS hE hCmp (m := m₁) (by dsimp [t]; omega)
      (by dsimp [t]; omega) (by dsimp [t]; omega) (by dsimp [t]; omega) hcs
      (by exact ((hBelow a.1 hal).2 _).trans hu0)
      (by exact ((hBelow a.1 hal).2 _).trans hu1)
      (by exact ((hBelow b.1 hbl).2 _).trans hv0)
      (by exact ((hBelow b.1 hbl).2 _).trans hv1)
      ht (by change c.2 + 2 ≤ store.len c.1; rw [(hBelow c.1 hcl).1]; exact hc)
      (by change s.2 + 2 ≤ store.len s.1; rw [(hBelow s.1 hsl).1]; exact hs))).mono
        ?_ (fun _ _ h => h)
  change Store.inBlock m.store.length 0 7 ⊔ Fp.blocks [c, s] [2, 2] ≤ _
  exact sup_le (Fp.inBlock_le_sup_above le_rfl) le_sup_left

end NLAlib.ShiftedQR
