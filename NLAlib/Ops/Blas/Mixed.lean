/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1

/-!
# BLAS with finite range and absolute rounding allowances

The existing word-level execution proofs are independent of an error model. These consequences
reuse them with a mixed relative/absolute model and explicit guards on every rounded target.
The addition guard uses the computed product. Empty lengths need no per-element range facts.
These are total weakest-precondition results, not canonical resource certificates.

## Main results

* `NLAlib.Ops.wp_axpyLoop_mixed`: actual stored vector with a mixed forward-error bound.
* `NLAlib.Ops.wp_scalLoop_mixed`: actual stored division with a mixed forward-error bound.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]

/-- The two exact targets executed by each axpy component are in the model's finite range. -/
def AxpySafe (dec : K → ℝ) (M : Machine K) (safe : ℝ → Prop) (n : ℕ)
    (a : K) (x y : ℕ → K) : Prop :=
  ∀ i < n, safe (dec a * dec (x i)) ∧ safe (dec (y i) + dec (M.mul a (x i)))

/-- Every scaling division has a nonzero divisor and an in-range exact quotient. -/
def ScalSafe (dec : K → ℝ) (safe : ℝ → Prop) (n : ℕ) (a : K) (x : ℕ → K) : Prop :=
  ∀ i < n, dec a ≠ 0 ∧ safe (dec (x i) / dec a)

omit [Has ScalarOp Op] in
/-- Componentwise axpy error, with the propagated absolute allowance of two rounded steps. -/
theorem isAxpyMixedErr_axpyF {u eta : ℝ} {dec : K → ℝ} {M : Machine K}
    {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe) (a : K) (x y : ℕ → K) (n : ℕ)
    (hs : AxpySafe dec M safe n a x y) :
    IsAxpyMixedErr dec ((1 + u) ^ 2 - 1) ((2 + u) * eta) n a x y
      (vec (axpyF M a x y n)) := by
  intro i hi
  have hv : vec (axpyF M a x y n) i = M.add (y i) (M.mul a (x i)) := by
    simp [vec, axpyF, List.getD_eq_getElem?_getD, hi]
  rw [hv]
  exact hM.abs_add_mul_sub_le _ _ _ (hs i hi).1 (hs i hi).2

omit [Has ScalarOp Op] in
/-- Componentwise scaling error, retaining both the range and nonzero-divisor guards. -/
theorem isScalMixedErr_scalF {u eta : ℝ} {dec : K → ℝ} {M : Machine K}
    {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe) (a : K) (x : ℕ → K) (n : ℕ)
    (hs : ScalSafe dec safe n a x) :
    IsScalMixedErr dec u eta n a x (vec (scalF M a x n)) := by
  intro _ i hi
  have hv : vec (scalF M a x n) i = M.div (x i) a := by
    simp [vec, scalF, List.getD_eq_getElem?_getD, hi]
  rw [hv]
  exact hM.div _ _ (hs i hi).1 (hs i hi).2

/-- The existing axpy program succeeds and stores a vector satisfying the finite-range mixed
error bound. Only the numerical consequence is new; the execution proof is reused. -/
theorem wp_axpyLoop_mixed {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {u eta : ℝ} {dec : K → ℝ} {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe)
    {τ : Tape K} {n : ℕ} {al x y : ℕ × ℕ} {m : Mem K} {a : K} {xs ys : List K}
    (hal : al.1 ≠ y.1) (hxy : x.1 ≠ y.1) (hl : m.Live [al, x, y])
    (ha : m.store.get al.1 al.2 = some a) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : m.store.readBlock y.1 y.2 n = some ys)
    (hs : AxpySafe dec M safe n a (vec xs) (vec ys)) :
    Wp .total I τ (axpyLoop (Op := Op) (Tst := Tst)).body (Env.frame [n] [al, x, y, y])
      (fun m' => m'.pos = m.pos ∧ ∃ zs, m'.store.readBlock y.1 y.2 n = some zs ∧
        IsAxpyMixedErr dec ((1 + u) ^ 2 - 1) ((2 + u) * eta) n a (vec xs) (vec ys) (vec zs))
      m := by
  refine wp_axpyLoop hI hal hxy hl ha hx hy ?_
  exact ⟨rfl, _, Store.readBlock_updBlock_of_readBlock hy (length_axpyF ..),
    isAxpyMixedErr_axpyF hM a (vec xs) (vec ys) n hs⟩

/-- The existing division loop stores a vector satisfying the guarded mixed error bound. -/
theorem wp_scalLoop_mixed {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {u eta : ℝ} {dec : K → ℝ} {safe : ℝ → Prop} (hM : MixedModel u eta dec M safe)
    {τ : Tape K} {n : ℕ} {al x : ℕ × ℕ} {m : Mem K} {a : K} {xs : List K}
    (hal : al.1 ≠ x.1) (ha : m.store.get al.1 al.2 = some a)
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hs : ScalSafe dec safe n a (vec xs)) :
    Wp .total I τ (scalLoop (Op := Op) (Tst := Tst)).body (Env.frame [n] [al, x, x])
      (fun m' => m'.pos = m.pos ∧ ∃ zs, m'.store.readBlock x.1 x.2 n = some zs ∧
        IsScalMixedErr dec u eta n a (vec xs) (vec zs)) m := by
  refine wp_scalLoop hI hal ha hx ?_
  exact ⟨rfl, _, Store.readBlock_updBlock_of_readBlock hx (length_scalF ..),
    isScalMixedErr_scalF hM a (vec xs) n hs⟩

/-- The complete instrumented axpy tree still has exactly n multiplications and n additions.
This projects its static count; structural instructions remain in the full count. -/
theorem original_stmtCost_axpyLoop (n a x y z : ℕ) :
    Count.original (stmtCost (axpyLoop (Op := ScalarOp) (Tst := Empty)).body.instrument
      (Env.frame [n] [(0, a), (1, x), (2, y), (2, z)]).idx) =
      n • (Count.one .mul [] + Count.one .add []) := by
  classical
  simp [axpyLoop, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
    IExp.bookkeeping, stmtCost, useCost, IExp.eval]
  rfl

/-- The complete instrumented division loop retains exactly one division per component. -/
theorem original_stmtCost_scalLoop (n a x z : ℕ) :
    Count.original (stmtCost (scalLoop (Op := ScalarOp) (Tst := Empty)).body.instrument
      (Env.frame [n] [(0, a), (1, x), (1, z)]).idx) = n • Count.one .div [] := by
  classical
  simp [scalLoop, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
    IExp.bookkeeping, stmtCost, useCost, IExp.eval]
  rfl

end NLAlib.Ops
