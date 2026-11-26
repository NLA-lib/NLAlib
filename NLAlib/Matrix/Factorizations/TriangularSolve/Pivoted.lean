/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Exact
public import NLAlib.Matrix.Factorizations.LU.ApplyLog
public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.CopyAlias

/-!
# Solving through stored factors and an actual pivot history

Copy the original right-hand side, replay the actual stored row choices, then apply the
existing scalar lower and direct upper substitutions. The original factors, history and
right-hand side are retained. The output equation identifies its permutation from stored
history words, with no successful-factorization or unstored permutation hypothesis.

## Main results

* `NLAlib.TriangularSolve.pivoted_meets`: exact solve through the actual stored factors and log.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]

/-- Copy and permute the right-hand side from the reported row log, then solve through the
actual stored lower and upper factors. The only output is the solution vector. -/
def pivoted : Routine Op Tst :=
  routine% [n] (L : n * n, U : n * n, H : n, b : n) → (x : n) {
    run copyLoopRoutine [n] (b, x);
    run LU.applyLog [n] (H, x);
    run forward [n] (L, x);
    run upper [n] (U, x)
  }

variable [Inhabited K]

/-- Triangular factors with nonzero stored diagonals and an active stored row history give
the product-system equation for the original right-hand side permuted by that history. -/
def pivotedSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (ls, us, hs, bs) → (xs) requires
    ((decodeMatrix dec n n ls).IsLowerTriangular ∧
      (decodeMatrix dec n n us).IsUpperTriangular ∧
      (∀ i < n, dec (vec ls (i * n + i)) ≠ 0) ∧
      (∀ i < n, dec (vec us (i * n + i)) ≠ 0) ∧
      ∃ p : Fin n → Fin n, (∀ i : Fin n, i ≤ p i) ∧
        ∀ i : Fin n, dec (vec hs i.val) = (p i).val) ensures
    ∀ p : Fin n → Fin n, (∀ i : Fin n, dec (vec hs i.val) = (p i).val) →
      (decodeMatrix dec n n ls * decodeMatrix dec n n us) *ᵥ decv dec n xs =
        decv dec n bs ∘ luPivotPermutation p n

/-- Actual log replay and two scalar substitutions solve the reported product system under
exact arithmetic and bounded index queries. No run or precomputed solution is assumed. -/
theorem pivoted_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (pivoted (Op := Op) (Tst := Tst)).Meets I (pivotedSpec dec) := by
  routine_intro [n] (L, U, H, b, x) reads (ls, us, hs, bs)
  obtain ⟨hL, hU, hdL, hdU, hlog⟩ := hpre
  call (copyLoopRoutine_meets hI (fun _ => True)) [n] (b, x)
    as m₁ hfr₁ hpos₁ (copied) hcopy
  have he : copied = bs := (List.cons.inj hcopy).1
  subst copied
  call (LU.applyLog_meets hI hQ) [n] (H, x) (pre := hlog)
    as m₂ hfr₂ hpos₂ (permuted) happly
  call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
    as m₃ hfr₃ hpos₃ (ys) hforward
  have hLy := forwardSpec_mulVec_eq (τ := τ.shift m₂.pos) hforward hL hdL
  call (upper_meets hI hM.toStdModel_zero) [n] (U, x) (pre := hdU)
    as m₄ hfr₄ hpos₄ (zs) hupper
  have hUz := upperSpec_mulVec_eq (τ := τ.shift m₃.pos) hupper hU hdU
  routine_exit
  intro p hp
  rw [← Matrix.mulVec_mulVec, hUz, hLy]
  have hwords := LU.vec_eq_of_applyLogSpec (τ := τ.shift m₁.pos) happly p hp
  funext i
  exact congrArg dec (hwords i)

/-- The same stored-factor solve body accepts an exact RHS/output alias or disjoint blocks.
Only factors and the log must be apart from the output. This is the raw operand rule used by
factor-then-solve programs whose original matrix and in-place RHS may overlap. -/
theorem pivoted_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {L U H b x : ℕ × ℕ} {ls us hs bs : List K}
    (hlive : m.Live [L, U, H, b, x]) (hLx : L.1 ≠ x.1) (hUx : U.1 ≠ x.1) (hHx : H.1 ≠ x.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (hls : m.store.readBlock L.1 L.2 (n * n) = some ls)
    (hus : m.store.readBlock U.1 U.2 (n * n) = some us)
    (hhs : m.store.readBlock H.1 H.2 n = some hs)
    (hbs : m.store.readBlock b.1 b.2 n = some bs)
    (hroom : x.2 + n ≤ m.store.len x.1)
    (hpre : (pivotedSpec dec).pre [n] (τ.shift m.pos) [ls, us, hs, bs]) :
    Writes .total I τ (pivoted (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [L, U, H, b, x]) (Store.inBlock x.1 x.2 n)
      (fun m' => m'.pos = m.pos ∧ ∃ zs : List K,
        m'.store.readBlock x.1 x.2 n = some zs ∧
        (pivotedSpec dec).post [n] (τ.shift m.pos) [ls, us, hs, bs] [zs]) m := by
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlU : U.1 < m.store.length := hlive U (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  have hlb : b.1 < m.store.length := hlive b (by simp)
  have hlx : x.1 < m.store.length := hlive x (by simp)
  have hlbx : m.Live [b, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hlb, hlx, trivial⟩
  obtain ⟨hL, hU, hdL, hdU, hlog⟩ := hpre
  unfold pivoted
  refine ((copyLoopRoutine_writes_of_disj_or_eq hI hbx hbs hroom).in_frame
    rfl rfl hlbx).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, hcopy⟩
  have hls₁ : m₁.store.readBlock L.1 L.2 (n * n) = some ls := by keep
  have hus₁ : m₁.store.readBlock U.1 U.2 (n * n) = some us := by keep
  have hhs₁ : m₁.store.readBlock H.1 H.2 n = some hs := by keep
  call (LU.applyLog_meets hI hQ) [n] (H, x) (pre := hlog)
    as m₂ hfr₂ hpos₂ (permuted) happly
  call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
    as m₃ hfr₃ hpos₃ (ys) hforward
  have hLy := forwardSpec_mulVec_eq (τ := τ.shift m₂.pos) hforward hL hdL
  call (upper_meets hI hM.toStdModel_zero) [n] (U, x) (pre := hdU)
    as m₄ hfr₄ hpos₄ (zs) hupper
  have hUz := upperSpec_mulVec_eq (τ := τ.shift m₃.pos) hupper hU hdU
  refine ⟨by omega, zs, hzs, ?_⟩
  intro p hp
  rw [← Matrix.mulVec_mulVec, hUz, hLy]
  have hwords := LU.vec_eq_of_applyLogSpec (τ := τ.shift m₁.pos) happly p hp
  funext i
  exact congrArg dec (hwords i)

end NLAlib.TriangularSolve
