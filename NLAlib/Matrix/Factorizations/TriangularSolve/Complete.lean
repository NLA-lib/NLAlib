/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.PivotedValues
public import NLAlib.Matrix.Factorizations.LU.UnapplyLog

/-!
# Solving through factors and two actual pivot histories

The row log permutes the original RHS before triangular substitution. Reverse replay of the
column log restores the original solution coordinates. The resulting system matrix is read
from the actual factor product and the two histories, so no unstored matrix enters the tree.

## Main results

* `NLAlib.TriangularSolve.completePivoted_writes`: the same scalar body with an in-place RHS.
* `NLAlib.TriangularSolve.completePivoted_meets`: the separate-output routine interface.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]

/-- Solve through actual stored factors and row history, then undo the actual column history. -/
def completePivoted : Routine Op Tst :=
  routine% [n] (L : n * n, U : n * n, H : n, Q : n, b : n) → (x : n) {
    run pivoted [n] (L, U, H, b, x);
    run LU.unapplyLog [n] (Q, x)
  }

variable [Inhabited K]

/-- The original-coordinate system reconstructed from the two stored logs and factor
product maps the actual solution to the original RHS. -/
def completePivotedSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] tape t (ls, us, hs, qs, bs) → (xs) requires
    ((pivotedSpec dec).pre [n] t [ls, us, hs, bs] ∧
      ∃ q : Fin n → Fin n, (∀ i : Fin n, i ≤ q i) ∧
        ∀ i : Fin n, dec (vec qs i.val) = (q i).val) ensures
    ∀ p q : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) →
      (∀ i : Fin n, dec (vec qs i.val) = (q i).val) →
      (decodeMatrix dec n n ls * decodeMatrix dec n n us).submatrix
        (luPivotPermutation p n).symm (luPivotPermutation q n).symm *ᵥ decv dec n xs = decv dec n bs

/-- The actual two-log factor solve admits exact RHS/output aliases or disjoint blocks.
The stored factors and histories stay apart from the output and are retained. -/
theorem completePivoted_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {L U H C b x : ℕ × ℕ} {ls us hs qs bs : List K}
    (hlive : m.Live [L, U, H, C, b, x])
    (hLx : L.1 ≠ x.1) (hUx : U.1 ≠ x.1) (hHx : H.1 ≠ x.1) (hCx : C.1 ≠ x.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (hls : m.store.readBlock L.1 L.2 (n * n) = some ls)
    (hus : m.store.readBlock U.1 U.2 (n * n) = some us)
    (hhs : m.store.readBlock H.1 H.2 n = some hs)
    (hqs : m.store.readBlock C.1 C.2 n = some qs)
    (hbs : m.store.readBlock b.1 b.2 n = some bs)
    (hroom : x.2 + n ≤ m.store.len x.1)
    (hpre : (completePivotedSpec dec).pre [n] (τ.shift m.pos) [ls, us, hs, qs, bs]) :
    Writes .total I τ (completePivoted (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [L, U, H, C, b, x]) (Store.inBlock x.1 x.2 n)
      (fun m' => m'.pos = m.pos ∧ ∃ zs : List K,
        m'.store.readBlock x.1 x.2 n = some zs ∧
        (completePivotedSpec dec).post [n] (τ.shift m.pos) [ls, us, hs, qs, bs] [zs]) m := by
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlU : U.1 < m.store.length := hlive U (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  have hlC : C.1 < m.store.length := hlive C (by simp)
  have hlb : b.1 < m.store.length := hlive b (by simp)
  have hlx : x.1 < m.store.length := hlive x (by simp)
  have hlRow : m.Live [L, U, H, b, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hlL, hlU, hlH, hlb, hlx, trivial⟩
  obtain ⟨hrowPre, hcolPre⟩ := hpre
  unfold completePivoted
  refine ((pivoted_writes hI hQ hM hlRow hLx hUx hHx hbx hls hus hhs hbs hroom hrowPre).in_frame
    rfl rfl hlRow).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hpos₁, ys, hys, hsolve⟩
  have hqs₁ : m₁.store.readBlock C.1 C.2 n = some qs := by keep
  have hlen₁ := hfr₁.length_eq
  have hroom₁ : x.2 + n ≤ m₁.store.len x.1 := by rw [hfr₁.len_eq]; exact hroom
  call (LU.unapplyLog_meets hI hQ) [n] (C, x) (pre := hcolPre)
    as m₂ hfr₂ hpos₂ (zs) hundolog
  refine ⟨hpos₂.trans hpos₁, zs, hzs, ?_⟩
  intro p q hp hq
  let P := luPivotPermutation p n
  let Q := luPivotPermutation q n
  let B := (decodeMatrix dec n n ls * decodeMatrix dec n n us).submatrix P.symm Q.symm
  have heq : B.submatrix P Q = decodeMatrix dec n n ls * decodeMatrix dec n n us := by
    ext i j
    simp only [B, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hsol := mulVec_eq_of_submatrix_solve (A := B) P Q (by rw [heq]; exact hsolve p hp)
  have hwords := LU.vec_eq_of_unapplyLogSpec (τ := τ.shift m₁.pos) hundolog q hq
  have hx : decv dec n zs = decv dec n ys ∘ Q.symm := by
    funext i
    exact congrArg dec (hwords i)
  rw [← hx] at hsol
  exact hsol

/-- The separate-output interface of the same actual complete-pivot triangular solve body. -/
theorem completePivoted_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (completePivoted (Op := Op) (Tst := Tst)).Meets I (completePivotedSpec dec) := by
  routine_intro [n] (L, U, H, C, b, x) reads (ls, us, hs, qs, bs)
  refine (completePivoted_writes hI hQ hM hlive hLx hUx hHx hCx
    (.inl (Fp.disj_inBlock_of_ne hbx)) hls hus hhs hqs hbs hroom hpre).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, zs, hzs, hsolve⟩
  exact ⟨hpos, [zs], Mem.readBlocks_of_cons hzs rfl, hsolve⟩

end NLAlib.TriangularSolve
