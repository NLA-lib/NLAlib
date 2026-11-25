/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyColumnsRounding
public import NLAlib.Matrix.Perturbation.CholeskyMargin
public import NLAlib.Matrix.Perturbation.CholeskySchurError
public import NLAlib.Matrix.Perturbation.CholeskyColumnError

/-!
# Numerical invariants for the rounded Cholesky driver

The residual is compared only on its active block. Completed factor columns retain exact
triangular zeros and positive diagonal, together with an entrywise forward error bound.

## Main results

* `NLAlib.Computation.CholeskyRounding.abs_column_sub_choleskyLower_le`: a completed column
  obeys the terminal input-margin error budget.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation.CholeskyRounding

variable {P K : Type} [DecidableEq P]

/-- The specific stored Cholesky loop invariant: one scratch residual, its active numerical
error, completed factor cells, and the complete original output-block frame. -/
structure State (dec : P → K → ℝ) (u μ B e : ℝ) (base : Store P K) (p : P)
    (R L lo : ℕ) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (s : Store P K) : Prop where
  /-- All writes stay in the output block or the one residual scratch buffer. -/
  frame : ∃ g, Store.BlockFrame base p R L lo (N * N) s g
  /-- The actual decoded residual, which may have symmetry drift. -/
  residual : ∃ M : Matrix (Fin N) (Fin N) ℝ, HoldsDecoded s dec p R 0 M ∧
    ∀ i j, k ≤ i.val → k ≤ j.val → |M i j - gaussState A k i j| ≤ choleskySchurErrorBound u B μ k
  /-- Completed factor entries preserve their actual word and decoded structural guarantees. -/
  factor : ∀ i j : Fin N, j.val < k → ∃ w,
    s.read p L (lo + i.val + N * j.val) = some w ∧
    (i < j → dec p w = 0) ∧ (i = j → 0 < dec p w) ∧
    |dec p w - choleskyLower A i j| ≤ e

/-- A positive input margin and the propagated active residual budget bound every entry of
the actual completed column relative to the exact Cholesky factor. -/
theorem abs_column_sub_choleskyLower_le {N : ℕ} {u μ B : ℝ}
    {A M : Matrix (Fin N) (Fin N) ℝ} (hμ : 0 < μ) (hμB : μ ≤ B)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) {k : ℕ} (hk : k < N)
    (hη : choleskySchurErrorBound u B μ N < μ / 2)
    (herr : ∀ i j, k ≤ i.val → k ≤ j.val →
      |M i j - gaussState A k i j| ≤ choleskySchurErrorBound u B μ k)
    (w : Fin N → ℝ) (hz : ∀ i, i.val < k → w i = 0)
    (hroot : RelErr u (Real.sqrt (M ⟨k, hk⟩ ⟨k, hk⟩)) (w ⟨k, hk⟩))
    (hdiv : ∀ i, k < i.val → RelErr u (M i ⟨k, hk⟩ / w ⟨k, hk⟩) (w i)) :
    ∀ i, |w i - choleskyLower A i ⟨k, hk⟩| ≤
      (2 * (1 + B / μ) * choleskySchurErrorBound u B μ N + 16 * u * B) / Real.sqrt μ := by
  have hA : A.PosDef := by
    have h := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hlo)
    simpa only [add_sub_cancel] using h
  let r : Fin N := ⟨k, hk⟩
  let η := choleskySchurErrorBound u B μ k
  have hB : 0 ≤ B := hμ.le.trans hμB
  have hη0 : 0 ≤ η := choleskySchurErrorBound_nonneg hu hB hμ k
  have hηN := choleskySchurErrorBound_le_choleskySchurErrorBound hu hB hμ (Nat.le_of_lt hk)
  have hp : μ ≤ gaussState A k r r := le_gaussState_apply_self_of_smul_one_le hμ hlo r
  have hE : ∀ i j, |gaussState A k i j| ≤ B := by
    intro i j
    simpa only [Real.norm_eq_abs] using hA.posSemidef.norm_gaussState_apply_le hscale k i j
  have ha : μ / 2 ≤ M r r := by
    have h := (abs_le.mp (herr r r le_rfl le_rfl)).1
    dsimp [r] at h
    linarith
  have hm : ∀ i j, k ≤ i.val → k ≤ j.val → |M i j| ≤ 2 * B := by
    intro i j hi hj
    calc |M i j| ≤ |M i j - gaussState A k i j| + |gaussState A k i j| := by
           simpa only [sub_add_cancel] using
             abs_add_le (M i j - gaussState A k i j) (gaussState A k i j)
         _ ≤ η + B := add_le_add (herr i j hi hj) (hE i j)
         _ ≤ 2 * B := by dsimp [η]; linarith
  intro i
  have hbound : |w i - choleskyLower A i r| ≤
      (2 * (1 + B / μ) * η + 16 * u * B) / Real.sqrt μ := by
    rcases lt_trichotomy i r with hi | rfl | hi
    · rw [hz i hi, isLowerTriangular_choleskyLower A hi, sub_self, abs_zero]
      positivity
    · rw [hA.isHermitian.choleskyLower_apply_self]
      exact abs_sub_sqrt_le_of_relErr hu hμ hμB hη0 (by linarith)
        ((le_abs_self _).trans (hm r r le_rfl le_rfl)) hp (herr r r le_rfl le_rfl) hroot
    · have hf := abs_sub_div_sqrt_le_of_pivot_relErr hu hu1 hμ hB ha hp
        (hm i r hi.le le_rfl) (hE i r) (herr i r hi.le le_rfl) (herr r r le_rfl le_rfl)
        hroot (hdiv i hi)
      simpa only [choleskyLower, Matrix.of_apply, if_pos hi.le, RCLike.re_to_real,
        RCLike.ofReal_real_eq_id, id_eq] using hf
  apply hbound.trans
  gcongr

end NLAlib.Computation.CholeskyRounding
