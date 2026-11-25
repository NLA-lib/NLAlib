/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.CholeskyErr
public import NLAlib.Matrix.Norms.Compare

/-!
# Cholesky backward error from forward factor error

An approximation of an exact Cholesky factor gives an absolute spectral residual bound.
The estimate includes the quadratic term in the factor perturbation.

## Main results

* `NLAlib.IsCholesky.isCholeskyErr_of_specNorm_sub_le`: a spectral forward-to-backward bridge.
* `NLAlib.IsCholesky.isCholeskyErr_of_forall_abs_sub_le`: an entrywise forward-to-backward bridge.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

/-- An approximate triangular positive-diagonal factor within spectral distance $\delta$
of an exact Cholesky factor has absolute residual at most
$\delta(2\sqrt B+\delta)$ when the input spectral norm is at most $B$. -/
theorem IsCholesky.isCholeskyErr_of_specNorm_sub_le {A F L : Matrix n n 𝕜}
    (hF : IsCholesky A F) {B δ : ℝ} (hB : specNorm A ≤ B)
    (hL : L.IsLowerTriangular) (hdiag : ∀ i, 0 < L i i) (hδ : specNorm (F - L) ≤ δ) :
    IsCholeskyErr (δ * (2 * Real.sqrt B + δ)) A L := by
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hB0 : 0 ≤ B := (specNorm_nonneg A).trans hB
  have hFn : specNorm F ≤ Real.sqrt B := by
    have hs : specNorm F ^ 2 ≤ B := by
      rw [← specNorm_mul_conjTranspose_self, ← hF.eq_mul_conjTranspose]
      exact hB
    exact (Real.le_sqrt (specNorm_nonneg F) hB0).mpr hs
  have hLn : specNorm L ≤ Real.sqrt B + δ := by
    have he : L = F - (F - L) := by abel
    calc specNorm L = specNorm (F - (F - L)) := congrArg specNorm he
         _ ≤ specNorm F + specNorm (F - L) := specNorm_sub_le _ _
         _ ≤ Real.sqrt B + δ := add_le_add hFn hδ
  have he : A - L * Lᴴ = (F - L) * Fᴴ + L * (F - L)ᴴ := by
    rw [hF.eq_mul_conjTranspose, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  refine ⟨hL, hdiag, ?_⟩
  rw [he]
  calc specNorm ((F - L) * Fᴴ + L * (F - L)ᴴ)
      ≤ specNorm ((F - L) * Fᴴ) + specNorm (L * (F - L)ᴴ) := specNorm_add_le _ _
    _ ≤ specNorm (F - L) * specNorm F + specNorm L * specNorm (F - L) := by
      simpa only [specNorm_conjTranspose] using
        add_le_add (specNorm_mul_le (F - L) Fᴴ) (specNorm_mul_le L (F - L)ᴴ)
    _ ≤ δ * Real.sqrt B + (Real.sqrt B + δ) * δ := by gcongr
    _ = δ * (2 * Real.sqrt B + δ) := by ring

/-- A uniform entrywise factor approximation gives an absolute spectral Cholesky error.
No nonempty-index assumption is needed; an empty factor gives zero error. -/
theorem IsCholesky.isCholeskyErr_of_forall_abs_sub_le {A F L : Matrix n n ℝ}
    (hF : IsCholesky A F) {B e : ℝ} (hB : specNorm A ≤ B) (he : 0 ≤ e)
    (hL : L.IsLowerTriangular) (hdiag : ∀ i, 0 < L i i)
    (hentry : ∀ i j, |F i j - L i j| ≤ e) :
    IsCholeskyErr ((Fintype.card n * e) * (2 * Real.sqrt B + Fintype.card n * e)) A L := by
  exact hF.isCholeskyErr_of_specNorm_sub_le hB hL hdiag
    ((specNorm_le_frobNorm _).trans (frobNorm_le_card_mul_of_forall_abs_le he hentry))

end NLAlib
