/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Separation bounds for the Sylvester operator

For matrices `L` and `M` whose spectra are separated, the Sylvester operator `X ↦ L * X - X * M`
is bounded below: `δ ‖X‖ ≤ ‖L X - X M‖`. These bounds are the engine of the `sin Θ` theorems.

Two regimes are covered. When one spectrum lies in a disc and the other outside a larger
concentric disc (in particular: Hermitian `M` with spectrum in an interval and Hermitian `L` with
spectrum outside a wider interval) the bound holds in every unitarily invariant norm. For
Hermitian matrices with arbitrarily interleaved spectra at distance `δ` it holds in the Frobenius
norm.

## Main results

* `NLAlib.SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul`: disc separation, any
  unitarily invariant norm.
* `NLAlib.SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue`: interval
  separation for Hermitian matrices.
* `NLAlib.mul_frobNorm_le_frobNorm_mul_sub_mul`: arbitrary separation, Frobenius norm.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Disc separation, every unitarily invariant norm -/

/-- **Sylvester separation bound, disc form.** If `‖M‖₂ ≤ r` and `L` is bounded below by
`r + δ`, in the form `(r + δ)² • 1 ≤ Lᴴ L`, then `δ ‖X‖ ≤ ‖L X - X M‖` in every unitarily
invariant norm. Apply it to `L - c • 1` and `M - c • 1` for a disc centred at `c`.
[Bhatia1997, Theorem VII.2.8]. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul (Φ : SymmetricGauge)
    {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {r δ : ℝ} (hM : specNorm M ≤ r)
    (hL : ((r + δ) ^ 2) • (1 : Matrix m m 𝕜) ≤ Lᴴ * L) (X : Matrix m n 𝕜) :
    δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  sorry

/-- The disc form with the roles of the two matrices exchanged: `‖L‖₂ ≤ r` and `M` bounded
below by `r + δ`, in the form `(r + δ)² • 1 ≤ M Mᴴ`. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul' (Φ : SymmetricGauge)
    {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {r δ : ℝ} (hL : specNorm L ≤ r)
    (hM : ((r + δ) ^ 2) • (1 : Matrix n n 𝕜) ≤ M * Mᴴ) (X : Matrix m n 𝕜) :
    δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  sorry

/-! ### Interval separation for Hermitian matrices -/

/-- A Hermitian matrix with spectrum in `[a, b]` is within `(b - a) / 2` of the midpoint.
Port of `NLAlib.specNorm_shift_le_half_width`. -/
theorem specNorm_sub_smul_one_le_of_le {M : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ M) (h₂ : M ≤ b • (1 : Matrix n n 𝕜)) :
    specNorm (M - ((a + b) / 2) • (1 : Matrix n n 𝕜)) ≤ (b - a) / 2 := by
  sorry

/-- A Hermitian matrix whose eigenvalues are at distance at least `s` from `c` is bounded below
by `s` after the shift: `s² • 1 ≤ (L - c • 1)ᴴ (L - c • 1)`.
Port of `NLAlib.mulVec_shift_sq_ge_of_eigenvalue_abs_sub_ge`. -/
theorem _root_.Matrix.IsHermitian.sq_smul_one_le_sub_smul_one_conjTranspose_mul_self
    {L : Matrix m m 𝕜} (hL : L.IsHermitian) {s c : ℝ} (hs : 0 ≤ s)
    (h : ∀ i, i < Fintype.card m → s ≤ |eigenvalue L i - c|) :
    (s ^ 2) • (1 : Matrix m m 𝕜) ≤
      (L - c • (1 : Matrix m m 𝕜))ᴴ * (L - c • (1 : Matrix m m 𝕜)) := by
  sorry

/-- **Sylvester separation bound, interval form.** For Hermitian `L` and `M`, if the spectrum of
`M` lies in `[a, b]` and every eigenvalue of `L` lies outside `(a - δ, b + δ)`, then
`δ ‖X‖ ≤ ‖L X - X M‖` in every unitarily invariant norm.
[Bhatia1997, Theorem VII.2.8 and §VII.3]; [DavisKahan1970].
Port of `NLAlib.mul_specNorm_le_specNorm_sylvester_of_interval`, there over `ℝ` in the spectral
norm.
Result: sylvester-separation -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue
    (Φ : SymmetricGauge) {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} (hL : L.IsHermitian) {a b δ : ℝ}
    (hM₁ : a • (1 : Matrix n n 𝕜) ≤ M) (hM₂ : M ≤ b • (1 : Matrix n n 𝕜))
    (hLsep : ∀ i, i < Fintype.card m → eigenvalue L i ≤ a - δ ∨ b + δ ≤ eigenvalue L i)
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  sorry

/-- **Sylvester separation bound, one-sided form.** If `L ≤ (α - δ) • 1` and `α • 1 ≤ M`, then
`δ ‖X‖ ≤ ‖L X - X M‖` in every unitarily invariant norm.
Port of `NLAlib.mul_specNorm_le_specNorm_sylvester_of_one_sided`. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_le (Φ : SymmetricGauge)
    {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {α δ : ℝ}
    (hL : L ≤ (α - δ) • (1 : Matrix m m 𝕜)) (hM : α • (1 : Matrix n n 𝕜) ≤ M)
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  sorry

/-- The one-sided form with `L` above `M`: `(α + δ) • 1 ≤ L` and `M ≤ α • 1`. -/
theorem SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_ge (Φ : SymmetricGauge)
    {L : Matrix m m 𝕜} {M : Matrix n n 𝕜} {α δ : ℝ}
    (hL : (α + δ) • (1 : Matrix m m 𝕜) ≤ L) (hM : M ≤ α • (1 : Matrix n n 𝕜))
    (X : Matrix m n 𝕜) : δ * Φ.matrixNorm X ≤ Φ.matrixNorm (L * X - X * M) := by
  sorry

/-- The interval form in the spectral norm. -/
theorem mul_specNorm_le_specNorm_mul_sub_mul_of_eigenvalue {L : Matrix m m 𝕜}
    {M : Matrix n n 𝕜} (hL : L.IsHermitian) {a b δ : ℝ} (hM₁ : a • (1 : Matrix n n 𝕜) ≤ M)
    (hM₂ : M ≤ b • (1 : Matrix n n 𝕜))
    (hLsep : ∀ i, i < Fintype.card m → eigenvalue L i ≤ a - δ ∨ b + δ ≤ eigenvalue L i)
    (X : Matrix m n 𝕜) : δ * specNorm X ≤ specNorm (L * X - X * M) := by
  sorry

/-! ### Arbitrary separation, Frobenius norm -/

/-- **Sylvester separation bound in the Frobenius norm.** For Hermitian `L` and `M` whose
eigenvalues are pairwise at distance at least `δ`, `δ ‖X‖_F ≤ ‖L X - X M‖_F`. No interval
structure is needed.
[Bhatia1997, §VII.2]; [StewartSun1990, §V.3].
Port of `NLAlib.mul_frobNorm_le_frobNorm_sylvester`, there over `ℝ`.
Result: sylvester-separation -/
theorem mul_frobNorm_le_frobNorm_mul_sub_mul {L : Matrix m m 𝕜} {M : Matrix n n 𝕜}
    (hL : L.IsHermitian) (hM : M.IsHermitian) {δ : ℝ}
    (hsep : ∀ i, i < Fintype.card m → ∀ j, j < Fintype.card n →
      δ ≤ |eigenvalue L i - eigenvalue M j|)
    (X : Matrix m n 𝕜) : δ * frobNorm X ≤ frobNorm (L * X - X * M) := by
  sorry

/-- A Sylvester equation with separated Hermitian coefficients has only the trivial homogeneous
solution: if `L X = X M` and the spectra are disjoint, then `X = 0`. -/
theorem eq_zero_of_mul_eq_mul_of_eigenvalue_ne {L : Matrix m m 𝕜} {M : Matrix n n 𝕜}
    (hL : L.IsHermitian) (hM : M.IsHermitian)
    (hsep : ∀ i, i < Fintype.card m → ∀ j, j < Fintype.card n → eigenvalue L i ≠ eigenvalue M j)
    {X : Matrix m n 𝕜} (h : L * X = X * M) : X = 0 := by
  sorry

end NLAlib
