/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import NLAlib.Matrix.Norms.Loewner

/-!
# Bounding the spectral norm on a net

The spectral norm of a matrix is controlled by its values on a finite ε-net of the unit sphere,
and such a net exists with at most `(1 + 2 / ε) ^ d` points, where `d` is the real dimension of
the space. This is the discretisation step in bounds for random matrices.

The nets are Mathlib's `Metric.IsCover` in `EuclideanSpace 𝕜 n`. The two headline statements
`NLAlib.exists_finset_specNorm_le_div` and `NLAlib.exists_finset_specNorm_le_div_of_isHermitian`
hide the cover and give a finite set of unit vectors in `n → 𝕜` that works for every matrix.

## Main results

* `NLAlib.specNorm_le_div_of_isCover`: `specNorm A ≤ M / (1 - ε)` from a bound `M` on the net.
* `Matrix.IsHermitian.specNorm_le_div_of_isCover`: for Hermitian `A`, from a bound on the
  quadratic form on the net, with `1 - 2 ε`.
* `NLAlib.exists_finite_isCover_sphere`: a net of the sphere with at most `(1 + 2 / ε) ^ d`
  points.
* `NLAlib.exists_finset_specNorm_le_div`, `NLAlib.exists_finset_specNorm_le_div_of_isHermitian`:
  the two combined.
-/

@[expose] public section

open scoped Matrix NNReal

universe u

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The real dimension of `n → 𝕜` is the number of coordinates times the real dimension of `𝕜`:
`card n` over `ℝ` and `2 * card n` over `ℂ`. -/
theorem finrank_real_fun (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] :
    Module.finrank ℝ (n → 𝕜) = Fintype.card n * Module.finrank ℝ 𝕜 := by
  sorry

/-- **Spectral norm from a net.** If `N` is an `ε`-net of the unit sphere with `ε < 1` and
`‖A x‖ ≤ M` for every `x` in `N`, then `specNorm A ≤ M / (1 - ε)`.
[Vershynin2018, Lemma 4.4.1]. Port of `NLAlib.specNorm_le_div_of_net`, there over `ℝ` with the
net property as a raw condition. -/
theorem specNorm_le_div_of_isCover (A : Matrix m n 𝕜) {N : Set (EuclideanSpace 𝕜 n)} {ε : ℝ≥0}
    (hε : ε < 1) (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ N, ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ M) :
    specNorm A ≤ M / (1 - ε) := by
  sorry

/-- **Spectral norm from two nets.** If `N` and `N'` are `ε`-nets of the unit spheres of the
domain and codomain with `ε < 1 / 2`, contained in the unit balls, and `|yᴴ A x| ≤ M` on
`N' × N`, then `specNorm A ≤ M / (1 - 2 ε)`.
[Vershynin2018, Exercise 4.4.3]. Port of `NLAlib.specNorm_le_div_of_net_bilinear`. -/
theorem specNorm_le_div_of_isCover_of_isCover (A : Matrix m n 𝕜)
    {N : Set (EuclideanSpace 𝕜 n)} {N' : Set (EuclideanSpace 𝕜 m)} {ε : ℝ≥0} (hε : ε < 1 / 2)
    (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N)
    (hN' : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 m) 1) N')
    (hNs : N ⊆ Metric.closedBall 0 1) (hNs' : N' ⊆ Metric.closedBall 0 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ N, ∀ y ∈ N', ‖star (WithLp.ofLp y) ⬝ᵥ (A *ᵥ WithLp.ofLp x)‖ ≤ M) :
    specNorm A ≤ M / (1 - 2 * ε) := by
  sorry

/-- **Spectral norm of a Hermitian matrix from a net.** If `N` is an `ε`-net of the unit sphere
with `ε < 1 / 2`, contained in the unit ball, and `|xᴴ A x| ≤ M` for every `x` in `N`, then
`specNorm A ≤ M / (1 - 2 ε)`.
[Vershynin2018, Exercise 4.4.3]. Port of `NLAlib.specNorm_le_div_of_net_quadForm`, there over
`ℝ`. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_div_of_isCover {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {N : Set (EuclideanSpace 𝕜 n)} {ε : ℝ≥0} (hε : ε < 1 / 2)
    (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N)
    (hNs : N ⊆ Metric.closedBall 0 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ N, |RCLike.re (quadForm A (WithLp.ofLp x))| ≤ M) :
    specNorm A ≤ M / (1 - 2 * ε) := by
  sorry

/-- **A finite net of the sphere.** For every `ε > 0` the unit sphere of `EuclideanSpace 𝕜 n` has
an `ε`-net of unit vectors with at most `(1 + 2 / ε) ^ d` points, `d` the real dimension.
[Vershynin2018, Corollary 4.2.13]. Port of `NLAlib.exists_finset_sphere_net`, there over `ℝ`. -/
theorem exists_finite_isCover_sphere (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ N : Finset (EuclideanSpace 𝕜 n),
      (N : Set (EuclideanSpace 𝕜 n)) ⊆ Metric.sphere 0 1 ∧
      Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) (N : Set (EuclideanSpace 𝕜 n)) ∧
      (N.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ Module.finrank ℝ (EuclideanSpace 𝕜 n) := by
  sorry

/-- **A finite set of unit vectors that controls every spectral norm.** For `0 < ε < 1` there is
a set `N` of at most `(1 + 2 / ε) ^ d` unit vectors of `n → 𝕜`, `d` the real dimension, such that
every matrix `A` with `n` columns and `‖A x‖ ≤ M` on `N` has `specNorm A ≤ M / (1 - ε)`.
[Vershynin2018, Lemma 4.4.1 with Corollary 4.2.13].
Port of `NLAlib.exists_finset_net_specNorm_le`, there over `ℝ`.
Result: spectral-norm-net -/
theorem exists_finset_specNorm_le_div (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N : Finset (n → 𝕜), (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ (n → 𝕜) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      ∀ {m : Type u} [Fintype m] (A : Matrix m n 𝕜) {M : ℝ}, 0 ≤ M →
        (∀ x ∈ N, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ M) → specNorm A ≤ M / (1 - ε) := by
  sorry

/-- **A finite set of unit vectors that controls every Hermitian spectral norm.** For
`0 < ε < 1 / 2` there is a set `N` of at most `(1 + 2 / ε) ^ d` unit vectors of `n → 𝕜` such that
every Hermitian `A` with `|xᴴ A x| ≤ M` on `N` has `specNorm A ≤ M / (1 - 2 ε)`.
[Vershynin2018, Exercise 4.4.3 with Corollary 4.2.13].
Result: spectral-norm-net -/
theorem exists_finset_specNorm_le_div_of_isHermitian (𝕜 : Type*) [RCLike 𝕜] (n : Type*)
    [Fintype n] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ N : Finset (n → 𝕜), (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ (n → 𝕜) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      ∀ (A : Matrix n n 𝕜), A.IsHermitian → ∀ {M : ℝ}, 0 ≤ M →
        (∀ x ∈ N, |RCLike.re (quadForm A x)| ≤ M) → specNorm A ≤ M / (1 - 2 * ε) := by
  sorry

end NLAlib
