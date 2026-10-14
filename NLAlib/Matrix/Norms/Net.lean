/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Topology.MetricSpace.CoveringNumbers
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
* `Metric.IsCover.exists_mem_norm_toLp_sub_le`: a unit vector is within `ε` of the net.
* `NLAlib.exists_finite_isCover_sphere`: a net of the sphere with at most `(1 + 2 / ε) ^ d`
  points.
* `NLAlib.exists_finset_specNorm_le_div`, `NLAlib.exists_finset_specNorm_le_div_of_isHermitian`:
  the two combined.
-/

@[expose] public section

open Metric
open scoped Matrix NNReal

universe u

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The real dimension of `n → 𝕜` is the number of coordinates times the real dimension of `𝕜`:
`card n` over `ℝ` and `2 * card n` over `ℂ`. -/
theorem finrank_real_fun (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] :
    Module.finrank ℝ (n → 𝕜) = Fintype.card n * Module.finrank ℝ 𝕜 := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **A unit vector is within `ε` of an `ε`-net of the sphere, in coordinates**: if `N` is an
`ε`-net of the unit sphere of `EuclideanSpace 𝕜 n` and `y : n → 𝕜` has Euclidean norm `1`, some
`x ∈ N` has `‖y - x‖ ≤ ε`. The coordinate form of `Metric.IsCover.subset_iUnion_closedBall`. -/
theorem _root_.Metric.IsCover.exists_mem_norm_toLp_sub_le {N : Set (EuclideanSpace 𝕜 n)}
    {ε : ℝ≥0} (hN : IsCover ε (sphere (0 : EuclideanSpace 𝕜 n) 1) N) {y : n → 𝕜}
    (hy : ‖WithLp.toLp 2 y‖ = 1) : ∃ x ∈ N, ‖WithLp.toLp 2 (y - WithLp.ofLp x)‖ ≤ ε := by
  have h := hN.subset_iUnion_closedBall (mem_sphere_zero_iff_norm.2 hy)
  simp only [Set.mem_iUnion, mem_closedBall, exists_prop] at h
  obtain ⟨x, hx, hxy⟩ := h
  refine ⟨x, hx, ?_⟩
  rwa [WithLp.toLp_sub, WithLp.toLp_ofLp, ← dist_eq_norm]

/-- **Spectral norm from a net.** If `N` is an `ε`-net of the unit sphere with `ε < 1` and
`‖A x‖ ≤ M` for every `x` in `N`, then `specNorm A ≤ M / (1 - ε)`.
[Vershynin2018, Lemma 4.4.1]. Port of `NLAlib.specNorm_le_div_of_net`, there over `ℝ` with the
net property as a raw condition. -/
theorem specNorm_le_div_of_isCover (A : Matrix m n 𝕜) {N : Set (EuclideanSpace 𝕜 n)} {ε : ℝ≥0}
    (hε : ε < 1) (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ N, ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ M) :
    specNorm A ≤ M / (1 - ε) := by
  have hε' : (ε : ℝ) < 1 := mod_cast hε
  have key : specNorm A ≤ M + specNorm A * ε := by
    refine specNorm_le_of_forall_norm_eq_one (by positivity) fun y hy => ?_
    obtain ⟨x, hxN, hxy⟩ := hN.exists_mem_norm_toLp_sub_le hy
    have hsplit : A *ᵥ y = A *ᵥ WithLp.ofLp x + A *ᵥ (y - WithLp.ofLp x) := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    rw [hsplit, WithLp.toLp_add]
    refine (norm_add_le _ _).trans (add_le_add (hM x hxN) ?_)
    exact (norm_toLp_mulVec_le A _).trans (by gcongr)
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Spectral norm from two nets.** If `N` and `N'` are `ε`-nets of the unit spheres of the
domain and codomain with `ε < 1 / 2`, the codomain net `N'` contained in the unit ball, and
`|yᴴ A x| ≤ M` on `N' × N`, then `specNorm A ≤ M / (1 - 2 ε)`.
[Vershynin2018, Exercise 4.4.3]. Port of `NLAlib.specNorm_le_div_of_net_bilinear`. -/
theorem specNorm_le_div_of_isCover_of_isCover (A : Matrix m n 𝕜)
    {N : Set (EuclideanSpace 𝕜 n)} {N' : Set (EuclideanSpace 𝕜 m)} {ε : ℝ≥0} (hε : ε < 1 / 2)
    (hN : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) N)
    (hN' : Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 m) 1) N')
    (hNs' : N' ⊆ Metric.closedBall 0 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ N, ∀ y ∈ N', ‖star (WithLp.ofLp y) ⬝ᵥ (A *ᵥ WithLp.ofLp x)‖ ≤ M) :
    specNorm A ≤ M / (1 - 2 * ε) := by
  have hε' : (ε : ℝ) < 1 / 2 := mod_cast hε
  have key : specNorm A ≤ M + 2 * ε * specNorm A := by
    refine specNorm_le_of_forall_norm_star_dotProduct_mulVec_le (by positivity)
      fun u x hu hx => ?_
    obtain ⟨x₀, hx₀N, hx₀⟩ := hN.exists_mem_norm_toLp_sub_le hx
    obtain ⟨u₀, hu₀N, hu₀⟩ := hN'.exists_mem_norm_toLp_sub_le hu
    have hu₀1 : ‖WithLp.toLp 2 (WithLp.ofLp u₀)‖ ≤ 1 := mem_closedBall_zero_iff.1 (hNs' hu₀N)
    have hsplit : star u ⬝ᵥ (A *ᵥ x) = star (WithLp.ofLp u₀) ⬝ᵥ (A *ᵥ WithLp.ofLp x₀) +
        star (u - WithLp.ofLp u₀) ⬝ᵥ (A *ᵥ x) +
        star (WithLp.ofLp u₀) ⬝ᵥ (A *ᵥ (x - WithLp.ofLp x₀)) := by
      simp only [Matrix.mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub]
      ring
    have h1 : ‖star (u - WithLp.ofLp u₀) ⬝ᵥ (A *ᵥ x)‖ ≤ ε * specNorm A := by
      refine (norm_star_dotProduct_mulVec_le A _ x).trans ?_
      rw [hx, mul_one]
      gcongr
    have h2 : ‖star (WithLp.ofLp u₀) ⬝ᵥ (A *ᵥ (x - WithLp.ofLp x₀))‖ ≤ ε * specNorm A := by
      refine (norm_star_dotProduct_mulVec_le A _ _).trans ?_
      calc ‖WithLp.toLp 2 (WithLp.ofLp u₀)‖ * specNorm A * ‖WithLp.toLp 2 (x - WithLp.ofLp x₀)‖
          ≤ 1 * specNorm A * ε := by gcongr
        _ = ε * specNorm A := by ring
    rw [hsplit]
    refine (norm_add₃_le).trans ?_
    linarith [hM x₀ hx₀N u₀ hu₀N]
  rw [le_div_iff₀ (by linarith)]
  linarith [specNorm_nonneg A]

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
  have hε' : (ε : ℝ) < 1 / 2 := mod_cast hε
  have key : specNorm A ≤ M + 2 * ε * specNorm A := by
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [Subsingleton.elim A 0, specNorm_zero]
      positivity
    obtain ⟨x, hx, hxA⟩ := hA.exists_norm_eq_one_and_abs_re_quadForm_eq_specNorm
    obtain ⟨x₀, hx₀N, hx₀⟩ := hN.exists_mem_norm_toLp_sub_le hx
    have hx₀1 : ‖WithLp.toLp 2 (WithLp.ofLp x₀)‖ ≤ 1 := mem_closedBall_zero_iff.1 (hNs hx₀N)
    have hsplit : quadForm A x = quadForm A (WithLp.ofLp x₀) +
        star (x - WithLp.ofLp x₀) ⬝ᵥ (A *ᵥ x) +
        star (WithLp.ofLp x₀) ⬝ᵥ (A *ᵥ (x - WithLp.ofLp x₀)) := by
      simp only [quadForm_def, Matrix.mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub]
      ring
    have h1 : ‖star (x - WithLp.ofLp x₀) ⬝ᵥ (A *ᵥ x)‖ ≤ ε * specNorm A := by
      refine (norm_star_dotProduct_mulVec_le A _ x).trans ?_
      rw [hx, mul_one]
      gcongr
    have h2 : ‖star (WithLp.ofLp x₀) ⬝ᵥ (A *ᵥ (x - WithLp.ofLp x₀))‖ ≤ ε * specNorm A := by
      refine (norm_star_dotProduct_mulVec_le A _ _).trans ?_
      calc ‖WithLp.toLp 2 (WithLp.ofLp x₀)‖ * specNorm A * ‖WithLp.toLp 2 (x - WithLp.ofLp x₀)‖
          ≤ 1 * specNorm A * ε := by gcongr
        _ = ε * specNorm A := by ring
    refine hxA.symm.le.trans ?_
    rw [hsplit, map_add, map_add]
    refine (abs_add_three _ _ _).trans ?_
    linarith [hM x₀ hx₀N, (RCLike.abs_re_le_norm _).trans h1, (RCLike.abs_re_le_norm _).trans h2]
  rw [le_div_iff₀ (by linarith)]
  linarith [specNorm_nonneg A]

/-- **A finite net of the sphere.** For every `ε > 0` the unit sphere of `EuclideanSpace 𝕜 n` has
an `ε`-net of unit vectors with at most `(1 + 2 / ε) ^ d` points, `d` the real dimension.
[Vershynin2018, Corollary 4.2.13]. Port of `NLAlib.exists_finset_sphere_net`, there over `ℝ`. -/
theorem exists_finite_isCover_sphere (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ N : Finset (EuclideanSpace 𝕜 n),
      (N : Set (EuclideanSpace 𝕜 n)) ⊆ Metric.sphere 0 1 ∧
      Metric.IsCover ε (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) (N : Set (EuclideanSpace 𝕜 n)) ∧
      (N.card : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ Module.finrank ℝ (EuclideanSpace 𝕜 n) :=
  Metric.exists_finset_isCover_sphere_card_le (EuclideanSpace 𝕜 n) hε

/-- The coordinates of a finite net of the sphere: a finite set of unit vectors of `n → 𝕜`, of the
volumetric cardinality, whose image in `EuclideanSpace 𝕜 n` is an `ε`-net of the unit sphere. -/
private theorem exists_finset_isCover_image_toLp (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset (n → 𝕜), (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ (n → 𝕜) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      IsCover ⟨ε, hε.le⟩ (sphere (0 : EuclideanSpace 𝕜 n) 1)
        (WithLp.toLp 2 '' (N : Set (n → 𝕜))) := by
  classical
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_finite_isCover_sphere 𝕜 n (ε := ⟨ε, hε.le⟩) hε
  refine ⟨N.image WithLp.ofLp, ?_, fun x hx => ?_, ?_⟩
  · rw [← (WithLp.linearEquiv 2 ℝ (n → 𝕜)).finrank_eq]
    exact (Nat.cast_le.2 Finset.card_image_le).trans hN3
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
    exact mem_sphere_zero_iff_norm.1 (hN1 hz)
  · convert hN2 using 1
    ext z
    simp

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
  obtain ⟨N, hcard, hunit, hcov⟩ := exists_finset_isCover_image_toLp 𝕜 n hε0
  refine ⟨N, hcard, hunit, fun A M hM0 hM => ?_⟩
  refine specNorm_le_div_of_isCover A (ε := ⟨ε, hε0.le⟩) (mod_cast hε1) hcov hM0 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hM x hx

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
  obtain ⟨N, hcard, hunit, hcov⟩ := exists_finset_isCover_image_toLp 𝕜 n hε0
  refine ⟨N, hcard, hunit, fun A hA M hM0 hM => ?_⟩
  refine hA.specNorm_le_div_of_isCover (ε := ⟨ε, hε0.le⟩) (mod_cast hε1) hcov ?_ hM0 ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.2 (hunit x hx).le
  · rintro _ ⟨x, hx, rfl⟩
    exact hM x hx

end NLAlib
