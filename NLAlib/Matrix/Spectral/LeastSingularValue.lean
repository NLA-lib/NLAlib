/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SingularValues

/-!
# Singular vectors and the least singular value

Each singular value of a matrix is the norm of the image of a unit vector, a right singular
vector. For the least singular value this gives the deterministic step of the "invertibility via
distance" argument: when the least singular value is small, some column of the matrix is close to
the span of the others.

## Main results

* `NLAlib.exists_norm_eq_one_and_norm_mulVec_eq_singularValues`: `σ_k(A) = ‖A x‖` for a unit
  vector `x`; in particular the least singular value is attained on the unit sphere.
* `NLAlib.exists_iInf_norm_mulVec_le_of_singularValues_le`: a small least singular value puts a
  column within `√n` times it of the span of the other columns.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Every singular value is attained at a unit vector**: for `k` below the number of columns
there is a unit vector `x`, a right singular vector, with `‖A x‖ = σ_k(A)`. With
`k + 1 = Fintype.card n` it says that the least singular value is the minimum of `‖A x‖` over
the unit sphere (`NLAlib.singularValues_last_mul_norm_le` is the lower bound); the case `k = 0` is
`NLAlib.exists_norm_eq_one_and_norm_mulVec_eq_specNorm`. [HornJohnson2013, §2.6]. -/
theorem exists_norm_eq_one_and_norm_mulVec_eq_singularValues (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) :
    ∃ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 ∧ ‖WithLp.toLp 2 (A *ᵥ x)‖ = singularValues A k := by
  obtain ⟨u, hu, hAu⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_norm_eq_one_and_mulVec_eq hk
  refine ⟨u, hu, ?_⟩
  have h := re_quadForm_of_mulVec_eq_smul hu hAu
  rw [quadForm_conjTranspose_mul_self, RCLike.ofReal_re, ← sq_singularValues] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (singularValues_nonneg A k)).mp h

/-- **A small least singular value puts a column near the span of the others.** If the least
singular value of a matrix with `n` columns is at most `s`, then for some column `j` the infimum
of `‖A x‖` over the vectors `x` with `x j = 1`, which is the distance from column `j` to the span
of the other columns, is at most `√n * s`. This is the deterministic step of the "invertibility
via distance" argument for the least singular value of a random matrix.
[RudelsonVershynin2008, Lemma 3.5]; stated there for square real matrices, in probability.
Port of `NLAlib.exists_iInf_norm_mulVec_le_of_singularValues_last_le`, there over `ℝ`. -/
theorem exists_iInf_norm_mulVec_le_of_singularValues_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {s : ℝ} (hs : singularValues A k ≤ s) :
    ∃ j : n, ⨅ x : {x : n → 𝕜 // x j = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ ≤
      √(Fintype.card n) * s := by
  obtain ⟨u, hu, hAu⟩ :=
    exists_norm_eq_one_and_norm_mulVec_eq_singularValues A (k := k) (by omega)
  have hn : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖u i‖) Finset.univ_nonempty
  have hsum : (1 : ℝ) ≤ Fintype.card n * ‖u j‖ ^ 2 := by
    have h1 : ‖WithLp.toLp 2 u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    rw [hu, one_pow] at h1
    rw [h1, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hj i (Finset.mem_univ i)) 2
  have huj : 0 < ‖u j‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
    rw [← h0] at hsum
    norm_num at hsum
  have hsqrt : 1 ≤ √(Fintype.card n) * ‖u j‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (u j)), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.one_le_sqrt.mpr hsum
  have hbdd : BddBelow (Set.range fun x : {x : n → 𝕜 // x j = 1} =>
      ‖WithLp.toLp 2 (A *ᵥ x.1)‖) := ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  have hxj : ((u j)⁻¹ • u) j = 1 := by
    rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ (norm_pos_iff.mp huj)]
  refine ⟨j, (ciInf_le hbdd ⟨(u j)⁻¹ • u, hxj⟩).trans ?_⟩
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, norm_inv, hAu, inv_mul_le_iff₀ huj]
  have hs0 : 0 ≤ s := (singularValues_nonneg A k).trans hs
  calc singularValues A k ≤ 1 * s := by rwa [one_mul]
    _ ≤ √(Fintype.card n) * ‖u j‖ * s := mul_le_mul_of_nonneg_right hsqrt hs0
    _ = ‖u j‖ * (√(Fintype.card n) * s) := by ring

end NLAlib
