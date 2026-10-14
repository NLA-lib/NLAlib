/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.PolarFrames

/-!
# Procrustes problems

The orthogonal Procrustes problem asks for the unitary `U` that brings `U B` closest to `A` in
the Frobenius norm. It is solved by an isometric polar factor of `A Bᴴ`, and the least value is
`‖A‖_F² + ‖B‖_F² - 2 ‖A Bᴴ‖_*`. With a unitary factor on each side the least value is the
distance between the sorted singular values.

## Main results

* `NLAlib.HasOrthonormalCols.frobInner_eq_nuclearNorm_of_mul_sqrt_eq`,
  `NLAlib.frobInner_polarFactor`: a polar factor attains the nuclear dual pairing.
* `NLAlib.frobNorm_sub_mul_sq_of_mul_sqrt_eq`: the objective at a polar factor of `A Bᴴ`.
* `NLAlib.isLeast_frobNorm_sub_mul_sq`: the orthogonal Procrustes problem.
* `NLAlib.isLeast_frobNorm_sub_mul_mul_sq`: the two-sided Procrustes problem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

omit [DecidableEq m] in
/-- **An isometric polar factor attains the nuclear dual pairing.** If `M = U |M|` with `U` of
orthonormal columns and `|M| = CFC.sqrt (Mᴴ * M)`, then `⟨M, U⟩ = ‖M‖_*`. This is the case of
equality in `NLAlib.abs_frobInner_le_nuclearNorm_mul_specNorm`. Rectangular, any rank.
[HornJohnson2013, §7.4.4].
Port of `NLAlib.frobInner_eq_nuclearNorm_of_polar`, there over `ℝ` for square matrices. -/
theorem HasOrthonormalCols.frobInner_eq_nuclearNorm_of_mul_sqrt_eq [DecidableEq n]
    {M U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (h : U * CFC.sqrt (Mᴴ * M) = M) :
    frobInner M U = nuclearNorm M := by
  rw [nuclearNorm_eq_re_trace_sqrt, frobInner_eq_re_trace_mul_conjTranspose]
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt (Mᴴ * M) := ⟨_, rfl⟩
  rw [← hS] at h ⊢
  rw [← h, Matrix.trace_mul_comm, hU.conjTranspose_mul_cancel_left]

omit [DecidableEq m] in
/-- **The polar factor attains the nuclear dual pairing**: `⟨M, polarFactor M⟩ = ‖M‖_*`, for
every shape and rank; the polar factor is then a partial isometry and need not have orthonormal
columns. [HornJohnson2013, §7.4.4]. -/
theorem frobInner_polarFactor [DecidableEq n] (M : Matrix m n 𝕜) :
    frobInner M (polarFactor M) = nuclearNorm M := by
  rw [nuclearNorm_eq_re_trace_sqrt, frobInner_eq_re_trace, polarFactor, ← Matrix.mul_assoc]
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt (Mᴴ * M) := ⟨_, rfl⟩
  have hSS : S * S = Mᴴ * M := by
    rw [hS]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  rw [← hS, ← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm, mul_pinv_mul_self]

/-- The Procrustes objective through the inner product of `A Bᴴ` with the unitary factor. -/
private theorem frobNorm_sub_mul_sq_eq (A B : Matrix m n 𝕜) {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U) :
    frobNorm (A - U * B) ^ 2 =
      frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * frobInner (A * Bᴴ) U := by
  rw [frobNorm_sub_sq, hU.frobNorm_mul_left, frobInner_eq_re_trace_mul_conjTranspose A,
    frobInner_eq_re_trace_mul_conjTranspose (A * Bᴴ), Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc]
  ring

/-- The Procrustes objective at a polar factor of `A Bᴴ`.
Port of `NLAlib.frobSq_sub_mul_eq_of_cross_polar`. -/
theorem frobNorm_sub_mul_sq_of_mul_sqrt_eq {A B : Matrix m n 𝕜} {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U)
    (h : U * CFC.sqrt ((A * Bᴴ)ᴴ * (A * Bᴴ)) = A * Bᴴ) :
    frobNorm (A - U * B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ) := by
  rw [frobNorm_sub_mul_sq_eq A B hU, hU.frobInner_eq_nuclearNorm_of_mul_sqrt_eq h]

/-- **The orthogonal Procrustes problem.** The least value of `‖A - U B‖_F²` over unitary `U` is
`‖A‖_F² + ‖B‖_F² - 2 ‖A Bᴴ‖_*`, attained at a polar factor of `A Bᴴ`.
[GolubVanLoan2013, §6.4.1]; [HornJohnson2013, §7.4.5].
Port of `NLAlib.isLeast_frobSq_sub_orthogonal_mul`, there over `ℝ`.
Result: procrustes -/
theorem isLeast_frobNorm_sub_mul_sq (A B : Matrix m n 𝕜) :
    IsLeast ((fun U : Matrix m m 𝕜 => frobNorm (A - U * B) ^ 2) '' {U | HasOrthonormalCols U})
      (frobNorm A ^ 2 + frobNorm B ^ 2 - 2 * nuclearNorm (A * Bᴴ)) := by
  constructor
  · obtain ⟨U, hU, h⟩ := exists_hasOrthonormalCols_mul_sqrt_eq (A * Bᴴ) le_rfl
    exact ⟨U, hU, frobNorm_sub_mul_sq_of_mul_sqrt_eq hU h⟩
  · rintro _ ⟨U, hU, rfl⟩
    have hU' : HasOrthonormalCols U := hU
    have h1 : frobInner (A * Bᴴ) U ≤ nuclearNorm (A * Bᴴ) :=
      (le_abs_self _).trans ((abs_frobInner_le_nuclearNorm_mul_specNorm _ _).trans
        (mul_le_of_le_one_right (nuclearNorm_nonneg _) hU'.specNorm_le_one))
    simp only
    rw [frobNorm_sub_mul_sq_eq A B hU']
    linarith

/-- **The two-sided Procrustes problem.** The least value of `‖A - U B W‖_F²` over unitary `U`,
`W` is `∑ (σ_i(A) - σ_i(B))²`. [HornJohnson2013, §7.4.1 context].
Port of `NLAlib.isLeast_frobSq_sub_orthogonal_mul_mul`, there over `ℝ`. -/
theorem isLeast_frobNorm_sub_mul_mul_sq [DecidableEq n] (A B : Matrix m n 𝕜) :
    IsLeast
      ((fun P : Matrix m m 𝕜 × Matrix n n 𝕜 => frobNorm (A - P.1 * B * P.2) ^ 2) ''
        {P | HasOrthonormalCols P.1 ∧ HasOrthonormalCols P.2})
      (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) := by
  obtain ⟨k, hk⟩ : ∃ k, k = min (Fintype.card m) (Fintype.card n) := ⟨_, rfl⟩
  rw [← hk]
  constructor
  · -- Align the singular vectors of `B` with those of `A`.
    have hkm : k ≤ Fintype.card m := hk.trans_le (min_le_left _ _)
    have hkn : k ≤ Fintype.card n := hk.trans_le (min_le_right _ _)
    obtain ⟨UA, VA, hA⟩ := exists_isSVD A
      (hk.symm ▸ le_min A.rank_le_card_height A.rank_le_card_width) hkm hkn
    obtain ⟨UB, VB, hB⟩ := exists_isSVD B
      (hk.symm ▸ le_min B.rank_le_card_height B.rank_le_card_width) hkm hkn
    obtain ⟨P, hP, hPU⟩ :=
      hB.hasOrthonormalCols_left.exists_mul_eq hA.hasOrthonormalCols_left
    obtain ⟨R, hR, hRV⟩ :=
      hB.hasOrthonormalCols_right.exists_mul_eq hA.hasOrthonormalCols_right
    refine ⟨(P, Rᴴ), ⟨hP, hR.conjTranspose⟩, ?_⟩
    have h1 : P * B * Rᴴ =
        UA * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) * VAᴴ :=
      calc P * B * Rᴴ
        _ = P * (UB * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) * VBᴴ) *
            Rᴴ := by rw [← hB.eq]
        _ = P * UB * Matrix.diagonal (fun i : Fin k => ((singularValues B i : ℝ) : 𝕜)) *
            (R * VB)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPU, hRV]
    have h2 : A - P * B * Rᴴ = UA * Matrix.diagonal (fun i : Fin k =>
        ((singularValues A i : ℝ) : 𝕜) - ((singularValues B i : ℝ) : 𝕜)) * VAᴴ := by
      rw [h1, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← hA.eq]
    simp only
    rw [h2, Matrix.mul_assoc, hA.hasOrthonormalCols_left.frobNorm_mul_left,
      hA.hasOrthonormalCols_right.frobNorm_mul_conjTranspose_right, frobNorm_diagonal_sq,
      ← Fin.sum_univ_eq_sum_range (fun i => (singularValues A i - singularValues B i) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, sq_abs]
  · rintro _ ⟨⟨P, W⟩, ⟨hP, hW⟩, rfl⟩
    have hP' : HasOrthonormalCols P := hP
    have hW' : HasOrthonormalCols W := hW
    have hsv : singularValues (P * B * W) = singularValues B := by
      rw [Matrix.mul_assoc, hP'.singularValues_mul_left]
      have h := hW'.conjTranspose.singularValues_mul_conjTranspose_right B
      rwa [Matrix.conjTranspose_conjTranspose] at h
    have h := sum_sq_singularValues_sub_le_frobNorm_sub_sq A (P * B * W) (Finset.range k)
    rwa [hsv] at h

end NLAlib
