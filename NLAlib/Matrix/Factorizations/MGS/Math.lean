/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GramSchmidt

/-!
# Mathematical identities for rank-revealing modified Gram–Schmidt

The column sweep agrees with the existing Gram–Schmidt factors without a rank
assumption. These identities concern matrices and vectors only.

## Main results

* `NLAlib.MGS.mgsSweep_gramSchmidtQ` identifies the residual of each column.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.MGS

variable {𝕜 : Type} [RCLike 𝕜]

/-- The nonzero Gram–Schmidt columns are orthonormal; zero columns remain zero. -/
theorem dotProduct_gramSchmidtQ_col {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜)
    (c c' : Fin k) : star ((gramSchmidtQ M).col c) ⬝ᵥ (gramSchmidtQ M).col c' =
      if c = c' then (if gramSchmidtR M c c = 0 then 0 else 1) else 0 := by
  have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self M) c) c'
  rw [Matrix.mul_apply, Matrix.diagonal_apply] at h
  rw [← h, dotProduct]
  rfl

/-- Inner products with original columns give the Gram–Schmidt triangular factor. -/
theorem star_col_dotProduct_eq_gramSchmidtR {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜)
    (c j : Fin k) : star ((gramSchmidtQ M).col c) ⬝ᵥ M.col j = gramSchmidtR M c j := by
  rw [gramSchmidtR, Matrix.mul_apply, dotProduct]
  rfl

/-- The sweep of column `j` against the earlier Gram–Schmidt columns. -/
theorem mgsSweep_gramSchmidtQ {N k : ℕ} (M : Matrix (Fin N) (Fin k) 𝕜) (j : ℕ)
    (hj : j < k) :
    mgsSweep (fun c a => if h : c < k then gramSchmidtQ M a ⟨c, h⟩ else 0) (M.col ⟨j, hj⟩) j =
      gramSchmidtR M ⟨j, hj⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨j, hj⟩ := by
  set Vc : ℕ → Fin N → 𝕜 := fun c a => if h : c < k then gramSchmidtQ M a ⟨c, h⟩ else 0
  have hV : ∀ c (h : c < k), Vc c = (gramSchmidtQ M).col ⟨c, h⟩ := fun c h => by
    ext a; simp [Vc, h, Matrix.col]
  rw [mgsSweep_eq_sub_sum, gramSchmidtR_apply_self_smul_col]
  · congr 1
    set g : ℕ → Fin N → 𝕜 := fun i => if h : i < k then
      gramSchmidtR M ⟨i, h⟩ ⟨j, hj⟩ • (gramSchmidtQ M).col ⟨i, h⟩ else 0
    have hg : ∀ c : Fin k, gramSchmidtR M c ⟨j, hj⟩ • (gramSchmidtQ M).col c = g c := fun c => by
      simp [g, c.2]
    rw [Finset.sum_congr rfl fun c _ => hg c]
    change _ = ∑ c ∈ Finset.Iio (⟨j, hj⟩ : Fin k), g (Fin.valEmbedding c)
    rw [← Finset.sum_map (Finset.Iio ⟨j, hj⟩) Fin.valEmbedding g, Fin.map_valEmbedding_Iio,
      Nat.Iio_eq_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := (Finset.mem_range.mp hi).trans hj
    simp only [g, hik, dif_pos, hV i hik]
    rw [← star_col_dotProduct_eq_gramSchmidtR]
  · intro i hi i' hi'
    rw [hV i (hi.trans hj), hV i' ((hi'.trans hi).trans hj), dotProduct_gramSchmidtQ_col,
      if_neg (fun h => by simp [Fin.ext_iff] at h; omega)]

/-- The squared norm of a nonzero Gram–Schmidt residual has positive real part;
its scalar square root is exactly the nonnegative diagonal coefficient. -/
theorem sqrt_residual_norm {n : ℕ} (q : Fin n → 𝕜) (ρ : 𝕜) (hρ : 0 ≤ ρ)
    (hne : ρ ≠ 0) (hq : star q ⬝ᵥ q = 1) :
    0 < RCLike.re (star (ρ • q) ⬝ᵥ (ρ • q)) ∧
      RCLike.ofReal (Real.sqrt (RCLike.re (star (ρ • q) ⬝ᵥ (ρ • q)))) = ρ := by
  obtain ⟨r, hr, hrρ⟩ := RCLike.nonneg_iff_exists_ofReal.mp hρ
  have hd : star (ρ • q) ⬝ᵥ (ρ • q) = RCLike.ofReal (r ^ 2) := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, hq, ← hrρ]
    simp [pow_two]
  have hrne : r ≠ 0 := fun h => hne (by rw [← hrρ, h, RCLike.ofReal_zero])
  rw [hd, RCLike.ofReal_re]
  exact ⟨sq_pos_of_ne_zero hrne, by rw [Real.sqrt_sq hr, hrρ]⟩

/-- Guarded normalization returns the desired column even when its diagonal
coefficient vanishes. In the nonzero branch the divisor is explicitly nonzero. -/
theorem normalize_residual {n : ℕ} (q : Fin n → 𝕜) (ρ : 𝕜) (hρ : 0 ≤ ρ)
    (hz : ρ = 0 → q = 0) (hu : ρ ≠ 0 → star q ⬝ᵥ q = 1) :
    (if RCLike.re (star (ρ • q) ⬝ᵥ (ρ • q)) = 0 then ρ • q else
      fun i => (ρ • q) i /
        RCLike.ofReal (Real.sqrt (RCLike.re (star (ρ • q) ⬝ᵥ (ρ • q))))) = q := by
  by_cases he : ρ = 0
  · simp [he, hz he]
  · obtain ⟨hp, hs⟩ := sqrt_residual_norm q ρ hρ he (hu he)
    rw [if_neg (ne_of_gt hp), hs]
    funext i
    exact mul_div_cancel_left₀ (q i) he

end NLAlib.MGS
