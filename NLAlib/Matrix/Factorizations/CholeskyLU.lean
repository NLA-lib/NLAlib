/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Factorizations.LU

/-!
# Converting canonical LU factors to Cholesky

Scaling each column of the unit lower LU factor of a positive definite matrix by the square
root of its positive upper-factor pivot gives the canonical Cholesky factor.

## Main results

* `Matrix.PosDef.luLower_mul_sqrt_luUpper_apply`: the entrywise column-scaling identity.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}

/-- Scaling a canonical unit lower LU column by its positive pivot's square root gives the
canonical Cholesky column. [GolubVanLoan2013, §4.2]. -/
theorem _root_.Matrix.PosDef.luLower_mul_sqrt_luUpper_apply (hA : A.PosDef) (i j : Fin N) :
    luLower A i j * ((Real.sqrt (RCLike.re (luUpper A j j)) : ℝ) : 𝕜) =
      choleskyLower A i j := by
  rw [luUpper_apply_self]
  have hp := hA.gaussState_apply_self_pos j
  have hre := (hA.isHermitian.gaussState j).coe_re_apply_self j
  have hr : 0 < RCLike.re (gaussState A j j j) := by
    rw [← hre, RCLike.ofReal_pos] at hp
    exact hp
  have hs : (((Real.sqrt (RCLike.re (gaussState A j j j))) : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hsq : (((Real.sqrt (RCLike.re (gaussState A j j j))) : ℝ) : 𝕜) ^ 2 =
      gaussState A j j j := by
    rw [← RCLike.ofReal_pow, Real.sq_sqrt hr.le, hre]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [luLower, choleskyLower, hij.not_ge, hij.not_gt, hij.ne]
  · rw [hA.isHermitian.choleskyLower_apply_self]
    simp [luLower]
  · simp only [luLower, Matrix.of_apply, if_pos hij, choleskyLower, if_pos hij.le]
    nth_rewrite 1 [← hsq]
    field_simp

end NLAlib
