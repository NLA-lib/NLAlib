/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Matrix.Norms.SchattenPowers

/-!
# The matrix absolute value

The absolute value of a rectangular matrix `A` is `|A| = (Aᴴ A)^{1/2}`, spelled
`CFC.sqrt (Aᴴ * A)`; for a square matrix this is Mathlib's `CFC.abs A` by definition. Its
eigenvalues are the singular values of `A`, so the nuclear norm is `tr |A|` and the Schatten
norms are traces of powers of `Aᴴ A`. For an even natural exponent the trace form, with natural
powers, is `NLAlib.schattenNorm_two_mul_natCast_pow`.

For a Hermitian matrix, `CFC.abs A = cfc |·| A` is Mathlib's `CFC.abs_eq_cfc_norm`, and the
positive and negative parts `A⁺`, `A⁻` are Mathlib's, with `CFC.le_posPart`,
`CFC.posPart_sub_negPart` and `CFC.abs_eq_posPart_add_negPart`.

## Main results

* `NLAlib.eigenvalue_sqrt_conjTranspose_mul_self`: the eigenvalues of `|A|`.
* `NLAlib.nuclearNorm_eq_re_trace_sqrt`: `‖A‖_* = tr |A|`.
* `NLAlib.schattenNorm_rpow_eq_re_trace_rpow`: `‖A‖_p^p = tr (Aᴴ A)^{p/2}`.
* `Matrix.IsHermitian.le_abs`, `Matrix.IsHermitian.neg_abs_le`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

open scoped Classical in
/-- **The eigenvalues of the absolute value are the singular values**:
`λ_k((Aᴴ A)^{1/2}) = σ_k(A)` for `k` below the number of columns. -/
theorem eigenvalue_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) : eigenvalue (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A) hG.nonneg, cfcₙ_eq_cfc,
    hG.isHermitian.eigenvalue_cfc_of_monotoneOn (s := Set.univ)
      (fun x _ y _ h => Real.sqrt_le_sqrt h) (Set.subset_univ _) hk,
    ← sq_singularValues, Real.sqrt_sq (singularValues_nonneg A k)]

open scoped Classical in
/-- The absolute value has the same singular values as the matrix. -/
theorem singularValues_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hH : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  refine congrFun (singularValues_eq_of_conjTranspose_mul_self_eq ?_) k
  rw [hH.eq, CFC.sqrt_mul_sqrt_self (Aᴴ * A) hG.nonneg]

open scoped Classical in
/-- **The nuclear norm is the trace of the absolute value**: `‖A‖_* = tr (Aᴴ A)^{1/2}`.
[HornJohnson2013, §7.4.1 context]. -/
theorem nuclearNorm_eq_re_trace_sqrt (A : Matrix m n 𝕜) :
    nuclearNorm A = RCLike.re (CFC.sqrt (Aᴴ * A)).trace := by
  have hS : (CFC.sqrt (Aᴴ * A)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  rw [← hS.nuclearNorm_eq_re_trace, nuclearNorm_eq_sum_range A A.rank_le_card_width,
    nuclearNorm_eq_sum_range _ (Matrix.rank_le_card_width _)]
  exact Finset.sum_congr rfl fun i _ => (singularValues_sqrt_conjTranspose_mul_self A i).symm

/-- **Schatten norms as traces**: `‖A‖_p^p = tr (Aᴴ A)^{p/2}` for `0 < p < ∞`. -/
theorem schattenNorm_rpow_eq_re_trace_rpow [DecidableEq n] (A : Matrix m n 𝕜) {p : ℝ}
    (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) A ^ p = RCLike.re ((Aᴴ * A) ^ (p / 2)).trace := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have h := schattenNorm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top A
    A.rank_le_card_width
  rw [ENNReal.toReal_ofReal hp.le] at h
  rw [h, CFC.rpow_eq_cfc_real hG.nonneg, hG.isHermitian.re_trace_cfc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sq_singularValues, ← Real.rpow_natCast, ← Real.rpow_mul (singularValues_nonneg A i)]
  congr 1
  push_cast
  ring

open scoped Classical in
/-- A Hermitian matrix is at most its absolute value. -/
theorem _root_.Matrix.IsHermitian.le_abs {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A ≤ CFC.abs A := by
  have hsa : IsSelfAdjoint A := hA
  rw [← sub_nonneg, CFC.abs_sub_self A hsa]
  exact nsmul_nonneg (CFC.negPart_nonneg A) 2

open scoped Classical in
/-- A Hermitian matrix is at least minus its absolute value. -/
theorem _root_.Matrix.IsHermitian.neg_abs_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    -CFC.abs A ≤ A := by
  have hsa : IsSelfAdjoint A := hA
  rw [neg_le_iff_add_nonneg', CFC.abs_add_self A hsa]
  exact nsmul_nonneg (CFC.posPart_nonneg A) 2

/-- The spectral norm bounds the absolute value in the Loewner order: `|A| ≤ ‖A‖₂ • 1`, for
every square matrix `A`. -/
theorem abs_le_specNorm_smul_one [DecidableEq n] (A : Matrix n n 𝕜) :
    CFC.abs A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  rcases isEmpty_or_nonempty n with h | h
  · exact le_of_eq (Subsingleton.elim _ _)
  · have hH : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
    have h1 := hH.le_eigenvalue_zero_smul_one
    rwa [eigenvalue_sqrt_conjTranspose_mul_self A Fintype.card_pos,
      singularValues_zero_eq_specNorm] at h1

end NLAlib
