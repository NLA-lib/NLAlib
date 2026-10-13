/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.ENNReal.Holder
public import NLAlib.Matrix.Majorization.Horn
public import NLAlib.Matrix.Norms.Schatten

/-!
# Hölder's inequality and duality for Schatten norms

For exponents with `1/q + 1/r = 1/s`, `‖A B‖_s ≤ ‖A‖_q ‖B‖_r`; for conjugate exponents,
`|tr (Aᴴ B)| ≤ ‖A‖_q ‖B‖_r`, with equality attained, so the Schatten `q`-norm is the dual of the
Schatten `r`-norm under the Frobenius inner product. Exponent relations are Mathlib's
`ENNReal.HolderTriple` and `ENNReal.HolderConjugate`.

## Main results

* `NLAlib.schattenNorm_mul_le`: Hölder's inequality for products.
* `NLAlib.norm_trace_conjTranspose_mul_le_schattenNorm_mul`: Hölder's inequality for the trace.
* `NLAlib.isGreatest_frobInner_schattenNorm`: duality.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- **Hölder's inequality for Schatten norms.** If `1/q + 1/r = 1/s` with `q, r ≠ 0`, then
`‖A B‖_s ≤ ‖A‖_q ‖B‖_r`.
[HornJohnson1991, Theorem 3.3.14]; [Bhatia1997, Exercise IV.2.7].
Port of `NLAlib.schattenNorm_mul_le_mul`, there over `ℝ` for exponents at least one.
Result: schatten-holder -/
theorem schattenNorm_mul_le {q r s : ℝ≥0∞} [ENNReal.HolderTriple q r s] (hq : q ≠ 0)
    (hr : r ≠ 0) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    schattenNorm s (A * B) ≤ schattenNorm q A * schattenNorm r B := by
  sorry

/-- **Hölder's inequality for the trace.** For conjugate exponents,
`|tr (Aᴴ B)| ≤ ‖A‖_q ‖B‖_r`.
[Bhatia1997, Corollary IV.2.6].
Port of `NLAlib.abs_frobInner_le_schattenNorm_mul`, there over `ℝ` for the real part.
Result: schatten-holder -/
theorem norm_trace_conjTranspose_mul_le_schattenNorm_mul {q r : ℝ≥0∞}
    [ENNReal.HolderConjugate q r] (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm q A * schattenNorm r B := by
  sorry

/-- Hölder's inequality for the trace of a product `A * B` with `B` of the transposed shape. -/
theorem norm_trace_mul_le_schattenNorm_mul {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    ‖(A * B).trace‖ ≤ schattenNorm q A * schattenNorm r B := by
  sorry

/-- Hölder's inequality for the Frobenius inner product: `|⟨A, B⟩_F| ≤ ‖A‖_q ‖B‖_r`.
Port of `NLAlib.abs_frobInner_le_schattenNorm_mul`, there over `ℝ`. -/
theorem abs_frobInner_le_schattenNorm_mul {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A B : Matrix m n 𝕜) : |frobInner A B| ≤ schattenNorm q A * schattenNorm r B := by
  sorry

/-- Equality in Hölder's inequality is attained: there is `B` in the unit ball of the Schatten
`r`-norm with `⟨A, B⟩_F = ‖A‖_q`.
Port of `NLAlib.exists_schattenNorm_le_one_frobInner_eq`, there over `ℝ`. -/
theorem exists_schattenNorm_le_one_frobInner_eq {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜, schattenNorm r B ≤ 1 ∧ frobInner A B = schattenNorm q A := by
  sorry

/-- **Duality of Schatten norms.** For conjugate exponents, the Schatten `q`-norm is the largest
Frobenius inner product with a matrix in the unit ball of the Schatten `r`-norm.
[Bhatia1997, §IV.2]. Port of `NLAlib.isGreatest_schattenNorm_frobInner`, there over `ℝ`.
Result: schatten-duality -/
theorem isGreatest_frobInner_schattenNorm {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | schattenNorm r B ≤ 1})
      (schattenNorm q A) := by
  sorry

end NLAlib
