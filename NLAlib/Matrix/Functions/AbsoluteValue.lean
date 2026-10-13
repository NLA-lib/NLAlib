/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Matrix.Norms.Schatten

/-!
# The matrix absolute value

The absolute value of a rectangular matrix `A` is `|A| = (Aᴴ A)^{1/2}`, spelled
`CFC.sqrt (Aᴴ * A)`; for a square matrix this is Mathlib's `CFC.abs A` by definition. Its
eigenvalues are the singular values of `A`, so the nuclear norm is `tr |A|` and the Schatten
norms are traces of powers of `Aᴴ A`.

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

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The eigenvalues of the absolute value are the singular values**:
`λ_k((Aᴴ A)^{1/2}) = σ_k(A)` for `k` below the number of columns. -/
theorem eigenvalue_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) : eigenvalue (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  sorry

/-- The absolute value has the same singular values as the matrix. -/
theorem singularValues_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  sorry

/-- **The nuclear norm is the trace of the absolute value**: `‖A‖_* = tr (Aᴴ A)^{1/2}`.
[HornJohnson2013, §7.4.1 context]. -/
theorem nuclearNorm_eq_re_trace_sqrt (A : Matrix m n 𝕜) :
    nuclearNorm A = RCLike.re (CFC.sqrt (Aᴴ * A)).trace := by
  sorry

/-- **Schatten norms as traces**: `‖A‖_p^p = tr (Aᴴ A)^{p/2}` for `0 < p < ∞`. -/
theorem schattenNorm_rpow_eq_re_trace_rpow (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) A ^ p = RCLike.re ((Aᴴ * A) ^ (p / 2)).trace := by
  sorry

/-- Even Schatten norms as traces of powers: `‖A‖_{2q}^{2q} = tr (Aᴴ A)^q` for `q ≥ 1`. -/
theorem schattenNorm_pow_eq_re_trace_pow (A : Matrix m n 𝕜) {q : ℕ} (hq : 0 < q) :
    schattenNorm (2 * q : ℕ) A ^ (2 * q) = RCLike.re ((Aᴴ * A) ^ q).trace := by
  sorry

/-- A Hermitian matrix is at most its absolute value. -/
theorem _root_.Matrix.IsHermitian.le_abs {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A ≤ CFC.abs A := by
  sorry

/-- A Hermitian matrix is at least minus its absolute value. -/
theorem _root_.Matrix.IsHermitian.neg_abs_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    -CFC.abs A ≤ A := by
  sorry

/-- The spectral norm of a Hermitian matrix bounds it in the Loewner order through the absolute
value: `|A| ≤ ‖A‖₂ • 1`. -/
theorem abs_le_specNorm_smul_one (A : Matrix n n 𝕜) :
    CFC.abs A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  sorry

end NLAlib
