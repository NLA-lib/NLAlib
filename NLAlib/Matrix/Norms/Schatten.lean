/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import NLAlib.Matrix.Norms.Nuclear

/-!
# Schatten norms

The Schatten `q`-norm `NLAlib.schattenNorm q A` of a matrix is the `ℓ^q` norm of its singular
values, for `q : ℝ≥0∞`. The cases `q = 1`, `q = 2` and `q = ⊤` are the nuclear, Frobenius and
spectral norms. It is defined as Mathlib's `PiLp` norm of the vector of the first
`min (card m) (card n)` singular values, so `q = ⊤` needs no separate definition, and the
degenerate `q = 0` gives the rank.

Statements that hold for every exponent take `q` alone; homogeneity, definiteness and the
comparisons need `q ≠ 0`; the triangle inequality needs `1 ≤ q`, as an explicit hypothesis.
Natural exponents have their own power-sum and trace forms, with `ℕ` powers.

## Main definitions

* `NLAlib.schattenNorm`: the Schatten `q`-norm.

## Main results

* `NLAlib.schattenNorm_one`, `NLAlib.schattenNorm_two`, `NLAlib.schattenNorm_top`: the nuclear,
  Frobenius and spectral norms.
* `NLAlib.schattenNorm_eq_sum_rpow`: the formula for finite positive `q`.
* `NLAlib.schattenNorm_two_mul_natCast_pow`: even Schatten norms as traces of powers.
* `NLAlib.schattenNorm_add_le`: the triangle inequality for `1 ≤ q`.
* `NLAlib.schattenNorm_anti`, `NLAlib.schattenNorm_le_rank_rpow_mul_schattenNorm`: comparison
  between exponents.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **Schatten `q`-norm**: the `ℓ^q` norm of the singular values, for `q : ℝ≥0∞`.
For `q = 1`, `2`, `⊤` it is the nuclear, Frobenius and spectral norm; it is a norm for `1 ≤ q`.
For `q = 0` it is the rank, following Mathlib's convention for `ℓ^0`.
[HornJohnson2013, §7.4.7]; [Bhatia1997, §IV.2]. Port of `NLAlib.schattenNorm`, with the arguments
in the other order. -/
noncomputable def schattenNorm (q : ℝ≥0∞) (A : Matrix m n 𝕜) : ℝ :=
  ‖(WithLp.toLp q fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i :
    PiLp q fun _ : Fin (min (Fintype.card m) (Fintype.card n)) => ℝ)‖

/-- Schatten norms are nonnegative. Port of `NLAlib.schattenNorm_nonneg`. -/
theorem schattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n 𝕜) : 0 ≤ schattenNorm q A := by
  sorry

/-! ### Special exponents -/

/-- The Schatten `∞`-norm is the spectral norm. Port of `NLAlib.schattenNorm_top`. -/
@[simp]
theorem schattenNorm_top (A : Matrix m n 𝕜) : schattenNorm ⊤ A = specNorm A := by
  sorry

/-- The Schatten `1`-norm is the nuclear norm. Port of `NLAlib.schattenNorm_one`. -/
@[simp]
theorem schattenNorm_one (A : Matrix m n 𝕜) : schattenNorm 1 A = nuclearNorm A := by
  sorry

/-- The Schatten `2`-norm is the Frobenius norm. Port of `NLAlib.schattenNorm_two`, there over
`ℝ`. -/
@[simp]
theorem schattenNorm_two (A : Matrix m n 𝕜) : schattenNorm 2 A = frobNorm A := by
  sorry

/-- The Schatten `0`-"norm" is the rank. -/
theorem schattenNorm_zero_eq_rank (A : Matrix m n 𝕜) : schattenNorm 0 A = A.rank := by
  sorry

/-- **The Schatten norm as a power sum.** For `0 < q < ∞` and any `N` at least the rank,
`‖A‖_q = (∑ i < N, σ_i ^ q) ^ (1 / q)`.
Port of `NLAlib.schattenNormReal_eq_sum_range_rpow_of_min_le` and
`NLAlib.schattenNormReal_eq_sum_rank_rpow`. -/
theorem schattenNorm_eq_sum_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm q A = (∑ i ∈ Finset.range N, singularValues A i ^ q.toReal) ^ q.toReal⁻¹ := by
  sorry

/-- The `q`-th power of the Schatten `q`-norm is the sum of the `q`-th powers of the singular
values. -/
theorem schattenNorm_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm q A ^ q.toReal = ∑ i ∈ Finset.range N, singularValues A i ^ q.toReal := by
  sorry

/-! ### Natural exponents -/

/-- For a natural exponent `p ≠ 0`, the `p`-th power of the Schatten `p`-norm is the sum of the
`p`-th powers of the singular values, with natural-number powers. -/
theorem schattenNorm_natCast_pow {p : ℕ} (hp : p ≠ 0) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm p A ^ p = ∑ i ∈ Finset.range N, singularValues A i ^ p := by
  sorry

/-- **Even Schatten norms as traces.** For a natural number `p ≠ 0`,
`‖A‖_{2p}^{2p} = re tr ((Aᴴ A)^p)`. This is the form used by the moment method.
[Bhatia1997, §IV.2]. -/
theorem schattenNorm_two_mul_natCast_pow [DecidableEq n] {p : ℕ} (hp : p ≠ 0)
    (A : Matrix m n 𝕜) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re ((Aᴴ * A) ^ p).trace := by
  sorry

/-- For a Hermitian matrix and a natural number `p ≠ 0`, `‖A‖_{2p}^{2p} = re tr (A^{2p})`. -/
theorem _root_.Matrix.IsHermitian.schattenNorm_two_mul_natCast_pow [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℕ} (hp : p ≠ 0) :
    schattenNorm (2 * p) A ^ (2 * p) = RCLike.re (A ^ (2 * p)).trace := by
  sorry

/-- **The moment bound for the spectral norm**: `‖A‖₂^{2p} ≤ re tr ((Aᴴ A)^p)`. -/
theorem specNorm_pow_le_re_trace_pow [DecidableEq n] (A : Matrix m n 𝕜) {p : ℕ} (hp : p ≠ 0) :
    specNorm A ^ (2 * p) ≤ RCLike.re ((Aᴴ * A) ^ p).trace := by
  sorry

/-! ### Norm properties -/

/-- Schatten norms of the zero matrix vanish. -/
@[simp]
theorem schattenNorm_zero (q : ℝ≥0∞) : schattenNorm q (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- Schatten norms are definite. Port of `NLAlib.schattenNorm_eq_zero_iff`. -/
theorem schattenNorm_eq_zero_iff (q : ℝ≥0∞) {A : Matrix m n 𝕜} : schattenNorm q A = 0 ↔ A = 0 := by
  sorry

/-- Schatten norms are absolutely homogeneous, for `q ≠ 0`.
Port of `NLAlib.schattenNorm_smul`. -/
theorem schattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : 𝕜) (A : Matrix m n 𝕜) :
    schattenNorm q (c • A) = ‖c‖ * schattenNorm q A := by
  sorry

/-- Schatten norms are even. -/
@[simp]
theorem schattenNorm_neg (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (-A) = schattenNorm q A := by
  sorry

/-- Schatten norms are invariant under the conjugate transpose. -/
@[simp]
theorem schattenNorm_conjTranspose (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q Aᴴ = schattenNorm q A := by
  sorry

/-- Schatten norms are invariant under the transpose. Port of `NLAlib.schattenNorm_transpose`. -/
@[simp]
theorem schattenNorm_transpose (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q Aᵀ = schattenNorm q A := by
  sorry

/-- Schatten norms are invariant under relabelling rows and columns.
Port of `NLAlib.schattenNormReal_reindex`. -/
@[simp]
theorem schattenNorm_submatrix_equiv (q : ℝ≥0∞) (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    schattenNorm q (A.submatrix e₁ e₂) = schattenNorm q A := by
  sorry

/-- Schatten norms are invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.schattenNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.schattenNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (Q * A) = schattenNorm q A := by
  sorry

/-- Schatten norms are invariant under right multiplication by the conjugate transpose of a
matrix with orthonormal columns. Port of `NLAlib.schattenNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.schattenNorm_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (A * Qᴴ) = schattenNorm q A := by
  sorry

/-- **The triangle inequality for Schatten norms**, `1 ≤ q`.
[Bhatia1997, §IV.2]. Port of `NLAlib.schattenNorm_add_le`, there over `ℝ`.
Result: schatten-norm -/
theorem schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n 𝕜) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  sorry

/-- The reverse triangle inequality for Schatten norms, `1 ≤ q`. -/
theorem abs_schattenNorm_sub_schattenNorm_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n 𝕜) :
    |schattenNorm q A - schattenNorm q B| ≤ schattenNorm q (A - B) := by
  sorry

/-! ### Comparison between exponents -/

/-- Schatten norms decrease in the exponent.
Port of `NLAlib.schattenNorm_le_of_le`, there over `ℝ` for `1 ≤ q`. -/
theorem schattenNorm_anti {q r : ℝ≥0∞} (hq : q ≠ 0) (h : q ≤ r) (A : Matrix m n 𝕜) :
    schattenNorm r A ≤ schattenNorm q A := by
  sorry

/-- The spectral norm is at most every Schatten norm with `q ≠ 0`.
Port of `NLAlib.specNorm_le_schattenNormReal`. -/
theorem specNorm_le_schattenNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n 𝕜) :
    specNorm A ≤ schattenNorm q A := by
  sorry

/-- Comparison in the other direction, with the rank: for `q ≤ r`,
`‖A‖_q ≤ rank(A) ^ (1/q - 1/r) ‖A‖_r`.
Port of `NLAlib.schattenNorm_le_rank_rpow_mul`, there over `ℝ` for `1 ≤ q`. -/
theorem schattenNorm_le_rank_rpow_mul_schattenNorm {q r : ℝ≥0∞} (hq : q ≠ 0) (h : q ≤ r)
    (A : Matrix m n 𝕜) :
    schattenNorm q A ≤ (A.rank : ℝ) ^ (q.toReal⁻¹ - r.toReal⁻¹) * schattenNorm r A := by
  sorry

/-- `‖A‖_q ≤ rank(A) ^ (1/q) ‖A‖₂`.
Port of `NLAlib.schattenNormReal_le_rank_rpow_mul_specNorm`. -/
theorem schattenNorm_le_rank_rpow_mul_specNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n 𝕜) :
    schattenNorm q A ≤ (A.rank : ℝ) ^ q.toReal⁻¹ * specNorm A := by
  sorry

/-! ### Products with a spectral-norm factor -/

/-- `‖A B‖_q ≤ ‖A‖₂ ‖B‖_q`.
Port of `NLAlib.schattenNormReal_mul_le_specNorm_mul`, there over `ℝ`. -/
theorem schattenNorm_mul_le_specNorm_mul {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m p 𝕜)
    (B : Matrix p n 𝕜) : schattenNorm q (A * B) ≤ specNorm A * schattenNorm q B := by
  sorry

/-- `‖A B‖_q ≤ ‖A‖_q ‖B‖₂`.
Port of `NLAlib.schattenNormReal_mul_le_mul_specNorm`, there over `ℝ`. -/
theorem schattenNorm_mul_le_mul_specNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m p 𝕜)
    (B : Matrix p n 𝕜) : schattenNorm q (A * B) ≤ schattenNorm q A * specNorm B := by
  sorry

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.schattenNorm q A` is nonnegative. -/
@[positivity NLAlib.schattenNorm _ _]
meta def evalSchattenNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.schattenNorm_nonneg #[e.appFn!.appArg!, e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
