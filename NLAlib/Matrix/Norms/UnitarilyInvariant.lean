/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Schatten
public import NLAlib.Matrix.Norms.SymmetricGauge

/-!
# Unitarily invariant norms

For a symmetric gauge function `Φ`, `Φ.matrixNorm A` is `Φ` applied to the singular values of
`A`. It is a norm on matrices of every shape, invariant under multiplication by matrices with
orthonormal columns; the Schatten and Ky Fan norms are the cases `lpGauge q` and `kyFanGauge k`.
Results stated for `Φ.matrixNorm` hold for all of them at once, across shapes: for example
`Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B`, where `A * B` and `B` have different shapes.

## Main definitions

* `NLAlib.singularValuesFinsupp`: the singular values as a finitely supported sequence.
* `NLAlib.SymmetricGauge.matrixNorm`: the unitarily invariant norm of a gauge.

## Main results

* `NLAlib.SymmetricGauge.matrixNorm_add_le`: the triangle inequality.
* `NLAlib.SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le`: Fan dominance.
* `NLAlib.SymmetricGauge.apply_singularValuesFinsupp_sub_le`: Mirsky's theorem.
* `NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_rank_le`: the truncated SVD is a best
  low-rank approximation in every unitarily invariant norm.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Singular values as a finitely supported sequence -/

/-- Only finitely many singular values are nonzero. -/
theorem finite_support_singularValues (A : Matrix m n 𝕜) :
    (Function.support (singularValues A)).Finite := by
  sorry

/-- The singular values of a matrix as a finitely supported sequence, the argument of a symmetric
gauge function. As a function it is `singularValues A`. It is a cast, used only as the
argument of a gauge, never in a hypothesis or conclusion of its own. -/
noncomputable def singularValuesFinsupp (A : Matrix m n 𝕜) : ℕ →₀ ℝ :=
  Finsupp.ofSupportFinite (singularValues A) (finite_support_singularValues A)

/-- `singularValuesFinsupp A` is `singularValues A` as a function. -/
@[simp]
theorem coe_singularValuesFinsupp (A : Matrix m n 𝕜) :
    ⇑(singularValuesFinsupp A) = singularValues A :=
  rfl

/-- `singularValuesFinsupp` agrees with Mathlib's singular values of the associated linear map
between Euclidean spaces. -/
theorem singularValuesFinsupp_eq_linearMap [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValuesFinsupp A = LinearMap.singularValues A.toEuclideanLin := by
  sorry

/-! ### The norm of a gauge -/

namespace SymmetricGauge

variable (Φ : SymmetricGauge)

/-- The **unitarily invariant norm** of a symmetric gauge function: the gauge of the singular
values. [HornJohnson2013, Theorem 7.4.7.2] (von Neumann).
Port of `NLAlib.SymmetricGauge.matrixValue`, there for one shape over `ℝ`. -/
noncomputable def matrixNorm (A : Matrix m n 𝕜) : ℝ :=
  Φ (singularValuesFinsupp A)

/-- The norm of a gauge is the gauge of the singular values. -/
theorem matrixNorm_def (A : Matrix m n 𝕜) : Φ.matrixNorm A = Φ (singularValuesFinsupp A) :=
  rfl

/-- Matrices with the same singular values have the same norm, whatever their shapes. -/
theorem matrixNorm_congr {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : singularValues A = singularValues B) : Φ.matrixNorm A = Φ.matrixNorm B := by
  sorry

/-- Unitarily invariant norms are nonnegative. -/
theorem matrixNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ Φ.matrixNorm A := by
  sorry

/-- The norm of the zero matrix vanishes. -/
@[simp]
theorem matrixNorm_zero : Φ.matrixNorm (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- Unitarily invariant norms are definite.
Port of `NLAlib.SymmetricGauge.eq_zero_of_matrixValue_eq_zero`. -/
@[simp]
theorem matrixNorm_eq_zero_iff {A : Matrix m n 𝕜} : Φ.matrixNorm A = 0 ↔ A = 0 := by
  sorry

/-- Unitarily invariant norms are absolutely homogeneous.
Port of `NLAlib.SymmetricGauge.matrixValue_smul`. -/
theorem matrixNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (c • A) = ‖c‖ * Φ.matrixNorm A := by
  sorry

/-- Unitarily invariant norms are even. -/
@[simp]
theorem matrixNorm_neg (A : Matrix m n 𝕜) : Φ.matrixNorm (-A) = Φ.matrixNorm A := by
  sorry

/-- Unitarily invariant norms are invariant under the conjugate transpose. -/
@[simp]
theorem matrixNorm_conjTranspose (A : Matrix m n 𝕜) : Φ.matrixNorm Aᴴ = Φ.matrixNorm A := by
  sorry

/-- Unitarily invariant norms are invariant under the transpose. -/
@[simp]
theorem matrixNorm_transpose (A : Matrix m n 𝕜) : Φ.matrixNorm Aᵀ = Φ.matrixNorm A := by
  sorry

/-- Unitarily invariant norms are invariant under relabelling rows and columns. -/
@[simp]
theorem matrixNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    Φ.matrixNorm (A.submatrix e₁ e₂) = Φ.matrixNorm A := by
  sorry

/-- **Invariance**: left multiplication by a matrix with orthonormal columns preserves the norm.
The factor need not be square. -/
theorem matrixNorm_mul_left_of_hasOrthonormalCols [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : Φ.matrixNorm (Q * A) = Φ.matrixNorm A := by
  sorry

/-- **Invariance**: right multiplication by the conjugate transpose of a matrix with orthonormal
columns preserves the norm. -/
theorem matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A * Qᴴ) = Φ.matrixNorm A := by
  sorry

/-! ### Monotonicity, Fan dominance and the triangle inequality -/

/-- A matrix with smaller singular values has a smaller norm. The shapes may differ. -/
theorem matrixNorm_le_of_singularValues_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ i, singularValues A i ≤ singularValues B i) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  sorry

/-- **Fan dominance.** If every Ky Fan norm of `A` is at most that of `B`, then every unitarily
invariant norm of `A` is at most that of `B`. The shapes may differ.
[HornJohnson2013, Theorem 7.4.8.4]; [Bhatia1997, Theorem IV.2.2].
Port of `NLAlib.forall_invariantNorm_le_iff_weaklyMajorized`, there for one shape over `ℝ`.
Result: fan-dominance -/
theorem matrixNorm_le_of_forall_kyFanNorm_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ k, kyFanNorm k A ≤ kyFanNorm k B) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  sorry

/-- **The triangle inequality** for unitarily invariant norms.
[HornJohnson2013, Theorem 7.4.7.2].
Port of `NLAlib.SymmetricGauge.matrixValue_add_le`, there over `ℝ`.
Result: unitarily-invariant-norm -/
theorem matrixNorm_add_le (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (A + B) ≤ Φ.matrixNorm A + Φ.matrixNorm B := by
  sorry

/-- The reverse triangle inequality for unitarily invariant norms. -/
theorem abs_matrixNorm_sub_matrixNorm_le (A B : Matrix m n 𝕜) :
    |Φ.matrixNorm A - Φ.matrixNorm B| ≤ Φ.matrixNorm (A - B) := by
  sorry

/-! ### Products -/

/-- `‖A B‖ ≤ ‖A‖₂ ‖B‖` for every unitarily invariant norm.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Proposition IV.2.4]. -/
theorem matrixNorm_mul_le_specNorm_mul (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B := by
  sorry

/-- `‖A B‖ ≤ ‖A‖ ‖B‖₂` for every unitarily invariant norm. -/
theorem matrixNorm_mul_le_mul_specNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ Φ.matrixNorm A * specNorm B := by
  sorry

/-- Multiplying by a star projection on the left does not increase a unitarily invariant norm. -/
theorem matrixNorm_mul_le_of_isStarProjection {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : Φ.matrixNorm (P * A) ≤ Φ.matrixNorm A := by
  sorry

/-- A submatrix has a smaller unitarily invariant norm. -/
theorem matrixNorm_submatrix_le (A : Matrix m n 𝕜) {f : l → m} {g : p → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Φ.matrixNorm (A.submatrix f g) ≤ Φ.matrixNorm A := by
  sorry

/-! ### Comparison with the spectral and nuclear norms -/

/-- Every unitarily invariant norm dominates a multiple of the spectral norm. -/
theorem apply_single_mul_specNorm_le (A : Matrix m n 𝕜) :
    Φ (Finsupp.single 0 1) * specNorm A ≤ Φ.matrixNorm A := by
  sorry

/-- Every unitarily invariant norm is dominated by a multiple of the nuclear norm. -/
theorem matrixNorm_le_apply_single_mul_nuclearNorm (A : Matrix m n 𝕜) :
    Φ.matrixNorm A ≤ Φ (Finsupp.single 0 1) * nuclearNorm A := by
  sorry

/-! ### Perturbation of singular values and low-rank approximation -/

/-- **Mirsky's theorem.** In every unitarily invariant norm, the sorted singular values are
`1`-Lipschitz: the gauge of the difference of the singular value sequences of `A` and `B` is at
most the norm of `A - B`.
[HornJohnson2013, Corollary 7.4.9.3]; [Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.invariantNorm_rectangularDiagonal_singularValues_add_sub_le`, there over `ℝ`.
Result: mirsky-inequality -/
theorem apply_singularValuesFinsupp_sub_le (A B : Matrix m n 𝕜) :
    Φ (singularValuesFinsupp A - singularValuesFinsupp B) ≤ Φ.matrixNorm (A - B) := by
  sorry

/-- **Eckart–Young–Mirsky.** The truncated SVD is a best approximation of rank at most `k` in
every unitarily invariant norm.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Exercise IV.3.5]. -/
theorem matrixNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : Φ.matrixNorm (A - truncatedSVD A k) ≤ Φ.matrixNorm (A - B) := by
  sorry

end SymmetricGauge

/-! ### Schatten and Ky Fan norms as gauge norms -/

/-- The norm of the `ℓ^q` gauge is the Schatten `q`-norm.
Port of `NLAlib.schattenInvariantNorm_apply`. -/
@[simp]
theorem lpGauge_matrixNorm {q : ℝ≥0∞} (hq : 1 ≤ q) (A : Matrix m n 𝕜) :
    (lpGauge q hq).matrixNorm A = schattenNorm q A := by
  sorry

/-- The norm of the `ℓ^∞` gauge is the spectral norm. -/
theorem lpGauge_top_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge ⊤ le_top).matrixNorm A = specNorm A := by
  sorry

/-- The norm of the `ℓ^2` gauge is the Frobenius norm. -/
theorem lpGauge_two_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 2 one_le_two).matrixNorm A = frobNorm A := by
  sorry

/-- The norm of the `ℓ^1` gauge is the nuclear norm. -/
theorem lpGauge_one_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 1 le_rfl).matrixNorm A = nuclearNorm A := by
  sorry

/-- The norm of the Ky Fan `k`-gauge is the Ky Fan `k`-norm.
Port of `NLAlib.kyFanInvariantNorm`. -/
@[simp]
theorem kyFanGauge_matrixNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    (kyFanGauge k hk).matrixNorm A = kyFanNorm k A := by
  sorry

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `Φ.matrixNorm A` is nonnegative. -/
@[positivity NLAlib.SymmetricGauge.matrixNorm _ _]
meta def evalSymmetricGaugeMatrixNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.SymmetricGauge.matrixNorm_nonneg #[e.appFn!.appArg!, e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
