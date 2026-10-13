/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Functions.Complexification
public import NLAlib.Matrix.Inequalities.Order

/-!
# Operator monotone and operator convex functions

The Löwner–Heinz theorem: `t ↦ t ^ r` for `0 ≤ r ≤ 1` and the logarithm are operator monotone;
the powers are operator concave. Operator convexity of a function `f` on an interval is the
predicate `NLAlib.OperatorConvexOn s f`, and operator convex functions satisfy the operator Jensen
inequality `f(Kᴴ A K) ≤ Kᴴ f(A) K` for an isometry `K` (Hansen–Pedersen).

The results are stated over `𝕜`; they are proved over `ℂ`, where Mathlib has the corresponding
C⋆-algebra facts (`CFC.rpow_le_rpow`, `CFC.sqrt_le_sqrt`, `CFC.log_le_log`, in the scope
`Matrix.Norms.L2Operator`), and transferred through `NLAlib.complexify`.

## Main definitions

* `NLAlib.OperatorConvexOn`: operator convexity on a set, for Hermitian matrices of every size.

## Main results

* `Matrix.PosSemidef.rpow_le_rpow`, `Matrix.PosSemidef.sqrt_le_sqrt`,
  `Matrix.PosDef.cfc_log_le_cfc_log`: Löwner–Heinz.
* `NLAlib.concaveOn_rpow`: operator concavity of the powers.
* `NLAlib.operatorConvexOn_neg_log`, `NLAlib.operatorConvexOn_inv`, `NLAlib.operatorConvexOn_sq`.
* `NLAlib.OperatorConvexOn.cfc_conjTranspose_mul_mul_le`,
  `NLAlib.OperatorConvexOn.cfc_sum_conjTranspose_mul_mul_le`: the operator Jensen inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Löwner–Heinz -/

/-- **The Löwner–Heinz theorem.** For `0 ≤ r ≤ 1`, `t ↦ t ^ r` is operator monotone on positive
semidefinite matrices. [Bhatia1997, Theorem V.1.9].
Port of `NLAlib.cfc_rpow_le_cfc_rpow`, there over `ℝ`.
Result: loewner-heinz -/
theorem _root_.Matrix.PosSemidef.rpow_le_rpow {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : A ^ r ≤ B ^ r := by
  sorry

/-- **The square root is operator monotone.** [Bhatia1997, Proposition V.1.8].
Port of `NLAlib.sqrt_le_sqrt_of_posSemidef_le`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.sqrt_le_sqrt {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  sorry

/-- **The logarithm is operator monotone** on positive definite matrices.
[Bhatia1997, Exercise V.1.10]. Port of `NLAlib.cfc_log_le_cfc_log`, there over `ℝ`.
Result: loewner-heinz -/
theorem _root_.Matrix.PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (h : A ≤ B) : cfc Real.log A ≤ cfc Real.log B := by
  sorry

/-- A matrix above a positive definite matrix is positive definite.
Port of `NLAlib.posDef_of_posDef_le`. -/
theorem _root_.Matrix.PosDef.posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B.PosDef := by
  sorry

/-- **The powers `t ^ r`, `0 ≤ r ≤ 1`, are operator concave** on positive semidefinite matrices.
[Bhatia1997, Theorem V.2.5]. Port of `NLAlib.concaveOn_cfc_rpow`, there over `ℝ`. -/
theorem concaveOn_rpow {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosSemidef} fun A => A ^ r := by
  sorry

/-- The description of `B ≤ A` through a contraction: for positive definite `A`,
`B ≤ A` exactly when `A^{-1/2} B A^{-1/2} ≤ 1`.
Port of `NLAlib.le_iff_exists_sqrt_congruence_contraction`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.le_iff_inv_sqrt_mul_mul_inv_sqrt_le_one {A B : Matrix n n 𝕜}
    (hA : A.PosDef) : B ≤ A ↔ (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹ ≤ 1 := by
  sorry

/-! ### Operator convexity -/

/-- A function is **operator convex** on a convex set `s` of reals if
`f(a A + b B) ≤ a f(A) + b f(B)` for all weights `a + b = 1` and all Hermitian matrices `A`, `B`
of every size with spectrum in `s`. It is stated for complex matrices indexed by `Fin d`; the
consequences below hold over any `RCLike` field and any index type.
[Bhatia1997, §V.1]; [Tropp2015, Definition 8.4.1]. Port of `NLAlib.OperatorConvexOn`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      cfc f (a • A + b • B) ≤ a • cfc f A + b • cfc f B

/-- An operator convex function is convex. -/
theorem OperatorConvexOn.convexOn {s : Set ℝ} {f : ℝ → ℝ} (hf : OperatorConvexOn s f) :
    ConvexOn ℝ s f := by
  sorry

/-- **Operator convexity for matrices over any field and index type.** -/
theorem OperatorConvexOn.cfc_smul_add_smul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAs : spectrum ℝ A ⊆ s) (hBs : spectrum ℝ B ⊆ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : cfc f (a • A + b • B) ≤ a • cfc f A + b • cfc f B := by
  sorry

/-- `t ↦ t²` is operator convex on `ℝ`. [Bhatia1997, Example V.1.3]. -/
theorem operatorConvexOn_sq : OperatorConvexOn Set.univ fun x : ℝ => x ^ 2 := by
  sorry

/-- `t ↦ t⁻¹` is operator convex on `(0, ∞)`. [Bhatia1997, §V.1]. -/
theorem operatorConvexOn_inv : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => x⁻¹ := by
  sorry

/-- **`t ↦ -log t` is operator convex on `(0, ∞)`.**
[Bhatia1997, §V.2]; [Tropp2015, §8.4].
Port of `NLAlib.operatorConvexOn_neg_log`. -/
theorem operatorConvexOn_neg_log : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => -Real.log x := by
  sorry

/-- `t ↦ t log t` is operator convex on `(0, ∞)`. [Bhatia1997, §V.2]. -/
theorem operatorConvexOn_mul_log : OperatorConvexOn (Set.Ioi 0) fun x : ℝ => x * Real.log x := by
  sorry

/-! ### The operator Jensen inequality -/

/-- **The operator Jensen inequality for an isometry** (Hansen–Pedersen). If `f` is operator
convex on `s`, `A` is Hermitian with spectrum in `s`, and `K` has orthonormal columns, then
`f(Kᴴ A K) ≤ Kᴴ f(A) K`.
[Tropp2015, Theorem 8.5.2]; [Bhatia1997, Theorem V.2.3].
Port of `NLAlib.OperatorConvexOn.cfc_conjTranspose_mul_mul_le`, there over `ℂ`.
Result: operator-jensen -/
theorem OperatorConvexOn.cfc_conjTranspose_mul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {A : Matrix m m 𝕜} (hA : A.IsHermitian)
    (hAs : spectrum ℝ A ⊆ s) {K : Matrix m n 𝕜} (hK : HasOrthonormalCols K) :
    cfc f (Kᴴ * A * K) ≤ Kᴴ * cfc f A * K := by
  sorry

/-- **The operator Jensen inequality.** If `f` is operator convex on `s`, the `A i` are Hermitian
with spectrum in `s`, and `∑ i, (K i)ᴴ * K i = 1`, then
`f(∑ Kᵢᴴ Aᵢ Kᵢ) ≤ ∑ Kᵢᴴ f(Aᵢ) Kᵢ`.
[Tropp2015, Theorem 8.5.2]. Port of `NLAlib.operator_jensen`, there for two terms over `ℂ`.
Result: operator-jensen -/
theorem OperatorConvexOn.cfc_sum_conjTranspose_mul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorConvexOn s f) {ι : Type*} [Fintype ι] {A : ι → Matrix m m 𝕜}
    (hA : ∀ i, (A i).IsHermitian) (hAs : ∀ i, spectrum ℝ (A i) ⊆ s) {K : ι → Matrix m n 𝕜}
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    cfc f (∑ i, (K i)ᴴ * A i * K i) ≤ ∑ i, (K i)ᴴ * cfc f (A i) * K i := by
  sorry

end NLAlib
