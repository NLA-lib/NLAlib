/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.OperatorMonotone

/-!
# The matrix perspective

The perspective of `f : ℝ → ℝ` at a pair of positive definite matrices is
`A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}`. The perspective of an operator convex function is
jointly operator convex (Effros; Ebadian, Nikoufar and Eshaghi Gordji), which is the source of
the joint convexity of the matrix relative entropy.

## Main definitions

* `NLAlib.matrixPerspective`: the matrix perspective of a function.

## Main results

* `NLAlib.matrixPerspective_smul_one`: for multiples of the identity it is the scalar
  perspective.
* `NLAlib.OperatorConvexOn.matrixPerspective_smul_add_smul_le`: joint operator convexity.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **matrix perspective** `A^{1/2} f(A^{-1/2} H A^{-1/2}) A^{1/2}` of a function `f` at a
positive definite `A` and a Hermitian `H`; the square root and the inverse give junk values when
`A` is not positive definite. [Tropp2015, Definition 8.6.1]. Port of `NLAlib.matrixPerspective`. -/
noncomputable def matrixPerspective (f : ℝ → ℝ) (A H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  CFC.sqrt A * cfc f ((CFC.sqrt A)⁻¹ * H * (CFC.sqrt A)⁻¹) * CFC.sqrt A

/-- The matrix perspective is Hermitian. -/
theorem isHermitian_matrixPerspective (f : ℝ → ℝ) (A H : Matrix n n 𝕜) :
    (matrixPerspective f A H).IsHermitian := by
  sorry

/-- The perspective at the identity is the function itself. -/
theorem matrixPerspective_one (f : ℝ → ℝ) (H : Matrix n n 𝕜) :
    matrixPerspective f 1 H = cfc f H := by
  sorry

/-- The perspective of two multiples of the identity is the scalar perspective `a f(h / a)`. -/
theorem matrixPerspective_smul_one (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (h : ℝ) :
    matrixPerspective f (a • (1 : Matrix n n 𝕜)) (h • (1 : Matrix n n 𝕜)) =
      (a * f (h / a)) • (1 : Matrix n n 𝕜) := by
  sorry

/-- The perspective is positively homogeneous: `ψ_f(t A, t H) = t ψ_f(A, H)` for `t > 0`. -/
theorem matrixPerspective_smul_smul (f : ℝ → ℝ) (A H : Matrix n n 𝕜) {t : ℝ} (ht : 0 < t) :
    matrixPerspective f (t • A) (t • H) = t • matrixPerspective f A H := by
  sorry

/-- **The perspective of an operator convex function is jointly operator convex**: for positive
definite `A₁`, `A₂`, `H₁`, `H₂` and weights `a + b = 1`,
`ψ_f(a A₁ + b A₂, a H₁ + b H₂) ≤ a ψ_f(A₁, H₁) + b ψ_f(A₂, H₂)`.
[Tropp2015, Theorem 8.6.2].
Port of `NLAlib.matrixPerspective_jointly_operatorConvex`, there over `ℂ` on `Fin d`.
Result: perspective-convexity -/
theorem OperatorConvexOn.matrixPerspective_smul_add_smul_le {f : ℝ → ℝ}
    (hf : OperatorConvexOn (Set.Ioi 0) f) {A₁ A₂ H₁ H₂ : Matrix n n 𝕜} (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef) (hH₁ : H₁.PosDef) (hH₂ : H₂.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    matrixPerspective f (a • A₁ + b • A₂) (a • H₁ + b • H₂) ≤
      a • matrixPerspective f A₁ H₁ + b • matrixPerspective f A₂ H₂ := by
  sorry

end NLAlib
