/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.BasisExtension

/-!
# Exact column-wise two-pass classical Gram–Schmidt extends a basis

Column-wise classical Gram–Schmidt with two passes reduces column $c$ of a block $\mathbf{W}$
against the stored basis $\mathbf{Q}$ and the new columns $\mathbf{q}'_{c'}$, $c' < c$, twice, and
normalizes the result, writing a zero column when the result is zero. The recursion over the
columns is written as matrix identities: the coefficients against the earlier new columns are the
strictly upper triangular part of $\mathbf{Q}'^{\mathsf{H}}\mathbf{W}$. The result is an exact
extension `NLAlib.IsBasisExtension` of $\mathbf{Q}$ by $\mathbf{W}$ for an arbitrary basis
$\mathbf{Q}$; only the orthonormality clause of the contract uses the orthonormality of
$\mathbf{Q}$ on its support. Design: `docs/design/LowRank-BlockLanczos.md` §3.5.

## Main definitions

* `NLAlib.strictUpper`: the strictly upper triangular part of a square matrix.
* `NLAlib.colsBefore`: the columns before a given one, the others replaced by zero.

## Main results

* `NLAlib.blockTriangular_strictUpper`, `NLAlib.mul_strictUpper_col`: the strictly upper
  triangular part is upper triangular, and its product with a block uses the earlier columns.
* `NLAlib.isBasisExtension_of_two_passes`: exact column-wise classical Gram–Schmidt with two
  passes and the zero guard is an exact extension of the basis.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} {b : ℕ}

/-- The strictly upper triangular part of a square matrix $\mathbf{A}$: the entry $(i, j)$ is
$a_{ij}$ for $i < j$ and $0$ otherwise. -/
def strictUpper (A : Matrix (Fin b) (Fin b) 𝕜) : Matrix (Fin b) (Fin b) 𝕜 :=
  Matrix.of fun i j => if i < j then A i j else 0

/-- The columns of $\mathbf{Q}'$ before column $c$: column $c'$ is $\mathbf{q}'_{c'}$ for
$c' < c$ and zero otherwise. The zero columns change neither the column space nor the Gram defect
on the support. -/
def colsBefore (Q' : Matrix m (Fin b) 𝕜) (c : Fin b) : Matrix m (Fin b) 𝕜 :=
  Matrix.of fun i c' => if c' < c then Q' i c' else 0

/-- The strictly upper triangular part of a square matrix is upper triangular. -/
theorem blockTriangular_strictUpper (A : Matrix (Fin b) (Fin b) 𝕜) :
    (strictUpper A).BlockTriangular id := by
  intro i j hij
  have hji : ¬ i < j := not_lt.2 (le_of_lt hij)
  simp [strictUpper, hji]

/-- Column $c$ of the product of a block $\mathbf{Q}'$ with the strictly upper triangular part
$\mathbf{S}$ of a square matrix $\mathbf{A}$ combines the columns of $\mathbf{Q}'$ before $c$
only: $(\mathbf{Q}'\mathbf{S})_c = \mathbf{Q}'_{<c}\,\mathbf{a}_c$, where $\mathbf{Q}'_{<c}$ is
$\mathbf{Q}'$ with the columns $c' \ge c$ replaced by zero and $\mathbf{a}_c$ is column $c$ of
$\mathbf{A}$. -/
theorem mul_strictUpper_col (Q' : Matrix m (Fin b) 𝕜) (A : Matrix (Fin b) (Fin b) 𝕜)
    (c : Fin b) : (Q' * strictUpper A).col c = colsBefore Q' c *ᵥ A.col c := by
  funext i
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, strictUpper,
    colsBefore, Matrix.of_apply]
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h : c' < c <;> simp [h]

/-- **Exact column-wise classical Gram–Schmidt with two passes extends a basis.** Let
$\mathbf{Q}$ be an arbitrary basis, $\mathbf{W}$ a block of $b$ columns, and write
$\operatorname{su}(\mathbf{A})$ for the strictly upper triangular part of $\mathbf{A}$. Let
$\mathbf{H}_1 = \mathbf{Q}^{\mathsf{H}}\mathbf{W}$,
$\mathbf{R}_1 = \operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W})$,
$\mathbf{W}_1 = \mathbf{W} - \mathbf{Q}\mathbf{H}_1 - \mathbf{Q}'\mathbf{R}_1$ be the first pass,
$\mathbf{H}_2 = \mathbf{Q}^{\mathsf{H}}\mathbf{W}_1$,
$\mathbf{R}_2 = \operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W}_1)$,
$\mathbf{W}_2 = \mathbf{W}_1 - \mathbf{Q}\mathbf{H}_2 - \mathbf{Q}'\mathbf{R}_2$ the second, and
let column $c$ of $\mathbf{Q}'$ be $\|\mathbf{w}\|^{-1}\mathbf{w}$ with $\mathbf{w}$ column $c$ of
$\mathbf{W}_2$ (the zero column when $\mathbf{w} = \mathbf{0}$). Then $\mathbf{Q}'$ with the
coefficients $\mathbf{H}_1 + \mathbf{H}_2$ and $\mathbf{R}_1 + \mathbf{R}_2 + \mathbf{D}$,
$\mathbf{D}$ the diagonal matrix of the norms of the columns of $\mathbf{W}_2$, is an exact
extension of $\mathbf{Q}$ by $\mathbf{W}$. No hypothesis on $\mathbf{Q}$: the orthonormality of
$\mathbf{Q}$ on its support is used only by the clause that preserves it. No printed source;
`docs/design/LowRank-BlockLanczos.md` §3.5. -/
theorem isBasisExtension_of_two_passes {n k : ℕ} {Q : Matrix (Fin n) (Fin k) 𝕜}
    {W Q' W₁ W₂ : Matrix (Fin n) (Fin b) 𝕜} {H₁ H₂ : Matrix (Fin k) (Fin b) 𝕜}
    {R₁ R₂ : Matrix (Fin b) (Fin b) 𝕜}
    (hH₁ : H₁ = Qᴴ * W) (hR₁ : R₁ = strictUpper (Q'ᴴ * W))
    (hW₁ : W₁ = W - Q * H₁ - Q' * R₁)
    (hH₂ : H₂ = Qᴴ * W₁) (hR₂ : R₂ = strictUpper (Q'ᴴ * W₁))
    (hW₂ : W₂ = W₁ - Q * H₂ - Q' * R₂)
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c) :
    IsBasisExtension Q W Q' (H₁ + H₂)
      (R₁ + R₂ + Matrix.diagonal fun c => ((‖WithLp.toLp 2 (W₂.col c)‖ : ℝ) : 𝕜)) := by
  -- `repr`: `hQ'` gives `W₂ = Q' * diagonal (norms)` column by column (a zero column on both
  -- sides when the norm vanishes), and `hW₁`, `hW₂` give `W = W₂ + Q * (H₁ + H₂) + Q' * (R₁ + R₂)`.
  -- `upper`: `blockTriangular_strictUpper` twice and `Matrix.blockTriangular_diagonal`.
  -- `span`: strong induction on `c` with `mul_strictUpper_col`: column `c` of `Q'` is a multiple
  -- of `w_c - Q * x - colsBefore Q' c *ᵥ y`, and the columns before `c` are combinations.
  -- `zero_col`: a zero column of `W` gives zero columns `c` of `H₁`, `R₁`, `W₁`, `H₂`, `R₂`, `W₂`.
  -- `coef_zero_left`, `coef_zero_right`: row `j` of `Qᴴ * X` vanishes when column `j` of `Q`
  -- does; a zero column `c` of `Q'` forces `W₂.col c = 0` by `hQ'`, so the diagonal entry is `0`.
  -- `orth`: induction on `c` on the Gram defect of `fromCols Q (colsBefore Q' c)`
  -- (`gramDefect_fromCols`); with it zero, `V * Vᴴ` is the projector
  -- (`mul_conjTranspose_eq_rangeProjector_of_gramDefect_eq_zero`), `W₁.col c = (1 - V * Vᴴ) w_c`
  -- is orthogonal to `V`, the second pass leaves it unchanged, and `hQ'` normalizes it.
  sorry

end NLAlib
