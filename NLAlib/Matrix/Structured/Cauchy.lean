/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Matrix.Order

/-!
# Cauchy and Hilbert matrices

The Cauchy matrix of two families `x`, `y` has entries `1 / (x i + y j)`. Its determinant is
Cauchy's double product, which is positive for increasing positive families; the Hilbert matrix
is the case `x i = i + 1`, `y j = j`.

## Main definitions

* `NLAlib.cauchyMatrix`, `NLAlib.hilbertMatrix`.

## Main results

* `NLAlib.det_cauchyMatrix`: Cauchy's determinant formula.
* `NLAlib.det_cauchyMatrix_pos`, `NLAlib.det_hilbertMatrix_pos`.
* `NLAlib.posDef_hilbertMatrix`: the Hilbert matrix is positive definite.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {K : Type*} [Field K] {m n : Type*}

/-- The **Cauchy matrix** of two families: entries `1 / (x i + y j)`.
Port of `NLAlib.cauchyMatrix`, there over `ℝ`. -/
def cauchyMatrix (x : m → K) (y : n → K) : Matrix m n K :=
  Matrix.of fun i j => (x i + y j)⁻¹

/-- Entries of a Cauchy matrix. -/
@[simp]
theorem cauchyMatrix_apply (x : m → K) (y : n → K) (i : m) (j : n) :
    cauchyMatrix x y i j = (x i + y j)⁻¹ :=
  rfl

/-- The transpose of a Cauchy matrix is the Cauchy matrix of the swapped families. -/
theorem transpose_cauchyMatrix (x : m → K) (y : n → K) :
    (cauchyMatrix x y)ᵀ = cauchyMatrix y x := by
  sorry

/-- **Cauchy's determinant.** For families with nonvanishing denominators,
`det = ∏_{i < j} (x j - x i)(y j - y i) / ∏_{i, j} (x i + y j)`.
[HornJohnson2013, §0.9.12]. Port of `NLAlib.det_cauchyMatrix_eq_prod_differences`. -/
theorem det_cauchyMatrix {n : ℕ} (x y : Fin n → K) (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i) * (y j - y i)) / ∏ i, ∏ j, (x i + y j) := by
  sorry

/-- The determinant of a Cauchy matrix of strictly increasing families with positive denominators
is positive. Port of `NLAlib.det_cauchyMatrix_pos_of_strictMono`. -/
theorem det_cauchyMatrix_pos {n : ℕ} {x y : Fin n → ℝ} (hx : StrictMono x) (hy : StrictMono y)
    (h : ∀ i j, 0 < x i + y j) : 0 < (cauchyMatrix x y).det := by
  sorry

/-- The **Hilbert matrix** of order `n`: entries `1 / (i + j + 1)`.
Port of `NLAlib.hilbertMatrix`. -/
noncomputable def hilbertMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ((i : ℝ) + j + 1)⁻¹

/-- The Hilbert matrix is a Cauchy matrix. Port of `NLAlib.hilbertMatrix_eq_cauchyMatrix`. -/
theorem hilbertMatrix_eq_cauchyMatrix (n : ℕ) :
    hilbertMatrix n = cauchyMatrix (fun i : Fin n => (i : ℝ) + 1) fun j : Fin n => (j : ℝ) := by
  sorry

/-- The determinant of the Hilbert matrix is positive. Port of `NLAlib.det_hilbertMatrix_pos`. -/
theorem det_hilbertMatrix_pos (n : ℕ) : 0 < (hilbertMatrix n).det := by
  sorry

/-- **The Hilbert matrix is positive definite.** [HornJohnson2013, §7.1.P19 context]. -/
theorem posDef_hilbertMatrix (n : ℕ) : (hilbertMatrix n).PosDef := by
  sorry

end NLAlib
