/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Basic.OrthonormalBasis

/-!
# Polar factors and frames under unitary maps

Facts about the polar factor and about matrices with orthonormal columns that the Haar frame law
(`NLAlib/RandomMatrix/Haar/`) is built on: the polar factor commutes with a coisometry on the
right, has the range of its matrix and spectral norm at most one, and normalises a column; two
frames with the same number of columns differ by a unitary on the left; and a matrix that every
unitary conjugation fixes is a multiple of the identity.

This file collects the Matrix-layer additions of `docs/design/RandomMatrix-R5.md` §1 while they are
proved. At the wrap-up, the polar-factor statements join `NLAlib/Matrix/Factorizations/Polar.lean`
and the frame statements join `NLAlib/Matrix/Basic/OrthonormalBasis.lean`.

## Main results

* `NLAlib.polarFactor_mul_right`: `polarFactor (A V) = polarFactor A * V` for a coisometry `V`.
* `NLAlib.rangeProjector_mul_polarFactor`: `range (A * polarFactor B) = range (A * B)`.
* `NLAlib.specNorm_polarFactor_le_one`.
* `NLAlib.polarFactor_replicateCol`: the polar factor of a column is the normalised column.
* `NLAlib.HasOrthonormalCols.exists_mul_eq`: unitaries act transitively on frames.
* `NLAlib.eq_smul_one_of_forall_mul_mul_conjTranspose_eq`: a matrix commuting with every unitary
  is scalar.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype q]

/-! ### The polar factor -/

/-- **The polar factor commutes with a coisometry on the right**: for `V` with orthonormal rows
(`V Vᴴ = 1`; in particular any unitary), `polarFactor (A V) = polarFactor A * V`. The right-hand
twin of `polarFactor_mul_left`. -/
theorem polarFactor_mul_right [DecidableEq n] [DecidableEq q] {V : Matrix n q 𝕜}
    (hV : HasOrthonormalCols Vᴴ) (A : Matrix m n 𝕜) :
    polarFactor (A * V) = polarFactor A * V := by
  -- Proof: `polarFactor_conjTranspose` twice around `polarFactor_mul_left` with `W = Vᴴ`.
  sorry

/-- **Right multiplication by a polar factor keeps the range**: the range projector of
`A * polarFactor B` is that of `A * B`, for every shape and rank. The column spaces agree because
`polarFactor B = B * pinv (CFC.sqrt (Bᴴ * B))` and `B = polarFactor B * CFC.sqrt (Bᴴ * B)`. -/
theorem rangeProjector_mul_polarFactor [DecidableEq n] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    rangeProjector (A * polarFactor B) = rangeProjector (A * B) := by
  -- Proof: mutual range inclusion from the definition and `polarFactor_mul_sqrt`.
  sorry

/-- The polar factor of `B` has the range of `B`: `rangeProjector (polarFactor B) =
rangeProjector B` (the case `A = 1` of `rangeProjector_mul_polarFactor`). -/
theorem rangeProjector_polarFactor [DecidableEq n] (B : Matrix m n 𝕜) :
    rangeProjector (polarFactor B) = rangeProjector B := by
  sorry

/-- **The polar factor has spectral norm at most one**: it is a partial isometry, with norm `1`
unless the matrix is `0`. -/
theorem specNorm_polarFactor_le_one [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm (polarFactor A) ≤ 1 := by
  -- Proof: `conjTranspose_polarFactor_mul_self` is a projector, whose norm is at most `1`.
  sorry

/-- **The polar factor of a column is the normalised column**: `polarFactor [x] = [x / ‖x‖]`, the
real scalar `‖x‖⁻¹` acting on `x`. True at `x = 0`, where both sides are `0` (`0⁻¹ = 0`). -/
theorem polarFactor_replicateCol (x : m → 𝕜) :
    polarFactor (Matrix.replicateCol Unit x) =
      Matrix.replicateCol Unit ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) • x) := by
  sorry

/-! ### Frames under unitary maps -/

/-- **Unitaries act transitively on frames**: two matrices with orthonormal columns and the same
column index differ by a unitary factor on the left. Port of the private
`exists_hasOrthonormalCols_mul_eq` of `NLAlib/Matrix/Factorizations/Procrustes.lean`, made public
here (`docs/design/RandomMatrix-R5.md` §1, addition 5). -/
theorem HasOrthonormalCols.exists_mul_eq [DecidableEq m] {r : Type*} [Finite r] [DecidableEq r]
    {X Y : Matrix m r 𝕜} (hX : HasOrthonormalCols X) (hY : HasOrthonormalCols Y) :
    ∃ U : Matrix m m 𝕜, HasOrthonormalCols U ∧ U * X = Y := by
  sorry

/-- **A matrix fixed by every unitary conjugation is scalar**: if `U M Uᴴ = M` for every unitary
`U`, then `M = (tr M / card n) • 1`. For empty `n` both sides are `0`. Unlike Mathlib's
`Matrix.mem_range_scalar_of_commute_single`, the hypothesis quantifies over unitaries only
(signed permutation matrices suffice). -/
theorem eq_smul_one_of_forall_mul_mul_conjTranspose_eq [DecidableEq n] {M : Matrix n n 𝕜}
    (h : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → U * M * Uᴴ = M) :
    M = (M.trace / Fintype.card n) • (1 : Matrix n n 𝕜) := by
  -- Proof: diagonal sign changes kill the off-diagonal entries; transpositions equate the
  -- diagonal ones.
  sorry

end NLAlib
