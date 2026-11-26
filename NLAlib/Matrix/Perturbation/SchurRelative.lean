/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Rounding

/-!
# Relative defect of saved-pivot Schur arithmetic

The rounded minus-one literal, reciprocal, two products and final sum give a five-factor
rank-one defect, together with the separate original-entry rounding term.

## Main results

* `NLAlib.Computation.abs_sub_schurUpdate_le_of_relErr`: the local saved-pivot update bound.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Five rounded scalar operations give the saved-pivot Schur defect, with no restriction on
five times the roundoff. Only roundoff below one is needed. -/
theorem abs_sub_schurUpdate_le_of_relErr {u a x y pivot ell c t q z : ℝ}
    (hu : u < 1) (hell : RelErr u (-1) ell) (hc : RelErr u (ell / pivot) c)
    (ht : RelErr u (c * y) t) (hq : RelErr u (x * t) q) (hz : RelErr u (a + q) z) :
    |z - (a - x * y / pivot)| ≤ u * |a| + roundingFactor 5 u * |x * y / pivot| := by
  obtain ⟨δ₀, hδ₀, he₀⟩ := hell
  obtain ⟨δ₁, hδ₁, he₁⟩ := hc
  obtain ⟨δ₂, hδ₂, he₂⟩ := ht
  obtain ⟨δ₃, hδ₃, he₃⟩ := hq
  obtain ⟨δ₄, hδ₄, he₄⟩ := hz
  let θ := (1 + δ₀) * (1 + δ₁) * (1 + δ₂) * (1 + δ₃) * (1 + δ₄) - 1
  have hθ : IsRoundingProduct u 5 θ := by
    convert ((((isRoundingProduct_one_of_abs_le hδ₀).mul
      (isRoundingProduct_one_of_abs_le hδ₁)).mul
      (isRoundingProduct_one_of_abs_le hδ₂)).mul
      (isRoundingProduct_one_of_abs_le hδ₃)).mul
      (isRoundingProduct_one_of_abs_le hδ₄) using 1
    dsimp [θ]
    ring
  have he : z - (a - x * y / pivot) = a * δ₄ - (x * y / pivot) * θ := by
    rw [he₄, he₃, he₂, he₁, he₀]
    dsimp [θ]
    ring
  calc
    |z - (a - x * y / pivot)| = |a * δ₄ - (x * y / pivot) * θ| := congrArg abs he
    _ ≤ |a * δ₄| + |(x * y / pivot) * θ| := abs_sub _ _
    _ = |a| * |δ₄| + |x * y / pivot| * |θ| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * u + |x * y / pivot| * roundingFactor 5 u :=
      add_le_add (mul_le_mul_of_nonneg_left hδ₄ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hθ.abs_le hu) (abs_nonneg _))
    _ = u * |a| + roundingFactor 5 u * |x * y / pivot| := by ring

end NLAlib.Computation
