/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order

/-!
# The embedding of an `RCLike` field into `ℂ`

Every `RCLike` field embeds in `ℂ` by `x ↦ ⟨re x, im x⟩`. The embedding is an injective real star
algebra homomorphism: the inclusion for `ℝ`, the identity for `ℂ`. Mathlib has the equivalences
`RCLike.realRingEquiv` and `RCLike.complexRingEquiv` under a hypothesis on `RCLike.I`; this map
needs none. Upstream candidate for `Mathlib.Analysis.RCLike.Basic`.

## Main definitions

* `RCLike.toComplex`: the embedding, as a star algebra homomorphism over `ℝ`.
-/

@[expose] public section

open scoped ComplexOrder

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The embedding of an `RCLike` field into `ℂ`, `x ↦ ⟨re x, im x⟩`. -/
noncomputable def toComplex : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun x := ⟨re x, im x⟩
  map_one' := by apply Complex.ext <;> simp
  map_mul' x y := by apply Complex.ext <;> simp
  map_zero' := by apply Complex.ext <;> simp
  map_add' x y := by apply Complex.ext <;> simp
  commutes' r := by apply Complex.ext <;> simp
  map_star' x := by apply Complex.ext <;> simp

/-- The embedding in coordinates. -/
theorem toComplex_apply (x : 𝕜) : toComplex x = ⟨re x, im x⟩ :=
  rfl

/-- The real part of the embedded element. -/
@[simp]
theorem re_toComplex (x : 𝕜) : (toComplex x).re = re x :=
  rfl

/-- The imaginary part of the embedded element. -/
@[simp]
theorem im_toComplex (x : 𝕜) : (toComplex x).im = im x :=
  rfl

/-- The embedding is injective. -/
theorem toComplex_injective : Function.Injective (toComplex : 𝕜 → ℂ) :=
  fun _ _ h => RCLike.ext (congrArg Complex.re h) (congrArg Complex.im h)

/-- The embedding of a real number. -/
@[simp]
theorem toComplex_ofReal (r : ℝ) : toComplex (r : 𝕜) = (r : ℂ) := by
  apply Complex.ext <;> simp

/-- The embedding is an isometry. -/
@[simp]
theorem norm_toComplex (x : 𝕜) : ‖toComplex x‖ = ‖x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def, re_toComplex, im_toComplex]

/-- The embedding preserves and reflects the order. -/
@[simp]
theorem toComplex_le_toComplex_iff {x y : 𝕜} : toComplex x ≤ toComplex y ↔ x ≤ y := by
  rw [Complex.le_def, RCLike.le_iff_re_im (z := x)]
  rfl

/-- The embedding is continuous. -/
theorem continuous_toComplex : Continuous (toComplex : 𝕜 → ℂ) :=
  (AddMonoidHomClass.isometry_of_norm toComplex norm_toComplex).continuous

/-- On `ℂ` the embedding is the identity. -/
@[simp]
theorem toComplex_complex (z : ℂ) : toComplex z = z :=
  rfl

end RCLike
