/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.FiniteRange
public import NLAlib.Matrix.FinitePrecision.OpsBinaryFinite

/-!
# Cholesky on bounded represented binary words

The finite-carrier quantizer realizes the mixed arithmetic hypotheses of the full Cholesky
range theorem. Exact targets outside the finite exponent range are rejected. The original
input inequalities guarantee every target is accepted, including subnormal arithmetic.
This is a mathematical bounded-format backend, with no native IEEE accuracy assertion.

## Main results

* `NLAlib.Cholesky.rightLooking_meets_binaryFinite`: bounded binary factorization success.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops Computation

variable {Op Tst : Type} [Has ScalarOp Op]

/-- On represented binary words the actual Cholesky routine succeeds and satisfies the
full mixed residual bound from the original spectral input band and scalar range conditions.
The finite carrier includes gradual underflow, and its local interpretation rejects overflow. -/
theorem rightLooking_meets_binaryFinite (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits)
    (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ))
    (I : Interp Op Tst (BinaryFloat fmt)) {B μ Ω : ℝ}
    (hI : IsGuardedScalar (BinaryFinite.machine fmt he r hr) Subtype.val
      (fun x => |x| ≤ fmt.maxFinite) I) (hΩ : Ω ≤ fmt.maxFinite) :
    letI : Inhabited (BinaryFloat fmt) := ⟨BinaryFinite.zero fmt he⟩
    (rightLooking (Op := Op) (Tst := Tst)).Meets I
      (rightLookingMixedSpec (BinaryFinite.machine fmt he r hr) Subtype.val
        ((2 : ℝ)⁻¹ ^ fmt.mantissaBits) ((2 : ℝ) ^ fmt.minExponent / 2) B μ Ω) := by
  let : Inhabited (BinaryFloat fmt) := ⟨BinaryFinite.zero fmt he⟩
  exact rightLooking_meets_mixed hI (BinaryFinite.mixedModel_machine fmt he r hr)
    (BinaryFinite.decode_lit_zero fmt he r hr) (fun _ hx => hx.trans hΩ)

end NLAlib.Cholesky
