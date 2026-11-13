/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.ResidualCache
public import NLAlib.Matrix.FinitePrecision.OpsFloat
public import NLAlib.Matrix.FinitePrecision.OpsBinaryFloat
public import NLAlib.Ops.Examples.FixedPoint

/-!
# Concrete finite-format residual-cache kernels

Native logical binary64 words and bounded nearest-grid fixed-point words instantiate the
same actual scalar-lowered kernel. Arbitrary binary formats also have a mathematical
quantizer endpoint on the real carrier. All range hypotheses concern supplied residuals;
no measured intermediate range or arithmetic-accuracy assumption is required.

These results concern the recursive residual cache. The mixed-error zero-cache consequence
is `norm_sq_le_of_residualCache_eq_zero`; a full true-residual claim also needs a residual gap.
The binary64 arithmetic is core's logical native Float arithmetic; the fixed-point tie and
saturation policies and the real-carrier binary quantizer are stated in their operation models.

## Main results

* `NLAlib.Krylov.CG.wp_residualCache_float64`: actual finite Float words.
* `NLAlib.Krylov.CG.wp_residualCache_binaryQuantized`: arbitrary mathematical binary formats.
* `NLAlib.Krylov.CG.wp_residualCache_fixedPoint`: finite nearest-grid fixed-point words.
-/

@[expose] public section

namespace NLAlib.Krylov.CG

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]
  [Apart Blas1Op ScalarOp Op]

/-- The finite binary64 carrier includes the positive-zero word. -/
local instance instInhabitedFiniteFloat : Inhabited Computation.FiniteFloat :=
  ⟨Float64.zeroWord⟩

/-- Actual finite binary64 arithmetic writes the residual cache under an input-only
largest-finite-result bound. The model supplies gradual-underflow accuracy itself. -/
theorem wp_residualCache_float64 {I : Interp Op Tst Computation.FiniteFloat}
    (hI : IsScalar Float64.machine I) {τ : Tape Computation.FiniteFloat}
    {n : ℕ} {r z : ℕ × ℕ} {m : Mem Computation.FiniteFloat}
    {rs : List Computation.FiniteFloat} (hl : m.Live [r, z])
    (hr : m.store.readBlock r.1 r.2 n = some rs) (hz : z.2 < m.store.len z.1)
    (hRange : (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * n) *
        ‖WithLp.toLp 2 (decv Float64.decode n rs)‖ ^ 2 +
      n * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * n) *
        (2 + Float.Model.Format.binary64.unitRoundoff) *
          Float.Model.Format.binary64.underflowBound ≤ Float.Model.Format.binary64.maxFinite) :
    Wp .total I τ (dotSum.body.link Blas.sumSeqTable) (Env.frame [n] [r, r, z])
      (fun out => ∃ cache, out = m.upd z cache ∧ out.store.get z.1 z.2 = some cache ∧
        Computation.AbsRelErr ((1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * n) - 1)
          (n * (1 + Float.Model.Format.binary64.unitRoundoff) ^ (2 * n) *
            (2 + Float.Model.Format.binary64.unitRoundoff) *
              Float.Model.Format.binary64.underflowBound)
          (‖WithLp.toLp 2 (decv Float64.decode n rs)‖ ^ 2) (Float64.decode cache)) m := by
  have h := wp_residualCache (I := I) (τ := τ) (m := m) (r := r) (z := z)
    hI Float64.mixedModel_machine Float64.decode_lit_zero hl hr hz
    (fun _ ha => ha) hRange
  exact h.mono fun _ ⟨cache, he, hg, herr, _⟩ => ⟨cache, he, hg, herr⟩

/-- A general binary-format quantizer certifies the same kernel, on a mathematical real
carrier. The nearest-selector law fixes the tie policy independently of execution. -/
theorem wp_residualCache_binaryQuantized (fmt : Float.Model.Format) {round : ℝ → ℤ}
    (hRound : ∀ a, Computation.AbsRelErr 0 (1 / 2) a (round a : ℝ))
    {I : Interp Op Tst ℝ} (hI : IsScalar (BinaryQuantized.machine fmt round) I)
    {τ : Tape ℝ} {n : ℕ} {r z : ℕ × ℕ} {m : Mem ℝ} {rs : List ℝ}
    (hl : m.Live [r, z]) (hr : m.store.readBlock r.1 r.2 n = some rs)
    (hz : z.2 < m.store.len z.1)
    (hRange : (1 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) ^ (2 * n) *
        ‖WithLp.toLp 2 (decv id n rs)‖ ^ 2 +
      n * (1 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) ^ (2 * n) *
        (2 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) * ((2 : ℝ) ^ fmt.minExponent / 2) ≤ fmt.maxFinite) :
    Wp .total I τ (dotSum.body.link Blas.sumSeqTable) (Env.frame [n] [r, r, z])
      (fun out => ∃ cache, out = m.upd z cache ∧ out.store.get z.1 z.2 = some cache ∧
        Computation.AbsRelErr ((1 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) ^ (2 * n) - 1)
          (n * (1 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) ^ (2 * n) *
            (2 + (2 : ℝ)⁻¹ ^ fmt.mantissaBits) * ((2 : ℝ) ^ fmt.minExponent / 2))
          (‖WithLp.toLp 2 (decv id n rs)‖ ^ 2) cache) m := by
  have h := wp_residualCache (I := I) (τ := τ) (m := m) (r := r) (z := z)
    hI (BinaryQuantized.mixedModel_machine fmt hRound)
    (BinaryQuantized.decode_lit_zero fmt hRound) hl hr hz (fun _ ha => ha) hRange
  exact h.mono fun _ ⟨cache, he, hg, herr, _⟩ => ⟨cache, he, hg, herr⟩

/-- Bounded nearest-grid fixed-point arithmetic has an absolute half-grid allowance.
The resulting cache error is at most `n/scale`, and a zero cache bounds the residual by
that same value. Saturation is excluded by the supplied input-only range inequality. -/
theorem wp_residualCache_fixedPoint (bound scale : ℕ) (hs : 0 < scale)
    {I : Interp Op Tst (Examples.FixedPoint.Word bound)}
    (hI : IsScalar (Examples.FixedPoint.machine bound scale) I)
    {τ : Tape (Examples.FixedPoint.Word bound)} {n : ℕ} {r z : ℕ × ℕ}
    {m : Mem (Examples.FixedPoint.Word bound)} {rs : List (Examples.FixedPoint.Word bound)}
    (hl : m.Live [r, z]) (hr : m.store.readBlock r.1 r.2 n = some rs)
    (hz : z.2 < m.store.len z.1)
    (hRange : ‖WithLp.toLp 2 (decv (Examples.FixedPoint.decode scale) n rs)‖ ^ 2 +
      n / (scale : ℝ) ≤ (bound : ℝ) / scale) :
    Wp .total I τ (dotSum.body.link Blas.sumSeqTable) (Env.frame [n] [r, r, z])
      (fun out => ∃ cache, out = m.upd z cache ∧ out.store.get z.1 z.2 = some cache ∧
        |‖WithLp.toLp 2 (decv (Examples.FixedPoint.decode scale) n rs)‖ ^ 2 -
          Examples.FixedPoint.decode scale cache| ≤ n / (scale : ℝ) ∧
        (Examples.FixedPoint.decode scale cache = 0 →
          ‖WithLp.toLp 2 (decv (Examples.FixedPoint.decode scale) n rs)‖ ^ 2 ≤
            n / (scale : ℝ))) m := by
  have hzero : Examples.FixedPoint.decode scale
      ((Examples.FixedPoint.machine bound scale).lit 0) = 0 := by
    simp [Examples.FixedPoint.decode, Examples.FixedPoint.machine,
      Examples.FixedPoint.quantize, Examples.FixedPoint.roundedWord]
  have hD : (n : ℝ) * 1 * 2 * ((1 / 2 : ℝ) / scale) =
      n / (scale : ℝ) := by ring
  have hRange' : (1 + (0 : ℝ)) ^ (2 * n) *
      ‖WithLp.toLp 2 (decv (Examples.FixedPoint.decode scale) n rs)‖ ^ 2 +
      n * (1 + (0 : ℝ)) ^ (2 * n) * (2 + 0) * ((1 / 2 : ℝ) / scale) ≤
        (bound : ℝ) / scale := by simpa only [hD, add_zero, one_pow, one_mul] using hRange
  have h := wp_residualCache (I := I) (τ := τ) (m := m) (r := r) (z := z)
    hI (Examples.FixedPoint.mixedModel_machine bound scale hs) hzero hl hr hz
    (fun _ ha => ha) hRange'
  refine h.mono fun out ⟨cache, he, hg, herr, _⟩ => ⟨cache, he, hg, ?_, ?_⟩
  · simpa only [Computation.AbsRelErr, add_zero, one_pow, sub_self, zero_mul,
      zero_add, hD] using herr
  · intro hc
    have he' := herr
    rw [hc] at he'
    simpa only [Computation.AbsRelErr, sub_zero, add_zero, one_pow, sub_self, zero_mul,
      zero_add, hD, abs_of_nonneg (sq_nonneg
        ‖WithLp.toLp 2 (decv (Examples.FixedPoint.decode scale) n rs)‖)] using he'

end NLAlib.Krylov.CG
