/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyFactorizationRange
public import NLAlib.Computation.BinaryFloatSem

/-!
# Cholesky under the bounded binary-format semantics

The concrete quantizer rejects out-of-range exact results and includes gradual underflow.
Its arithmetic, minus-one literal and square-root laws discharge the full stored Cholesky
theorem from numerical input conditions. The nearest tie selector remains explicit.
This mathematical finite-format semantics is separate from native Float implementation claims.

## Main results

* `NLAlib.Computation.exec_cholesky_binaryFloatSem`: actual full finite-format success,
  the complete original-store factor write and a mixed-error Cholesky residual bound.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

omit [DecidableEq P] in
private theorem binaryFloat_minus_one (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits)
    (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (p : P)
    (hΩ : 1 ≤ fmt.maxFinite) :
    ∃ ell, (binaryFloatSem fmt he r hr).lit p (-1) = some ell ∧
      AbsRelErr fmt.unitRoundoff fmt.underflowBound (-1) ell.val := by
  obtain ⟨ell, hell⟩ := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr
    (a := -1) (by simpa using hΩ)
  refine ⟨ell, ?_, ?_⟩
  · simpa only [binaryFloatSem, Rat.cast_neg, Rat.cast_one] using hell
  · rw [val_eq_binaryFloatRound_of_binaryFloatQuantize hell]
    simpa only [Float.Model.Format.unitRoundoff, Float.Model.Format.underflowBound,
      zpow_neg, zpow_natCast, inv_pow] using absRelErr_binaryFloatRound fmt hr (-1)

omit [DecidableEq P] in
private theorem binaryFloat_sqrt (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits)
    (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ)) (p : P)
    (v : BinaryFloat fmt) (hv : 0 ≤ v.val) (hΩ : |Real.sqrt v.val| ≤ fmt.maxFinite) :
    ∃ d, (binaryFloatSem fmt he r hr).un p .sqrt v = some d ∧
      AbsRelErr fmt.unitRoundoff fmt.underflowBound (Real.sqrt v.val) d.val := by
  obtain ⟨d, hd⟩ := exists_binaryFloatQuantize_eq_some_of_abs_le fmt he r hr hΩ
  refine ⟨d, ?_, ?_⟩
  · simpa only [binaryFloatSem, hv, if_pos] using hd
  · rw [val_eq_binaryFloatRound_of_binaryFloatQuantize hd]
    simpa only [Float.Model.Format.unitRoundoff, Float.Model.Format.underflowBound,
      zpow_neg, zpow_natCast, inv_pow] using absRelErr_binaryFloatRound fmt hr (Real.sqrt v.val)

/-- The actual stored Cholesky routine succeeds under the concrete bounded binary quantizer
when its explicit numerical input conditions and source spectral band hold. Overflow rejection
and additive subnormal error are part of this interpretation; no successful-run, computed-pivot
or trace-range hypothesis is assumed. The actual packed factor has its complete original-store
write, decoded storage guarantee and absolute Cholesky backward error. Original input and
output may overlap, and empty matrices need no valid handles. The format and nearest tie
selector are arbitrary subject to their stated certificates; this does not identify the
mathematical quantizer with native Float operations. [Higham2002, §2.2; §10.1]. -/
theorem exec_cholesky_binaryFloatSem (fmt : Float.Model.Format) (he : 2 ≤ fmt.exponentBits)
    (r : ℝ → ℤ) (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ))
    (I : Interp P ι (BinaryFloat fmt) C) (hI : I.sem = binaryFloatSem fmt he r hr) (p : P)
    (st : St P (BinaryFloat fmt) C) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) {μ B : ℝ}
    (hc : CholeskyRangeConditions n.eval fmt.unitRoundoff fmt.underflowBound B μ fmt.maxFinite)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hinput : HoldsDecoded st.store (fun _ w => w.val) p Ab ao.eval A)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    let e := choleskyMixedColumnErrorBound fmt.unitRoundoff fmt.underflowBound B μ
      (choleskyMixedSchurErrorBound fmt.unitRoundoff fmt.underflowBound B μ n.eval)
    ∃ (out : St P (BinaryFloat fmt) C) (W : Array (BinaryFloat fmt)),
      exec I (cholesky p n Ab ao L lo).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p L lo.eval W = some out.store ∧
      HoldsDecoded out.store (fun _ w => w.val) p L lo.eval
        (unflatten n.eval n.eval (W.map (·.val))) ∧
      IsCholeskyErr ((n.eval * e) * (2 * Real.sqrt B + n.eval * e)) A
        (unflatten n.eval n.eval (W.map (·.val))) := by
  have h : IsArithErrSem
      (fun (_ : P) _ => AbsRelErr fmt.unitRoundoff fmt.underflowBound)
      (fun _ (w : BinaryFloat fmt) => w.val) (fun _ a => |a| ≤ fmt.maxFinite) I.sem := by
    rw [hI]
    simpa only [Float.Model.Format.unitRoundoff, Float.Model.Format.underflowBound,
      zpow_neg, zpow_natCast, inv_pow] using isArithErrSem_binaryFloatSem (P := P) fmt he r hr
  exact h.exec_cholesky I p st n Ab L ao lo A hc hlo hscale (fun _ ha => ha)
    (by rw [hI]; exact binaryFloat_minus_one fmt he r hr p hc.literal_le)
    (by rw [hI]; exact binaryFloat_sqrt fmt he r hr p) hinput hL

/-- The concrete bounded binary quantizer supplies a typed Cholesky routine certificate from
the same numerical input conditions and spectral band. Scratch release, the packed factor
write, structural guarantees and mixed-error residual all follow from the actual full run. -/
theorem isCholeskyRoutine_cholesky_binaryFloatSem (fmt : Float.Model.Format)
    (he : 2 ≤ fmt.exponentBits) (r : ℝ → ℤ)
    (hr : ∀ x, AbsRelErr 0 (1 / 2) x (r x : ℝ))
    (I : Interp P ι (BinaryFloat fmt) C) (hI : I.sem = binaryFloatSem fmt he r hr) (p : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {μ B : ℝ}
    (hc : CholeskyRangeConditions N fmt.unitRoundoff fmt.underflowBound B μ fmt.maxFinite)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (Ab L : ℕ) (ao lo : IExp ℕ) :
    let e := choleskyMixedColumnErrorBound fmt.unitRoundoff fmt.underflowBound B μ
      (choleskyMixedSchurErrorBound fmt.unitRoundoff fmt.underflowBound B μ N)
    IsCholeskyRoutine I (fun _ w => w.val) p A ((N * e) * (2 * Real.sqrt B + N * e))
      (fun s => HoldsDecoded s (fun _ w => w.val) p Ab ao.eval A) L lo
      (cholesky p (.const N) Ab ao L lo) := by
  dsimp only
  refine ⟨executionComposable_cholesky I p (.const N) Ab ao L lo, ?_⟩
  intro st hp hw
  obtain ⟨out, W, hr, hsize, hwrite, -, he⟩ := exec_cholesky_binaryFloatSem fmt he r hr I hI p
    st (.const N) Ab L ao lo A hc hlo hscale hp hw
  exact ⟨out, W, hsize, hr, hwrite, he⟩

end NLAlib.Computation
