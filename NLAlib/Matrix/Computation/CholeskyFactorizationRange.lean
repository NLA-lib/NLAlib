/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRoutine
public import NLAlib.Matrix.Computation.CholeskyRangeBody
public import NLAlib.Matrix.Computation.CholeskyRangeOutput
public import NLAlib.Matrix.Perturbation.CholeskyForwardError

/-!
# Full Cholesky with finite range and mixed rounding errors

Quantitative scalar input conditions and a spectral input band guarantee that every actual
instruction succeeds, including the reciprocal coefficient and all retired residual entries.
The returned packed factor has exact triangular zeros, positive diagonal and an absolute
spectral residual bound retaining additive underflow. The existing builder is unchanged.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_cholesky`: full successful execution and decoded
  Cholesky backward error from input-level finite-range and mixed-error conditions.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual full Cholesky builder succeeds under mixed arithmetic errors with finite
range from numerical input conditions and the spectral band
$\mu\mathbf I\preceq\mathbf A$, $\|\mathbf A\|_2\le B$.
The explicit backend laws for the minus-one literal and in-range square root supplement the
arithmetic-only contract; no successful run, trace safety or computed-pivot premise is used.
With uniform factor-entry error $e$ given by the mixed column budget, the actual decoded
factor has absolute spectral residual at most $(Ne)(2\sqrt B+Ne)$.
Only the original output block remains written. Input and output may overlap, arbitrary word
carriers and charge monoids are supported, and the empty case reads no matrix cells.
This is a conservative conditioning-dependent guarantee with additive underflow, rather than
a native floating-point implementation claim. No printed source; the local model is
[Higham2002, §2.2; §10.1]. -/
theorem IsArithErrSem.exec_cholesky {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) {μ B Ω : ℝ}
    (hc : CholeskyRangeConditions n.eval (u p) (τ p) B μ Ω)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (hinput : HoldsDecoded st.store dec p Ab ao.eval A)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    let e := choleskyMixedColumnErrorBound (u p) (τ p) B μ
      (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval)
    ∃ (out : St P K C) (W : Array K),
      exec I (cholesky p n Ab ao L lo).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p L lo.eval W = some out.store ∧
      HoldsDecoded out.store dec p L lo.eval (unflatten n.eval n.eval (W.map (dec p))) ∧
      IsCholeskyErr ((n.eval * e) * (2 * Real.sqrt B + n.eval * e)) A
        (unflatten n.eval n.eval (W.map (dec p))) := by
  dsimp only
  obtain ⟨out, hr, W, hWs, hw, hlower, hdiag, hentry, hdecoded⟩ := exists_exec_alloc I p (n * n)
    (fun R => (do
      copyv p Ab ao R 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n R L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n R 0 (.var k)).run) st
    (fun s => ∃ W : Array K, W.size = n.eval * n.eval ∧
      st.store.writeBlock p L lo.eval W = some s ∧
      (unflatten n.eval n.eval (W.map (dec p))).IsLowerTriangular ∧
      (∀ i, 0 < unflatten n.eval n.eval (W.map (dec p)) i i) ∧
      (∀ i j, |unflatten n.eval n.eval (W.map (dec p)) i j - choleskyLower A i j| ≤
        choleskyMixedColumnErrorBound (u p) (τ p) B μ
          (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval)) ∧
      HoldsDecoded s dec p L lo.eval (unflatten n.eval n.eval (W.map (dec p))))
    (fun σ hσ => by
      obtain ⟨out, hr, hs⟩ :=
        CholeskyRange.exec_body I h p n hc hrange hminus hsqrt st.store σ Ab L ao lo A
        hlo hscale hinput hL hσ
      obtain ⟨W, hsize, hw, hlower, hdiag, hentry, hdecoded⟩ :=
        CholeskyRange.State.writeBlock_pop (hσ ▸ hs) hL
      exact ⟨out, hr, W, hsize, hw, hlower, hdiag, hentry, hdecoded⟩)
  refine ⟨out, W, ?_, hWs, hw, hdecoded, ?_⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · have hA : A.PosDef := by
      have hp := (Matrix.PosDef.one.smul hc.margin_pos).add_posSemidef (Matrix.le_iff.mp hlo)
      simpa only [add_sub_cancel] using hp
    have hB : 0 ≤ B := hc.margin_pos.le.trans hc.margin_le_scale
    have he : 0 ≤ choleskyMixedColumnErrorBound (u p) (τ p) B μ
        (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval) :=
      choleskyMixedColumnErrorBound_nonneg hc.roundoff_nonneg hc.underflow_nonneg hB hc.margin_pos
        (choleskyMixedSchurErrorBound_nonneg hc.roundoff_nonneg hc.underflow_nonneg
          hB hc.margin_pos _)
        hc.root_margin_pos
    simpa only [Fintype.card_fin] using
      hA.isCholesky_choleskyLower.isCholeskyErr_of_forall_abs_sub_le
      hscale he hlower hdiag (fun i j => (abs_sub_comm _ _).trans_le (hentry i j))

/-- The actual full finite-range Cholesky builder supplies a typed routine certificate under
the numerical input conditions and source spectral band. Its only storage precondition is the
decoded input; writable output capacity is supplied by the certificate's run method. -/
theorem IsArithErrSem.isCholeskyRoutine_cholesky {u τ : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {μ B Ω : ℝ}
    (hc : CholeskyRangeConditions N (u p) (τ p) B μ Ω)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (Ab L : ℕ) (ao lo : IExp ℕ) :
    let e := choleskyMixedColumnErrorBound (u p) (τ p) B μ
      (choleskyMixedSchurErrorBound (u p) (τ p) B μ N)
    IsCholeskyRoutine I dec p A ((N * e) * (2 * Real.sqrt B + N * e))
      (fun s => HoldsDecoded s dec p Ab ao.eval A) L lo
      (cholesky p (.const N) Ab ao L lo) := by
  dsimp only
  refine ⟨executionComposable_cholesky I p (.const N) Ab ao L lo, ?_⟩
  intro st hp hw
  obtain ⟨out, W, hr, hsize, hwrite, -, he⟩ := h.exec_cholesky I p st (.const N) Ab L ao lo A
    hc hlo hscale hrange hminus hsqrt hp hw
  exact ⟨out, W, hsize, hr, hwrite, he⟩

end NLAlib.Computation
