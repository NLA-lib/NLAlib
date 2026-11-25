/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRoutine
public import NLAlib.Matrix.Computation.CholeskyRoundingBody
public import NLAlib.Matrix.Computation.CholeskyRoundingOutput
public import NLAlib.Matrix.Perturbation.CholeskyForwardError

/-!
# Full rounded Cholesky with input numerical margins

A conservative input-only condition guarantees success of the existing saved-pivot full Schur
driver, then bounds its actual decoded Cholesky residual. The margin condition depends on
conditioning through the ratio of the input spectral norm bound to its lower spectral margin.
The factor's triangular structure is exact because the actual driver zeros each upper prefix.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_cholesky`: full success, original output-block frame and
  an absolute decoded Cholesky backward error from quantitative input conditions.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual full Cholesky routine succeeds in the standard relative-error model with every
result in range, from a spectral input band $0<\mu\le B$, $\mu\mathbf I\preceq\mathbf A$,
$\|\mathbf A\|_2\le B$, roundoff $0\le u_p\le1/10$, and propagated Schur error less than
$\mu/2$. Writing $\eta$ for the terminal error recurrence and
$$e=\frac{2(1+B/\mu)\eta+16u_pB}{\sqrt{\mu}},$$
the actual factor has spectral residual at most
$$ (Ne)(2\sqrt B+Ne). $$
These conservative bounds depend on conditioning; every pivot margin is derived from the
input, and no successful execution is assumed. The arbitrary word carrier and charge monoid
need no algebraic structure. Input and output may alias or overlap. The only net store effect
is the full output block write, and the empty case requires no valid input or output handles.
No printed source; the local standard model is [Higham2002, §2.2; §10.1]. -/
theorem IsRelErrSem.exec_cholesky {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) {μ B : ℝ}
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hu1 : u p ≤ 1 / 10) (hη : choleskySchurErrorBound (u p) B μ n.eval < μ / 2)
    (hinput : HoldsDecoded st.store dec p Ab ao.eval A)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    let e := (2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) /
      Real.sqrt μ
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
        (2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ) ∧
      HoldsDecoded s dec p L lo.eval (unflatten n.eval n.eval (W.map (dec p))))
    (fun σ hσ => by
      obtain ⟨out, hr, hs⟩ := CholeskyRounding.exec_body I h p hμ hμB hu1 st.store σ n Ab L ao lo A
        hlo hscale hη hinput hL hσ
      obtain ⟨W, hsize, hw, hlower, hdiag, hentry, hdecoded⟩ :=
        CholeskyRounding.State.writeBlock_pop (hσ ▸ hs) hL
      exact ⟨out, hr, W, hsize, hw, hlower, hdiag, hentry, hdecoded⟩)
  refine ⟨out, W, ?_, hWs, hw, hdecoded, ?_⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · have hA : A.PosDef := by
      have hp := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hlo)
      simpa only [add_sub_cancel] using hp
    have hu : 0 ≤ u p := h.nonneg trivial
    have hB : 0 ≤ B := hμ.le.trans hμB
    have he : 0 ≤ (2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) /
        Real.sqrt μ := by
      have hη0 := choleskySchurErrorBound_nonneg hu hB hμ n.eval
      positivity
    simpa only [Fintype.card_fin] using
      hA.isCholesky_choleskyLower.isCholeskyErr_of_forall_abs_sub_le
      hscale he hlower hdiag (fun i j => (abs_sub_comm _ _).trans_le (hentry i j))

/-- The actual rounded full Cholesky builder supplies a typed routine certificate under the
same quantitative input spectral band, roundoff upper bound and terminal recurrence margin.
Its precondition is decoded input storage; factor capacity is supplied by the certificate's
run method. Both an empty factor and overlapping original input/output blocks are supported.
The certificate has the absolute residual allowance $(Ne)(2\sqrt B+Ne)$, with
$e=(2(1+B/\mu)\eta+16u_pB)/\sqrt{\mu}$ and terminal propagated error $\eta$. -/
theorem IsRelErrSem.isCholeskyRoutine_cholesky {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {μ B : ℝ} (hμ : 0 < μ) (hμB : μ ≤ B)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hu1 : u p ≤ 1 / 10) (hη : choleskySchurErrorBound (u p) B μ N < μ / 2)
    (Ab L : ℕ) (ao lo : IExp ℕ) :
    let e := (2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ N + 16 * u p * B) / Real.sqrt μ
    IsCholeskyRoutine I dec p A ((N * e) * (2 * Real.sqrt B + N * e))
      (fun s => HoldsDecoded s dec p Ab ao.eval A) L lo
      (cholesky p (.const N) Ab ao L lo) := by
  dsimp only
  refine ⟨executionComposable_cholesky I p (.const N) Ab ao L lo, ?_⟩
  intro st hp hw
  obtain ⟨out, W, hr, hsize, hwrite, -, he⟩ := h.exec_cholesky I p st (.const N) Ab L ao lo A
    hμ hμB hlo hscale hu1 hη hp hw
  exact ⟨out, W, hsize, hr, hwrite, he⟩

end NLAlib.Computation
