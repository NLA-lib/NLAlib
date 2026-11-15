/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Guards
public import NLAlib.Krylov.FinitePrecision.PCGRunConstruction

/-!
# Existing PCG runs extracted from rounded operation bounds

A first active zero-start step determines an existing mathematical PCG run with exactly its
computed terminal state and pairings. The preconditioner spectral precision window guarantees
that the final pairing is nonnegative, including an exactly zero final residual.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.RoundBounds.exists_pcgRun_one` extracts the existing run.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open scoped Matrix

/-- The actual first zero-start rounded recurrence is an existing one-step PCG run.
The system is Hermitian, the reference inverse preconditioner is SPD, local errors fit a
common allowance at most one percent, and the preconditioner spectrum satisfies the stated
precision window. No execution-success or final-pairing positivity premise is required.
[Saad2003, Algorithm 9.1]. -/
theorem RoundBounds.exists_pcgRun_one {n : ℕ} {em u ed ea e p p' : ℝ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {b : Fin n → ℝ}
    {next : PCGState ℝ (Fin n)} {rho rho' : ℝ}
    (h : RoundBounds em u ed ea A O ⟨0, b, O.mulVec b, O.mulVec b⟩ next rho rho')
    (hA : A.IsHermitian) (hP : P.PosDef)
    (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) (he : e ≤ 1 / 100)
    (hp : 0 < p) (hs : spectrum ℝ P ⊆ Set.Icc p p')
    (hprec : 3 * e * p' ≤ p) (hOe : O.ε ≤ e) :
    ∃ R : PCGRun n 1, R.A = A ∧ R.M = P ∧ HEq R.preconditioner O ∧ R.b = b ∧ R.ε = e ∧
      R.state 1 = next ∧ R.ν 0 = rho ∧ R.ν 1 = rho' := by
  have hPT : Pᵀ = P := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.isHermitian
  have hlast : 0 ≤ rho' := by
    obtain ⟨q, curv, alpha, beta, _, _, _, _, _, _, _, _, hz, hn', _, _⟩ := h
    exact pairing_nonneg_of_spectrum_subset_Icc hPT hp hs (hu.trans hue) hprec hd hde
      hOe hz hn'
  obtain ⟨q, curv, alpha, beta, eg, eb, hmv, hrho, hcurv, hn, hc, halpha, heg,
    hbeta, heb, hz, hn', hx, hr, hdir⟩ := h.exists_run_errors hu hd ha hem hue hde hae
  let R := PCGRun.ofOneStep n A P O b next q e rho rho' curv alpha eg beta eb hA hP
    (hu.trans hue) he hz hn hn' hlast hrho hcurv hmv
    (by simpa only [abs_sub_comm] using hc) halpha heg hbeta heb
    (by simpa only [WithLp.toLp_zero, norm_zero, zero_add] using hx) hr hdir
  exact ⟨R, rfl, rfl, HEq.rfl, rfl, rfl, by cases next; rfl, rfl, rfl⟩

open Ops

/-- A first active rounded PCG step executes totally and stores an existing one-step run.
Its guards follow from the raw matrix spectral windows, precision inequalities and nonzero
right-hand side; the initial state is exactly the preceding oracle initializer's output. -/
theorem step_writes_pcgRun_one {Op Tst : Type}
    [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
    [Has (Tagged Preconditioner OperatorOp) Op]
    {F : Machine ℝ} {n : ℕ} {em u e a a' p p' : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop} {b : Fin n → ℝ}
    (hS : IsScalar F I) (hF : StdModel u id F) (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hOp : IsMatvec id A (em * specNorm A) I)
    (hOracle : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hA : A.IsHermitian) (hP : P.PosDef) (hu : 0 ≤ u)
    (hd : 0 ≤ ε.dot n) (hv : 0 ≤ ε.axpy) (hem : em ≤ e) (hue : u ≤ e)
    (hde : ε.dot n ≤ e) (hve : ε.axpy ≤ e) (he : e ≤ 1 / 100)
    (ha : 0 < a) (hp : 0 < p) (hAspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hPspec : spectrum ℝ P ⊆ Set.Icc p p') (hAprec : 3 * e * a' ≤ a)
    (hPprec : 3 * e * p' ≤ p) (hOe : O.ε ≤ e) (hb : b ≠ 0)
    {τ : Tape ℝ} {μ : Mem ℝ} {x r z v : ℕ × ℕ}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxv : x.1 ≠ v.1)
    (hrz : r.1 ≠ z.1) (hrv : r.1 ≠ v.1) (hzv : z.1 ≠ v.1)
    (hl : μ.Live [x, r, z, v])
    (hstate : StoresState id n x r z v ⟨0, b, O.mulVec b, O.mulVec b⟩ μ)
    (hroom : μ.Room [x, r, z, v] [n, n, n, n]) :
    Writes .total I τ step (Env.frame [n] [x, r, z, v, x, r, z, v])
      (Fp.blocks [x, r, z, v] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ R : PCGRun n 1,
        R.A = A ∧ R.M = P ∧ HEq R.preconditioner O ∧ R.b = b ∧ R.ε = e ∧
        StoresState id n x r z v (R.state 1) μ') μ := by
  have hAT : Aᵀ = A := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hPT : Pᵀ = P := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.isHermitian
  have hm := margins_zero_start_of_spectrum_subset_Icc hAT hPT ha hp hAspec hPspec
    (hu.trans hue) hAprec hPprec hd hde hem hOe hb
  refine (step_writes hS hF hB hok hOp hOracle hxr hxz hxv hrz hrv hzv hl hstate hm
    hroom).mono le_rfl ?_
  rintro μ' _ ⟨hpos, next, rho, rho', hstored, hbounds⟩
  obtain ⟨R, hRA, hRM, hRO, hRb, hRe, hRn, _, _⟩ :=
    hbounds.exists_pcgRun_one hA hP hu hd hv hem hue hde hve he hp hPspec hPprec hOe
  exact ⟨hpos, R, hRA, hRM, hRO, hRb, hRe, hRn.symm ▸ hstored⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
