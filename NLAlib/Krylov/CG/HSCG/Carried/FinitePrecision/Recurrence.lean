/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Bounds
public import NLAlib.Krylov.FinitePrecision.CGRunConstruction

/-!
# Existing CG runs extracted from rounded Ops recurrences

The rounded program's local bounds produce the existing mathematical run records. The
construction retains the actual decoded vectors and residual cache. It neither assumes a
successful program execution nor creates a parallel recurrence model.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.RoundBounds.exists_cgRun_one` starts a run.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.RoundBounds.exists_cgRun_succ` extends a run.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open scoped Matrix

/-- The first rounded zero-start recurrence and its computed initial self-dot determine an
existing one-step CGRun, including actual final vectors and cache. [Greenbaum1997SIMAX, §2]. -/
theorem RoundBounds.exists_cgRun_one {n : ℕ} {em u ed ea e : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {next : CGState ℝ (Fin n)}
    {rho rho' : ℝ} (h : RoundBounds em u ed ea A ⟨0, b, b⟩ next rho rho')
    (hA : Aᵀ = A) (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) (he : e ≤ 1 / 100)
    (hcache : |rho - b ⬝ᵥ b| ≤ ed * ∑ i, |b i * b i|) :
    ∃ R : CGRun n 1, R.A = A ∧ R.b = b ∧ R.ε = e ∧
      (⟨R.x 1, R.r 1, R.p 1⟩ : CGState ℝ (Fin n)) = next ∧ R.ν 1 = rho' := by
  obtain ⟨q, curv, alpha, beta, theta, eg, eb, hmv, hrho, hcurv, htheta, hthetae,
    hc, halpha, hege, hbeta, hebe, hx, hr, hp⟩ := h.exists_run_errors hu hd ha hem hue hde hae
  obtain ⟨theta0, htheta0, htheta0eq⟩ := self_dot_relative hd b hcache
  let R := CGRun.ofOneStep n A b next q e rho rho' theta0 theta curv alpha
    eg beta eb hA (hu.trans hue) he htheta0eq htheta (htheta0.trans hde) hthetae
    hrho hcurv (by simpa using hmv)
    hc halpha hege hbeta hebe
    (by simpa using hx) hr hp
  exact ⟨R, rfl, rfl, rfl, by cases next; rfl, rfl⟩

/-- A rounded recurrence extends an already extracted existing run without assuming another
successful execution. Every previous value is retained by its pure append constructor.
[Greenbaum1997SIMAX, §2]. -/
theorem RoundBounds.exists_cgRun_succ {n k : ℕ} (R : CGRun n k) {em u ed ea : ℝ}
    {next : CGState ℝ (Fin n)} {rho' : ℝ}
    (h : RoundBounds em u ed ea R.A ⟨R.x k, R.r k, R.p k⟩ next (R.ν k) rho')
    (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hem : em ≤ R.ε) (hue : u ≤ R.ε) (hde : ed ≤ R.ε) (hae : ea ≤ R.ε) :
    ∃ S : CGRun n (k + 1), S.A = R.A ∧ S.b = R.b ∧ S.ε = R.ε ∧
      (⟨S.x (k + 1), S.r (k + 1), S.p (k + 1)⟩ : CGState ℝ (Fin n)) = next ∧
      S.ν (k + 1) = rho' := by
  obtain ⟨q, curv, alpha, beta, theta, eg, eb, hmv, hrho, hcurv, htheta, hthetae,
    hc, halpha, hege, hbeta, hebe, hx, hr, hp⟩ := h.exists_run_errors hu hd ha hem hue hde hae
  obtain ⟨S, hA, hb, he, hx', hr', hp', hnu, _⟩ := R.exists_extend next q
    rho' theta curv alpha eg beta eb hrho hcurv htheta hthetae
    (by simpa using hmv)
    hc halpha hege hbeta hebe hx hr hp
  refine ⟨S, hA, hb, he, ?_, ?_⟩
  · rw [hx', hr', hp']
    simp only [Function.update_self]
  · rw [hnu, Function.update_self]

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
