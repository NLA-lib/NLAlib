/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedHistory
public import NLAlib.Krylov.Lanczos.Reorth.RoundedOrthogonality
public import NLAlib.Krylov.FinitePrecision.LanczosReorthStep

/-!
# Orthogonalization guarantees for the final rounded Lanczos history

The actual transition witnesses retain the vectors before and after both classical passes,
pre/post norms, normalization, and the final archived basis. Their proven local budgets give
the existing orthogonalization guarantee without replaying execution. Strict admissibility
of a global reorthogonalized Lanczos prefix remains a separate condition on computed values.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Local.exists_isOrthErr`: actual transition witnesses
  and orthogonalization against the archived basis.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.History.exists_isOrthErr`: that guarantee for every
  executed step, with all arguments expressed using the same final archive.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ} {e : Blas1Err}

/-- The actual raw and reduced vectors of one executed transition meet the existing
orthogonalization interface. The same witnesses retain its numerical update, both computed
norms and normalization into the archived next vector. The allowance is derived from dot and
sequential-AXPY errors. No prior success, near-orthogonality conclusion or nonbreakdown is
assumed; near-basis accuracy is the antecedent inside `IsOrthErr`. -/
theorem Local.exists_isOrthErr {done : ℕ} {z : Lanczos.Rounded.Values n}
    {q : Fin n → ℝ} {a b nu η c : ℝ} (h : Local dec A em u e done z q a b nu)
    (hd : 0 ≤ e.dot n) (ha : 0 ≤ e.axpy) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100)
    (hc : c ≤ 1 / 100)
    (hbudget : (done + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (done + 1) - 1) *
        (1 + (done + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∃ first raw reduced ys : List K, ∃ norm beta' : K, ∃ coefficients : Fin (done + 1) → ℝ,
      q = decv dec n ys ∧ b = dec beta' ∧ nu = dec norm ∧
      Lanczos.Rounded.UpdateBounds em (e.dot n) e.axpy A (z.v done) (z.v (done + 1))
        (decv dec n first) (decv dec n raw) (z.beta done) a ∧
      IsNrm2Err dec (e.dot n) u n (vec raw) norm ∧
      IsNrm2Err dec (e.dot n) u n (vec reduced) beta' ∧
      IsScalErr dec e.scal n beta' (vec reduced) (vec ys) ∧
      (decv dec n reduced = 0 → decv dec n ys = 0) ∧
      IsOrthErr η (2 * c) (3 * c) (2 * (η + c) ^ 2)
        (LanczosReorthRun.basisOf z.v (done + 1)) (decv dec n raw) coefficients
        (decv dec n reduced) := by
  obtain ⟨ps, qs, basis, first, raw, reduced, ys, beta, alpha, norm, beta',
    hps, hqs, hbeta, hQ, hq, halpha, hbn, hnu, hbounds, hnorm, hpasses, hn, hs, hzero⟩ := h
  obtain ⟨mid, h₁, h₂, _, _, horth⟩ := hpasses.isOrthErr hd ha hη₀ hη hc
    (by simpa only [Nat.cast_add, Nat.cast_one] using hbudget)
  have hQeq : basisMatrix dec n basis (done + 1) =
      LanczosReorthRun.basisOf z.v (done + 1) := by
    ext i j
    exact congrFun (hQ j j.isLt) i
  rw [hQeq] at horth
  refine ⟨first, raw, reduced, ys, norm, beta', _, hq, hbn, hnu, ?_, hnorm, hn, hs, hzero, horth⟩
  simpa only [hps, hqs, hbeta, ← halpha] using hbounds

/-- Every actual transition in the final history inherits local two-pass orthogonalization
with its own actual vector/norm witnesses and the same final archived basis. The size-only
budget is required for each executed prefix; strict tau-admissibility is not asserted. -/
theorem History.exists_isOrthErr {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    {η c : ℝ} (h : History dec A rhs em u E e done z nus)
    (hd : 0 ≤ e.dot n) (ha : 0 ≤ e.axpy) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100)
    (hc : c ≤ 1 / 100)
    (hbudget : ∀ j < done, (j + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (j + 1) - 1) *
        (1 + (j + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∀ j < done, ∃ first raw reduced ys : List K, ∃ norm beta' : K,
      ∃ coefficients : Fin (j + 1) → ℝ,
      z.v (j + 2) = decv dec n ys ∧ z.beta (j + 1) = dec beta' ∧ nus (j + 1) = dec norm ∧
      Lanczos.Rounded.UpdateBounds em (e.dot n) e.axpy A (z.v j) (z.v (j + 1))
        (decv dec n first) (decv dec n raw) (z.beta j) (z.alpha (j + 1)) ∧
      IsNrm2Err dec (e.dot n) u n (vec raw) norm ∧
      IsNrm2Err dec (e.dot n) u n (vec reduced) beta' ∧
      IsScalErr dec e.scal n beta' (vec reduced) (vec ys) ∧
      (decv dec n reduced = 0 → decv dec n ys = 0) ∧
      IsOrthErr η (2 * c) (3 * c) (2 * (η + c) ^ 2)
        (LanczosReorthRun.basisOf z.v (j + 1)) (decv dec n raw) coefficients
        (decv dec n reduced) := by
  intro j hj
  exact (h.local j hj).exists_isOrthErr hd ha hη₀ hη hc (hbudget j hj)

/-- Actual numerical witnesses of a rounded reorthogonalized transition supply the same
pure `RoundedStep` interface used by the existing finite-precision run theory. Every norm,
update, normalization and orthogonalization clause follows from its primitive budgets. -/
theorem Local.exists_roundedStep {done : ℕ} {z : Lanczos.Rounded.Values n}
    {q : Fin n → ℝ} {a b nu η c : ℝ} (h : Local dec A em u e done z q a b nu)
    (hprec : Lanczos.Rounded.Precision em u E e n)
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hbudget : (done + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (done + 1) - 1) *
        (1 + (done + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∃ U W Z Z' : Fin n → ℝ, ∃ H : Fin (done + 1) → ℝ,
      LanczosReorthImplementation.RoundedStep A E
        (IsOrthErr η (2 * c) (3 * c) (2 * (η + c) ^ 2))
        (LanczosReorthRun.basisOf z.v (done + 1)) (z.v done) (z.v (done + 1)) q
        (z.beta done) a nu b U W Z Z' H := by
  obtain ⟨first, raw, reduced, ys, norm, beta', coefficients,
    hq, hb, hnu, hupdate, hnorm, hn, hs, hzero, horth⟩ :=
    h.exists_isOrthErr hprec.dot_nonneg hprec.axpy_nonneg hη₀ hη hc hbudget
  obtain ⟨mv, hmv, hw, ha, hz⟩ := hupdate.normwise hprec
  obtain ⟨hnonneg, hnuerr⟩ := hprec.nrm2_bounds hnorm
  obtain ⟨_, hbetaerr⟩ := hprec.nrm2_bounds hn
  obtain ⟨_, hscale, hunit⟩ := hprec.norm_bounds hn hs
  refine ⟨mv, decv dec n first, decv dec n raw, decv dec n reduced, coefficients,
    ⟨hmv, hw, ha, hz, ?_, ?_, horth, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [hnu] using hnonneg
  · simpa only [hnu] using hnuerr
  · simpa only [hb] using hbetaerr
  · simpa only [hq, hb] using hscale
  · simpa only [hq, hb] using hunit
  · intro hbzero
    have hz : decv dec n reduced = 0 := by
      by_contra hne
      exact (hn.dec_pos_of_ne_zero hprec.dot_lt hprec.scalar_lt hne).ne' (hb ▸ hbzero)
    exact hq.trans (hzero hz)

/-- Each executed step of the final history has a pure rounded-step witness with exactly its
archived vectors, alpha, beta and saved norm. Strict admissibility is left to prefix selection. -/
theorem History.exists_roundedStep {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    {η c : ℝ} (h : History dec A rhs em u E e done z nus)
    (hprec : Lanczos.Rounded.Precision em u E e n)
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 100) (hc : c ≤ 1 / 100)
    (hbudget : ∀ j < done, (j + 1 + 1 : ℝ) * e.dot n * (1 + η) ^ 2 +
      ((1 + e.axpy) ^ (j + 1) - 1) *
        (1 + (j + 1 : ℝ) * (1 + e.dot n) * (1 + η) ^ 2) ≤ c) :
    ∀ j < done, ∃ U W Z Z' : Fin n → ℝ, ∃ H : Fin (j + 1) → ℝ,
      LanczosReorthImplementation.RoundedStep A E
        (IsOrthErr η (2 * c) (3 * c) (2 * (η + c) ^ 2))
        (LanczosReorthRun.basisOf z.v (j + 1)) (z.v j) (z.v (j + 1)) (z.v (j + 2))
        (z.beta j) (z.alpha (j + 1)) (nus (j + 1)) (z.beta (j + 1)) U W Z Z' H := by
  intro j hj
  exact (h.local j hj).exists_roundedStep hprec hη₀ hη hc (hbudget j hj)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
