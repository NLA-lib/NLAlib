/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded
public import NLAlib.Krylov.Lanczos.RoundedBounds

/-!
# Primitive precision for a complete rounded Lanczos run

The same input bounds cover initialization and every active round. Nearly unit output vectors
are derived from norm and division contracts, including the terminal zero-vector case.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Precision`: shared primitive error assumptions.
* `NLAlib.Krylov.Lanczos.Rounded.Precision.norm_bounds`: normalized output defects.
* `NLAlib.Krylov.Lanczos.Rounded.UpdateBounds.normwise`: decoded update defects.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

/-- Primitive errors dominated by one small local Lanczos error allowance. -/
structure Precision (em u E : ℝ) (e : Blas1Err) (n : ℕ) : Prop where
  /-- Nonnegative common allowance. -/
  nonneg : 0 ≤ E
  /-- Local-error range of the existing LanczosRun. -/
  small : E ≤ 1 / 100
  /-- Nonnegative scalar allowance. -/
  scalar_nonneg : 0 ≤ u
  /-- Nonnegative dot allowance. -/
  dot_nonneg : 0 ≤ e.dot n
  /-- Nonnegative axpy allowance. -/
  axpy_nonneg : 0 ≤ e.axpy
  /-- Nonnegative scaling allowance. -/
  scal_nonneg : 0 ≤ e.scal
  /-- Self-dot and square root preserve positivity. -/
  gamma_lt : e.dot n + u * (1 + e.dot n) < 1
  /-- Matvec defect is dominated by the common allowance. -/
  matvec_le : em ≤ E
  /-- Dot defect is dominated by the common allowance. -/
  dot_le : e.dot n ≤ E
  /-- Axpy defect is dominated by the common allowance. -/
  axpy_le : e.axpy ≤ E
  /-- Division defect is dominated by the common allowance. -/
  scal_le : e.scal ≤ E
  /-- Derived squared-norm error is dominated by the common allowance. -/
  unit_le : let g := e.dot n + u * (1 + e.dot n)
    let t := (e.scal + g) / (1 - g); t * (2 + t) ≤ E

variable {em u E : ℝ} {e : Blas1Err} {n : ℕ}

/-- Simple input-only budget comparisons discharge the nonlinear normalization condition.
Scalar, dot and division allowances at most E/16 suffice; matvec and axpy may use all of E. -/
theorem Precision.of_budgets (hE : 0 ≤ E) (hsmall : E ≤ 1 / 100)
    (hu : 0 ≤ u) (hd : 0 ≤ e.dot n) (ha : 0 ≤ e.axpy) (hc : 0 ≤ e.scal)
    (hm : em ≤ E) (huE : u ≤ E / 16) (hdE : e.dot n ≤ E / 16)
    (haE : e.axpy ≤ E) (hcE : e.scal ≤ E / 16) : Precision em u E e n := by
  let g := e.dot n + u * (1 + e.dot n)
  have hd1 : e.dot n ≤ 1 := by linarith
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    nlinarith [mul_nonneg hu hd]
  have hgE : g ≤ E / 4 := by
    have hm := mul_le_mul_of_nonneg_left hd1 hu
    dsimp only [g]
    nlinarith
  have hg1 : g < 1 := by linarith
  have hden : 0 < 1 - g := by linarith
  let t := (e.scal + g) / (1 - g)
  have ht0 : 0 ≤ t := div_nonneg (add_nonneg hc hg0) hden.le
  have hEE := mul_nonneg hE (show 0 ≤ 1 / 100 - E by linarith)
  have htE : t ≤ E / 3 := by
    apply (div_le_iff₀ hden).mpr
    have hEg := mul_le_mul_of_nonneg_left hgE hE
    nlinarith
  have ht2 := mul_self_le_mul_self ht0 htE
  have hunit : t * (2 + t) ≤ E := by nlinarith
  exact ⟨hE, hsmall, hu, hd, ha, hc, hg1, hm, by linarith, haE, by linarith, hunit⟩

/-- The scalar square-root error is below one. -/
theorem Precision.scalar_lt (h : Precision em u E e n) : u < 1 := by
  nlinarith [h.gamma_lt, h.dot_nonneg, mul_nonneg h.scalar_nonneg h.dot_nonneg]

/-- The dot error is below one. -/
theorem Precision.dot_lt (h : Precision em u E e n) : e.dot n < 1 := by
  nlinarith [h.gamma_lt, mul_nonneg h.scalar_nonneg (by linarith [h.dot_nonneg] : 0 ≤ 1 + e.dot n)]

/-- The norm error derived from self-dot and square-root rounding is dominated by the
common envelope. This follows from the same normalization budget as the unit-vector bound. -/
theorem Precision.norm_error_le (h : Precision em u E e n) :
    e.dot n + u * (1 + e.dot n) ≤ E := by
  let g := e.dot n + u * (1 + e.dot n)
  let t := (e.scal + g) / (1 - g)
  have hg₀ : 0 ≤ g := add_nonneg h.dot_nonneg
    (mul_nonneg h.scalar_nonneg (by linarith [h.dot_nonneg]))
  have hden : 0 < 1 - g := by dsimp only [g]; linarith [h.gamma_lt]
  have ht₀ : 0 ≤ t := div_nonneg (add_nonneg h.scal_nonneg hg₀) hden.le
  have hgt : g ≤ t := (le_div_iff₀ hden).mpr (by nlinarith [h.scal_nonneg, sq_nonneg g])
  have hunit : t * (2 + t) ≤ E := h.unit_le
  have htE : t ≤ E := by nlinarith
  exact hgt.trans htE

/-- An actual computed norm satisfies the common error envelope and is nonnegative.
The proof uses its actual dot/square-root witnesses rather than an assumed norm oracle. -/
theorem Precision.nrm2_bounds {K : Type} [Inhabited K] {dec : K → ℝ}
    (h : Precision em u E e n) {xs : List K} {b : K}
    (hn : IsNrm2Err dec (e.dot n) u n (vec xs) b) :
    0 ≤ dec b ∧ |dec b - ‖WithLp.toLp 2 (decv dec n xs)‖| ≤
      E * ‖WithLp.toLp 2 (decv dec n xs)‖ := by
  obtain ⟨hb, he⟩ := hn.norm_error_bounds h.dot_lt h.scalar_nonneg h.scalar_lt
  exact ⟨hb, he.trans (mul_le_mul_of_nonneg_right h.norm_error_le (norm_nonneg _))⟩

/-- The actual normalized vector has a bounded defect and is nearly unit whenever its
computed norm is nonzero. These facts follow from primitive contracts. -/
theorem Precision.norm_bounds {K : Type} [Inhabited K] {dec : K → ℝ}
    (h : Precision em u E e n) {zs qs : List K} {b : K}
    (hn : IsNrm2Err dec (e.dot n) u n (vec zs) b)
    (hs : IsScalErr dec e.scal n b (vec zs) (vec qs)) :
    0 ≤ dec b ∧ ‖WithLp.toLp 2 (decv dec n zs - dec b • decv dec n qs)‖ ≤
      E * ‖WithLp.toLp 2 (decv dec n zs)‖ ∧
      (dec b ≠ 0 → |‖WithLp.toLp 2 (decv dec n qs)‖ ^ 2 - 1| ≤ E) := by
  obtain ⟨hb, hd, hv⟩ := nrm2_scal_bounds h.dot_nonneg h.scalar_nonneg h.scal_nonneg hn hs
    h.gamma_lt
  exact ⟨hb, hd.trans (mul_le_mul_of_nonneg_right h.scal_le (norm_nonneg _)),
    fun hb => (hv hb).trans h.unit_le⟩

/-- A computed self-dot used for the guard detects the same zero case as the computed norm. -/
theorem Precision.guard_iff {K : Type} [Inhabited K] {dec : K → ℝ}
    (h : Precision em u E e n) {zs : List K} {b s : K}
    (hn : IsNrm2Err dec (e.dot n) u n (vec zs) b)
    (hd : IsDotErr dec (e.dot n) n (vec zs) (vec zs) s) :
    0 ≤ dec s ∧ (0 < dec s ↔ dec b ≠ 0) := by
  have hp := hn.dec_pos_iff h.dot_lt h.scalar_lt
  by_cases hz : decv dec n zs = 0
  · have hs : dec s = 0 := by simpa [hz] using hd.decoded
    have hb := hn.eq_zero_of_decoded_eq_zero hz
    simp [hs, hb]
  · have hs := hd.self_pos_of_ne_zero h.dot_lt hz
    have hb := hn.dec_pos_of_ne_zero h.dot_lt h.scalar_lt hz
    exact ⟨hs.le, iff_of_true hs hb.ne'⟩

/-- The same componentwise-to-norm conversion serves the first and every later round. -/
theorem UpdateBounds.normwise {A : Matrix (Fin n) (Fin n) ℝ}
    {prev cur first raw : Fin n → ℝ} {beta alpha : ℝ}
    (hb : UpdateBounds em (e.dot n) e.axpy A prev cur first raw beta alpha)
    (h : Precision em u E e n) :
    ∃ mv : Fin n → ℝ,
    ‖WithLp.toLp 2 (A *ᵥ cur - mv)‖ ≤ E * specNorm A * ‖WithLp.toLp 2 cur‖ ∧
    ‖WithLp.toLp 2 (mv - beta • prev - first)‖ ≤
      E * (‖WithLp.toLp 2 mv‖ + |beta| * ‖WithLp.toLp 2 prev‖) ∧
    |cur ⬝ᵥ first - alpha| ≤ E * ‖WithLp.toLp 2 cur‖ * ‖WithLp.toLp 2 first‖ ∧
    ‖WithLp.toLp 2 (first - alpha • cur - raw)‖ ≤
      E * (‖WithLp.toLp 2 first‖ + |alpha| * ‖WithLp.toLp 2 cur‖) := by
  obtain ⟨mv, hmv, hw', ha', hz'⟩ := hb
  have hw := EuclideanSpace.norm_sub_add_smul_le_of_componentwise (a := -beta)
    (x := prev) (y := mv) (z := first) h.axpy_nonneg (fun i => by
      simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
        ← sub_eq_add_neg, abs_neg, abs_sub_comm] using hw' i)
  have hz := EuclideanSpace.norm_sub_add_smul_le_of_componentwise (a := -alpha)
    (x := cur) (y := first) (z := raw) h.axpy_nonneg (fun i => by
      simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
        ← sub_eq_add_neg, abs_neg, abs_sub_comm] using hz' i)
  have ha := EuclideanSpace.abs_dotProduct_sub_le_of_componentwise h.dot_nonneg
    (by simpa only [abs_sub_comm] using ha')
  refine ⟨mv, hmv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h.matvec_le (specNorm_nonneg _)) (norm_nonneg _)),
    ?_, ha.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h.dot_le (norm_nonneg _)) (norm_nonneg _)), ?_⟩
  · simpa only [neg_smul, ← sub_eq_add_neg, abs_neg] using
      hw.trans (mul_le_mul_of_nonneg_right h.axpy_le (by positivity))
  · simpa only [neg_smul, ← sub_eq_add_neg, abs_neg] using
      hz.trans (mul_le_mul_of_nonneg_right h.axpy_le (by positivity))

end NLAlib.Krylov.Lanczos.Rounded
