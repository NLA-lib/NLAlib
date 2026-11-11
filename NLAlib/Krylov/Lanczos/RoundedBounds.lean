/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Math.RoundedLocal
public import NLAlib.Krylov.Lanczos.Math.NormGuard

/-!
# Decoded normalization defects for Lanczos

Actual norm and reciprocal-scaling contracts imply the Euclidean normalization defect and
near-unit estimate required by the established finite-precision run model. The bound is
computed from primitive tolerances, rather than assumed as an output property.

## Main results

* `NLAlib.Krylov.Lanczos.nrm2_scal_bounds` connects decoded primitive errors to norm defects.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

/-- A rounded self-dot/square-root norm and rounded vector division imply the normalization
residual and a near-unit output whenever the stored norm is nonzero. Zero norm is included. -/
theorem nrm2_scal_bounds {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
    {ed es ec : ℝ} {zs qs : List K} {β : K}
    (hed : 0 ≤ ed) (hes : 0 ≤ es) (hec : 0 ≤ ec)
    (hn : IsNrm2Err dec ed es n (vec zs) β)
    (hs : IsScalErr dec ec n β (vec zs) (vec qs)) (hg : ed + es * (1 + ed) < 1) :
    0 ≤ dec β ∧
      ‖WithLp.toLp 2 (decv dec n zs - dec β • decv dec n qs)‖ ≤
        ec * ‖WithLp.toLp 2 (decv dec n zs)‖ ∧
      (dec β ≠ 0 → let t := (ec + (ed + es * (1 + ed))) / (1 - (ed + es * (1 + ed)))
        |‖WithLp.toLp 2 (decv dec n qs)‖ ^ 2 - 1| ≤ t * (2 + t)) := by
  obtain ⟨σ, hσ, hβ⟩ := hn
  have hd : ed < 1 := by nlinarith [mul_nonneg hes (by linarith : 0 ≤ 1 + ed)]
  have hσnonneg : 0 ≤ dec σ := by
    by_cases hz : decv dec n zs = 0
    · have he : dec σ = 0 := by simpa [hz] using hσ.decoded
      rw [he]
    · exact (hσ.self_pos_of_ne_zero hd hz).le
  have hsum : (∑ i : Fin n, |decv dec n zs i * decv dec n zs i|) =
      decv dec n zs ⬝ᵥ decv dec n zs := by
    exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (mul_self_nonneg _)
  have hdot : |dec σ - ‖WithLp.toLp 2 (decv dec n zs)‖ ^ 2| ≤
      ed * ‖WithLp.toLp 2 (decv dec n zs)‖ ^ 2 := by
    simpa only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hsum] using hσ.decoded
  exact normalization_bounds_of_self_dot_sqrt_div hed hes hec hσnonneg hdot (hβ hσnonneg)
    (fun hb i => by simpa only [abs_sub_comm] using hs.decoded hb i) hg

end NLAlib.Krylov.Lanczos
