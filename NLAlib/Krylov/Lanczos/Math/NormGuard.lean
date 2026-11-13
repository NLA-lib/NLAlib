/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Decoded
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Safe norm and normalization guards

A rounded self-dot with error below one is positive on a nonzero decoded vector. A square
root with relative error below one preserves that positivity, supplying the divisor guard.
Zero vectors produce zero norms even though the norm contract is stated through an
intermediate self-dot.

## Main results

* `NLAlib.Ops.StdModel.dec_sqrt_pos`: positivity of the computed square root on its domain.
* `NLAlib.Ops.IsNrm2Err.dec_pos_iff`: the computed norm detects decoded zero vectors.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type} [Inhabited K] {dec : K → ℝ}

omit [Inhabited K] in
/-- A relative-error square root preserves strict positivity when its error is below one. -/
theorem StdModel.dec_sqrt_pos {u : ℝ} {M : Machine K} (hM : StdModel u dec M)
    (hu : u < 1) {a : K} (ha : 0 < dec a) : 0 < dec (M.sqrt a) := by
  have hs := hM.sqrt a (le_of_lt ha)
  have hp : 0 < √(dec a) := Real.sqrt_pos.mpr ha
  have hm := mul_lt_mul_of_pos_right hu hp
  have hl := neg_abs_le (dec (M.sqrt a) - √(dec a))
  linarith

/-- A zero decoded vector forces both the norm's intermediate self-dot and final norm to zero. -/
theorem IsNrm2Err.eq_zero_of_decoded_eq_zero {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hx : decv dec n xs = 0) : dec ν = 0 := by
  obtain ⟨σ, hσ, hν⟩ := h
  have hσ0 : dec σ = 0 := by simpa [hx] using hσ.decoded
  have he := hν (by rw [hσ0])
  simpa [hσ0] using he

/-- A computed norm of a nonzero decoded vector is positive when both error parameters are
below one. This supplies the nonzero divisor for the subsequent vector scaling. -/
theorem IsNrm2Err.dec_pos_of_ne_zero {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hd : ed < 1) (hs : es < 1)
    (hx : decv dec n xs ≠ 0) : 0 < dec ν := by
  obtain ⟨σ, hσ, hν⟩ := h
  have hσp := hσ.self_pos_of_ne_zero hd hx
  have he := hν (le_of_lt hσp)
  have hp : 0 < √(dec σ) := Real.sqrt_pos.mpr hσp
  have hm := mul_lt_mul_of_pos_right hs hp
  have hl := neg_abs_le (dec ν - √(dec σ))
  linarith

/-- Under the explicit small-error conditions, a norm positivity test succeeds exactly for a
nonzero decoded vector. Failed tests are genuine zero-vector exits, rather than unsafe divides. -/
theorem IsNrm2Err.dec_pos_iff {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hd : ed < 1) (hs : es < 1) :
    0 < dec ν ↔ decv dec n xs ≠ 0 := by
  constructor
  · intro hp hz
    exact hp.ne' (h.eq_zero_of_decoded_eq_zero hz)
  · exact h.dec_pos_of_ne_zero hd hs

/-- At zero dot and square-root error, the computed norm is the exact Euclidean norm. -/
theorem IsNrm2Err.eq_norm {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec 0 0 n (vec xs) ν) :
    dec ν = ‖WithLp.toLp 2 (decv dec n xs)‖ := by
  obtain ⟨σ, hσ, hν⟩ := h
  have hσeq : dec σ = decv dec n xs ⬝ᵥ decv dec n xs := by
    simpa [sub_eq_zero] using hσ.decoded
  have hnorm : dec σ = ‖WithLp.toLp 2 (decv dec n xs)‖ ^ 2 :=
    hσeq.trans (EuclideanSpace.norm_toLp_sq_eq_dotProduct_self _).symm
  have hs := hν (by rw [hnorm]; positivity)
  have hνeq : dec ν = √(dec σ) := by simpa [sub_eq_zero] using hs
  rw [hνeq, hnorm, Real.sqrt_sq (norm_nonneg _)]

/-- Extract the real self-dot and square-root bounds from an actual computed norm. The
self-dot allowance below one makes its decoded input nonnegative, including zero vectors. -/
theorem IsNrm2Err.dot_sqrt_bounds {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hd : ed < 1) :
    ∃ σ : ℝ, 0 ≤ σ ∧
      |σ - ‖WithLp.toLp 2 (decv dec n xs)‖ ^ 2| ≤
        ed * ‖WithLp.toLp 2 (decv dec n xs)‖ ^ 2 ∧
      |dec ν - Real.sqrt σ| ≤ es * Real.sqrt σ := by
  obtain ⟨σ, hσ, hν⟩ := h
  have hσnonneg : 0 ≤ dec σ := by
    by_cases hz : decv dec n xs = 0
    · have he : dec σ = 0 := by simpa [hz] using hσ.decoded
      rw [he]
    · exact (hσ.self_pos_of_ne_zero hd hz).le
  have hsum : (∑ i : Fin n, |decv dec n xs i * decv dec n xs i|) =
      decv dec n xs ⬝ᵥ decv dec n xs :=
    Finset.sum_congr rfl fun _ _ => abs_of_nonneg (mul_self_nonneg _)
  refine ⟨dec σ, hσnonneg, ?_, hν hσnonneg⟩
  simpa only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hsum] using hσ.decoded

/-- The actual computed norm is nonnegative and has relative norm error at most the dot
allowance plus the square-root allowance times one plus the dot allowance. Both primitive
allowances are below one; the square-root allowance is nonnegative. [Higham2002, §3.1]. -/
theorem IsNrm2Err.norm_error_bounds {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hd : ed < 1) (hes : 0 ≤ es) (hs : es < 1) :
    0 ≤ dec ν ∧ |dec ν - ‖WithLp.toLp 2 (decv dec n xs)‖| ≤
      (ed + es * (1 + ed)) * ‖WithLp.toLp 2 (decv dec n xs)‖ := by
  have hn : 0 ≤ dec ν := by
    by_cases hz : decv dec n xs = 0
    · simpa only [h.eq_zero_of_decoded_eq_zero hz] using (le_refl (0 : ℝ))
    · exact (h.dec_pos_of_ne_zero hd hs hz).le
  obtain ⟨σ, hσ, hdot, hsqrt⟩ := h.dot_sqrt_bounds hd
  exact ⟨hn, by simpa only [abs_sub_comm] using
    EuclideanSpace.abs_norm_sub_le_of_self_dot_sqrt hes hσ hdot hsqrt⟩

end NLAlib.Ops
