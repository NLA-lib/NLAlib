/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Decoded

/-!
# Safe norm and normalization guards

A rounded self-dot with error below one is positive on a nonzero decoded vector. A square
root with relative error below one preserves that positivity, supplying the divisor guard.
Zero vectors produce zero norms even though the norm contract is stated through an
intermediate self-dot.

## Main results

* `NLAlib.Ops.StdModel.sqrt_pos`: positivity of the computed square root on its domain.
* `NLAlib.Ops.IsNrm2Err.pos_iff`: the computed norm detects decoded zero vectors.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type} [Inhabited K] {dec : K → ℝ}

omit [Inhabited K] in
/-- A relative-error square root preserves strict positivity when its error is below one. -/
theorem StdModel.sqrt_pos {u : ℝ} {M : Machine K} (hM : StdModel u dec M)
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
theorem IsNrm2Err.pos_of_ne_zero {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
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
theorem IsNrm2Err.pos_iff {ed es : ℝ} {n : ℕ} {xs : List K} {ν : K}
    (h : IsNrm2Err dec ed es n (vec xs) ν) (hd : ed < 1) (hs : es < 1) :
    0 < dec ν ↔ decv dec n xs ≠ 0 := by
  constructor
  · intro hp hz
    exact hp.ne' (h.eq_zero_of_decoded_eq_zero hz)
  · exact h.pos_of_ne_zero hd hs

end NLAlib.Ops
