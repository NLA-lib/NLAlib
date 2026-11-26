/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Upper
public import NLAlib.Ops.Catalog.Orth

/-!
# Exact systems recovered from substitution traces

At zero unit roundoff, the shared backward-error theorems force every perturbation entry to
zero. Forward and back substitution therefore solve their projected triangular systems
exactly. These are numerical consequences of the existing traces, independent of memory or
successful-execution assumptions; factorization-and-solve routines consume them.

## Main results

* `NLAlib.Computation.IsSubstTrace.mulVec_eq`: exact forward substitution.
* `NLAlib.Computation.IsBackSubstTrace.mulVec_eq`: exact transposed-lower substitution.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix

/-- A forward-substitution trace at zero roundoff, with nonzero diagonal, solves the
lower-triangular system exactly, including order zero. -/
theorem IsSubstTrace.mulVec_eq {n : ℕ} {L : ℕ → ℕ → ℝ} {b x : ℕ → ℝ}
    (h : IsSubstTrace (fun _ => RelErr 0) L b n x) (hd : ∀ i < n, L i i ≠ 0) :
    lowerOf L n *ᵥ (fun i : Fin n => x i) = fun i : Fin n => b i := by
  obtain ⟨D, hD, hs⟩ := h.exists_lower_mulVec_eq hd (le_refl 0) zero_lt_one
  have hz : D = 0 := by
    ext i j
    apply abs_nonpos_iff.mp
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self, zero_mul] using hD i j
  simpa only [hz, add_zero] using hs

/-- A back-substitution trace at zero roundoff, with nonzero diagonal, solves the transpose
of its lower-triangular argument exactly, including order zero. -/
theorem IsBackSubstTrace.mulVec_eq {n : ℕ} {L : ℕ → ℕ → ℝ} {b x : ℕ → ℝ}
    (h : IsBackSubstTrace 0 L b n x) (hd : ∀ i < n, L i i ≠ 0) :
    (lowerOf L n)ᵀ *ᵥ (fun i : Fin n => x i) = fun i : Fin n => b i := by
  obtain ⟨D, hD, hs⟩ := h.exists_upper_mulVec_eq hd (le_refl 0) zero_lt_one
  have hz : D = 0 := by
    ext i j
    apply abs_nonpos_iff.mp
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self, zero_mul] using hD i j
  simpa only [hz, add_zero] using hs

end NLAlib.Computation

namespace NLAlib.TriangularSolve

open Ops Computation
open scoped Matrix

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
  {as bs xs : List K} {τ : Tape K}

/-- Projecting the decoded words of a lower triangular matrix retains that matrix. -/
theorem lowerOf_eq_decodeMatrix (as : List K)
    (hL : (decodeMatrix dec n n as).IsLowerTriangular) :
    lowerOf (fun i j => dec (vec as (j * n + i))) n = decodeMatrix dec n n as := by
  ext i j
  change (if j ≤ i then dec (vec as (j * n + i)) else 0) = _
  by_cases hij : j ≤ i
  · simp only [if_pos hij, decodeMatrix_apply]
  · rw [if_neg hij, hL (lt_of_not_ge hij)]

/-- The zero-roundoff forward-substitution postcondition solves the actual decoded lower
matrix, with its stored nonzero diagonal. This includes an empty matrix. -/
theorem forwardSpec_mulVec_eq
    (hpost : (forwardSpec 0 dec).post [n] τ [as, bs] [xs])
    (hL : (decodeMatrix dec n n as).IsLowerTriangular)
    (hd : ∀ i < n, dec (vec as (i * n + i)) ≠ 0) :
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs := by
  have htr : IsSubstTrace (fun _ => RelErr 0) (fun i j => dec (vec as (j * n + i)))
      (fun i => dec (vec bs i)) n (fun i => dec (vec xs i)) := hpost
  rw [← lowerOf_eq_decodeMatrix as hL]
  exact htr.mulVec_eq hd

/-- The zero-roundoff transposed-lower postcondition solves the transpose of the actual
decoded lower matrix, with its stored nonzero diagonal, including order zero. -/
theorem backwardSpec_mulVec_eq
    (hpost : (backwardSpec 0 dec).post [n] τ [as, bs] [xs])
    (hL : (decodeMatrix dec n n as).IsLowerTriangular)
    (hd : ∀ i < n, dec (vec as (i * n + i)) ≠ 0) :
    (decodeMatrix dec n n as)ᵀ *ᵥ decv dec n xs = decv dec n bs := by
  have htr : IsBackSubstTrace 0 (fun i j => dec (vec as (j * n + i)))
      (fun i => dec (vec bs i)) n (fun i => dec (vec xs i)) := hpost
  rw [← lowerOf_eq_decodeMatrix as hL]
  exact htr.mulVec_eq hd

/-- The zero-roundoff direct upper-substitution postcondition solves the actual decoded
upper matrix, with its stored nonzero diagonal, including order zero. -/
theorem upperSpec_mulVec_eq
    (hpost : (upperSpec 0 dec).post [n] τ [as, bs] [xs])
    (hU : (decodeMatrix dec n n as).IsUpperTriangular)
    (hd : ∀ i < n, dec (vec as (i * n + i)) ≠ 0) :
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs := by
  have htr : IsBackSubstTrace 0 (fun i j => dec (vec as (i * n + j)))
      (fun i => dec (vec bs i)) n (fun i => dec (vec xs i)) := hpost
  have he : (lowerOf (fun i j => dec (vec as (i * n + j))) n)ᵀ =
      decodeMatrix dec n n as := by
    ext i j
    change (if i ≤ j then dec (vec as (j * n + i)) else 0) = _
    by_cases hij : i ≤ j
    · simp only [if_pos hij, decodeMatrix_apply]
    · rw [if_neg hij, hU (lt_of_not_ge hij)]
  rw [← he]
  exact htr.mulVec_eq hd

end NLAlib.TriangularSolve
