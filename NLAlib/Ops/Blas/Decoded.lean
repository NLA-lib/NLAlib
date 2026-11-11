/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Operator

/-!
# Decoded vector equations for BLAS1 contracts

The block contracts use natural indices below a length. These lemmas present their conclusions
as equations and bounds on finite decoded vectors for the mathematical layer.

## Main results

* `NLAlib.Ops.dotExactRel_decoded`, `NLAlib.Ops.axpyExactRel_decoded`,
  `NLAlib.Ops.copyRel_decoded`: exact vector equations.
* `NLAlib.Ops.IsDotErr.decoded`: the componentwise dot-product bound over finite vectors.
* `NLAlib.Ops.IsAxpyErr.decoded`, `NLAlib.Ops.IsScalErr.decoded`: the componentwise vector
  bounds used in perturbed recurrences.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}

/-- The dot product of decoded blocks is the sum over their natural indices. -/
theorem dotProduct_decv (xs ys : List K) :
    decv dec n xs ⬝ᵥ decv dec n ys =
      ∑ i ∈ Finset.range n, dec (vec xs i) * dec (vec ys i) := by
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => dec (vec xs i) * dec (vec ys i)) n

/-- An exact dot-product call gives the dot product of the decoded input vectors. -/
theorem dotExactRel_decoded {xs ys : List K} {v : K}
    (h : (dotExactRel dec).rel [n] [xs, ys] [] [[v]]) :
    dec v = decv dec n xs ⬝ᵥ decv dec n ys := by
  simpa [dotExactRel, dotProduct_decv] using h

/-- An exact axpy call gives the vector update on the decoded inputs. -/
theorem axpyExactRel_decoded {a : K} {xs ys zs : List K}
    (h : (axpyExactRel dec).rel [n] [[a], xs, ys] [] [zs]) :
    decv dec n zs = decv dec n ys + dec a • decv dec n xs := by
  funext i
  exact h i i.isLt

/-- An exact copy call preserves the decoded vector. -/
theorem copyRel_decoded {xs ys : List K} (h : (copyRel (K := K)).rel [n] [xs] [] [ys]) :
    decv dec n ys = decv dec n xs := by
  have he : ys = xs := by simpa [copyRel] using h
  rw [he]

/-- The rounded dot-product bound as a statement on finite decoded vectors. -/
theorem IsDotErr.decoded {e : ℝ} {xs ys : List K} {v : K}
    (h : IsDotErr dec e n (vec xs) (vec ys) v) :
    |dec v - decv dec n xs ⬝ᵥ decv dec n ys| ≤
      e * ∑ i : Fin n, |decv dec n xs i * decv dec n ys i| := by
  simpa only [IsDotErr, dotProduct_decv, decv,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => |dec (vec xs i) * dec (vec ys i)|)] using h

/-- The axpy error bound on every component of the decoded finite vectors. -/
theorem IsAxpyErr.decoded {e : ℝ} {a : K} {xs ys zs : List K}
    (h : IsAxpyErr dec e n a (vec xs) (vec ys) (vec zs)) (i : Fin n) :
    |decv dec n zs i - (decv dec n ys i + dec a * decv dec n xs i)| ≤
      e * (|decv dec n ys i| + |dec a * decv dec n xs i|) :=
  h i i.isLt

/-- The division error bound on every decoded component, under the nonzero-divisor guard. -/
theorem IsScalErr.decoded {e : ℝ} {a : K} {xs zs : List K}
    (h : IsScalErr dec e n a (vec xs) (vec zs)) (ha : dec a ≠ 0) (i : Fin n) :
    |decv dec n zs i - decv dec n xs i / dec a| ≤ e * |decv dec n xs i / dec a| :=
  h ha i i.isLt

end NLAlib.Ops
