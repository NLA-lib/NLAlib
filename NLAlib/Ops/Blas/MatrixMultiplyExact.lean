/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.MatrixMultiply
public import NLAlib.Ops.Catalog.Orth

/-!
# Exact mathematical meaning of scalar matrix multiplication

The machine-word result of the actual column-major scalar product decodes to the usual
matrix product under `ExactModel`. This is a mathematical consequence of the shared streamed
accumulation, not an additional primitive contract or execution assumption. Empty dimensions
are included. Padding defaults are the same on both sides, so no list-length premise is needed.

## Main results

* `NLAlib.Ops.ScalarMatrix.map_wordMatrix`: decode the actual word product as matrix multiplication.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarMatrix

variable {K : Type} [Inhabited K] {M : Machine K} {dec : K → ℝ}

omit [Inhabited K] in
private theorem decode_sumWord (hM : ExactModel dec M) (xs ys : ℕ → K) (n : ℕ) :
    dec (ScalarProducts.sumWord M xs ys n) =
      ∑ q ∈ Finset.range n, dec (xs q) * dec (ys q) := by
  induction n with
  | zero => simpa [ScalarProducts.sumWord] using hM.lit 0
  | succ n ih =>
    rw [ScalarProducts.sumWord, hM.add, hM.mul, ih, Finset.sum_range_succ]

/-- Exact scalar arithmetic turns the same packed word product into ordinary multiplication
of the two decoded matrices, without rank, nonzero-size or initialized-padding assumptions. -/
theorem map_wordMatrix (hM : ExactModel dec M) (rows inner cols : ℕ) (as bs : List K) :
    (wordMatrix M rows inner cols as bs).map dec =
      decodeMatrix dec rows inner as * decodeMatrix dec inner cols bs := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  let f := fun q => dec (vec as (q * rows + i)) * dec (vec bs (j * inner + q))
  calc
    dec (wordMatrix M rows inner cols as bs i j) = ∑ q ∈ Finset.range inner, f q := by
      rw [wordMatrix, columnEntry, decode_sumWord hM]
      apply Finset.sum_congr rfl
      intro q hq
      have hq' : q < inner := Finset.mem_range.mp hq
      simp [f, rowWords, vec, hq', List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hq', List.getElem?_drop, Nat.mul_comm]
    _ = ∑ q : Fin inner, f q := (Fin.sum_univ_eq_sum_range f inner).symm
    _ = ∑ q : Fin inner,
        decodeMatrix dec rows inner as i q * decodeMatrix dec inner cols bs q j := by
      simp only [f, decodeMatrix_apply]

end NLAlib.Ops.ScalarMatrix
