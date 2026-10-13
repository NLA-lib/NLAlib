/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TraceFunctions

/-!
# Traces of powers and of products of matrix functions

For Hermitian `A` and `B` with unitary diagonalisations, the trace `tr (f(A) g(B))` is a
nonnegative combination of the products `f(λ_i) g(μ_j)`, with weights the squared overlaps of the
eigenvectors. Scalar inequalities in two variables therefore lift to trace inequalities. This file
records the lifting principle and the trace-power inequalities that the moment method and the
method of exchangeable pairs for random matrices use.

## Main results

* `NLAlib.re_trace_cfc_mul_cfc_eq_sum`: the overlap formula.
* `NLAlib.sum_re_trace_cfc_mul_cfc_le_of_forall`: lifting a two-variable inequality.
* `Matrix.IsHermitian.re_trace_pow`, `Matrix.IsHermitian.specNorm_pow_le_re_trace_pow`.
* `NLAlib.re_trace_mul_pow_mul_pow_le`: `tr (C Hˡ C Hᵏ) ≤ tr (C² Hˡ⁺ᵏ)` for even `l + k`.
* `NLAlib.re_trace_cfc_sub_mul_cfc_sub_le`: the mean value trace inequality.
* `NLAlib.re_trace_mul_pow_le_add`: the trace Young inequality for powers.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The overlap formula -/

/-- **The overlap formula.** If `A = U diag(a) Uᴴ` and `B = V diag(b) Vᴴ` with `U`, `V` unitary
(orthonormal columns, as many columns as rows),
then `tr (f(A) g(B)) = ∑ i j, |(Uᴴ V)_{ij}|² f(a_i) g(b_j)`.
Port of `NLAlib.re_trace_pow_mul_pow_eq_sum_overlap`, there for powers over `ℂ`. -/
theorem re_trace_cfc_mul_cfc_eq_sum {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r]
    [DecidableEq s] {A B : Matrix n n 𝕜} {U : Matrix n r 𝕜} {V : Matrix n s 𝕜} {a : r → ℝ}
    {b : s → ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hr : Fintype.card r = Fintype.card n) (hs : Fintype.card s = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ)
    (hB : B = V * Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) * Vᴴ) (f g : ℝ → ℝ) :
    RCLike.re (cfc f A * cfc g B).trace = ∑ i, ∑ j, ‖(Uᴴ * V) i j‖ ^ 2 * (f (a i) * g (b j)) := by
  sorry

/-- **Lifting a two-variable inequality to traces.** If `∑ k, f k x * g k y ≤ ∑ k, f' k x * g' k y`
for all `x` in the spectrum of `A` and `y` in that of `B`, the same inequality holds for the
traces `∑ k, tr (f_k(A) g_k(B))`. [Tropp2015, Proposition 8.3.5]. -/
theorem sum_re_trace_cfc_mul_cfc_le_of_forall {ι : Type*} [Fintype ι] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f g f' g' : ι → ℝ → ℝ}
    (h : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B,
      ∑ k, f k x * g k y ≤ ∑ k, f' k x * g' k y) :
    ∑ k, RCLike.re (cfc (f k) A * cfc (g k) B).trace ≤
      ∑ k, RCLike.re (cfc (f' k) A * cfc (g' k) B).trace := by
  sorry

/-! ### Traces of powers -/

/-- The trace of a power of a Hermitian matrix is the power sum of its eigenvalues.
Port of `NLAlib.re_trace_pow_eq_sum_eigenvalues_pow`, there over `ℂ`. -/
theorem _root_.Matrix.IsHermitian.re_trace_pow {A : Matrix n n 𝕜} (hA : A.IsHermitian) (r : ℕ) :
    RCLike.re (A ^ r).trace = ∑ i ∈ Finset.range (Fintype.card n), eigenvalue A i ^ r := by
  sorry

/-- The trace of an even power of a Hermitian matrix is nonnegative.
Port of `NLAlib.re_trace_pow_nonneg_of_even`. -/
theorem _root_.Matrix.IsHermitian.re_trace_pow_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {r : ℕ} (hr : Even r) : 0 ≤ RCLike.re (A ^ r).trace := by
  sorry

/-- The trace of a power of a positive semidefinite matrix is nonnegative.
Port of `NLAlib.re_trace_pow_nonneg_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.re_trace_pow_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (r : ℕ) : 0 ≤ RCLike.re (A ^ r).trace := by
  sorry

/-- **The moment bound for the spectral norm**: `‖A‖₂^{2q} ≤ tr A^{2q}` for Hermitian `A` and
`q ≥ 1`. This is the first step of the moment method.
Port of `NLAlib.specNorm_pow_two_mul_le_trace_pow`. -/
theorem _root_.Matrix.IsHermitian.specNorm_pow_le_re_trace_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {q : ℕ} (hq : 0 < q) :
    specNorm A ^ (2 * q) ≤ RCLike.re (A ^ (2 * q)).trace := by
  sorry

/-- The trace of a power is at most the dimension times the power of the spectral norm. -/
theorem _root_.Matrix.IsHermitian.re_trace_pow_le_card_mul_specNorm_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (r : ℕ) :
    RCLike.re (A ^ r).trace ≤ Fintype.card n * specNorm A ^ r := by
  sorry

/-! ### Trace inequalities for powers -/

/-- **Rearranging powers inside a trace**: for Hermitian `C`, `H` and `l + k` even,
`tr (C Hˡ C Hᵏ) ≤ tr (C² Hˡ⁺ᵏ)`. [MackeyEtAl2014, §3].
Port of `NLAlib.re_trace_mul_pow_mul_le_trace_sq_mul_pow`, there over `ℂ`. -/
theorem re_trace_mul_pow_mul_pow_le {C H : Matrix n n 𝕜} (hC : C.IsHermitian)
    (hH : H.IsHermitian) {l k : ℕ} (h : Even (l + k)) :
    RCLike.re (C * H ^ l * C * H ^ k).trace ≤ RCLike.re (C ^ 2 * H ^ (l + k)).trace := by
  sorry

/-- **The mean value trace inequality.** For `g` non-decreasing on `s`, `h` with derivative `h'`
convex on `s`, and Hermitian `A`, `B` with spectrum in `s`,
`tr ((g(A) - g(B)) (h(A) - h(B))) ≤ ½ tr ((g(A) - g(B)) (A - B) (h'(A) + h'(B)))`.
[MackeyEtAl2014, Lemma 3.4].
Result: mean-value-trace-inequality -/
theorem re_trace_cfc_sub_mul_cfc_sub_le {g h h' : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s)
    (hh : ∀ x ∈ s, HasDerivWithinAt h (h' x) s x) (hh' : ConvexOn ℝ s h') {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAs : spectrum ℝ A ⊆ s)
    (hBs : spectrum ℝ B ⊆ s) :
    RCLike.re ((cfc g A - cfc g B) * (cfc h A - cfc h B)).trace ≤
      1 / 2 * RCLike.re ((cfc g A - cfc g B) * (A - B) * (cfc h' A + cfc h' B)).trace := by
  sorry

/-- The mean value trace inequality for powers: for Hermitian `H`, `K` and even `m`,
`tr ((H - K)(Hᵐ⁺¹ - Kᵐ⁺¹)) ≤ (m + 1)/2 · tr ((H - K)² (Hᵐ + Kᵐ))`.
[MackeyEtAl2014, Lemma 3.4]. Port of `NLAlib.re_trace_sub_mul_sub_pow_le`, there over `ℂ`. -/
theorem re_trace_sub_mul_pow_sub_pow_le {H K : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hK : K.IsHermitian) {m : ℕ} (hm : Even m) :
    RCLike.re ((H - K) * (H ^ (m + 1) - K ^ (m + 1))).trace ≤
      (m + 1 : ℝ) / 2 * RCLike.re ((H - K) ^ 2 * (H ^ m + K ^ m)).trace := by
  sorry

/-- **The trace Young inequality for powers**: for positive semidefinite `V` and Hermitian `H`,
`(q + 1)(2q + 1) tr (V H^{2q}) ≤ (2q + 1)^{q+1} tr V^{q+1} + q tr H^{2q+2}`.
[MackeyEtAl2014, proof of Theorem 7.1].
Port of `NLAlib.nat_mul_mul_re_trace_mul_pow_le`, there over `ℂ` with `p = q + 1`. -/
theorem re_trace_mul_pow_le_add {V H : Matrix n n 𝕜} (hV : V.PosSemidef) (hH : H.IsHermitian)
    (q : ℕ) :
    (q + 1 : ℝ) * (2 * q + 1) * RCLike.re (V * H ^ (2 * q)).trace ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace +
        q * RCLike.re (H ^ (2 * q + 2)).trace := by
  sorry

/-- **Young's inequality for traces**: for positive semidefinite `A`, `B` and conjugate exponents
`p`, `q`, `tr (A B) ≤ tr Aᵖ / p + tr B^q / q`. [Bhatia1997, §IV.2 context]. -/
theorem re_trace_mul_le_re_trace_rpow_add {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {p q : ℝ} (hpq : p.HolderConjugate q) :
    RCLike.re (A * B).trace ≤ RCLike.re (A ^ p).trace / p + RCLike.re (B ^ q).trace / q := by
  sorry

end NLAlib
