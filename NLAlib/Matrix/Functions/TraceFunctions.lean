/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Majorization.Schur

/-!
# Trace functions

For `f : ℝ → ℝ`, the trace function `A ↦ re (cfc f A).trace = ∑ f(λ_i(A))` on Hermitian matrices
inherits monotonicity and convexity from `f`. With `f = exp` this gives the monotonicity and
convexity of the trace exponential. Quadratic forms satisfy Jensen's inequality
`φ(xᴴ A x) ≤ xᴴ φ(A) x` for convex `φ` and unit `x`.

The intrinsic dimension `NLAlib.intrinsicDimension A = tr A / ‖A‖₂` of a positive semidefinite
matrix replaces the ambient dimension in trace bounds.

## Main definitions

* `NLAlib.intrinsicDimension`: the ratio of the trace to the spectral norm.

## Main results

* `NLAlib.re_trace_cfc_le_re_trace_cfc_of_le`: monotone `f` gives a monotone trace function.
* `NLAlib.convexOn_re_trace_cfc`: convex `f` gives a convex trace function.
* `NLAlib.re_trace_mul_cfc_le_re_trace_cfc_sub`: Klein's inequality.
* `NLAlib.apply_re_quadForm_le_re_quadForm_cfc`: Jensen for quadratic forms.
* `NLAlib.re_trace_cfc_conjTranspose_mul_mul_le`: trace Jensen for compressions.
* `NLAlib.re_trace_exp_le_re_trace_exp_of_le`, `NLAlib.convexOn_re_trace_exp`.
* `Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`: the intrinsic dimension lemma.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### Monotonicity and convexity -/

/-- **A monotone function gives a monotone trace function**: if `A ≤ B` have spectrum in `s` and
`f` is non-decreasing on `s`, then `tr f(A) ≤ tr f(B)`.
[Tropp2015, §2.1 and §8.3]; [Carlen2010, Theorem 2.10].
Port of `NLAlib.traceExp_le_traceExp`, there for the exponential over `ℂ`.
Result: trace-monotonicity -/
theorem re_trace_cfc_le_re_trace_cfc_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (h : A ≤ B)
    {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) (hAs : spectrum ℝ A ⊆ s)
    (hBs : spectrum ℝ B ⊆ s) : RCLike.re (cfc f A).trace ≤ RCLike.re (cfc f B).trace := by
  sorry

/-- **A convex function gives a convex trace function** on the Hermitian matrices with spectrum
in the domain of convexity.
[Carlen2010, Theorem 2.10]; [Bhatia1997, Problem IX.8.14 context].
Port of `NLAlib.convexOn_traceExp_isHermitian` and `NLAlib.convexOn_traceEvenPower`, there for
the exponential and for even powers.
Result: trace-convexity -/
theorem convexOn_re_trace_cfc {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ {A : Matrix n n 𝕜 | A.IsHermitian ∧ spectrum ℝ A ⊆ s}
      fun A => RCLike.re (cfc f A).trace := by
  sorry

/-- **Klein's inequality.** For `f` convex on `s` with derivative `f'`, and Hermitian `A`, `B`
with spectrum in `s`, `tr ((A - B) f'(B)) ≤ tr f(A) - tr f(B)`.
[Carlen2010, Theorem 2.11]; [Tropp2015, §8.3].
Port of `NLAlib.generalized_klein`, in its classical form.
Result: klein-inequality -/
theorem re_trace_mul_cfc_le_re_trace_cfc_sub {f f' : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hBs : spectrum ℝ B ⊆ s) :
    RCLike.re ((A - B) * cfc f' B).trace ≤
      RCLike.re (cfc f A).trace - RCLike.re (cfc f B).trace := by
  sorry

/-- **The generalized Klein inequality.** If `∑ i, f i a * g i h ≥ 0` for all `a`, `h` in `s`,
then `∑ i, tr (f_i(A) g_i(H)) ≥ 0` for Hermitian `A`, `H` with spectrum in `s`.
[Tropp2015, Proposition 8.3.5]. Port of `NLAlib.generalized_klein`. -/
theorem sum_re_trace_cfc_mul_cfc_nonneg {ι : Type*} [Fintype ι] {f g : ι → ℝ → ℝ} {s : Set ℝ}
    (hfg : ∀ a ∈ s, ∀ h ∈ s, 0 ≤ ∑ i, f i a * g i h) {A H : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hH : H.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hHs : spectrum ℝ H ⊆ s) :
    0 ≤ ∑ i, RCLike.re (cfc (f i) A * cfc (g i) H).trace := by
  sorry

/-! ### Jensen for quadratic forms and compressions -/

/-- **Jensen's inequality for a quadratic form.** For `φ` convex on a set containing the spectrum
of the Hermitian matrix `A` and a unit vector `x`, `φ(xᴴ A x) ≤ xᴴ φ(A) x`.
[HalkoMartinssonTropp2011, Proposition 8.6 context]. -/
theorem apply_re_quadForm_le_re_quadForm_cfc {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    φ (RCLike.re (quadForm A x)) ≤ RCLike.re (quadForm (cfc φ A) x) := by
  sorry

/-- **The power scheme bound.** For positive semidefinite `B` and `Q` with orthonormal columns,
`‖Qᴴ B Q‖₂^{q+1} ≤ ‖Qᴴ B^{q+1} Q‖₂`. This is why power iteration improves the randomized range
finder. [HalkoMartinssonTropp2011, Proposition 8.6]. -/
theorem specNorm_conjTranspose_mul_mul_pow_le {B : Matrix n n 𝕜} (hB : B.PosSemidef)
    {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q) (q : ℕ) :
    specNorm (Qᴴ * B * Q) ^ (q + 1) ≤ specNorm (Qᴴ * B ^ (q + 1) * Q) := by
  sorry

/-- **Trace Jensen for compressions** (Berezin's inequality). For `f` convex on a set containing
the spectrum of `A` and `Q` with orthonormal columns, `tr f(Qᴴ A Q) ≤ tr (Qᴴ f(A) Q)`.
[Carlen2010, Theorem 2.12 context]; [Bhatia1997, Problem IX.8.14]. -/
theorem re_trace_cfc_conjTranspose_mul_mul_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) :
    RCLike.re (cfc f (Qᴴ * A * Q)).trace ≤ RCLike.re (Qᴴ * cfc f A * Q).trace := by
  sorry

/-! ### The trace exponential -/

/-- **The trace exponential is monotone** in the Loewner order.
[Tropp2015, §2.1]. Port of `NLAlib.traceExp_le_traceExp`, there over `ℂ`. -/
theorem re_trace_exp_le_re_trace_exp_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : A ≤ B) : RCLike.re (exp A).trace ≤ RCLike.re (exp B).trace := by
  sorry

/-- **The trace exponential is convex** on the Hermitian matrices.
[Tropp2015, §8.3]. Port of `NLAlib.convexOn_traceExp_isHermitian`, there over `ℂ`. -/
theorem convexOn_re_trace_exp :
    ConvexOn ℝ {A : Matrix n n 𝕜 | A.IsHermitian} fun A => RCLike.re (exp A).trace := by
  sorry

/-- The trace exponential is stable under perturbation:
`tr exp A ≤ exp ‖A - B‖₂ · tr exp B` for Hermitian `A`, `B`.
Port of `NLAlib.traceExp_le_exp_mul_traceExp_of_norm_sub_le`. -/
theorem re_trace_exp_le_exp_specNorm_sub_mul {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    RCLike.re (exp A).trace ≤ Real.exp (specNorm (A - B)) * RCLike.re (exp B).trace := by
  sorry

/-! ### Intrinsic dimension -/

/-- The **intrinsic dimension** of a matrix: the ratio of its trace to its spectral norm. For a
nonzero positive semidefinite matrix it lies between `1` and the rank.
[Tropp2015, Definition 7.1.1]. Port of `NLAlib.intrinsicDimension`, there over `ℂ`. -/
noncomputable def intrinsicDimension (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re A.trace / specNorm A

/-- The intrinsic dimension of a nonzero positive semidefinite matrix is at least one. -/
theorem _root_.Matrix.PosSemidef.one_le_intrinsicDimension {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≠ 0) : 1 ≤ intrinsicDimension A := by
  sorry

/-- The intrinsic dimension of a positive semidefinite matrix is at most its rank. -/
theorem _root_.Matrix.PosSemidef.intrinsicDimension_le_rank {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : intrinsicDimension A ≤ A.rank := by
  sorry

/-- The intrinsic dimension of a block diagonal positive semidefinite matrix is at most the sum
of the intrinsic dimensions of the blocks.
[Tropp2015, §7.3]. Port of `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem intrinsicDimension_fromBlocks_le {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    intrinsicDimension (Matrix.fromBlocks A 0 0 B) ≤
      intrinsicDimension A + intrinsicDimension B := by
  sorry

/-- The intrinsic dimension of a block diagonal positive semidefinite matrix is at least the
smaller of the intrinsic dimensions of the blocks.
Port of `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem min_intrinsicDimension_le_intrinsicDimension_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    min (intrinsicDimension A) (intrinsicDimension B) ≤
      intrinsicDimension (Matrix.fromBlocks A 0 0 B) := by
  sorry

/-- **The intrinsic dimension lemma.** For `φ` convex on `[0, ∞)` with `φ 0 = 0` and positive
semidefinite `A`, `tr φ(A) ≤ intdim(A) · φ(‖A‖₂)`.
[Tropp2015, Lemma 7.5.1].
Port of `NLAlib.traceFunction_le_intrinsicDimension_mul`, there over `ℂ`.
Result: intrinsic-dimension -/
theorem _root_.Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 = 0) :
    RCLike.re (cfc φ A).trace ≤ intrinsicDimension A * φ (specNorm A) := by
  sorry

end NLAlib
