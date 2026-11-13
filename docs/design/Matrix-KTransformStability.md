# Matrix K-transform and local stability

The matrix K-transform controls the spectral edge in the block-Wishart variational formula of Montanari and Saeed. At a positive definite evaluation point, the derivative can be tested by one Frobenius operator norm or by finding one strict positive matrix supersolution. These alternatives let a consumer verify local stability without diagonalizing the derivative. The source is [Montanari and Saeed, equations (21), (103)–(109) and Lemma 6](https://arxiv.org/html/2606.27774v1).

## Domain and interfaces

Let `ν` be a finite measure on the self-adjoint complex matrices, with compact support. For a positive definite matrix `S`, the predicate `IsKTransformAdmissible ν S` requires `(S⁻¹ + T.val).PosDef` for every `T ∈ ν.support`. No point outside the support is constrained. The paper takes a probability measure. Its normalization plays no role in the local derivative or the local stability equivalences.

| File | Public interface | Consumer |
| --- | --- | --- |
| `ForMathlib/Analysis/Calculus/ParametricIntegral.lean` | `MeasureTheory.hasFDerivAt_integral_of_compact_support` differentiates a parameter integral from joint continuity and fibrewise differentiability near the support. | The matrix K-transform derivative. |
| `ForMathlib/Analysis/InnerProductSpace/Rayleigh.lean` | `ContinuousLinearMap.exists_norm_eigenvector_of_rayleigh_majorants` turns cone majorants for the Rayleigh quotient into a norm eigenvector in the cone. | Contraction from a strict positive supersolution. |
| `Matrix/Norms/HermitianFrobenius.lean` | `hermitianFrobenius 𝕜 n` is the real Hilbert space of Hermitian matrices with inner product `frobInner` and norm `frobNorm`. | The norm of an operator on Hermitian directions. |
| `Matrix/Spectral/PositiveCone.lean` | `norm_lt_one_iff_exists_posDef_sub_map`, `posSemidef_inverse_one_sub_apply`. | Positive-cone norm criterion and Neumann inverse. |
| `Matrix/Functions/KTransform.lean` | `matrixKTransform ν α S`, `matrixKTransformDeriv ν α S`, `matrixKStabilityMap ν α S`. | Differentiation and whitening on the positive domain. |
| `Matrix/Functions/KTransformStability.lean` | `matrixKStabilityFrobenius ν α S` and the three equivalences below. | Local K-transform stability. |

The public statements use these forms, with the hypotheses above and `0 < α` in the stability tests.

```lean
HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S) S

(∀ Δ : Matrix n n ℂ, Δ.IsHermitian → Δ ≠ 0 →
  0 < frobInner Δ (matrixKTransformDeriv ν α S Δ)) ↔
    ‖matrixKStabilityFrobenius ν α S‖ < 1

‖matrixKStabilityFrobenius ν α S‖ < 1 ↔
  ∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y - matrixKStabilityMap ν α S Y).PosDef

(∃ Y : Matrix n n ℂ, Y.PosDef ∧ (Y - matrixKStabilityMap ν α S Y).PosDef) ↔
  ∃ B : Matrix n n ℂ, B.PosDef ∧ (matrixKTransformDeriv ν α S B).PosDef
```

The norm equivalences take a nonempty finite index type. Differentiation, whitening, and the Neumann inverse also work in dimension zero. For a contraction `L`, `Ring.inverse (1 - L)` preserves the positive semidefinite cone. Its value on the identity is positive definite, dominates the identity, and satisfies the exact unit-gap equation.

## Mathlib bridges and proof organization

Mathlib provides `hasFDerivAt_ringInverse`, Fréchet differentiation under a dominated integral, `CFC.sqrt`, positive and negative parts under CFC, the finite-dimensional spectral theorem, and `geom_series_eq_inverse`. The two upstream-candidate files supply the compact-support and cone-majorant specializations absent from those APIs. Search of Mathlib and the existing library found no K-transform or positive-cone contraction API with these signatures.

The representation `hermitianFrobenius 𝕜 n` uses `selfAdjoint.submodule ℝ (Matrix n n 𝕜)`. Its Hilbert norm differs from the ambient spectral norm. The linear equivalence `hermitianFrobeniusEquiv` identifies the underlying spaces, while `inner_eq_frobInner` and `norm_eq_frobNorm` identify the inner product and norm. The stability map has a total Hermitian compression. At each admissible point the real-linear integral itself preserves Hermitian matrices, and `hermitianFrobeniusMatrix_matrixKStabilityFrobenius` identifies the two actions.

The original atlas card and its proof modules supplied the derivative, whitening identity, cone argument and two certificates. The port uses the library's `frobInner`, `frobNorm`, and positive-definite square-root lemmas. Compact support gives the local parameter neighborhood and an integrable bound. For the norm criterion, the positive and negative parts of a Hermitian matrix produce a positive semidefinite Rayleigh majorant. The Neumann series proves positivity of Mathlib's ring inverse. Local conjugation identities remain proof helpers. The positive-cone lemmas work over either real or complex matrices. For example, a single whitened coefficient with diagonal entries of opposite signs sends an off-diagonal Hermitian matrix to a negative scalar multiple of itself. The proof uses preservation of the positive semidefinite cone and the Rayleigh majorant, which remain valid for such coefficients. Each neighboring pair of equivalent conditions has one public theorem.
