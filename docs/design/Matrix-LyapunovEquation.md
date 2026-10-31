# Continuous Lyapunov equations under strict dissipativity

Design dated 2026-10-31. This file ports the finite-dimensional results from
`tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`,
`Matrix/Equations/LyapunovCoercivity.lean` and `LyapunovDissipative.lean`.
Those files supply formal provenance, not a verified printed citation.

## Objects and interfaces

No definitions, named constants, or new hypothesis predicates are introduced.
The native condition is the Loewner inequality
`hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)`. It applies to nonnormal matrices.
Positivity `0 < a` is separate and used only for inverse estimates and solvability.
The equation is stated directly as `A * X + X * Aᴴ = -Q`.
The source's public `lyapunovLinearMap` is replaced by a proof-local linear map.

All statements use `RCLike`, arbitrary finite index types, real scalar action,
`frobNorm`, `frobInner`, `SymmetricGauge.matrixNorm`, `Matrix.IsHermitian`,
`Matrix.PosSemidef`, and `HasOrthonormalCols`. Empty index types are permitted: their
unique matrix is the unique solution, every norm vanishes, and the bounds remain valid.
No stable-spectrum-only theorem or Hermitian restriction on the coefficient is claimed.

## Exact headline and supporting signatures

```lean
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem frobInner_mul_add_mul_conjTranspose_le
    {A : Matrix n n 𝕜} {a : ℝ}
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (E : Matrix n n 𝕜) :
    frobInner E (A * E + E * Aᴴ) ≤ -2 * a * frobNorm E ^ 2

theorem SymmetricGauge.matrixNorm_le_div_of_hermitianPart_le
    (Φ : SymmetricGauge) {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (E : Matrix n n 𝕜) :
    Φ.matrixNorm E ≤ Φ.matrixNorm (A * E + E * Aᴴ) / (2 * a)

theorem existsUnique_mul_add_mul_conjTranspose_eq_neg
    {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (Q : Matrix n n 𝕜) :
    ∃! X : Matrix n n 𝕜, A * X + X * Aᴴ = -Q

theorem _root_.Matrix.IsHermitian.isHermitian_of_mul_add_mul_conjTranspose_eq_neg
    {A Q X : Matrix n n 𝕜} (hQ : Q.IsHermitian) {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜))
    (hX : A * X + X * Aᴴ = -Q) : X.IsHermitian

theorem _root_.Matrix.PosSemidef.posSemidef_of_mul_add_mul_conjTranspose_eq_neg
    {A Q X : Matrix n n 𝕜} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜))
    (hX : A * X + X * Aᴴ = -Q) : X.PosSemidef

end NLAlib
```

Amendment 2026-10-31, approved before proof: consolidate the Frobenius and spectral
inverse estimates into one result for every `SymmetricGauge`. This also removes the
Hermitian restriction on the error matrix from the spectral specialization.
`lpGauge_two_matrixNorm`, `lpGauge_top_matrixNorm`, and `lpGauge_one_matrixNorm` give
Frobenius, spectral, and nuclear bounds directly; no public norm-specific twins remain.
The Frobenius inner-product inequality remains distinct because it supplies a signed
energy bound. The eigenvector identity now has only one consumer, positivity, and is
inlined there as a local fact instead of adding a public one-consumer helper.
The five public theorems use the groups `lyapunov-equation` and `lyapunov-coercivity`.

## Proof route and reuse search

Searched the target and pinned Mathlib for Lyapunov, Sylvester, and dissipativity.
No matching Lyapunov theory was found. The current Sylvester coercivity estimates
assume individually Hermitian coefficient matrices and do not cover this condition.
Use native congruence monotonicity, `re_trace_le_re_trace_of_le`, the Hermitian-part
identity, and Frobenius adjoint identities for coercivity; alternatively sum the
existing quadratic-form inequality over columns within the proof.
For the unitarily invariant inverse bound, use `exists_isSVD` with all singular values.
Compress the coefficient by the left and right singular-vector frames using
`HasOrthonormalCols.hermitianPart_conjTranspose_mul_mul_le`. The real diagonal entries
of both compressed coefficients are at most `-a`. The two SVD identities
`IsSVD.mul_right_eq` and `IsSVD.conjTranspose_mul_eq` therefore bound the negative
real diagonal of the compressed residual below by twice `a` times each singular value.
Restrict both frames to their first `min k (Fintype.card n)` columns, as in
`exists_trace_conjTranspose_mul_mul_eq_kyFanNorm`, then apply
`re_trace_conjTranspose_mul_mul_le_kyFanNorm`, `kyFanNorm_min_card`, and
`SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le`. Homogeneity gives division
by `2 * a`. Private intermediate lemmas express only the singular-coordinate and
Ky Fan proof steps for this Lyapunov expression, not new general infrastructure.
A proof-local linear map, the `lpGauge 2` specialization, and
`LinearMap.injective_iff_surjective` give existence and uniqueness.
Adjoint invariance gives Hermitian preservation. Unit eigenvectors from the native
spectral API give positivity. Empty index types need no separate case in the norm proof.
No spectral-basis object appears in a public statement.

## Consumers and files

`NLAlib/Matrix/Spectral/LyapunovEquation.lean` contains the statements above, in that
order. Consumers in matrix-equation approximation can use the inverse bounds with
`E = X - Y`; linearity makes the right side the residual. For two exact solutions,
the same bound gives forcing sensitivity without separate wrapper theorems.
The equation and positivity results are the foundation for later low-rank and
Krylov matrix-equation results, with no algorithms ported in this change.

The source's compression inheritance belongs in `Spectral/HermitianPart.lean`,
where the proposed generic native API is:

```lean
theorem HasOrthonormalCols.hermitianPart_conjTranspose_mul_mul_le
    {k : Type*} [DecidableEq k] {V : Matrix n k 𝕜}
    (hV : HasOrthonormalCols V) {A : Matrix n n 𝕜} {b : ℝ}
    (hA : hermitianPart A ≤ b • (1 : Matrix n n 𝕜)) :
    hermitianPart (Vᴴ * A * V) ≤ b • (1 : Matrix k k 𝕜)
```

This is an addition outside the new topic file because it is a statement about
compression of Hermitian parts, independently of Lyapunov equations. Root integration
owns it. Amendment 2026-10-31: generalize the existing identity
`hermitianPart_mul_mul_conjTranspose (U A : Matrix n n 𝕜)` in the same file to
`{m : Type*} (U : Matrix m n 𝕜) (A : Matrix n n 𝕜)`, retaining its
name, argument order, and proof. Existing square uses specialize automatically.
Then the compression inequality reuses that identity, native Loewner congruence,
and `hV.conjTranspose_mul_self`, without introducing a duplicate identity wrapper.
The output index type of the congruence and the column type of the compression need
not be finite; unused finiteness assumptions were removed after Lean's linter check.

## Deliberately omitted material and open questions

No source public linear-map object, repeated raw quadratic-form hypothesis, transpose
twin, algorithm wrapper, energy projection, or Galerkin algorithm is reproduced.
No new Mathlib deviation or vocabulary row is needed. Printed sources remain
unverified until inspected; interim docstrings say "No printed source." and give
the exact formal pin. Recommendation: retain the native condition and direct
equation signatures above; accept rectangular compression in its existing home.
