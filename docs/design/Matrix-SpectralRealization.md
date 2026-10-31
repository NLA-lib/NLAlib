# Spectral realization and triangularizing bases

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`bed23695d496f24548e0d8222b1096409fdb659c`.

## Objects and interfaces

Use the existing `Majorized`, `IsEigenvalueListing`, `hermitianPart`,
`HasOrthonormalCols` and `IsQR` interfaces, together with Mathlib's `IsUnit`,
`Matrix.IsUpperTriangular`, characteristic polynomials and matrix inverse. No new
definition, hypothesis interface, named bound or Mathlib deviation is introduced.
The realization theorem is complex because its prescribed eigenvalues are arbitrary
complex numbers. The triangularization equivalence works over either `RCLike` field.

## Statement shapes

Both files use arbitrary finite `n`, with `[Fintype n] [DecidableEq n]`.
`Matrix/Spectral/HermitianPart.lean` receives:

```lean
theorem exists_isEigenvalueListing_hermitianPart_of_majorized
    {x : n → ℝ} {z : n → ℂ} (h : Majorized (fun i => (z i).re) x) :
    ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
      IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ))

theorem majorized_re_iff_exists_isEigenvalueListing_hermitianPart
    (x : n → ℝ) (z : n → ℂ) :
    Majorized (fun i => (z i).re) x ↔
      ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
        IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ))
```

These statements specify multiplicities through characteristic-polynomial listings;
the lists need not be sorted or have distinct entries. The finite index type may be
empty. The equivalence completes the existing forward majorization statement and
shares its `real-part-majorization` result ID. The direct existence form is useful
for construction without extracting a direction of the equivalence.

`Matrix/Spectral/Simultaneous.lean` receives, with `{𝕜 : Type*} [RCLike 𝕜]`
and an arbitrary type `ι` indexing the family:

```lean
theorem exists_forall_isUpperTriangular_inv_mul_mul_iff [LinearOrder n]
    (A : ι → Matrix n n 𝕜) :
    (∃ V : Matrix n n 𝕜, IsUnit V ∧
      ∀ i, (V⁻¹ * A i * V).IsUpperTriangular) ↔
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧
      ∀ i, (Uᴴ * A i * U).IsUpperTriangular
```

No finiteness or nonemptiness assumption is imposed on the family, and its members
need not commute. The matrix labels carry a linear order because triangularity
depends on it. This replaces the original complex-only theorem and its separate
enumeration wrapper with one arbitrary-index, `RCLike` statement. The theorem shares
the existing `simultaneous-triangularization` result ID.

## Consumers and placement

The Hermitian-part results describe compatibility of a matrix spectrum with the
spectrum of its Hermitian part. They belong immediately after the forward
majorization theorem in `HermitianPart.lean`, supporting inverse spectral problems
and sharpness examples for spectral inequalities. The realization supplies a
matrix to later statements through `IsEigenvalueListing`, without exposing its
chosen triangular construction.

The triangularization equivalence belongs before the special commuting-family
theorems in `Simultaneous.lean`. It converts an algebraically constructed invariant
flag into an orthonormal basis for matrix-norm and perturbation arguments. Existing
commuting-family and normal-family theorems remain unchanged.

## Material and reuse audit

Original formal source: `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`:

| Original source | Decision |
|---|---|
| `Matrix/Inequalities/HermitianPartConverse.lean`: `exists_matrix_charpoly_and_selfAdjointPart_charpoly_of_majorized` | Express both characteristic-polynomial clauses through `IsEigenvalueListing`, and use the existing Hermitian part. |
| `Matrix/Inequalities/RealPartMajorization.lean`: `majorized_real_parts_iff_exists_charpoly_and_selfAdjointPart_charpoly` | Reuse the current forward theorem for the reverse implication. |
| `Matrix/Spectral/SimultaneousTriangularBasis.lean`: `exists_simultaneous_triangular_similarity_iff_unitary` | Generalize to `RCLike`; use QR rather than duplicate Gram–Schmidt flag machinery. |
| Same file: `exists_simultaneous_triangular_similarity_iff_unitary_of_equiv` | Covered by choosing the induced linear order; no separate public wrapper. |

Evaluated proof material also includes unmerged integration commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8` in `DiarHaidary/NLAlib`.
Horn--Johnson (2013), Theorem 4.3.50 gives exactly the compatibility equivalence for
the two prescribed spectra and its Schur--Horn/triangular construction. Its text
was checked on 2026-10-31 in the
[second-edition book text](https://studylib.net/doc/27327082/roger-a.horn.--matrix-analysis-2nd-edition-booksee.org-).
The original formal source also cites Theorem 2.3.3 for triangularization, but that
printed theorem concerns commuting families and does not state our general
equivalence. The new triangularization docstring therefore says "No printed
source" and identifies the QR proof and formal-source provenance rather than
claiming Theorem 2.3.3 as an exact source.

Searches of pinned Mathlib's matrix, eigenspace and triangularization developments
and current `NLAlib` found no equivalent statements. The realization reuses
`exists_hasOrthonormalCols_diag_eq_of_majorized`,
`Matrix.IsUpperTriangular.isEigenvalueListing_diag`, `complexify_mul`,
`complexify_conjTranspose`, `complexify_diagonal` and Mathlib's
`Matrix.charpoly_mul_comm` and `Matrix.charpoly_diagonal`. Its equivalence reuses
`majorized_re_of_isEigenvalueListing` rather than another eigenvalue-permutation
proof. The triangularization bridge reuses `exists_isQR`, `IsQR.mul_inv_eq`,
`IsQR.conjTranspose_mul_eq`, Mathlib's triangular-product closure, and
`Matrix.IsUpperTriangular.inv` from `NLAlib/Matrix/Factorizations/Triangular.lean`.

The added imports are `HermitianPart → Inequalities.SchurHorn` and
`Simultaneous → Factorizations.QR`; both remain within Matrix and are acyclic.
No public declaration is renamed or removed.

## Review decisions

No new interface or target requires a maintainer decision. Keep the existing
result groups, use one field-general triangularization theorem, and retain the
complex restriction only where prescribing arbitrary complex spectra requires it.
