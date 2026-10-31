# Left-right eigenvector deflation

Design dated 2026-10-31 against `NLA-lib/NLAlib` at
`a53d25688a8cee7e96899092e758e9f0771c75dc`.

## Objects, interfaces, and scope

Use matrices over an arbitrary field, their existing left/right eigenvector equations,
Mathlib's `IsUnit`, `IsIdempotentElem`, `Matrix.vecMulVec`, `spectrum`, and characteristic
polynomial root multiplicity. There is no new definition, hypothesis bundle, vocabulary row,
named bound, or Mathlib deviation. The left vector is a bilinear row: over the complex field,
an adjoint convention is recovered by supplying the conjugated column as the row.

```lean
variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
```

Nonzero pairing implies a nonempty index type, so no additional nonemptiness assumption is
introduced. A one-dimensional matrix has an empty complementary block, which is included.
The simple-root result requires no algebraic closure. The scalar perturbation identity has
neither an invertibility assumption nor a nonzero-pairing assumption: its explicit inverse-row
hypothesis is enough, including Lean's total inverse convention.

## Exact statement shapes

The main result records one simultaneous witness. Its row, column, and projector conclusions
must refer to the same basis, so they remain together.

```lean
theorem exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero
    {A : Matrix n n K} {x y : n → K} {μ : K}
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y) (hpair : y ⬝ᵥ x ≠ 0) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y =
        S * Matrix.diagonal (Pi.single i 1) * S⁻¹

theorem not_mem_spectrum_submatrix_of_rootMultiplicity_eq_one
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hμ : M.charpoly.rootMultiplicity μ = 1) :
    μ ∉ spectrum K (M.submatrix
      (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))

theorem exists_inv_mul_mul_apply_eq_of_rootMultiplicity_eq_one
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum K ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))
```

Split the source's converse bundle into independently applicable equations. The first needs
only an isolated column; the second only an isolated row. Nonzero vectors and the normalized
pairing are already consequences of invertibility in Mathlib, so no duplicate wrappers for
those facts are added.

```lean
theorem mulVec_col_eq_smul_of_inv_mul_mul_apply_eq
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hcol : ∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) :
    A *ᵥ Matrix.col S i = μ • Matrix.col S i

theorem vecMul_eq_smul_of_inv_mul_mul_apply_eq
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hrow : ∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) :
    (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j)

theorem nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div
    (S E : Matrix n n K) (i : n) (x y : n → K)
    (hcol : Matrix.col S i = x) (hrow : ∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) :
    (S⁻¹ * E * S) i i = (y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)
```

Rank-one action statements use an arbitrary scalar instead of hardwiring the normalized
scalar. The original normalized result is their specialization; zero pairing is included.

```lean
omit [DecidableEq n] in
theorem mul_smul_vecMulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hx : A *ᵥ x = μ • x) (c : K) :
    A * (c • Matrix.vecMulVec x y) = μ • (c • Matrix.vecMulVec x y)

omit [DecidableEq n] in
theorem smul_vecMulVec_mul_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hy : y ᵥ* A = μ • y) (c : K) :
    (c • Matrix.vecMulVec x y) * A = μ • (c • Matrix.vecMulVec x y)

theorem isIdempotentElem_inv_smul_vecMulVec {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] {x y : ι → K} :
    IsIdempotentElem ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y)
```

Block and characteristic-polynomial support belongs with the existing deflation lemmas in
`EigenvalueListing.lean`; the second declaration already exists privately and is promoted.

```lean
omit [Fintype n] in
theorem submatrix_eq_fromBlocks_of_isolated_coordinate (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0) :
    M.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => μ)) 0 0
        (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))

theorem charpoly_eq_X_sub_C_mul_charpoly_submatrix {M : Matrix n n K} {i₀ : n} {α : K}
    [DecidableEq {i // ¬i = i₀}] (hcol : ∀ i, M i i₀ = if i = i₀ then α else 0) :
    M.charpoly = (Polynomial.X - Polynomial.C α) *
      (M.submatrix (Subtype.val : {i // ¬i = i₀} → n) Subtype.val).charpoly
```

## Files, consumers, and reuse

- `Matrix/Spectral/EigenvectorPairing.lean`: rank-one eigenvector action, paired similarity,
  simple-root exclusion, converse equations, perturbation entry. These support spectral
  deflation, first-order simple-eigenvalue perturbation, and eventual Perron projection APIs.
- `Matrix/Spectral/EigenvalueListing.lean`: promote the characteristic factorization and derive
  the two-sided isolated block from `submatrix_sumCompl_eq_fromBlocks`; their subject is the
  same coordinate deflation already used by the module's triangularization.
- `Matrix/Subspaces/ObliqueProjector.lean`: normalized outer-product idempotence, because the
  assertion concerns an oblique projector and needs no eigenvalue hypothesis.

Mathlib searches found `exists_basis_of_pairing_ne_zero`, `Basis.invertibleToMatrix`,
`Basis.reindex`, `Matrix.mul_vecMulVec`, `Matrix.vecMulVec_mul`,
`Matrix.vecMulVec_mul_vecMulVec`, `Matrix.mem_spectrum_iff_isRoot_charpoly`, and
`Polynomial.rootMultiplicity_mul`. The corresponding APIs are used directly. No existing
exact statement of the paired similarity, reverse equations, normalized idempotence, or
spectral exclusion was found in Mathlib or the new library.

Reuse the current `rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero` and
`charpoly_mul_mul_of_mul_eq_one`, rather than add source similarity wrappers. The existing
`exists_adjugate_eq_smul_vecMulVec` already covers the source's adjugate result and is unchanged.
The general unisolated row/column block decomposition is not exported: there is no consumer.
No real/complex twins or backend definitions are introduced.

## Source correspondence and evidence

Original atlas pin: `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`. Evaluated proof material also includes the unmerged
new-library integration `af301c893d85b6ccc78f4144468b6dd07c7aaab8`; it is not merged wholesale.

| Original module and declaration | Current disposition |
| --- | --- |
| `EigenvectorPairing.normalized_vecMulVec_mul_self` | idempotence, including zero pairing |
| `EigenvectorPairing.mul_normalized_vecMulVec_eq_smul` | two scalar-general action statements |
| `EigenvectorDeflation.exists_isolated_eigenvector_similarity` | paired-similarity theorem |
| `EigenvectorDeflationSpectrum.not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple` | spectral exclusion, redundant row hypothesis removed |
| `EigenvectorDeflationSpectrum.exists_simple_eigenvalue_isolated_similarity` | simple-root corollary, algebraic closure removed |
| `EigenvectorDeflationBlocks.submatrix_eq_fromBlocks_of_isolated_coordinate` | short application of the existing block lemma |
| `EigenvectorDeflationBlocks.nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div` | perturbation entry identity |
| `EigenvectorDeflationConverse.eigenpair_of_isolated_similarity` | separate reverse equations plus existing inverse/independence API |

The original published-PDF-derived index `docs/coverage/hj13.md` records Theorem 1.4.7 as the
paired similarity and converse, and Lemma 6.3.10 as the simple-root spectral exclusion. These
locators agree with the original declaration docstrings; the book pages were not freshly
retrieved in this migration. The paired theorem gets `Result: left-right-eigenvectors`,
which is absent from the current new library. The other declarations are supporting API.

## Review

Independent design review accepted by the integrating agent on 2026-10-31 before proofs were
written. The arbitrary-field scope, scalar-general action, one-sided converse hypotheses,
zero-pairing convention, and simultaneous witness were checked explicitly. No maintainer
question or new interface is needed.
