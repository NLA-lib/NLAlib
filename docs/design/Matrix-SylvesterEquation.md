# Sylvester equations and block intertwiners

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`bed23695d496f24548e0d8222b1096409fdb659c`.

## Objects and interfaces

Extend `Matrix/Spectral/SylvesterEquation.lean` using ordinary matrix multiplication,
Mathlib's `IsCoprime`, `spectrum`, `Commute`, `Matrix.blockDiagonal'` and `Matrix.blockDiag'`,
and the library's existing `complexify`. No new definition, hypothesis interface, named bound,
vocabulary row or Mathlib deviation is needed. In particular, do not import the old
`sylvesterLinearMap` definition: the existing equation interface already states what consumers
need. Algebraic results use arbitrary fields; complex spectral conditions use `RCLike`.

## Statement shapes

The first two statements use `{K : Type*} [Field K] [IsAlgClosed K]` and arbitrary finite
index types `m`, `n`, with `DecidableEq` where the characteristic polynomial requires it.

```lean
theorem forall_eq_zero_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ X : Matrix m n K, A * X = X * B → X = 0) ↔
      Disjoint (spectrum K A) (spectrum K B)

theorem forall_existsUnique_mul_sub_mul_eq_iff_disjoint_spectrum [IsAlgClosed K]
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ C : Matrix m n K, ∃! X : Matrix m n K, A * X - X * B = C) ↔
      Disjoint (spectrum K A) (spectrum K B)

theorem isCoprime_charpoly_iff_disjoint_spectrum_complexify
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    IsCoprime A.charpoly B.charpoly ↔
      Disjoint (spectrum ℂ (complexify A)) (spectrum ℂ (complexify B))
```

The complexification bridge composes directly with the existing arbitrary-field
`existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`; no separate real and complex solution
wrappers are added. Neither matrix dimension is required to be positive.

For the block statements use arbitrary `[Field K]`, a finite block index `ι`, and finite
dependent row and column index types `p q : ι → Type*`, with the required decidable equalities.
The same block label can have different row and column sizes, including zero.

```lean
theorem blockDiagonal'_mul_eq_mul_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (p i) (p i) K) (B : ∀ i, Matrix (q i) (q i) K)
    (h : ∀ i j, i ≠ j → IsCoprime (A i).charpoly (B j).charpoly)
    (X : Matrix (Σ i, p i) (Σ i, q i) K) :
    Matrix.blockDiagonal' A * X = X * Matrix.blockDiagonal' B ↔
      X = Matrix.blockDiagonal' (Matrix.blockDiag' X) ∧
        ∀ i, A i * Matrix.blockDiag' X i = Matrix.blockDiag' X i * B i

theorem commute_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (p i) (p i) K)
    (h : Pairwise fun i j => IsCoprime (A i).charpoly (A j).charpoly)
    (X : Matrix (Σ i, p i) (Σ i, p i) K) :
    Commute (Matrix.blockDiagonal' A) X ↔
      ∃ Y : ∀ i, Matrix (p i) (p i) K,
        X = Matrix.blockDiagonal' Y ∧ ∀ i, Commute (A i) (Y i)
```

The off-diagonal coprimality condition does not constrain matching block spectra. The diagonal
intertwining or commutation condition is essential and is retained. The conjunction describes
one exact characterization rather than combining independent numerical estimates.

## Consumers and placement

All additions stay in `Matrix/Spectral/SylvesterEquation.lean`, the existing home of
qualitative Sylvester solvability and block diagonalization. The converse characterizes
uniqueness for perturbation equations. The complexification bridge lets real or complex
consumers express separation in the common complex spectrum. The block theorem supports
primary decomposition, invariant-subspace transport and block commutants without assuming
algebraic closure. No declaration is placed in a higher layer for its proof dependencies.

The existing forward equation theorem remains the application-facing sufficient criterion.
The new iff theorem joins its `sylvester-equation` result card; the block characterization
joins that card as a separate substantive clause. The zero-intertwiner criterion and
complexification bridge are supporting API without new card IDs.

## Material and reuse audit

Original formal source: `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`:

| Source | Integration decision |
|---|---|
| `Matrix/Spectral/SylvesterQualitative.lean`: `sylvesterLinearMap_injective_iff_disjoint_spectrum` | Express injectivity as the vanishing of homogeneous solutions, through the current equation API. |
| Same file: `sylvesterLinearMap_bijective_iff_disjoint_spectrum` | Express bijectivity as unique solvability for every right-hand side. |
| `Matrix/Spectral/SylvesterBlocks.lean`: `existsUnique_real_sylvester_of_disjoint_complex_spectrum` | Generalize its transport step to a reusable `RCLike` coprimality iff, and use the existing solver theorem. |
| Same file: `eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum` | Strengthen to an iff and use arbitrary-field coprimality instead of disjoint spectra over an algebraically closed field. |
| Same file: `commute_blockDiagonal'_iff` | Generalize to arbitrary fields through coprimality and derive it from the rectangular theorem. |

Proof material was also evaluated in unmerged integration commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8` of `DiarHaidary/NLAlib`.

Searches in current Mathlib and `NLAlib` found no equivalent theorem for the five signatures.
The proofs reuse the existing zero-intertwiner lemma, coprimality/spectrum equivalence and
unique-solvability theorem. The converse reuses
`exists_mulVec_eq_smul_of_mem_spectrum` and `exists_vecMul_eq_smul_of_mem_spectrum` with
Mathlib's `Matrix.vecMulVec`, `Matrix.mul_vecMulVec` and `Matrix.vecMulVec_mul`.
The scalar-extension bridge is a rewrite through `charpoly_complexify` and
`Polynomial.isCoprime_map`. Block reconstruction reuses `Matrix.blockDiagonal'_mul`,
`Matrix.blockDiagonal'_apply_eq` and `Matrix.blockDiagonal'_apply_ne`; block extraction is
elementary multiplication through the sigma-type sum. No independent linear-operator,
characteristic-polynomial or complexification infrastructure is introduced.

The mathematical locators were freshly checked on 2026-10-31 against the
[available text of Horn--Johnson (2013)](https://studylib.net/doc/27327082/roger-a.horn.--matrix-analysis-2nd-edition-booksee.org-),
Theorem 2.4.4.1 and Corollary 2.4.4.2 (printed pages 111--112; extracted lines 6859--6892).
The theorem gives unique solvability for every right-hand side exactly under disjoint spectra,
including the real-data case. The corollary gives the conformally partitioned block-intertwiner
conclusion. The Lean forms additionally allow arbitrary fields through coprimality, rectangular
matching blocks, and empty dimensions; the block implication is strengthened to an equivalence.

## Open questions

None for the proposed interfaces. If block-extraction lemmas acquire independent consumers,
their natural home is general matrix block algebra; this change needs only their local use
inside the characterization proof and does not add separate public wrappers.
