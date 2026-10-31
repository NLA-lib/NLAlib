# Eigenvalue multiplicities and eigenvector coordinates

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`a53d25688a8cee7e96899092e758e9f0771c75dc`.

## Objects and interfaces

Extend `Matrix/Spectral/Diagonalizable.lean` using its existing `IsDiagonalizable` predicate,
Mathlib's `Module.End.eigenspace`, `Module.finrank`, `Polynomial.rootMultiplicity`,
`Matrix.submatrix`, and `IsUnit`. There are no new definitions, interfaces, named bounds,
vocabulary rows, or Mathlib deviations. The matrix results are algebraic over any field;
restricting them to `RCLike` would discard valid uses. Only the converse multiplicity
criterion assumes an algebraically closed field, which ensures the characteristic polynomial
splits.

## Statement shapes

Use `{K : Type*} [Field K]`, arbitrary finite index types `m`, `n`, and their necessary
`DecidableEq` instances.

```lean
theorem IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity
    {A : Matrix n n K} (hA : IsDiagonalizable A) (μ : K) :
    Module.finrank K (Module.End.eigenspace A.toLin' μ) =
      A.charpoly.rootMultiplicity μ

theorem isDiagonalizable_iff_forall_finrank_eigenspace_eq_rootMultiplicity
    [IsAlgClosed K] (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∀ μ : K,
      Module.finrank K (Module.End.eigenspace A.toLin' μ) =
        A.charpoly.rootMultiplicity μ

theorem card_add_finrank_eigenspace_le
    (A : Matrix n n K) (μ : K) (s : Finset n) :
    s.card + Module.finrank K (Module.End.eigenspace A.toLin' μ) ≤
      Fintype.card n + Module.finrank K
        (Module.End.eigenspace
          (A.submatrix (fun j : s => j.val) (fun j : s => j.val)).toLin' μ)

theorem mem_spectrum_submatrix_of_card_lt_add_finrank_eigenspace
    (A : Matrix n n K) (μ : K) (s : Finset n)
    (h : Fintype.card n <
      s.card + Module.finrank K (Module.End.eigenspace A.toLin' μ)) :
    μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val))

theorem diagonal_mul_inv_mul_eq_inv_mul_diagonal
    {A V : Matrix n n K} {W : Matrix n m K} {d : n → K} {e : m → K}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal e) :
    Matrix.diagonal d * (V⁻¹ * W) = (V⁻¹ * W) * Matrix.diagonal e

theorem inv_mul_apply_eq_zero_of_ne
    {A V : Matrix n n K} {W : Matrix n m K} {d : n → K} {e : m → K}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal e) {i : n} {j : m} (hij : d i ≠ e j) :
    (V⁻¹ * W) i j = 0
```

The principal-submatrix bound needs no diagonalizability. Removing coordinates decreases
geometric multiplicity by at most the number removed; the addition form avoids truncated
natural subtraction. Every scalar is allowed, including scalars outside the spectrum.
The survival corollary follows by positivity of the submatrix eigenspace dimension.
The basis-change theorem allows different eigenvalue listings and a rectangular `W`;
neither linear independence nor invertibility of `W` is required. Empty index types are
included wherever the displayed hypotheses are satisfiable.

## Consumers and placement

All additions belong to `Matrix/Spectral/Diagonalizable.lean`: they describe eigenspace
dimensions, diagonalizability criteria, and coordinates in eigenvector bases. The multiplicity
criterion supports spectral decomposition and simple-eigenvalue arguments. The submatrix
bound supports eigenvalue survival under coordinate deletion and multiplicity-aware
compression arguments. The rectangular change-of-coordinates API supports selecting an
eigenvector family and proving that its coordinates lie in the matching eigenspaces.

The file order is basic criteria, multiplicity criteria, submatrix multiplicity and survival,
then eigenvector-coordinate transport. A proof-local helper that restricts an eigenvector
vanishing on removed coordinates may be private; reusable matrix statements remain public.

## Material and reuse audit

Original formal source: `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`:

| Original source | Destination / decision |
|---|---|
| `Diagonalizable.lean`: `IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity` | Same mathematical statement; use current semisimplicity bridge. |
| `Diagonalizable.lean`: `isDiagonalizable_iff_finrank_eigenspace_eq_rootMultiplicity` | Same criterion; name the explicit universal quantifier. |
| `DiagonalizablePrincipal.lean`: `mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt` | Strengthen to the full dimension inequality, then derive survival. |
| `DiagonalizablePrincipal.lean`: `mem_spectrum_principal_submatrix_of_le_finrank_eigenspace` | Derive the strict dimension hypothesis by transitivity; no extra public wrapper. |
| `DiagonalizableBlocks.lean`: `diagonal_mul_change_eigenbasis_eq_change_eigenbasis_mul_diagonal` | Generalize to different listings and rectangular second family. |
| `DiagonalizableBlocks.lean`: `change_eigenbasis_apply_eq_zero_of_eigenvalues_ne` | Generalized entrywise consequence. |
| `DiagonalizableBlocks.lean`: bundled change-of-basis consequence | Use the two separate statements, without another conjunction wrapper. |

Evaluated proof material also includes the unmerged integration commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8` in `DiarHaidary/NLAlib`.

Searches in pinned Mathlib and the current library found no existing equivalent matrix
statements for the six signatures above. Reuse is explicit:

- `LinearMap.finrank_maxGenEigenspace_eq` identifies generalized-eigenspace dimension with
  algebraic multiplicity. The existing `IsDiagonalizable.isSemisimple` and Mathlib's
  `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` give the forward criterion.
- `Submodule.eq_of_le_of_finrank_eq`, `Module.End.eigenspace_le_maxGenEigenspace`, and
  `Module.End.iSup_maxGenEigenspace_eq_top` give the converse.
- `LinearMap.finrank_range_add_finrank_ker` and an injective coordinate restriction give
  the stronger submatrix dimension bound; no parallel dimension machinery is introduced.
- `LinearMap.finrank_eigenspace_le` already proves geometric multiplicity is at most
  algebraic multiplicity; it is deliberately not reproved or wrapped.
- Matrix inverse cancellation and the existing diagonal multiplication API give the
  two eigenvector-coordinate identities.

The source's book labels are provenance rather than a fresh direct-page verification.
Its Theorem 1.4.10 locator is retained for principal-submatrix survival, but is not repeated
for the multiplicity criterion: the original PDF-derived coverage index identifies that
theorem as the principal-submatrix chain. The multiplicity criterion instead cites the
surrounding sections 1.3–1.4, with the field generalization stated explicitly. Eigenvector
coordinate transport retains Theorem 1.3.27 as its square aligned-list source.
The criterion carries the original `diagonalizable-def` result id. Principal-submatrix
survival carries `principal-submatrix-eigenvalue-survival`; its stronger dimension bound
and the coordinate lemmas are supporting API without additional headline metadata.

## Review and open questions

No maintainer decision or new shared interface is required. The parent agent independently
reviewed and approved these six signatures before implementation on 2026-10-31, with the
algebraic-closure boundary and source-locator limitation explicitly retained. The parent agent
runs all compilation and repository checks serially for the combined matrix-analysis batch.
