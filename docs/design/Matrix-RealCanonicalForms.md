# Real skew-symmetric and orthogonal canonical forms

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`bed23695d496f24548e0d8222b1096409fdb659c`.

## Objects, interfaces, and compatibility

Extend `Matrix/Spectral/RealSchur.lean` using `IsRealSchurForm`,
`HasOrthonormalCols`, Mathlib's `IsStarNormal`, matrix multiplication, conjugate
transpose, and reindexing. Introduce no definition, interface, bound, or Mathlib
deviation. The real field is essential: the conclusions describe real scalar
blocks and real rotation planes. A supplied equivalence `Fin k ≃ n` specifies
the ordering of an arbitrary finite input type. Empty dimensions are included.

Mathlib has no general star-algebra `IsSkewAdjoint` predicate in this pin
(`Algebra/Star/SelfAdjoint.lean` lists it as a TODO). Its form-relative
`Matrix.IsSkewAdjoint` is a different object. Thus the skew hypothesis remains
the native equation `Aᴴ = -A`, without inventing a new interface for one theorem.

The existing `Fin k` normal-form theorem retains its name and signature. A public
ordered arbitrary-index theorem carries the general statement, and the existing
theorem becomes its one-line identity-enumeration specialization. This replaces
the private reindexing helper in the prototype and avoids two independent proofs.

## Exact statement shapes

All declarations below have `{n : Type*} [Fintype n] [DecidableEq n]` and `{k : ℕ}`.

```lean
theorem exists_hasOrthonormalCols_isRealSchurForm_submatrix_of_isStarNormal
    {A : Matrix n n ℝ} (hA : IsStarNormal A) (order : Fin k ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm (T.submatrix order order) ∧
      ∀ i j, i ≠ j → T i j = -T j i

theorem exists_hasOrthonormalCols_isRealSchurForm_of_conjTranspose_eq_neg
    {A : Matrix n n ℝ} (hA : Aᴴ = -A) (order : Fin k ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm (T.submatrix order order) ∧
      (∀ i j, i ≠ j → T i j = -T j i) ∧ ∀ i, T i i = 0

theorem HasOrthonormalCols.exists_isRealSchurForm
    {A : Matrix n n ℝ} (hA : HasOrthonormalCols A) (order : Fin k ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm (T.submatrix order order) ∧
      (∀ i j, i ≠ j → T i j = -T j i) ∧
      (∀ i, (∀ j, j ≠ i → T j i = 0) → T i i = -1 ∨ T i i = 1) ∧
      (∀ i j : Fin k, (j : ℕ) + 1 = (i : ℕ) →
        T (order i) (order j) ≠ 0 →
        T (order j) (order j) ^ 2 + T (order i) (order j) ^ 2 = 1)
```

The skew form has zero scalar blocks and blocks with entries `0,b,-b,0`.
The orthogonal form has singleton signs and blocks with entries `a,b,-b,a`,
where `a^2+b^2=1`. Their signed coefficients are not normalized to positive
orientation. No particular angle in `(0, pi)` is chosen. The conjunctions keep
the properties of the same existentially supplied basis and matrix together.

## Placement, consumers, and reuse

All declarations remain in `Matrix/Spectral/RealSchur.lean`, next to the real
normal form they specialize. The order is the general normal form, the existing
finite-index corollary, then skew and orthogonal specializations. The existing
real QZ theorem is already covered and is not changed.

The arbitrary-index normal form supports downstream matrix functions and real
normal spectral calculations without forcing their inputs to `Fin`. The skew
form supplies rotation-plane decompositions for real skew matrix exponentials.
The orthogonal form supplies signs and unit-circle coefficients for real
orthogonal spectral analysis and canonical examples.

Reuse `exists_isRealSchurForm_conjTranspose_mul_mul` for the mathematical normal
form, `Matrix.submatrix_mul_equiv`, `Matrix.conjTranspose_submatrix`, and
`HasOrthonormalCols.submatrix` for transport. Orthogonal conjugation reuses
`HasOrthonormalCols.eq_mul_mul_conjTranspose_iff`, `.mul`, and `.conjTranspose`.
The two specializations and their block-support consequences have no existing
matching statement in the searched current NLAlib and pinned Mathlib. Local
column-support calculations stay private; no parallel Schur-form predicate is
introduced.

## Material and source relationship

Original formal source: `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`,
`Matrix/Spectral/RealNormalSpecializations.lean`:
`exists_orthogonal_real_skew_normal_form` and
`exists_orthogonal_real_orthogonal_normal_form`.
Evaluated port material: `DiarHaidary/NLAlib` commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8`, `Matrix/Spectral/RealSchur.lean`.

Printed source: Horn and Johnson, *Matrix Analysis*, second edition,
Theorem 2.5.8 and Corollary 2.5.11(b,c). The parent review checked the relevant
text on 2026-10-31 in the
[online text](https://studylib.net/doc/27327082/roger-a.horn.--matrix-analysis-2nd-edition-booksee.org-).
The printed corollary additionally normalizes the skew blocks to positive
coefficients and the orthogonal rotation angles to `(0, pi)`. The formal API
asserts the invariant block equations without those orientation choices, and
the docstrings explicitly record that difference.

## Result metadata

Both canonical-form corollaries extend the current `real-schur` result group.
The original backend used `normal-matrices`, but that identifier is absent from
the current exported data. Using the current owning topic keeps the general
decomposition and its real normal specializations together. The enumeration
theorem remains supporting API; no new result ID is introduced.

The extraction checker issues three T7 advisories for these new real-only
statements. This is intentional: `IsRealSchurForm` describes real scalar blocks
and real two-dimensional rotation planes. Replacing the field by an arbitrary
`RCLike` field would change that interface and the mathematical conclusion.

## Open questions

None: no new vocabulary, hypothesis interface, target, or approval-registry
change is proposed. Positive orientation can be supplied later when a concrete
consumer requires it, rather than creating redundant canonical-form statements.
