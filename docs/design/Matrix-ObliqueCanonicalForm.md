# Unitary canonical form of an idempotent

The oblique-projector clause of `cs-decomposition` describes the matrix itself in an
orthonormal basis. The unitary CS decomposition and the angle formula for the norm are
already in `Matrix/Subspaces/CSDecomposition.lean` and `ObliqueBases.lean`.
`Matrix/Subspaces/ObliqueCanonicalForm.lean` supplies the remaining conclusion for an
arbitrary real or complex idempotent, including zero, identity and empty matrices.

The input is Mathlib's `IsIdempotentElem P`. In range and complementary coordinates the
diagonal blocks are the identity and zero. The rectangular upper-right block is diagonal,
with entries given directly by the square roots of the squared singular values of `P`
minus one. Thus a consumer can read each two-dimensional invariant plane directly from
the change of basis. The complement dimension is specified by addition, and `Fin` orders
the singular values. The proof uses `HasOrthonormalCols` for the change of basis and
`singularValues` of the original input throughout.

Take the left singular frame of a compact SVD of `P` and complete it to a basis. The
idempotent fixes its range. The row Gram matrix of the resulting off-diagonal block is
the diagonal of squared positive singular values minus the identity. The eigenvalue
shift formula identifies its singular values; the equal-Gram isometry theorem rotates
only the complementary frame to make the block diagonal. These steps reuse the existing
frame, pseudoinverse and spectral interfaces. All new coordinate calculations have a
single consumer. The published reference is Horn and Johnson, *Matrix Analysis*,
second edition, Corollary 3.4.3.3. The [original atlas implementation](https://github.com/tchen-research/NLAlib/blob/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Subspaces/ComplexObliqueSpectrum.lean)
identifies the endpoint cases and the ordering of the planes. A search of the pinned
Mathlib found the idempotence predicate and block-matrix algebra, with no corresponding
matrix canonical-form theorem.

## Public signatures

Here `𝕜` is real or complex and `n` is any finite index type.

```lean
theorem IsIdempotentElem.exists_fromBlocks_of_rank_add_eq {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {s : ℕ} (hc : P.rank + s = Fintype.card n) :
    ∃ g ≤ min P.rank s, (∀ i, 1 < singularValues P i ↔ i < g) ∧
      (∀ i < P.rank, 1 ≤ singularValues P i) ∧
      ∃ H : Matrix n (Fin P.rank ⊕ Fin s) 𝕜, HasOrthonormalCols H ∧
        Hᴴ * P * H = Matrix.fromBlocks 1
          (Matrix.of fun (i : Fin P.rank) (j : Fin s) =>
            if i.val = j.val then ((Real.sqrt (singularValues P i ^ 2 - 1) : ℝ) : 𝕜) else 0)
          0 0
```

## Singular-value and basis consumers

A norm estimate for an idempotent should accept its rank index directly. A change of
basis should provide the basis immediately. The original joint theorem stays available
to callers that need the number of oblique planes and the basis together.

```lean
theorem IsIdempotentElem.one_le_singularValues {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {i : ℕ} (hi : i < P.rank) :
    1 ≤ singularValues P i

theorem IsIdempotentElem.exists_conjTranspose_mul_mul_eq_fromBlocks {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {s : ℕ} (hc : P.rank + s = Fintype.card n) :
    ∃ H : Matrix n (Fin P.rank ⊕ Fin s) 𝕜, HasOrthonormalCols H ∧
      Hᴴ * P * H = Matrix.fromBlocks 1
        (Matrix.of fun (i : Fin P.rank) (j : Fin s) =>
          if i.val = j.val then ((Real.sqrt (singularValues P i ^ 2 - 1) : ℝ) : 𝕜) else 0)
        0 0
```

The lower bound follows by multiplying by the orthogonal projector onto the range
and using its existing singular-value and norm theorems. The joint canonical-form
theorem consumes that bound. The basis conclusion supplies the coordinates for an
oblique projection without a separate plane-count witness at the call site.
The explorer ID for this form is `oblique-projector-canonical-form`. The unitary CS
decomposition retains `cs-decomposition`.
