# Design note: Matrix stage M3, spectral core

Status: written 2026-10-14 by the orchestrator; implemented without a maintainer approval stop, by
the standing instruction in `docs/port/status.md`. Choices a maintainer would have been asked
about are in §7. Every Lean signature below elaborates against the pinned Mathlib and the M1 and
M2 files.

## 0. Scope, and what moved

M3 is eigenvalues of Hermitian matrices, singular values, the SVD interface, the variational
characterisations, Weyl-type inequalities, Cauchy interlacing, and Eckart–Young.

Three things the brief listed under M3 are **moved to a new stage M3a, between M3 and M3b**:
the von Neumann trace inequality, Hoffman–Wielandt (Hermitian), Mirsky's inequality in Frobenius
norm, and Lidskii. In the prototype all four rest on majorization (`MajorizationWeights`, Ky Fan
prefix sums, doubly stochastic matrices), which the brief placed in M7. M3b (Schatten and
unitarily invariant norms) needs the same machinery for Fan dominance. So the order becomes

    M3 spectral core → M3a majorization, Ky Fan sums, trace inequalities, Hoffman–Wielandt,
    Mirsky, Lidskii → M3b Schatten and unitarily invariant norms → M4 → M5 → M6 → M7 (the rest
    of the inequalities stage) → …

The converse interlacing constructions (given interlacing sequences, build the bordered or
rank-one-updated matrix) move to M7 with Schur–Horn, their only consumer.

The bridges between norms and singular values (`specNorm A = singularValues A 0`,
`frobNorm A ^ 2 = ∑ σᵢ²`, rank bounds), which the M2 note sent to M3b, are in M3: Eckart–Young
cannot be stated without them.

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| eigenvalues of a Hermitian matrix | `eigenvalue A k : ℝ`, `k : ℕ`, non-increasing for `k < card n`, `0` for `k ≥ card n` and for non-Hermitian `A` | `hA.eigenvalue_eq_eigenvalues₀ : eigenvalue A i = hA.eigenvalues₀ i` for `i : Fin (card n)` |
| largest, smallest eigenvalue | `eigenvalue A 0`, `eigenvalue A (Fintype.card n - 1)` | — |
| singular values | `singularValues A k : ℝ`, `k : ℕ`, non-increasing, `0` for `k ≥ rank A`; no `DecidableEq` | `singularValues_eq_linearMap`, `rfl`, to `LinearMap.singularValues` |
| SVD | `IsSVD A U σ V`: `U : Matrix m r 𝕜`, `V : Matrix n r 𝕜` with orthonormal columns, `σ : r → ℝ` nonnegative, `A = U * diagonal σ * Vᴴ`, any finite index type `r` | — |
| best rank-`k` approximation | `truncatedSVD A k`; the optimal errors are `singularValues A k` (spectral) and `frobNorm (A - truncatedSVD A k)` (Frobenius) | — |
| spectral gap | `eigengap A k := eigenvalue A (k - 1) - eigenvalue A k`, `singularGap A k := singularValues A (k - 1) - singularValues A k`, the gap that separates the first `k` from the rest | — |
| invariant subspace, eigenvectors | `A * U = U * M` with `HasOrthonormalCols U`; a single eigenvector is `A *ᵥ u = c • u` with `‖toLp 2 u‖ = 1` | — |

There is no rectangular diagonal matrix, no `IsBestFrobRankApprox`, no `lamMax`/`lamMin`, no
`sigmaMin`, and no chosen eigenvector basis in any statement.

## 2. Interfaces

**`eigenvalue A k`.** A total function of the matrix and a natural number. The prototype and the
first contract wrote `hA.eigenvalues₀ i` with `i : Fin (card n)`. That spelling puts a proof
inside every statement about a derived matrix (`(hA.add hB).eigenvalues₀ ⟨i + j, hij⟩`), forces
`Fin` arithmetic with casts on every index shift (Weyl, interlacing, gaps, the last index), and
needs a congruence lemma to rewrite the matrix. With `eigenvalue`:

```lean
theorem eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j : ℕ} (hij : i + j < Fintype.card n) :
    eigenvalue (A + B) (i + j) ≤ eigenvalue A i + eigenvalue B j
```

and it lines up with `singularValues`: `singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k` for
every `k`, with no side condition. Mathlib's `eigenvalues₀` stays the source of truth; the bridge
is one lemma. The cost is that zero padding is not monotone for matrices with negative
eigenvalues, so statements that compare indices carry `k < Fintype.card n`. For positive
semidefinite matrices nothing carries a side condition.

**`IsSVD A U σ V`** is the thin form with a free index type. It covers the compact SVD
(`r` of size `rank A`), the thin SVD (size `min (card m) (card n)`), partial SVDs, and, with
`r` a sum type and `Matrix.fromCols`, the two-block splitting `A = U₁ Σ₁ V₁ᴴ + U₂ Σ₂ V₂ᴴ` that
Wedin and Davis–Kahan consume. It needs no rectangular diagonal. It is stable under the
operations randomized algorithms perform: `h.mul_left hQ : IsSVD (Q * A) (Q * U) σ V`. A full SVD
with square unitary factors is obtained when wanted by orthonormal completion
(`HasOrthonormalCols.exists_fromCols`, M1). The prototype's `IsSVD` had `Fin p`, `Fin q` square
factors and `rectDiag`, and was the reason `Fin` index types spread through its low-rank layer.

**Eigenvector hypotheses** are invariance equations, never Mathlib's chosen basis:
`A * U = U * Matrix.diagonal d` with `HasOrthonormalCols U`. Existence is
`Matrix.IsHermitian.exists_mul_eq_mul_diagonal`; uniqueness of the values is
`eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose`.

**Gaps** are named real-valued functions, used as `0 < eigengap A k` or `δ ≤ eigengap A k` in
hypotheses and as divisors in conclusions. The index is the dimension of the leading subspace, to
match `truncatedSVD A k` and the "top-`k` eigenspace" phrasing of the theorems that consume it.
The general two-block separation hypothesis of the `sin Θ` theorem (spectra of two blocks
separated by `δ`) is M6's to state, in Loewner form on the blocks; these gap functions are the
form it specialises to.

**Variational statements.** The workhorses are the two one-sided subspace forms, hypotheses
written homogeneously as `c * ‖x‖ ^ 2 ≤ re (quadForm A x)` (no `x ≠ 0`, no division). The
equational sup–inf and inf–sup forms use `rayleighQuotient`. Extremes are also given in Loewner
form, `A ≤ eigenvalue A 0 • 1`, which is how concentration results conclude.

## 3. Statement shapes

Variables: `{𝕜} [RCLike 𝕜] {l m n p r} [Fintype _]`, `DecidableEq` where needed.

### Eigenvalues

```lean
noncomputable def eigenvalue (A : Matrix n n 𝕜) (k : ℕ) : ℝ   -- classical; 0 off the valid range

theorem Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀ [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (i : Fin (Fintype.card n)) : eigenvalue A i = hA.eigenvalues₀ i

theorem Matrix.IsHermitian.exists_mul_eq_mul_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧
      A * U = U * Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)
```

API: `eigenvalue_of_card_le`, `eigenvalue_of_not_isHermitian`, antitonicity on the valid range
(`hA.eigenvalue_le_eigenvalue`), `hA.exists_norm_eq_one_and_mulVec_eq` (a unit eigenvector for
each valid index), uniqueness from a diagonalisation, trace as the sum, determinant as the
product, `frobNorm A ^ 2` as the sum of squares, rank as the number of nonzero values,
`eigenvalue_neg` (reversal), `eigenvalue_real_smul` for `0 ≤ c`, the shift
`eigenvalue (A + c • 1) k = eigenvalue A k + c`, `eigenvalue_diagonal` for an antitone
diagonal, invariance under unitary similarity and under relabelling, the bridge to Mathlib's
unordered `hA.eigenvalues`, `hA.eigenvectorUnitary` as a `HasOrthonormalCols` matrix, and the
positive semidefinite facts (`hA.posSemidef_iff_eigenvalue_nonneg`, global antitonicity).

### Courant–Fischer

```lean
theorem Matrix.IsHermitian.le_eigenvalue_of_forall_mem {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : ℕ} (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S) {c : ℝ}
    (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x)) : c ≤ eigenvalue A k

theorem Matrix.IsHermitian.eigenvalue_le_of_forall_mem {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : ℕ} (hk : k < Fintype.card n) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ}
    (h : ∀ x ∈ W, RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2) : eigenvalue A k ≤ c
```

with the two existence statements (a subspace attaining each bound), the equational forms, the
extreme cases on vectors, and in Loewner form `hA.le_eigenvalue_zero_smul_one`,
`hA.eigenvalue_last_smul_one_le`, `hA.le_smul_one_iff`, `hA.smul_one_le_iff`; then
`hA.specNorm_eq_max` and `Matrix.PosSemidef.specNorm_eq_eigenvalue_zero`.

### Weyl and interlacing

```lean
theorem eigenvalue_le_eigenvalue_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (hA : A.IsHermitian)
    (k : ℕ) : eigenvalue A k ≤ eigenvalue B k

theorem abs_eigenvalue_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) : |eigenvalue A k - eigenvalue B k| ≤ specNorm (A - B)

theorem Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q)
    {k : ℕ} (hk : k < Fintype.card p) : eigenvalue (Qᴴ * A * Q) k ≤ eigenvalue A k

theorem Matrix.IsHermitian.eigenvalue_le_eigenvalue_conjTranspose_mul_mul [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q)
    {k d : ℕ} (hk : k < Fintype.card p) (hd : Fintype.card p + d = Fintype.card n) :
    eigenvalue A (k + d) ≤ eigenvalue (Qᴴ * A * Q) k
```

Index shifts are written with an auxiliary `d` and an equation, never with truncated subtraction
in the statement. Principal submatrices are `A.submatrix s s` for injective `s`, corollaries of
the compression statements. Low-rank updates: `eigenvalue (A + B) (k + r) ≤ eigenvalue A k` and
its mirror for `B.rank ≤ r`; rank-one updates `A + vecMulVec z (star z)` interlace.

### Singular values and the SVD

```lean
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ

theorem sq_singularValues (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k
theorem singularValues_zero_eq_specNorm (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A
theorem singularValues_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    singularValues (A + B) (i + j) ≤ singularValues A i + singularValues B j

structure IsSVD [DecidableEq r] (A : Matrix m n 𝕜) (U : Matrix m r 𝕜) (σ : r → ℝ)
    (V : Matrix n r 𝕜) : Prop where
  hasOrthonormalCols_left : HasOrthonormalCols U
  hasOrthonormalCols_right : HasOrthonormalCols V
  nonneg : ∀ i, 0 ≤ σ i
  eq : A = U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ

theorem exists_isSVD (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) (hkm : k ≤ Fintype.card m)
    (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜),
      IsSVD A U (fun i => singularValues A i) V

theorem IsSVD.singularValues_eq {k : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin k) 𝕜}
    {σ : Fin k → ℝ} {V : Matrix n (Fin k) 𝕜} (h : IsSVD A U σ V) (hσ : Antitone σ) (i : Fin k) :
    singularValues A i = σ i

theorem IsSVD.mul_left [DecidableEq r] [DecidableEq m] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {σ : r → ℝ} {V : Matrix n r 𝕜} (h : IsSVD A U σ V) {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) : IsSVD (Q * A) (Q * U) σ V
```

`exists_isSVD` takes the number of columns `k` anywhere between the rank and the smaller
dimension, so one statement gives the compact and the thin SVD. `Fin k` is appropriate there:
the order of the singular values is the content.

### Eckart–Young

```lean
noncomputable def truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜

theorem rank_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) : (truncatedSVD A k).rank ≤ k
theorem specNorm_sub_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k
theorem frobNorm_sub_truncatedSVD_sq (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD A k) ^ 2 =
      ∑ i ∈ Finset.Ico k (Fintype.card n), singularValues A i ^ 2
theorem singularValues_le_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B)
theorem frobNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : frobNorm (A - truncatedSVD A k) ≤ frobNorm (A - B)
```

`truncatedSVD A k` is built from a chosen SVD; it is one best rank-`k` approximation, not the
only one when `σ_{k-1} = σ_k`. Its docstring says so, and every property is also available for
the truncation of an arbitrary `IsSVD` (`IsSVD.truncate`). The optimality statements are given as
inequalities, as above, and as `IsLeast` over `{B | B.rank ≤ k}` in Mathlib's vocabulary.

## 4. Consumers

| Item | Consumed by |
|---|---|
| `eigenvalue`, Loewner extremes | matrix concentration (`λ_max`, `λ_min` of sums); M6; M8 (`cfc` eigenvalues); Krylov (Ritz values) |
| Courant–Fischer, interlacing | M6; Krylov (Ritz value bounds); M9 rank-revealing; Nyström |
| Weyl, `abs_eigenvalue_sub_le` | M6 everywhere; stability of gaps |
| `singularValues`, bridges to norms | every later stage; M3b defines its norms from them |
| `IsSVD` | M4 (pseudoinverse through an SVD); M5 principal angles; M6 Wedin; randomized SVD; subspace iteration |
| `truncatedSVD`, Eckart–Young | all of low-rank approximation; range finder bounds |
| `eigengap`, `singularGap` | M6 Davis–Kahan and Wedin; subspace iteration and Lanczos convergence |

## 5. Files

Under `NLAlib/Matrix/Spectral/`:

1. `Eigenvalues.lean`: the accessor, bridges, diagonalisation, spectrum.
2. `EigenvalueTransform.lean` (imports 1, M2 `Frobenius`): trace, determinant, Frobenius norm,
   rank; negation, scaling, shifts, unitary similarity; PSD and PD in terms of eigenvalues.
3. `CourantFischer.lean` (imports 2, M1 `QuadForm`, M2 `Loewner`): variational forms, extremes,
   Loewner forms, the spectral norm of a Hermitian matrix.
4. `Weyl.lean` (imports 3): Loewner monotonicity, Weyl, perturbation, low-rank and rank-one
   updates, `eigengap`.
5. `Interlacing.lean` (imports 3): compressions, principal submatrices.
6. `SingularValues.lean` (imports 3, M2): the definition, the bridge, `sq_singularValues`, rank,
   norms, transposes, scaling, orthonormal invariance, the variational forms, the smallest
   singular value, the PSD case, the dilation.
7. `SVD.lean` (imports 6, M1 `OrthonormalBasis`): `IsSVD`, consequences, stability, rank and
   norms, uniqueness of the values, block splitting, existence.
8. `SingularValueInequalities.lean` (imports 4, 5, 6): Weyl for singular values, perturbation,
   products, submatrix interlacing, projections, `singularGap`.
9. `LowRank.lean` (imports 7, 8): `truncatedSVD`, Eckart–Young in both norms.

Independent for proving: 4 and 5 after 3; 7 and 8 after 6 (8 also needs 4 and 5).

## 6. Material

Read: prototype `Matrix/Spectral/{Core, SVD, CourantFischer, Weyl, EckartYoung, EigenvalueOrder,
SpectralBounds, TraceEigenvalues, SingularValue*, GramSingularValues, SingularInterlacing,
LowRankInterlacing, ProductSingularValues, ProductWeyl, Svd*, SpectralMinimum, Eigenframe*,
QuadraticProbe, SquareSmallestSingularValue}`, `Matrix/Norms/RankNorm`,
`Matrix/Perturbation/EigenvalueTrace` (for what depends on majorization).

Reused as mathematics and proofs: Courant–Fischer (already over `𝕜`), Weyl, interlacing for
compressions, the singular value API, existence of the SVD, Eckart–Young in both norms, low-rank
update interlacing, product inequalities.

Not reproduced: `lambdaMax`/`lambdaMin` as `sSup`/`sInf` of the spectrum; `rectDiag` and the
`Fin p`/`Fin q` `IsSVD`; `sortedEigenframe`, `topEigenframe`, `complementaryEigenframe` as
definitions (existence statements with `HasOrthonormalCols` replace them); `eigenvalues₀_congr`;
`bestRankFrobSq` and `IsBestFrobRankApprox`; `*_reindex` lemmas; real-only statements
(`EigenvalueOrder`, `LowRankInterlacing`, `SingularInterlacing`, `Svd*`, `Product*`), which are
restated over `𝕜`.

## 7. Decisions taken without approval

1. **Eigenvalues are read through `eigenvalue A k`, a total ℕ-indexed function**, not through
   `hA.eigenvalues₀ i`. This changes a §5.3 row and a line of the brief's §4 ("eigenvalues of
   Hermitian matrices are Mathlib's `eigenvalues₀`"). The brief's M3 question asks for the
   indexing to be chosen once for eigenvalues and singular values together; this is that choice.
   Mathlib's `eigenvalues₀` remains the definition underneath.
2. **`IsSVD` is the thin form with a free index type and an explicit `σ`.**
3. **No rectangular diagonal, no best-approximation predicate.**
4. **Gaps are functions indexed by the dimension of the leading subspace.**
5. **von Neumann, Hoffman–Wielandt, Mirsky (Frobenius), Lidskii move to a new stage M3a** with
   the majorization core; M3b follows it.
6. **Courant–Fischer hypotheses use `re (quadForm A x)` against `c * ‖x‖ ^ 2`**; the equational
   forms use `rayleighQuotient`.

## 8. Design review (Fable, 2026-10-14)

Rulings on the three questions put to the review:

- **Eigenvalue access: the total ℕ-indexed function** (§7.1 stands). The contract's own §5.2
  forbids proof terms in statements and `hA.eigenvalues₀ i` is one; every consumer states a
  derived matrix; ℕ-indexing matches Mathlib's `LinearMap.singularValues`.
- **SVD: the thin form with explicit `σ`, a `nonneg` field, sortedness as a separate hypothesis**
  (§7.2 stands). Fixing `σ = singularValues A` would force `Fin` on every index type.
- **Gaps: named functions indexed by dimension** (§7.4 stands), with `eigengap_succ` as the
  proof-facing form. The gap functions serve M6; subspace iteration and Lanczos consume ratios and
  relative gaps, which the Krylov layer will define.

Folded in from the further comments: the `IsSVD` structural API (`reindex`, `conjTranspose`,
`mul_left`, `mul_conjTranspose_right`, the block split `eq_add`/`fromCols_left`/`fromCols_right`,
`exists_isSVD_fromCols`, and for unsorted `σ` the bridges `rank_eq`, `specNorm_eq`,
`frobNorm_sq_eq`, `exists_equiv_singularValues_eq`); the Frobenius tail sum over
`Finset.Ico k (min (card m) (card n))`; the smallest eigenvalue primarily in Loewner form
(`hA.smul_one_le_iff`) with the last index given by an equation `k + 1 = card n`; the split of the
eigenvalue file in two; the contract amended in the same change (§5.2, §5.3, the §3 template).

**One ruling was overridden after it was made.** The review said to keep the name `eigenvalues`.
Typing the skeleton showed that the natural lemma names then collide with nine existing Mathlib
lemmas about its unsorted `hA.eigenvalues`, in the very namespaces the contract puts ours in:
`Matrix.IsHermitian.trace_eq_sum_eigenvalues`, `det_eq_prod_eigenvalues`,
`posSemidef_iff_eigenvalues_nonneg`, `posDef_iff_eigenvalues_pos`,
`Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.PosDef.eigenvalues_pos`, and more. Every Mathlib
bump would risk a new collision. The accessor is therefore **`eigenvalue A k`**, singular: "the
`k`-th eigenvalue of `A`". No Mathlib declaration in those namespaces uses the singular.
