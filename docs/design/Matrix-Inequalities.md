# Design note: Matrix stage M7, inequalities

Status: written 2026-10-14 by the orchestrator while M3b, M5 and M6 were in progress; to be
implemented without a maintainer approval stop, by the standing instruction in
`docs/port/status.md`. Choices a maintainer would have been asked about are in §7. The skeleton
(eight files) elaborates against the pinned Mathlib and the earlier stages.

## 0. Scope

What is left of the brief's M7 after M3a took majorization, Ky Fan, von Neumann, Lidskii and
Horn's product inequality: consequences of the Loewner order (trace, determinant, inverse,
congruence, generalized eigenvalues); positive semidefinite block matrices; determinant
inequalities (Hadamard, Fischer, Hadamard–Fischer, Minkowski, Szász); Hadamard products;
entrywise functions; Kantorovich and Wielandt; the Schur–Horn theorem.

Not here: statements that need matrix functions beyond the square root (operator monotonicity,
`sqrt_le_sqrt`, the description of `B ≤ A` by `A^{-1/2} B A^{-1/2}`) go to M8; real parts of the
eigenvalues of a general complex matrix against its Hermitian part go to M10 with Schur
triangularisation; strict versions through the spectral radius of a relative matrix are replaced
by the generalized-eigenvalue statements.

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| Hadamard product | Mathlib's `A ⊙ B` (`Matrix.hadamard`) | `Matrix.PosSemidef.hadamard` is the Schur product theorem |
| entrywise function | `A.map f` | — |
| principal minor | `principalMinor A s := (A.submatrix (↑) (↑) : Matrix s s R).det` for `s : Finset n` | `principalMinor_univ`, `principalMinor_singleton` |
| determinant of a Hermitian matrix | `RCLike.re A.det` in inequalities | `Matrix.IsHermitian.det_eq_re_det` |
| generalized eigenvalues of a pair `(B, A)` | `spectrum ℝ (A⁻¹ * B)` | — |
| matrix square root | Mathlib's `CFC.sqrt A`, used in one statement | — |

## 2. Interfaces

**Everything is over `𝕜`** except the entrywise exponential and power series (real matrices,
which is what kernels are) and Horn's theorem (a real orthogonal matrix, which is the stronger
conclusion). The prototype is real throughout.

**Determinants of Hermitian matrices are compared through `RCLike.re`.** No real-valued
determinant function is introduced.

**Two-sided bounds are Loewner bounds** `a • 1 ≤ A`, `A ≤ b • 1`, as in M2; the Kantorovich and
Wielandt inequalities take them as hypotheses, and one corollary restates Kantorovich with
`conditionNumber A`.

**Spectral equivalence** of a matrix `A` and a preconditioner `M` is the Loewner sandwich
`a • M ≤ A ≤ b • M`. `M⁻¹ * A` is not Hermitian, so `eigenvalue` and `conditionNumber` say
nothing about it; the statement a Krylov consumer needs is about the symmetrically preconditioned
matrix: for any `C` with `Cᴴ * M * C = 1`, `conditionNumber (Cᴴ * A * C) ≤ b / a`. The
description through `spectrum ℝ (M⁻¹ * A) ⊆ Set.Icc a b` is one bridge lemma.

**Block criteria without inverses**: the Cauchy–Schwarz test
`|xᴴ B y|² ≤ (xᴴ A x) (yᴴ C y)` and the contraction factor `B = A^{1/2} X C^{1/2}`; the Schur
complement criteria are already in M1 and M4.

**Principal minors get a definition**, `principalMinor A s` for `s : Finset n` over a commutative
ring, in `Determinant.lean`: Szász's inequality multiplies all minors of a given size, the
Hadamard–Fischer inequality is stated once through it, and `∑ s, principalMinor A s = det (1 + A)`
is the normalising constant of a determinantal point process. The product over a size is written
`∏ s ∈ Finset.univ.powersetCard k, …`, with no second definition. M9's leading minors on `Fin n`
prefixes are to be bridged to it when that stage is designed.

## 3. Statement shapes

```lean
theorem Matrix.PosSemidef.re_det_le_re_det_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det
theorem Matrix.PosDef.inv_le_inv_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹
theorem Matrix.PosDef.inv_conjTranspose_mul_mul_le {A : Matrix m m 𝕜} (hA : A.PosDef)
    {V : Matrix m n 𝕜} (hV : HasOrthonormalCols V) : (Vᴴ * A * V)⁻¹ ≤ Vᴴ * A⁻¹ * V
theorem Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (a b : ℝ) :
    a • A ≤ B ∧ B ≤ b • A ↔ spectrum ℝ (A⁻¹ * B) ⊆ Set.Icc a b

theorem posSemidef_fromBlocks_iff_forall_norm_sq_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔ ∀ (x : m → 𝕜) (y : n → 𝕜),
      ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y)
theorem posSemidef_fromBlocks_one_iff_specNorm_le_one (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosSemidef ↔ specNorm X ≤ 1
theorem posSemidef_fromBlocks_self_iff {A B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    (Matrix.fromBlocks A B B A).PosSemidef ↔ -A ≤ B ∧ B ≤ A

theorem Matrix.PosSemidef.re_det_le_prod_re_diag {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i)
theorem norm_det_le_prod_norm_col (B : Matrix n n 𝕜) : ‖B.det‖ ≤ ∏ i, ‖WithLp.toLp 2 (B.col i)‖
theorem re_det_fromBlocks_le_of_posSemidef {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    RCLike.re (Matrix.fromBlocks A B Bᴴ C).det ≤ RCLike.re A.det * RCLike.re C.det
theorem Matrix.PosSemidef.re_det_rpow_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹
theorem Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k d : ℕ} (hkd : k + d = Fintype.card n) :
    (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^ k ≤
      (∏ s ∈ Finset.univ.powersetCard k, RCLike.re (principalMinor A s)) ^ d

theorem Matrix.PosSemidef.hadamard_le_hadamard_of_le {A B C : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : B ≤ C) : A ⊙ B ≤ A ⊙ C
theorem Matrix.PosSemidef.smul_diagonal_le_hadamard {A B : Matrix n n 𝕜} {a : ℝ}
    (hB : B.PosSemidef) (hA : a • (1 : Matrix n n 𝕜) ≤ A) :
    a • Matrix.diagonal (fun i => B i i) ≤ A ⊙ B
theorem specNorm_hadamard_le (A B : Matrix m n 𝕜) : specNorm (A ⊙ B) ≤ specNorm A * specNorm B
theorem Matrix.PosDef.inv_hadamard_le_hadamard_inv {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊙ B)⁻¹ ≤ A⁻¹ ⊙ B⁻¹
theorem Matrix.PosSemidef.re_det_mul_prod_re_diag_le_re_det_hadamard {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det
theorem Matrix.PosSemidef.map_of_hasSum {A : Matrix n n ℝ} (hA : A.PosSemidef) {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) {f : ℝ → ℝ} (h : ∀ i j, HasSum (fun k => c k * A i j ^ k) (f (A i j))) :
    (A.map f).PosSemidef

theorem re_quadForm_mul_re_quadForm_inv_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (x : n → 𝕜) :
    RCLike.re (quadForm A x) * RCLike.re (quadForm A⁻¹ x) ≤
      (a + b) ^ 2 / (4 * a * b) * ‖WithLp.toLp 2 x‖ ^ 4

theorem majorized_iff_exists_hasOrthonormalCols_diag_eq {d lam : n → ℝ} :
    Majorized d lam ↔
      ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ (Q * Matrix.diagonal lam * Qᵀ).diag = d
```

## 4. Consumers

| Item | Consumed by |
|---|---|
| order consequences, inverse and compression inequalities | Nyström and sketched preconditioners; Schur complement analysis; comparison of estimators |
| spectral equivalence through generalized eigenvalues | preconditioned conjugate gradients (the condition number of `M⁻¹ A`), sketch-and-precondition |
| block criteria | semidefinite characterisations of norms; contraction arguments in M8 and in matrix concentration |
| Hadamard, Fischer, Minkowski | volume sampling and determinantal point processes; log-determinant estimation; D-optimal design |
| Szász, principal minors | volume sampling; maximum-volume submatrices (M9) |
| Hadamard product inequalities, entrywise functions | kernel matrices (polynomial, exponential, Gaussian); random features; Schur multipliers |
| Kantorovich, Wielandt | steepest descent and conjugate gradient rates |
| Schur–Horn | diagonal estimators; existence of matrices with prescribed diagonal and spectrum |

## 5. Files

Under `NLAlib/Matrix/Inequalities/`:

1. `Order.lean` (imports M2 `Loewner`, M3 `Weyl`, `SingularValues`).
2. `Block.lean` (imports M1 `SchurComplement`, M2 `Loewner`, Mathlib `Analysis.Matrix.Order`).
3. `Determinant.lean` (imports 1, M1 `SchurComplement`).
4. `PrincipalMinors.lean` (imports 3).
5. `HadamardProduct.lean` (imports 3, Mathlib `Kronecker`).
6. `EntrywiseFunctions.lean` (imports 5).
7. `Kantorovich.lean` (imports 1, M4 `ConditionNumber`).
8. `SchurHorn.lean` (imports M3a `Schur`, M1 `PlaneRotation`, M5 `Frames`).

Independent for proving: 1, 2, 8 at once; then 3, 7; then 4, 5; then 6.

## 6. Material

Read: prototype `Matrix/Inequalities/*` not already ported in M3a (44 modules).

Reused: the determinant inequalities and their equality cases; the Hadamard product chain
through the Kronecker product; the entrywise power series argument; Kantorovich through the
operator inequality; Horn's theorem through minimisation over the compact orthogonal group and
plane rotations.

Not reproduced: `principalMinorProduct` (written as a product); the normalised Szász chain with
binomial exponents (the unnormalised inequality is the content); statements through
`spectralRadius` of a relative matrix; real dot-product forms of the block tests; the
counterexample file; scalar helper lemmas; the many helper definitions of the prototype's proof of
Horn's theorem (`columnProjectionMass`, `coordinateSelector`, `projectedColumn`, …), which stay
private if the proof is ported.

## 7. Decisions taken without approval

1. **The stage is restated over `𝕜`**, with determinants through `RCLike.re`.
2. **`principalMinor` is a definition; the product of minors of a size is not.**
3. **Spectral equivalence is the Loewner sandwich `a • M ≤ A ≤ b • M`**, with
   `conditionNumber (Cᴴ * A * C) ≤ b / a` for `Cᴴ * M * C = 1` as its consequence and
   `spectrum ℝ (M⁻¹ * A) ⊆ Set.Icc a b` as one bridge; no `spectralRadius` statements.
4. **Horn's theorem produces a real orthogonal matrix**; the orbit statement for a Hermitian
   matrix over `𝕜` is a corollary.
5. **Operator-monotone statements and the Hermitian-part majorization leave this stage** (M8,
   M10).

## 8. Review (Fable, 2026-10-14) and what changed

The review confirmed `RCLike.re A.det` (a real-valued determinant would be a second spelling;
real-only statements would break the field rule), `principalMinor` on `Finset`s, and the truth of
every statement it was asked to check, including the Hadamard-inverse inequalities with `A⁻¹`
over `ℂ`, the semidefinite and size-zero cases, and the complex Wielandt inequality. Folded in:

1. Spectral equivalence is the Loewner sandwich, with the condition number of the symmetrically
   preconditioned matrix as the consumer-facing statement (decision 3 revised).
2. The Hadamard–Fischer inequality is stated once, through `principalMinor`, whose definition
   moved to `Determinant.lean`; `sum_principalMinor` added.
3. The two-sided Hadamard bound is two theorems; the equal-diagonal block criterion lost a
   redundant hypothesis; Kantorovich with the condition number is written
   `(κ + 1)² / (4 κ)`; Horn's theorem uses `ᴴ`.
4. Removed as duplicates of earlier stages or of Mathlib: `eigenvalue_last_pos`,
   `re_quadForm_mem_Icc`, `mul_conjTranspose_self_le_one_iff_specNorm_le_one`, `re_det_nonneg`.
   The Hadamard–Kronecker identity moved to `ForMathlib/LinearAlgebra/Matrix/Hadamard.lean`.
5. The two trace-tail lemmas were dropped: no consumer in the Matrix layer.
6. Left for M8: `log det (1 + A) ≤ tr A` and concavity of `log det`. Left for M9: the bridge from
   `principalMinor` to leading minors.
