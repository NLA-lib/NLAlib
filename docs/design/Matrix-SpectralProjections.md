# Frobenius spectral projections

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`a53d25688a8cee7e96899092e758e9f0771c75dc`.

## Objects and interfaces

Use the existing `hermitianPart`, `frobInner`, `frobNorm`, `eigenvalue`, Mathlib's
`cfc`, `Matrix.IsHermitian`, `Matrix.PosSemidef`, and Loewner order. The projected
matrix is `cfc (max a) (hermitianPart A)`. At zero floor this is
`(hermitianPart A)⁺`, Mathlib's positive part. No new definition, hypothesis
interface, constant, vocabulary row, or Mathlib deviation is introduced.

All analytical statements are over `[RCLike 𝕜]` and an arbitrary finite index
type. Empty matrices, negative floors, repeated eigenvalues, and non-Hermitian
inputs are included. Feasibility `a • 1 ≤ X` already implies Hermiticity; no
redundant `X.IsHermitian` assumption is added.

## Statement shapes

The common variables are `{𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]`,
with `[DecidableEq n]` only for identities and the matrix functional calculus.

The existing real-only theorem is generalized in place, retaining its name:

```lean
theorem Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    frobNorm (cfc f A - cfc f B) ≤ frobNorm (A - B)
```

Hermitian approximation support:

```lean
theorem hermitianPart_sub (A B : Matrix n n 𝕜) :
    hermitianPart (A - B) = hermitianPart A - hermitianPart B

theorem Matrix.IsHermitian.frobInner_sub_hermitianPart
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobInner (A - hermitianPart A) X = 0

theorem Matrix.IsHermitian.frobNorm_sub_sq
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobNorm (A - X) ^ 2 = frobNorm (A - hermitianPart A) ^ 2 +
      frobNorm (hermitianPart A - X) ^ 2

theorem Matrix.IsHermitian.frobNorm_sub_eq_frobNorm_sub_hermitianPart_iff
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (A : Matrix n n 𝕜) :
    frobNorm (A - X) = frobNorm (A - hermitianPart A) ↔ X = hermitianPart A
```

Spectral-floor results below use `P = cfc (max a) (hermitianPart A)` and
`Q = cfc (max a) (hermitianPart B)` in this note only; the actual signatures
write the expressions and introduce no local public vocabulary.

```lean
theorem Matrix.IsHermitian.smul_one_le_cfc_max
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (a : ℝ) :
    a • (1 : Matrix n n 𝕜) ≤ cfc (max a) H

theorem frobInner_sub_cfc_max_hermitianPart_le_zero
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobInner (A - cfc (max a) (hermitianPart A))
      (X - cfc (max a) (hermitianPart A)) ≤ 0

theorem frobNorm_sub_cfc_max_hermitianPart_sq_add_le
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ^ 2 +
      frobNorm (X - cfc (max a) (hermitianPart A)) ^ 2 ≤ frobNorm (A - X) ^ 2

theorem frobNorm_sub_cfc_max_hermitianPart_le
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ≤ frobNorm (A - X)

theorem frobNorm_sub_eq_frobNorm_sub_cfc_max_hermitianPart_iff
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - X) = frobNorm (A - cfc (max a) (hermitianPart A)) ↔
      X = cfc (max a) (hermitianPart A)

theorem frobNorm_cfc_max_hermitianPart_sub_le
    (A B : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (cfc (max a) (hermitianPart A) -
      cfc (max a) (hermitianPart B)) ≤ frobNorm (A - B)

theorem frobNorm_sub_cfc_max_hermitianPart_sq
    (A : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ^ 2 =
      frobNorm (A - hermitianPart A) ^ 2 +
        ∑ i ∈ Finset.range (Fintype.card n),
          max (a - eigenvalue (hermitianPart A) i) 0 ^ 2
```

The supporting zero-floor bridge is
`theorem cfc_max_zero (H : Matrix n n 𝕜) : cfc (max (0 : ℝ)) H = H⁺`, obtained from
`CFC.posPart_def` and `cfcₙ_eq_cfc`. No separate real or zero-floor versions
of the optimization theorems are exported. Clipping feasibility is public;
the correction/complementarity calculation may remain private if it has no
independent consumer. Squared-distance growth implies both minimum and
uniqueness, avoiding repeated proofs of those consequences.

## Placement and consumers

- `Matrix/Functions/HermitianCalculus.lean`: generalize the existing CFC
  contraction theorem, since its subject is functional calculus. The real
  specialization remains available under the same name.
- `Matrix/Spectral/HermitianPart.lean`: linearity, orthogonality, and nearest
  Hermitian approximation. These are reusable facts about the existing
  Hermitian-part operation, not private projection machinery.
- New `Matrix/Functions/PositivePart.lean`: clipping and Frobenius projection
  onto a lower spectral bound, in dependency order. At zero floor it gives
  nearest PSD approximation with the native positive part.
- `NLAlib.lean`: regenerated root imports only.
- `docs/references.bib`: add verified Higham1988 and ChengHigham1998 provenance.

Consumers include covariance repair, PSD rounding, stable matrix-function
approximations and projected iterations. They use the minimum inequality,
the error-to-minimizer bound, and nonexpansiveness directly. No algorithm or
cost target is added. Only the nearest-PSD theorem carries the existing
`nearest-psd-frobenius` Result id; supporting API has none. The existing
`lipschitz-cfc-frobenius` id remains on the generalized theorem.

## Material and duplicate search

Original formal source: `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Functions/NearestPSD.lean`. Its Hermitian/skew definitions
are replaced by the existing `hermitianPart` and subtraction. Its
`spectralClip` and `nearestPSD` definitions are replaced by `cfc`; `frobSq`
becomes `frobNorm` squared. The unique-minimizer conjunction is split into
independently usable conclusions, and redundant Hermiticity is removed.

Proof material was also evaluated from the unmerged integration commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8`; that branch is not imported.
The current Frobenius expansion and functional calculus API replace its
explicit eigenbasis calculations wherever possible.

Mathlib/current searches found `CFC.posPart_sub_negPart`,
`CFC.posPart_mul_negPart`, `CFC.posPart_nonneg`, `algebraMap_le_cfc`,
`cfc_sub`, `cfc_mul`, `Matrix.IsHermitian.re_trace_cfc`, the existing real
`Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le`, and Frobenius bilinearity and
norm expansions. No matrix spectral-floor optimization theorem was found.
PSD trace duality already exists and is not duplicated.

Printed provenance: Higham (1988), Theorem 2.1, gives the unique nearest
real symmetric PSD matrix and exact Frobenius distance. Its proof also
gives the Hermitian/skew orthogonal decomposition. The current statements
generalize to either RCLike field and every real floor. Cheng--Higham
(1998), Theorem 3.1, gives the nonnegative-floor real symmetric version.
Both locators were directly checked in the published PDFs hosted by the
author and the University of Manchester, respectively:
<https://nhigham.com/wp-content/uploads/2023/10/high88d.pdf> and
<https://eprints.maths.manchester.ac.uk/342/1/30289.pdf>.

## Review and open questions

No maintainer interface or target decision is required. Independently
reviewed before proofs on 2026-10-31: approved mathematical scope, names,
placement, native positive-part spelling and the in-place generalization.
The review shortened the Hermitian decomposition name and made the
zero-floor bridge unconditional. Firm nonexpansiveness is not added:
the existing CFC contraction supplies the needed stability result.
