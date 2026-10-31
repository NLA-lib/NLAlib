# Scaled-isometry Procrustes

Design dated 2026-10-31, against `NLA-lib/NLAlib` at
`2c59d004a38ae717f05aae5ffb620f667781e45e`.

## Objects and interfaces

Extend the existing Procrustes API. Use `HasOrthonormalCols`, `frobNorm`, `frobInner`,
`nuclearNorm`, Mathlib's `CFC.sqrt`, and the real scalar action on an `RCLike` matrix.
No new definition, predicate, vocabulary row, named bound, or Mathlib deviation is needed.

The factor is an arbitrary isometric polar extension, characterized by
`HasOrthonormalCols U` and `U * CFC.sqrt (Aᴴ * A) = A`. Do not substitute the canonical
`polarFactor A`: it need not have orthonormal columns when `A` is rank deficient.

## Statement shapes

All statements use the following variables, without a row-index decidable-equality hypothesis:

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
  [Fintype m] [Fintype n] [DecidableEq n]
```

The objective, its lower bound, and its attaining point are supporting API:

```lean
theorem HasOrthonormalCols.frobNorm_sub_smul_sq_of_mul_sqrt_eq
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) (c : ℝ) :
    frobNorm (A - c • U) ^ 2 =
      frobNorm A ^ 2 - 2 * c * nuclearNorm A + (Fintype.card n : ℝ) * c ^ 2

theorem HasOrthonormalCols.frobNorm_sq_sub_nuclearNorm_sq_div_le
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (A : Matrix m n 𝕜) (c : ℝ) :
    frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) ≤
      frobNorm (A - c • U) ^ 2

theorem HasOrthonormalCols.frobNorm_sub_div_smul_sq_of_mul_sqrt_eq
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) :
    frobNorm (A - (nuclearNorm A / (Fintype.card n : ℝ)) • U) ^ 2 =
      frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ)
```

The named mathematical result is the attained minimum:

```lean
theorem isLeast_frobNorm_sub_smul_sq (A : Matrix m n 𝕜)
    (hcard : Fintype.card n ≤ Fintype.card m) :
    IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix m n 𝕜),
      HasOrthonormalCols U ∧ frobNorm (A - c • U) ^ 2 = z}
      (frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ))
```

Negative real scales, zero matrices, rank-deficient inputs and empty column types are included.
For empty columns the objective and minimum are zero; Lean's total division makes a separate
empty-dimension theorem unnecessary. The dimension condition belongs only to the existence
statement; a supplied isometry already provides the feasibility needed by the other statements.
There is no uniqueness assertion about the optimizing factor or the signed scale.

## Reuse and duplicate search

Mathlib's matrix, polar/singular-value and norm APIs were searched: no joint scalar/isometry
optimization theorem was found. The current library already supplies the required mathematics:

| Needed fact | Existing declaration |
|---|---|
| Expansion of the objective | `frobNorm_sub_sq` |
| Real scaling | `frobInner_smul_right`, `frobNorm_real_smul` |
| Norm of an isometry | `HasOrthonormalCols.frobNorm_sq` |
| Nuclear dual bound | `abs_frobInner_le_nuclearNorm_mul_specNorm` |
| Contractivity | `HasOrthonormalCols.specNorm_le_one` |
| Equality for an isometric polar extension | `HasOrthonormalCols.frobInner_eq_nuclearNorm_of_mul_sqrt_eq` |
| Existence, including singular matrices | `exists_hasOrthonormalCols_mul_sqrt_eq` |

In particular, do not repeat the trace calculation establishing nuclear dual equality. The new
quadratic formula rewrites with the existing equality. Its average-scale specialization is a
short corollary, and the existence theorem applies the existing polar-extension theorem.

The four contracts serve different uses: arbitrary-scale error evaluation, a lower bound for
any supplied competitor, evaluation at a supplied optimal factor, and existence of a global
minimum. They are not real/complex or positive-dimension/empty-dimension twins.

## Consumers and placement

All four additions belong in `NLAlib/Matrix/Factorizations/Procrustes.lean`, after the existing
Procrustes problems, with updated module documentation. Their topic is matrix approximation by
scaled isometries, not construction of the polar decomposition. No other Lean file changes.

The objective formula supports scale selection and perturbation calculations. The universal
lower bound supplies certificates for candidate approximations. The equality theorem certifies
an explicitly supplied isometric polar extension. The attained-minimum theorem supports scaled
alignment and matrix approximation arguments without exposing an SVD construction.

## Source material and consolidation

Read the original [tchen-research/NLAlib library](https://github.com/tchen-research/NLAlib)
at `77514ce42a0e437d837797a063ac161f41022730`, module
`NLAlib.Matrix.Factorizations.ScaledOrthogonal`. Its six declarations are:

- `frobSq_sub_smul_polar_eq`;
- `frobSq_sub_nuclearNorm_sq_div_card_le_sub_smul`;
- `frobSq_sub_avg_smul_polar_eq`;
- `isLeast_frobSq_sub_scaled_orthogonal`;
- `isLeast_frobSq_sub_scaled_orthogonal_of_isEmpty`;
- `frobSq_sub_trace_rowGram_avg_smul_leftPolar_eq`.

The first five are covered by the four broader contracts above: rectangular matrices over any
`RCLike` field, with the dimension-zero case integrated. The last is a left-polar/trace spelling
of the equality theorem, derived by existing adjoint and nuclear-norm identities rather than
exported as a second theorem for the same optimum.

All six source-form specialization checks compiled on 2026-10-31. They express the old squared
Frobenius norm as the real entry sum using `frobNorm_sq_eq_sum_sq`, and retain the old positive
dimension assumptions where present, even though the new statements do not need them. For the
left-polar form, adjoint the supplied equation and apply the attaining-scale theorem to `Aᴴ`
and `Uᴴ`. Then `nuclearNorm_eq_re_trace_sqrt` at `Aᴴ`, `nuclearNorm_conjTranspose`, and
`frobNorm_conjTranspose` recover the old trace coefficient and error. This checks the source
formulations through the native API without importing the original library or exporting twins.

Earlier proof material exists in the unmerged integration commit
`af301c893d85b6ccc78f4144468b6dd07c7aaab8`, in `Factorizations/Polar.lean`. It is material for this
focused contribution, not a dependency; the earlier mixed branch remains separate. The old
backend's `frobSq` spelling, real/transpose variants and extra dimension assumptions are not
reintroduced. Public docstrings retain the original formal-library provenance and explain the
generalization. The backend's repeated locator 7.4.6 is corrected to 7.4.4: its published-PDF
coverage index, `docs/coverage/hj13.md` at the same source pin, line 558, identifies the best
scaled-unitary approximation there. Lines 559-560 distinguish ordinary Procrustes (7.4.5)
and the two-sided rotation problem (7.4.6). The docstring cites `[HornJohnson2013, §7.4.4]`
as square-case provenance and states the rectangular and empty-column generalizations.
The relevant printed pages could not be independently retrieved during this migration;
the corrected locator is supported by that local source index, not a new direct page review.

## Explorer metadata and validation

Use `Result: procrustes-scaled` only on `isLeast_frobNorm_sub_smul_sq`. This distinguishes the
joint optimization from `nearest-unitary`, which already describes the unscaled result, and
from `procrustes`, which already describes the fixed-target problem. Helpers remain ordinary
supporting API. No new Explorer schema or application change is needed.

Review exact signatures, placement, naming, source scope and the duplicate search before proofs.
Then run the touched-file rules check, a warning-fatal build, the complete unchanged
`scripts/stage_check.sh`, and a reuse report for the four new declarations. Check the original
square-real, empty-dimension and left-polar formulations by compiling external examples, without
adding duplicate public statements.

## Maintainer questions and review record

No new interface, vocabulary, target, check or allowlist decision is proposed. Recommendation:
keep this as one focused Procrustes contribution before moving to another matrix topic.

Design reviewed independently on 2026-10-31 before proof edits. The mathematical scope,
interface reuse, helper placement, degenerate cases and Explorer metadata were approved.
The reviewer requested the lower-bound name above under N8 and recommended the `div_smul`
name for the attaining-scale specialization; both amendments were accepted before implementation.
An independent source review then approved the four implementations, including the signed-scale
argument, absent row-index decidable-equality assumption, and singular and empty cases.

Validation completed on 2026-10-31: the unchanged `scripts/stage_check.sh` exited 0; all six
source-form checks compiled; the extraction-backed check of `Procrustes.lean` reported zero
errors and zero warnings. The duplicate report contained no new duplicate class and no public
duplicate class. Its eight existing private-only classes are in unrelated Krylov files. The
reuse report confirmed direct use of the existing nuclear dual-pairing theorem and polar
extension existence theorem. The `NLAlibTools` import-root check also passed.
