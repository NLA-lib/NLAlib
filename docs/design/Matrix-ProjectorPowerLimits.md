# Matrix powers converging to an idempotent

Design dated 2026-10-31 against `NLA-lib/NLAlib` commit
`bed23695d496f24548e0d8222b1096409fdb659c`.

## Objects and interfaces

Use Mathlib's `IsIdempotentElem`, ordinary multiplication equations, `Filter.Tendsto`,
and the existing `specRadius` and `specNorm`. No new definition, predicate, vocabulary
row, named bound, or Mathlib deviation is needed. The idempotent may be oblique:
self-adjointness is not assumed. The equations `T * P = P` and `P * T = P` retain the
actual invariant projection, rather than choosing an eigenbasis.

## Statement shapes

The algebraic identity belongs to `ForMathlib/Algebra/Ring/Idempotent.lean`, in the
namespace of the Mathlib predicate, for any possibly noncommutative ring:

```lean
theorem IsIdempotentElem.sub_pow_succ
    {R : Type*} [Ring R] {p : R} (hp : IsIdempotentElem p)
    {a : R} (hap : a * p = p) (hpa : p * a = p) (k : ℕ) :
    (a - p) ^ (k + 1) = a ^ (k + 1) - p
```

For `{𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]`,
extend `Matrix/Spectral/PowerBounds.lean`:

```lean
theorem tendsto_pow_iff_specRadius_sub_lt_one
    (T P : Matrix n n 𝕜) (hP : IsIdempotentElem P)
    (hTP : T * P = P) (hPT : P * T = P) :
    Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 P) ↔ specRadius (T - P) < 1

theorem exists_forall_specNorm_pow_sub_le_mul_pow
    (T P : Matrix n n 𝕜) (hP : IsIdempotentElem P)
    (hTP : T * P = P) (hPT : P * T = P)
    {r : ℝ} (hr : specRadius (T - P) < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, specNorm (T ^ k - P) ≤ C * r ^ k

theorem isUnit_of_specRadius_one_sub_mul_lt_one
    {A M : Matrix n n 𝕜} (hρ : specRadius (1 - M * A) < 1) : IsUnit A
```

The positive-power identity is not claimed at exponent zero. The norm estimate
handles that exponent separately, and its constant depends on the matrices and
the prescribed rate; it is not a universal constant. The growth estimate requires
only `specRadius (T - P) < r`, not `r < 1`. A rate below one gives convergence.
All matrix statements include empty index types. No diagonalizability or normality
is assumed. The first analytic theorem strengthens the source's implication to
an equivalence. The generic algebraic identity replaces the source's matrix-only
version, with no second public spelling.

## Consumers and placement

`PowerBounds.lean` owns the spectral-radius criterion, geometric error estimate,
and invertibility consequence. Perron projectors, deflated power methods, and
stationary iterations can consume them without recreating power estimates. The
original atlas already uses the projector result in `Matrix/Nonnegative/PerronDeflation.lean`.
The ring identity is independent of matrix vocabulary and is an upstream candidate
for Mathlib's `Algebra/Ring/Idempotent.lean`. It may also be used for endomorphisms.
A private eventual-equality lemma is local to transferring the two power limits.

## Material and reuse audit

Original formal source: `tchen-research/NLAlib` commit
`77514ce42a0e437d837797a063ac161f41022730`:

| Source declaration | Decision |
|---|---|
| `matrix_pow_mul_eq_of_mul_eq` | Local induction inside the generic identity; no matrix wrapper. |
| `matrix_sub_projector_pow_succ` | Generalize to `IsIdempotentElem.sub_pow_succ` over any ring. |
| `tendsto_matrix_pow_projector_of_deflated_spectralRadius_lt_one` | Generalize real to `RCLike`, and implication to equivalence. |
| `exists_specNorm_matrix_pow_sub_projector_le_geometric` | Use the native spectral radius and existing growth theorem; positive constant, including exponent zero. |
| `isUnit_sub_of_tendsto_splitting_pow_zero` | Extract the spectral invertibility consequence for an arbitrary square preconditioner. |

The first four are in `Matrix/Spectral/ProjectorDeflationPowers.lean`; the last is
in `Krylov/Solvers/StationarySplitting.lean`. Evaluated proof material also includes
unmerged integration commit `af301c893d85b6ccc78f4144468b6dd07c7aaab8` in
`DiarHaidary/NLAlib`.

Mathlib's `Algebra/Ring/Idempotent.lean`, `Algebra/Group/Idempotent.lean`, and
commuting-power API were searched: no equivalent power-subtraction identity was
found. Existing `IsIdempotentElem.pow_succ_eq` treats the idempotent's own powers,
not powers after subtracting it. The matrix proofs reuse
`tendsto_pow_zero_iff_specRadius_lt_one`, `exists_forall_specNorm_pow_le_mul_pow`,
and `isUnit_det_one_sub_of_specRadius_lt_one`; no spectral or norm construction is
reproved. The inherited literature context is Horn--Johnson, Chapter 8; the
generalized statements are documented as consequences of the existing power API,
without inventing an exact printed locator.

## Review decisions

No maintainer decision is required about a new interface or a target. The only new
module is the generic ring identity; all matrix results extend their existing topic.
The convergence criterion shares the existing `convergent-matrix` result group;
supporting growth and invertibility statements do not create duplicate cards.
