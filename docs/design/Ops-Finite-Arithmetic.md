# Finite arithmetic and BLAS proof trials

User refinement: test finite arithmetic and BLAS on the Ops core. Preserve the prior proof
trials and all registered targets/checks. No commits or pushes.

## Objects and statements

The existing StdModel explicitly assumes no underflow/overflow and applies to every rational
literal. It is not an appropriate finite-carrier hypothesis. Add `MixedModel u eta dec M safe`
in Ops/Catalog/Scalar: the same machine operations, but numerical accuracy is required only
when the exact operation result satisfies `safe`; errors are `u * abs target + eta`. Include
nonnegative error parameters and exact negation. Existing StdModel supplies the eta-zero case.
This models total machines with a specified overflow behavior; no accuracy is promised outside
safe. It introduces no evaluator, instruction or trust rule.

`MixedModel.abs_add_mul_sub_le` bounds the executed multiply-then-add by
`((1+u)^2-1)*(abs y+abs(a*x)) + (2+u)*eta`. The guards cover both the product and the addition
of its actual rounded value, not just the final ideal expression. Division retains a nonzero
input guard. Consumers are axpy and scal, including zero vectors and empty lengths.

Ops/Blas/Mixed: componentwise mixed-error theorems for axpyF/scalF and total WP theorems
for the existing axpyLoop/scalLoop. Reuse their functional execution proofs; do not reproduce
buffer/loop bookkeeping. The conclusions expose the actual updated memory and its numerical
bound. Resource/canonical certification is not inferred from these WP statements.

Ops/Examples/FixedPoint: bounded integer words scaled by a positive integer; nearest rounding
uses Mathlib `round`, with explicit saturation to the finite range. Prove the carrier finite,
prove the mixed model with u=0 and eta=1/(2*scale), and instantiate the shared BLAS proofs.
The witness uses actual finite words and nonzero rounding errors, not exact real arithmetic.
It is a mathematical fixed-point format, not a native IEEE accuracy claim.

## Shared machinery and searches

Mathlib `abs_sub_round`, `round_eq_iff`, finite integer intervals, and real inequalities.
Existing Ops `Machine`, `IsScalar`, `wp_axpyLoop`, `wp_scalLoop`, axpyF/scalF and their length
lemmas. Existing Computation binary floating-point proofs were inspected; Ops cannot import
Computation under its existing layer rule, and no duplicate binary representation is added.
MixedModel is the shared scalar hypothesis interface. `IsAxpyMixedErr` and `IsScalMixedErr`
are the mixed BLAS output predicates; their eta-zero bridges recover the existing predicates.
`AxpySafe` and `ScalSafe` name the executed-target range hypotheses. The separate tools-only
fixed-point example was also inspected: it uses unbounded integers and cannot witness a finite
carrier or be imported into the proved library.

## Validation plan

Focused --wfail builds, finite rounding regressions, source rules, full root build and unchanged
stage check. Record exact scope and any existing check failures. Numerical proofs must retain
both range guards and the absolute underflow term.

## Trial outcomes

The fixed-point carrier and its complete scalar model are shared across arbitrary bounds and
positive scales. The error allowance is exactly half a grid step; no hypothesis asserts a
relative-only model on the finite carrier. `not_stdModel_machine` explicitly proves that the
half-unit-grid witness cannot satisfy StdModel with u<1, using an underflowing literal.
`axpySafe_zero` supplies admitted inputs at every vector length, so guarded domains are nonempty.
The scalar interpretation is constructed from the very same finite machine.

Both AXPY and scaling numerical proofs reuse this model. Their total WP bridges to actual
stored vectors take three tactic lines each; no loop invariant or memory update proof is
repeated. The finite AXPY program proof is another direct application with its model supplied.
The instrumented static counts project to n multiplications plus n additions for AXPY and n
divisions for scaling. These count identities leave structural operations in the full count;
they are not new canonical resource certificates.

The concrete regressions prove actual rounding of 1/2 squared, underflow of 1/8 to zero,
saturation of 5 to 4, and a cancellation trap: 2*3-3 has ideal result 3, within [-4,4], but its
product 6 saturates to 4 and the computed result is 1. Dropping the intermediate guard would
make the claimed half-unit AXPY error bound false on this input.

## Scope and assessment

Finite carrier, executed programs and model realization are proved together. The shared
functional loop proofs were already general enough; their unconditional relative numerical
model was the wrong hypothesis for finite-range execution. The new guarded mixed model fixes
that proof interface without changing syntax or evaluator semantics. Existing statements and
all registered targets remain unchanged.

This trial uses a mathematical fixed-point format. Native IEEE overflow/NaN behavior,
ties-to-even accuracy and a full canonical Algorithm certificate for these kernels are not
established here. Saturation is the explicit finite witness policy, not an accuracy guarantee
outside the admitted range. Each later solver must prove its own per-operation range facts.

## Validation results

- Focused build of the finite-format witness and shared BLAS module: passed with `--wfail`.
- Full `lake build --wfail NLAlib`: passed, 4,637 jobs.
- `lake build --no-build --rehash NLAlib`: all targets current, 4,637 jobs.
- Source rules for all four new/changed finite-arithmetic files: zero errors; four warnings on
  pre-existing scalar docstrings. Reference check: zero problems. `git diff --check`: clean.
- All four finite-arithmetic modules (scalar catalog, BLAS catalog, mixed BLAS and finite
  fixed point): zero environment-linter errors under 14 linters.
- All new headline model, execution, count and finite-carrier results depend only on Lean's
  standard logical axioms.
- Unchanged repository stage: 954 proved modules build with zero warnings; global audit checks
  35,684 declarations with zero violations. The stage stops at the pre-existing CastOp
  deriving-instance unused-argument findings. No check, target or baseline was modified.
- Strict unmodified library replay (`REPLAY_ROOTS=NLAlib REPLAY_STRICT=NLAlib`): 35,685 constants
  of 955 modules replay through Lean's kernel with zero violations; the existing checker exempts
  its 83 standard compiler `_unsafe_rec` auxiliaries. This does not claim that the full stage
  passed or that the tools library was replayed.
