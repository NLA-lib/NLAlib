# Standard operation models and rounded Krylov programs

The standard model deliberately has unbounded exponents. There is no underflow, overflow,
or IEEE claim. Bounded-exponent arithmetic requires separate operation contracts.

## Named choices

`Ops.Standard.Scheme` supplies three choices, all backed by existing proved BLAS code:

| Scheme | Scalar arithmetic | BLAS reductions | Applicability |
|---|---|---|---|
| `.exact` | Unit roundoff zero | Sequential, zero error | Every length |
| `.sequential` | Relative error at supplied unit roundoff | Sequential accumulation | Every length |
| `.pairwise depth` | Relative error at supplied unit roundoff | Pairwise accumulation | `Nat.clog 2 n < depth` |

The errors come from `scheme.errors u`; they are derived from the selected implementations.
Matvec has a separate normwise allowance: `delta` means
`norm(A*v - computed) ≤ delta * norm(v)`. The exact scheme sets this allowance to zero too.
The solvers use the scale `em * specNorm A`. Matvec rounding is included in both run records.

A backend supplies a fixed scalar machine and decoding, its `StdModel` law, word-vector
matvec kernels and their local error bounds. `Standard.Model.ofKernels` constructs the memory
interfaces and a joint native witness. `model.access` derives the BLAS contracts and joint
realization with the proved profile. `model.laws` extracts precisely the declared interfaces
from an interpretation satisfying those contracts. `referenceModel` is an explicit idealized
real-valued rounded witness for every scheme; it is not a native hardware implementation.

## Structural membership

The operation type is closed to scalar, BLAS1 and matvec. Queries are exact comparisons;
comparison identifiers must fail when used as index conversions. There is no additional
interpreter-wide correctness assumption or escape operation.

The typing theorem in each solver's standard-model module proves that its complete fixed program
matches all signatures and uses only the declared cell format, for every named resource
configuration and every dimension. This is a kernel-checked fact, independent of linting.
Canonical `Ops.exec` enforces these signatures and counts primitive, query and structural
instructions. A full resource certificate is an `Ops.Algorithm`; a `ConditionalRuns` theorem is
proof infrastructure and is not presented as that certificate. Ordinary Lanczos and its
full-reorthogonalized variant have canonical constructors in their `Certificate.lean` modules.
Those fixed abstract BLAS trees certify the numerical output together with the mandatory
full instruction manifest, declared work/span, scoped scratch and supplied resident payload.

## Applying numerical results

1. Choose a scheme, primitive backend, matvec allowance and resource configuration.
2. Establish its model contracts, pairwise applicability if needed, and `Standard.Accuracy`.
   The envelope has `E ≤ 1/100`, matvec and axpy allowances at most `E`, and scalar/dot/scal
   allowances at most `E/16`. `Precision.of_budgets` derives Lanczos normalization safety.
3. Apply `runs_solve_of_model` in CG or Lanczos. CG additionally needs a positive spectral
   interval and its curvature and accumulated precision window. Ordinary Lanczos needs
   symmetry for its extracted numerical run. Reorthogonalized Lanczos needs symmetry for its
   stronger run/spectral analysis; its total actual two-pass history does not.
4. Take mathematical consequences from the actual returned output. Execution is not reproved.

CG, ordinary Lanczos and fully reorthogonalized Lanczos have total execution proofs under
their input assumptions, including rounded matvec. None assumes an existing successful run.
CG retains its residual-gap, physical energy and backward-model consequences.

Lanczos covers zero cap, zero input and early breakdown. Ordinary rounded Lanczos extracts
a run with exactly the executed number of rounds. Reorthogonalized Lanczos retains the full
executed history and selects a possibly shorter strictly admissible prefix for strong
numerical-run analysis; its first excluded coefficient is explicitly identified. Every packed
basis and coefficient entry matches the corresponding actual run or history; later entries
are initialized zeros. Initialization retains its actual input defect instead of assuming an
exact starting direction.

The reorthogonalized history retains both passes' coefficient and norm witnesses. Its local
orthogonalization guarantee is derived from those operations with an explicit accumulated
pass-error budget. The strongest numerical run applies to its selected admissible prefix.
For positive cap and nonzero input, ordinary `Output.exists_run_backward` transfers the existing
quadratic small-roundoff backward bound to the same physically identified ordinary run.

## Resource scope

`Standard.resources` offers unit scalar/BLAS charges or length-weighted BLAS work. Matvec work
and scratch are supplied explicitly. Span is sequential: choosing pairwise arithmetic alone
does not assert parallel scheduling. These are matrix-free operator models; resident supplied
data belong in `Problem.initial` buffers. A dense matrix hidden inside an oracle is not thereby
certified as free physical storage. Cells are abstract payload units here; physical storage
needs a representation bridge.

The solver model wrappers use the model's actual declared workspace. Linked-profile results
transfer primitive counts through sequential/pairwise BLAS lowering. Ordinary Lanczos also
has `SequentialCertification.algorithm` for the actual sequential scalar tree, with a fresh
full canonical instrumented manifest, work/span and payload bounds. Its reduction-error
budgets are derived from the scalar unit roundoff independently of the high-level BLAS scheme.
A conditional profile-transfer theorem alone is not that canonical certificate.

## Validation

Run focused warning-fatal endpoint builds, source rules, the generated root check, a full library
build and freshness check, axiom audit, scoped environment lint, strict kernel replay and the
unchanged stage script. Preserve registered targets and check scripts. Record any baseline
stage findings separately; no exemptions or compatibility shims are introduced.

## Curated Lanczos guide

[The Lanczos page](../algorithms/Lanczos.md) presents both variants' pseudocode, explicit
operation counts, resident output sizes, scratch bounds and mathematical guarantee scopes.
Exact stored prefixes support orthonormality/compression and Ritz convergence. Rounded
ordinary Ritz residuals refer to the actual decoded basis and tridiagonal and retain zero
cap/input outcomes in their full canonical postcondition.
