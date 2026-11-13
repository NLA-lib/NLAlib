# Programs and certificates

Part of the [contributor guide](../../CONTRIBUTING.md).

## Fixed programs and total guarantees

An algorithm is an `Ops.Algorithm`: one fixed `Ops.Program`, together with a proof for a
specified `Ops.Problem`, `Ops.AccessModel` and `Ops.Specification`. A theorem about an existing
program uses `Ops.Program.Certifies`. The program is fixed before dimensions, input data,
interpreters and tapes are quantified. It cannot inspect a theorem's proof or select a new
program from its input outside the syntax.

The certificate proves total execution for every admitted input and interpreter meeting the
model's declared contracts. The output property and all resource bounds refer to the same
instrumented run. A liberal weakest-precondition lemma is useful infrastructure; it does not
replace total correctness. Headline theorems state the mathematical, representation and range
assumptions needed to run, rather than assuming successful execution.

A problem declares input data, admitted dimensions and raw initial buffers. Inputs are not
silently replaced by a processed answer. An access model declares primitive and query contracts,
storage formats and costs, and jointly realizes those contracts at each admitted input. Read
these declarations alongside the output specification: the types enforce the promised statement,
while choosing a meaningful statement and faithful primitive meanings remains a review duty.

Programs have computable definitions [E2]. `scripts/OpsPrograms.lean` inventories fixed programs
and algorithm certificates, checks computability, and rejects imports of the retired execution
core. Whole-library axiom audits and kernel replay check proofs independently. The old target
registry and compiled-tree hash workflow are retired; they are not a second certificate system.

## Choosing an operation model

Choose the abstraction level explicitly: scalar arithmetic, BLAS operations, stored matrix
operators, or matrix multiplication and QR. Standard collections live under
`NLAlib/Ops/Catalog`; joint profiles live under `NLAlib/Ops/Profiles`. A custom collection has
its own explicit operand signatures, input admission and contracts, together with a joint
realization. A primitive contract describes that primitive, not the result of a whole algorithm.

An exact functional model identifies word operations with mathematical functions. A rounded
model additionally relates decoded outputs to exact arithmetic with explicit relative/absolute
errors and safe ranges. Exact functional contracts alone imply no numerical accuracy theorem.
Likewise, an opaque word type or a format tag does not establish physical IEEE arithmetic,
finite encodability, or elapsed time.

Aliasing belongs to the operation's admission conditions. Use spatial footprints to admit
separate views of one arena when their cells are disjoint. Exact in-place aliasing is allowed
only by a contract proved for it; shifted partial overlap must not inherit that guarantee.
BLAS reductions require their output apart from inputs, while supported maps permit either
exact aliasing or separation. Stored matrix operators make the actual data operand explicit;
dense and coordinate representations require their own packing and validity conditions.

## Proving programs as mathematics

1. State the pure function and its mathematical properties independently of memory. A program
   proof then identifies its actual stored output with that function.
2. Use `Ops.Writes` for a total or liberal postcondition with an explicit write footprint.
   Shared call rules consume declared operation contracts. `Ops.Writes.seq`,
   `Ops.Writes.keep` and read-only predicates compose calls while preserving disjoint inputs.
3. Express matrices with shared entry codecs and stored-block predicates. Capacity, subview
   containment, separation and packing round trips belong to shared layout APIs, not a new
   record per program stage.
4. Use shared loop rules with ordinary mathematical invariants: an iterate, an output prefix,
   or a family indexed by active slots. Independent iterations can use
   `Ops.writes_loop_disjoint_prefix` or its scratch-sharing version. Prove a reusable rule when
   a second algorithm needs the same memory or counted-loop argument.
5. Use scoped allocation rules to introduce fresh buffers and transport the postcondition back
   through cleanup. Supplied buffers include uninitialized capacity; scratch is measured above
   that initial storage.
6. Derive the public certificate with shared constructors. `Ops.Algorithm.ofWpActual` combines
   a total word proof with actual counted resource bounds. Its internal execution equations
   are proof tools, not hypotheses in the algorithm's total public guarantee.

Call specifications should accept index expressions at the abstraction level needed by their
callers. Avoid forcing a loop's variable offset to unify with a constant-only theorem. State
sub-blocks separately, elaborate each call theorem before composing it, and keep store transport
in the shared frame APIs. Default proof-length and heartbeat rules apply to program proofs too.

## Resources and probability

Canonical execution checks input formats and operation admission, then counts original calls,
queries, index evaluation, addressing, control, allocation and release. Allocation counts carry
`[format.bytes, elementCount]`; abstract cells do not become physical fp64 bytes by renaming.
Primitive and query workspace are additional declared charges. Certificates bound full counts,
work, sequential span, scratch payload and initial-plus-scratch payload.

Static manifests provide conservative bounds. Actual counted proofs may sharpen selected work
terms using loop invariants and partition inequalities while retaining conservative bookkeeping.
State which terms are sharp. Span adds across this sequential syntax; primitive parallel span
is not a scheduler or work-per-processor theorem.

For random algorithms, identify the exact tape windows consumed and the stored sample
transformation, including any normalization and rounding. A finite packed Gaussian sample tape
is not an infinite independent tape law. Probability transfers must include execution failure,
all resource failures and the claimed output failure on the same counted run. Use the shared
`NLAlib/Ops/Probability.lean` transfer rather than an assumption that execution succeeds.

## Checks and examples

`NLAlib/Ops/Tools/ProgramFixtures.lean` checks concrete full accounting, workspace reservations,
format and arity rejection, and failure diagnostics. `NLAlib/Ops/Tools/LintFixtures.lean` checks
heuristic review diagnostics. Structural rejection examples and canonical certificate examples
are ordinary kernel-checked library modules; lint is guidance, not a substitute for their types.

Worked developments include Gram–Schmidt, Hutch++, sign/deflation, and spectral bisection:
see [the algorithm pages](../algorithms/) for their model choices and assumptions. The core
reference is [Ops certification](../design/Ops-Certification.md), with
[resource accounting](../design/Ops-Resources.md) and the [Ops README](../../NLAlib/Ops/README.md).

During development, check only the edited modules and relevant dependents. The shared gate
`scripts/ops/lean_gated.sh` serializes Lean work on a shared host. Run the full
`scripts/stage_check.sh` once sources are stable, followed by the check-script unit tests when
scripts change. The complete validation procedure is in [CONTRIBUTING](../../CONTRIBUTING.md).
