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

A model of a published certificate is confined (`Ops.AccessModel.Confined`), and is uniform
(`Ops.AccessModel.Uniform`) unless it declares an oracle, which the certificate's documentation
names. State closed-form work and span: `Ops.Program.countPoly` computes an explicit polynomial
in the sizes from the fixed tree and `Ops.Algorithm.withCountPoly` restates a certificate with
it. Work defined as the weight of `staticCost` of the program is a manifest and is reported as
such. `scripts/OpsPrograms.lean` computes one line of properties for every certificate and
compares it with `scripts/ops_certificates.txt`: the model (`uniform`, `confined`, `charged`),
each resource field (`closed`, `manifest`, or `unknown` when the check cannot inspect it), the
problem (`derived` from a `Routine.Domain`, or `handwritten`), its derived slots and unstored
inputs, the `Oracles` declaration of a model that is not uniform, and the randomized claim. A
new certificate has a confined model, closed-form work and a derived problem. Read what a
certificate states with `OPS_CERTIFICATES_REPORT=Name lake env lean scripts/OpsPrograms.lean`
([Ops README](../../NLAlib/Ops/README.md), "What the model must also satisfy"). What client
code may depend on is listed there under "What client code may depend on".

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
6. Write a tree that other programs call, or that is certified, as a routine, with
   `routine% [n, k] (b : n, x : n) → (x, r : n, p : n) { … }`: the header is the interface
   (read, written and updated operands with their lengths; `draws`, `by blocks`, `isolated`,
   `unreported` where needed; an operand named again on the left, without its
   length, for a tree run with two of its operands equal). A tree is a routine when it has
   operands of its own and something calls it through its interface: a `run` in another tree, a
   linking table or a certificate. A piece of one routine's tree that works on buffers that
   routine allocates, or at offsets computed inside its operands, is a fragment: a plain `Stmt`
   written with `ops%`, with one statement of its run in operand form, used only inside the
   proof of the routine that contains it, and its docstring names that routine. A kernel that
   several routines run on operands of its own is a routine, as the fill and the batch of
   draws are (`Ops.fillRoutine`, `Ops.sampleRoutine`); the rotation and coefficient kernels of shifted
   QR and the small-eigenvalue solver and the matrix kernels of `NLAlib/Ops/Blas` are still
   operand-form trees from before routines existed, and are to be converted, so do not take
   them as a model. Every statement in operand form says in its docstring what it is: a
   fragment of a named tree, shared by named trees, or a step in the proof of a named theorem. A caller runs a routine by its interface,
   `run R [dims] (operands)`, and a fragment by its buffer variables. State its specification
   with `spec%` on named
   dimensions and blocks, or with `Ops.Routine.Spec.ofRel` when the routine implements an
   operation contract. Prove one statement, `XRoutine_meets : XRoutine.Meets I XSpec`, opening
   with the intro tactic of `NLAlib/Ops/Logic/RoutineIntro.lean`, using each callee by
   `call h [dims] (operands) as …`, and closing with the exit tactic of that file. Do not
   restate the result in operand form, and do not write an admission of
   operands or a lemma listing which operands are apart: separation is fixed by the modes. Three
   exceptions keep an operand-form lemma, with the reason stated at it: one tree that is the body
   of several routines or table entries (an operation admitted in several operand layouts) is
   proved once for all of them; the judgment of a loop body read on the loop's invariant; and a
   statement that must hold for an empty block placed past the end of a buffer
   (`NLAlib/Ops/README.md`, "One statement per routine"). A routine may have several judgments:
   a leaf with a definite output states it once for any machine as an exact-output judgment, and
   each error model's judgment reads its bound off it. A guarantee that holds only with high
   probability over the draws is stated with `Ops.PWrites` (`NLAlib/Ops/Logic/Probabilistic.lean`),
   in operand form, beside a judgment against `Ops.Routine.Spec.terminates`. A
   table that implements an operation by the routine uses `Ops.Routine.Meets.satisfies_ofRel`,
   with the interface checked by the implements tactic of `NLAlib/Ops/Logic/RoutineIntro.lean`
   (`NLAlib/Ops/README.md`, "Writing a routine and certifying it"). A counted run of the routine,
   for a profile that accounts a linked operation, is derived with
   `Ops.Routine.Meets.runs_ofRel`, not proved again.
   A routine on stored data (a matrix forwarded to the products of a matrix-free routine) is
   `R.withData lens T`, specified with `Ops.Routine.Spec.onData`, and its judgment is
   `Ops.Routine.Meets.withData` applied to the judgment of `R`; do not reprove the linked tree.
7. State the problem with `Ops.Routine.Domain` (`NLAlib/Ops/RoutineProblem.lean`): the admitted
   sizes, the type of the inputs, the admitted inputs, and for each operand whether its buffer
   holds an input (with its `Ops.Codec`), words computed from the inputs, or blank cells. Do
   not write a `Problem` by hand: its admissibility relation is then the author's, and a reader
   cannot see what is covered. Name it `inputs` and the problem `problem` (an `abbrev` of
   `(inputs …).problem`, so that the two are interchangeable in proofs). Every input satisfying
   the acceptance predicate is covered (`Ops.Routine.Domain.covers`); a restriction on the
   inputs belongs in that predicate, where the `_checked` theorem shows it as a hypothesis.
   An input that is in no buffer (the matrix of a matrix-free solver) is declared as the
   unstored part of the inputs, and the certificate states `Ops.Routine.Domain.Oracles` for
   its model: the operations that may depend on that data, with proofs that every other
   operation has one contract at all sizes and inputs and that a declared operation sees the
   input only through its unstored part. Data outside memory can hide work behind one call,
   so a reviewer reads the contracts and the costs of the declared operations, and the work
   of such a certificate is a count of calls of them.
   Derive the public certificate with `Ops.Routine.Domain.algorithm` against a
   stated `Specification`, and state what it says in a `_checked` theorem: the proposition
   `Ops.Routine.Domain.Checked` of the certificate (proved by `Ops.Routine.Domain.checked_all`;
   it includes every resource bound, the resident memory among them),
   or a form with the output on values (`Ops.Mem.Holds`: a buffer holds a value). Its docstring
   says what a reader checks beyond it: the declared oracles, or the probability theorem that
   carries the accuracy when the deterministic claim is termination. A counted certificate,
   `countedAlgorithm`, is that certificate with
   the work as a bound on the instruction polynomial of the tree
   (`Ops.Algorithm.withCountPoly`), for models whose weights are at most one; check the closed
   form of that polynomial with the kernel reflexivity tactic of
   `NLAlib/Ops/Logic/KernelRfl.lean` and evaluate it with the polynomial evaluation tactic of
   `NLAlib/Ops/OperationCount.lean`. `Ops.Routine.certify` is the same construction for a
   routine whose certificate states exactly its specification. A reviewer of the certificate reads the routine's
   specification, the problem, the operation model and the stated work; the tree, its proof and
   the count are checked by Lean.
8. For a program that is not the tree of a routine, `Ops.Algorithm.ofWpActual` combines
   a total word proof with actual counted resource bounds. Its internal execution equations
   are proof tools, not hypotheses in the algorithm's total public guarantee.

Call specifications should accept index expressions at the abstraction level needed by their
callers. Avoid forcing a loop's variable offset to unify with a constant-only theorem. State
sub-blocks separately, elaborate each call theorem before composing it, and keep store transport
in the shared frame APIs. The proof-length rule applies to program proofs too, and so does the
heartbeat rule: an override is allowed only with a comment that says what is expensive (rule F6).

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

State the result as a `Ops.RandomizedClaim` of the certificate (`NLAlib/Ops/Randomized.lean`),
named for the certificate with the suffix `Claim` (`claim` in a `Certification` namespace). Its
fields are what a reader checks: the law of the tape (`Ops.TapeModel.streams` for independent
entries with stated stream laws, `Ops.TapeModel.packed` for a packed random object, or the law
written out), the hypotheses on the input and on the interpretation, the accuracy event, the
failure bound, and the proof that the law is realizable (`Ops.TapeModel.Realizable`; the
streams of `streams` must be distinct). State the claim about the certificate at its own
parameters: a claim about the certificate at a fixed field or a bundle of operations is
recorded as `claim=related:…`, which is not a claim of the certificate. A certificate whose
routine has the specification `Ops.Routine.Spec.terminates`
must have a claim; the certificate check `scripts/OpsPrograms.lean` fails otherwise. The
headline theorem may stay as the statement the claim's proof applies.

## Names of routines, files and certificates

One name for each thing, in every family:

- **Routine, spec, judgment.** A routine `fooRoutine` has the specification `fooSpec`, and its
  judgment is named by appending the suffix "meets" after an underscore
  (`Ops.sumSeqRoutine`, `Ops.sumSeqSpec`, `Ops.sumSeqRoutine_meets`). The suffix `Routine`
  distinguishes it from its tree `foo`; a routine written with its tree in one `routine%` block
  and no separate tree is just `foo`, with `fooSpec` and the same suffix for its judgment.
- **A second judgment of the same routine** adds a tag after the judgment's name
  (`Ops.sumSeqRoutine_meets_exact`). When it is against
  another specification, that specification is `foo<Tag>Spec` (the rounded normalization, the
  exact-output `axpy` loop). When it is the same specification at particular parameters (zero
  error under an exact model, say) there is no second specification. The tag `of` names the
  form generic in its relations, with the specification `fooSpecOf`.
- **A linked or stored routine** meets the specification of the routine it is built from: a
  routine linked through a table is `R.link T`, one on stored data is `R.withData …`. The solver
  on stored data is named as the matrix-free one, in the namespace `X.Stored`
  (`HSCG.Stored.solveRoutine`, `HSCG.Stored.zeroStartRoutine`).
- **Namespaces of variants** are nested in one order: the family, its algorithmic variant
  (`Carried`, `Reorth`), `Rounded`, then `Stored`, `Linked` or `Scalar` (the solver on stored
  data, linked through a table, or linked down to scalar operations), then `Certification`,
  as in `Lanczos.Reorth.Rounded.Stored.Certification`. Directories follow the namespace as far
  as `Rounded/`; the stored, linked and scalar variants are files with that prefix.
- **Rounded variants** live in the namespace `X.Rounded` and the directory `X/Rounded/`, with
  the same file names as the exact family. A family whose namespace is not split (shifted QR,
  SmallEig) marks its rounded files and declarations with the prefix `Rounded`/`rounded`. The
  directories `Krylov/FinitePrecision` and `Matrix/FinitePrecision` hold the mathematics of
  rounding errors and the machines of the rounded models (with, in the `Ops*` files of
  `Matrix/FinitePrecision`, the statements of the matrix kernels on those machines), not solvers.
- **Files.** The certificate of a solver is in `Certification.lean`, matching the namespace
  `X.Certification`; a variant has a prefix (`StoredCertification.lean` for
  `X.Stored.Certification`, `LinkedCertification.lean`, `ScalarCertification.lean`). The trees
  and routine definitions of a solver are in `Alg.lean`. The specification and judgment of the
  routine `fooRoutine` are in a file named for it: `Foo.lean`, or `FooRoutine.lean` when
  `Foo.lean` holds the mathematics or the tree, and plain `Routine.lean` for the routine a
  directory is named after.
- **Certificates and programs.** The certificate of a routine is named for it with the suffix
  `Algorithm`, on the program with the suffix `Program` (`ShiftedQR.stepAlgorithm` on
  `ShiftedQR.stepProgram`, `Sign.signAlgorithm` on `Sign.signProgram`). In a namespace that
  holds one solver's certificate (`X.Certification`) or one solver on stored data (`X.Stored`),
  the solver's name is dropped: `algorithm`, `program`, `problem`, `specification`. A further
  certificate of the same solver has a prefix saying what it adds: `countedAlgorithm` has its
  work as a closed form, `scalarAlgorithm` and `scalarCountedAlgorithm` are those of the solver
  linked down to scalar operations, `exactReferenceAlgorithm` is the certificate at the exact
  reference model, `ritzAlgorithm` adds the Ritz postcondition. With a solver's name the prefix
  comes first (`ShiftedQR.exactDeflationAlgorithm`,
  `SpectralBisection.countedBisectionAlgorithm`).
- **Statements in operand form** about a tree are named for the tree, with the suffix `writes`
  after an underscore for a `Writes` statement (with its footprint), `wp` for a
  weakest-precondition statement without one, and `pwrites` for a probabilistic one
  (`Sign.loop_writes`); a second statement adds a tag after
  (`ShiftedQR.rotateRows_writes_word`). The rules of the program logic in `NLAlib/Ops/Logic`
  are about statement forms, not trees, and are named as Mathlib names rules, conclusion first
  (`Ops.writes_frame`).
- **In prose**, the interface of a routine is written with its modes,
  `[n] (x : read n, y : update n) → (z : write 1)`; the routine notation infers the modes from
  the side an operand is named on, so the header in the source does not show them.
- **Bound variables in the core.** `R` is a routine, `E` an implementation of an operation (a
  table entry), `B` a block relation, `S` a specification.

## Checks and examples

`NLAlib/Ops/Tools/ProgramFixtures.lean` checks concrete full accounting, workspace reservations,
format and arity rejection, and failure diagnostics. `NLAlib/Ops/Tools/LintFixtures.lean` checks
heuristic review diagnostics. Structural rejection examples and canonical certificate examples
are ordinary kernel-checked library modules; lint is guidance, not a substitute for their types.

Worked developments include Gram–Schmidt, Hutch++, sign/deflation, and spectral bisection:
see [the algorithm pages](../algorithms/) for their model choices and assumptions. The core
reference is the [Ops README](../../NLAlib/Ops/README.md), with
[resource accounting](../design/Ops-Resources.md); [Ops certification](../design/Ops-Certification.md)
records an earlier design.

During development, check only the edited modules and relevant dependents. The shared gate
`scripts/ops/lean_gated.sh` serializes Lean work on a shared host. Run the full
`scripts/stage_check.sh` once sources are stable, followed by the check-script unit tests when
scripts change. The complete validation procedure is in [CONTRIBUTING](../../CONTRIBUTING.md).
