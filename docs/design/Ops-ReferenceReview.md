# Reviewing the meaning of an Ops certificate

This is the human review boundary for the reference semantics, not a requirement
to inspect every algorithm proof. Start with the reference rules, follow the
shared definitions below, then inspect the particular problem, model and claim.
Generated constructors, projections and recursors are covered by their parent
structure or inductive declaration; their implementation is checked by Lean.

The reference rules share memory, index and format definitions with the
implementation. The equivalence proof establishes agreement with these explicit
shared choices. It does not independently validate their intended meaning.

## What this is, and what it is not

The reference rules are a readable restatement of execution and accounting. Lean checks that
they give exactly the outcome of the evaluator the certificates are defined with. That removes
the instrumentation and the counted evaluator from what a reader must study. It does not show
that the rules, or the definitions they share with the evaluator, express the intended
semantics: that is the judgement this review asks for.

The computed list of every library declaration a certificate's meaning depends on is
`scripts/ops_trusted_base.txt` ([checks](../contributing/checks.md), "The trusted base"). This
map explains the declarations of that list; the list is the authority on which they are.

### Modelling conventions fixed by the core

These are choices, not consequences. They hold for every model and every certificate.

| Convention | Where it is stated | What it means for a claim |
|---|---|---|
| The unit of memory is a word of an abstract type `K` | `Store`, `Buf` | A cell holds one value of `K`, which the core never inspects: a real number, a floating-point word or a bit, as the model chooses. |
| Storage widths are declared labels | `StorageFormat`, `StorageFormat.bytes` | Memory is width times capacity. Nothing proves that a value of `K` fits in the declared width. A real-number model charged eight bytes per cell states the real-RAM convention, not an encoding. |
| Index arithmetic has unit cost | `Reference.index`, `Reference.operands`, `Bookkeeping` | Each index operation, address resolution and loop round is one structural instruction whatever the magnitude of the numbers. The cost table is keyed by operation, so a cost growing with the size of an index cannot be expressed. Counts are word-RAM counts for control, also in a model whose words are bits. |
| An early-exit loop pays one final query evaluation | `Reference.Derives.whileFuel` | The dimension and address charges of the loop's query are added once with `exit`, also when the fuel runs out and no query is made. The count is then an upper allowance, by at most that one evaluation. |
| Query workspace is reserved, not tracked | `Reference.Execution`, `ResourceModel.queryReserve` | The largest workspace among the executed queries is added once to the allocation and primitive peak. The scratch figure is an envelope, not the maximum of simultaneously live bytes. |

## 1. The reference rules and their public meaning

Names in this section have the prefix `NLAlib.Ops.Reference`.

| Exact declarations | Source | What to check |
|---|---|---|
| `State` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | This is the existing state: memory/tape position, full counts, live scratch and peak. |
| `core`, `index`, `dimensions`, `operands` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | Each index constructor has its own charge. Operand offsets and address resolution are included. Allocation keys include width and capacity. |
| `charge`, `called`, `allocated`, `released` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | Charges preserve memory; calls reserve workspace above live scratch; allocation adds payload; release pops a buffer and restores the outer live payload. |
| `Derives` and every constructor | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | Sequence order, actual branch selection, live and shape-preserving primitive calls, index bounds, scoped allocation, frames and transparent notes. Abort has no success rule. |
| `Repeats.zero`, `Repeats.succ` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | A counted loop executes indices zero through the cap minus one, with one round charge each. |
| `While.cap`, `While.stop`, `While.step` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | A query precedes each body; false stops; zero fuel performs no query; the returned index is used by the continuation. |
| `Execution` | [Reference/Semantics.lean](../../NLAlib/Ops/Reference/Semantics.lean) | Initial counts/live scratch/peak are zero. Format and buffer-arity checks are required. The final peak adds the conservative query reservation exactly once. |
| `Accepts` | [Reference/Probability.lean](../../NLAlib/Ops/Reference/Probability.lean) | The same derived outcome satisfies all five resource bounds and the supplied accuracy event. No event means no accuracy claim. |

Read the statement of
[`Program.certifies_iff_reference`](../../NLAlib/Ops/Reference/Equivalence.lean)
next. It universally quantifies admitted sizes, inputs, interpretations satisfying
the model, and tapes. The existential outcome satisfies the source rules, scratch,
counts, work, span, resident memory and `good`, on that same execution.

For randomized claims, read
[`Algorithm.failsAtMost_iff_reference` and `RandomizedClaim.reference_holds`](../../NLAlib/Ops/Reference/Probability.lean).
They retain the original law, `admits`, `interprets`, event and bound. Negated
acceptance includes execution failure and every resource/event violation.

## 2. Shared memory and tape definitions

Names in this and the next sections have the prefix `NLAlib.Ops`.

| Exact declarations | Source | What to check |
|---|---|---|
| `StorageFormat`, `StorageFormat.bytes`, `.cell`, `.fp16`, `.bf16`, `.fp32`, `.fp64` | [Store.lean](../../NLAlib/Ops/Store.lean) | Width is positive. A tag declares modeled payload width; it does not prove an encoding of arbitrary words into that width. |
| `Buf`, `Store`, `Store.get`, `.len`, `.shape` | [Store.lean](../../NLAlib/Ops/Store.lean) | A store is a stack of buffers of optional words. Invalid/uninitialized reads fail. Shape records capacities, not values. |
| `Store.upd`, `.updBlock`, `.readBlock` | [Store.lean](../../NLAlib/Ops/Store.lean) | Exact locations and order of reads/writes. Bare updates are total and ignore out-of-range locations; success obligations supply capacity. |
| `Store.push`, `.pop` | [Store.lean](../../NLAlib/Ops/Store.lean) | Allocation appends a fresh uninitialized buffer; release removes the last buffer. |
| `Mem`, `Mem.upd`, `.updBlock`, `.advance`, `.write`, `.Live`, `.readBlocks` | [Store.lean](../../NLAlib/Ops/Store.lean) | Memory includes the tape position. Ordinary updates preserve it. Guarded writes check capacity; liveness checks buffer handles. |
| `Mem.updBlocks`, `.Room` | [BlockRel.lean](../../NLAlib/Ops/BlockRel.lean) | Multi-block updates follow the listed order, including aliases; output-room obligations match each supplied block length. |
| `Tape`, `Tape.shift`, `.window` | [Stream.lean](../../NLAlib/Ops/Stream.lean) | A tape is indexed by position then stream. Shifts affect every stream's position; windows are the stated finite positions. Stream names alone assert no distribution. |

## 3. Shared syntax, addressing and format checks

| Exact declarations | Source | What to check |
|---|---|---|
| `IExp`, `IExp.eval`, `.evalList` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | Unbound indices fail. Subtraction is truncated natural subtraction; division rounds down and returns zero on divisor zero. These are index operations, not scalar arithmetic. |
| `Operand`, `Operand.eval`, `.evalList` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | Buffer-variable lookup and evaluated offsets identify the actual operands. |
| `Env`, `Env.pushIdx`, `.pushBuf`, `.frame` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | Loops extend index scope; allocations extend handle scope; frames supply fresh dimensions, offsets and handles. |
| `Stmt`, `Note`, `Bookkeeping` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | The permitted statement forms, bounded control flow, metadata and distinct structural charge names. There are no runtime syntax-building callbacks. |
| `Program`, `Program.environment` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | One tree is fixed before runtime inputs. Its initial environment contains only sizes, zero offsets and supplied handles. |
| `OperandSignature`, `Operand.formatList`, `Stmt.wellTyped`, `Program.wellTyped` | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | All initial/allocated formats must be declared. Calls and both query forms match operand signatures; frames inherit the actual buffer formats, including aliases. |

## 4. Primitive meanings, counts and resources

| Exact declarations | Source | What to check |
|---|---|---|
| `Interp` | [Exec.lean](../../NLAlib/Ops/Exec.lean) | Primitives have the stated memory/tape arguments; Boolean/index queries have their stated arguments. Concrete meanings come from the model's contracts. |
| `Count`, `Count.one`, `.test`, `.lift` | [Exec.lean](../../NLAlib/Ops/Exec.lean) | Counts are Mathlib finite-support functions keyed by operation/query identity and dimensions. Structural keys are distinct from original operations. Weighting is additive. |
| `St`, `St.init` | [Exec.lean](../../NLAlib/Ops/Exec.lean) | `cur` is live scratch, `peak` is its allocation/primitive peak; both and all counts initially vanish. Supplied payload is accounted separately. |
| `ResourceModel` and all its fields | [Syntax.lean](../../NLAlib/Ops/Syntax.lean) | Formats, signatures, primitive/query workspace, and operation/query/core work/span weights are fixed by this execution model. The only built-in cost laws are span no greater than work. |
| `ResourceModel.work`, `.span` | [Exec.lean](../../NLAlib/Ops/Exec.lean) | Full counts, including structural instructions and queries, are weighted. Sequential syntax adds primitive spans; no scheduling theorem is asserted. |
| `ResourceModel.queryReserve` | [Exec.lean](../../NLAlib/Ops/Exec.lean) | Reservation is the maximum workspace among executed query keys. It is added to the allocation/primitive peak; it is not the exact maximum of simultaneous live bytes. |
| `Mode`, `Mode.Needs`, `.Holds`, `OpSpec`, `Contract`, `Contract.on`, `Interp.Satisfies` | [Contract.lean](../../NLAlib/Ops/Contract.lean) | Total contracts require success under the precondition. The contract receives only its declared tape window. Liberal satisfaction is not a certificate. |
| `QueryContract`, `Interp.SatisfiesQuery` | [Contract.lean](../../NLAlib/Ops/Contract.lean) | The declared Boolean/index relations constrain the actual query results, including possible failure. |
| `BlockRel`, `BlockRel.Post`, `.spec` | [BlockRel.lean](../../NLAlib/Ops/BlockRel.lean) | Operand lengths, input domain, output relation, exact tape advance, output capacity and frame behavior have the intended meaning. |
| `AccessModel`, `AccessModel.contracts` | [Contract.lean](../../NLAlib/Ops/Contract.lean) | The hypotheses are exactly the declared primitive/query contracts. They have a joint realization at each admitted input; the word/tape type is inhabited. |
| `Contract.Confined`, `QueryContract.Confined`, `AccessModel.Uniform`, `.Confined`, `.Charged` | [Confined.lean](../../NLAlib/Ops/Confined.lean) | Optional model properties describe locality, input independence and positive charges. They do not justify a primitive's chosen computational cost. |

## 5. The problem and standard arithmetic model used by a claim

These are part of each claim's review, not consequences of the generic execution
equivalence. A new proof may use established definitions, which reduces this work
to checking the chosen instantiation and its explicit assumptions.

| Exact declarations | Source | What to check |
|---|---|---|
| `Problem`, `Problem.Input`, `.initial`, `.initialBytes` | [Contract.lean](../../NLAlib/Ops/Contract.lean) | Admitted sizes/data/raw buffers cover the intended problem. Initial memory contains exactly the supplied words. Resident payload includes uninitialized capacity. |
| `Codec`, `Slot`, `Routine.Domain`, `Routine.Domain.problem`, `.buffers`, `.bytes` | [RoutineProblem.lean](../../NLAlib/Ops/RoutineProblem.lean) | Typed inputs, derived preprocessing buffers, blank outputs, unstored data and acceptance are all visible. Codecs invert at the declared lengths. |
| `Routine.Domain.Oracles` | [RoutineProblem.lean](../../NLAlib/Ops/RoutineProblem.lean) | Unstored data is reached through the declared operations. Their meaning and cost match the claimed abstraction. |
| `Specification`, `Runs`, `Program.Certifies` | [Static.lean](../../NLAlib/Ops/Static.lean) | All bounds and `good` concern the same counted outcome; input-dependent accuracy conditions have not been confused with size-only resource bounds. |
| `Algorithm` | [Cert.lean](../../NLAlib/Ops/Cert.lean) | The proof certifies the particular fixed program, model and specification under review. |
| `ScalarOp`, `Machine`, `Machine.fn`, `AnyOperands`, `IsScalar` | [Catalog/Scalar.lean](../../NLAlib/Ops/Catalog/Scalar.lean) | Scalar contracts refer to the intended word functions and decoding. |
| `StdModel` | [Catalog/Scalar.lean](../../NLAlib/Ops/Catalog/Scalar.lean) | Relative-error arithmetic includes square root; negation is exact. Division accuracy requires a nonzero decoded divisor and square-root accuracy a nonnegative argument. Overflow/underflow are outside this model. Check any additional roundoff hypotheses of the particular theorem. |
| `MixedModel`, `ExactModel` | [Catalog/Scalar.lean](../../NLAlib/Ops/Catalog/Scalar.lean) | Mixed relative/absolute allowances and safe ranges, or exact arithmetic, are the intended alternatives. |
| The actual model expression, e.g. `RoundedScalarBlas.model` | [Profiles/RoundedScalarBlas.lean](../../NLAlib/Ops/Profiles/RoundedScalarBlas.lean) | The certificate really uses that machine and primitive basis. Calling a vector operation once is different from lowering it to scalar operations. |

## 6. Extra declarations for randomized claims

| Exact declarations | Source | What to check |
|---|---|---|
| `Reference.Accepts` | [Reference/Probability.lean](../../NLAlib/Ops/Reference/Probability.lean) | Successful source execution, all resource bounds and the exact accuracy event. A separate deterministic output guarantee is still supplied by the algorithm certificate. |
| `Specification.Accepts` | [Probability.lean](../../NLAlib/Ops/Probability.lean) | The canonical event being bridged includes failure and every resource/event violation, rather than conditioning on successful execution. |
| `TapeModel`, `TapeModel.streams`, `.packed`, `.Realizable` | [Randomized.lean](../../NLAlib/Ops/Randomized.lean) | Which tapes and distributions are covered; stream identifiers are distinct; a probability-space witness exists under the claim's input assumptions. |
| `IsTapeLaw` | [TapeLaw.lean](../../NLAlib/Ops/TapeLaw.lean) | The specified entry distributions, measurability and joint independence are what the intended algorithm requires. |
| `Algorithm.FailsAtMost` | [Randomized.lean](../../NLAlib/Ops/Randomized.lean) | Quantifier order fixes the interpretation before sampling. The measure is finite; check that the chosen law gives the intended probability normalization. |
| `RandomizedClaim` and every field | [Randomized.lean](../../NLAlib/Ops/Randomized.lean) | `law`, `admits`, `interprets`, `event`, `bound`, `realizable`, `holds`. Realizability of the law does not by itself establish the numerical or interpreter assumptions. |

Mathlib supplies natural-number arithmetic, lists, finite-support functions,
finite-set maxima, measures, real-valued measure, laws and independence. The
read-back adds no new measurability premise or probability model. Lean's kernel
and the existing Lean/Mathlib foundation remain trusted dependencies.

## 7. Worked accounting read-back

[`Payload.resource_readback`](../../NLAlib/Ops/Examples/Reference.lean) states exact
values for an independently specified example. All byte quantities below are
modeled payload, not a hardware-layout assertion.

| Stage | Live scratch | Primitive temporary | Allocation/primitive peak so far |
|---|---:|---:|---:|
| Two supplied four-byte words | 0 | 0 | 0 |
| Three two-byte outer cells allocated | 6 | 0 | 6 |
| Two eight-byte inner cells allocated | 22 | 0 | 22 |
| Primitive call | 22 | 7 | 29 |
| Inner buffer released | 6 | 0 | 29 |
| False query, with five-byte query workspace | 6 | 0 | 29 |
| Outer buffer released | 0 | 0 | 29 |

Query workspace is accounted by the separate maximum-query reservation. Adding
that reservation gives `29 + 5 = 34` bytes of canonical scratch, and adding the
supplied payload gives `8 + 34 = 42`. This conservative envelope need not be the
maximum simultaneously live payload. `Payload.query_reserve_two_keys` separately
checks that two query keys reserve their maximum, not the sum of their workspaces.

The exact count is nine structural instructions, one primitive and one query.
Weights are deliberately unequal: work is `9 + 11 + 2 = 22` and span is
`9 + 3 + 1 = 13`. The theorem also states that final memory is the original memory
and live scratch returns to zero.

## 8. What the kernel checks after this review

[`Reference/Accounting.lean`](../../NLAlib/Ops/Reference/Accounting.lean) and
[`Reference/Equivalence.lean`](../../NLAlib/Ops/Reference/Equivalence.lean) establish
exact agreement with canonical execution, including failure, and the full
certificate read-back. The source bridge's live-scratch/peak invariant holds
from the initial zero state; the canonical theorem adds no hypothesis for it.

The probability bridge identifies acceptance events pointwise before taking
their measure. Tactics, static polynomial bounds, routine adapters and linking
proofs are ways of constructing certificates checked against these statements.
They do not replace the mathematical definitions listed above.

An independent review should record whether those definitions express the
intended semantics, separately from whether the proofs check. The complete
implementation/validation record is in
[Ops-ReferenceSemantics.md](Ops-ReferenceSemantics.md).
