# Operation core

The canonical API lives in the existing syntax, evaluator, contracts, static analysis and
certification files. Lint is optional prover guidance; none of these guarantees depends on it.

## Execution and operation models

`Program Op Tst r b` contains one first-order statement tree, fixed before runtime sizes or
inputs. Sizes enter `Program.environment`; raw buffers enter a separately specified `Problem`.
There is no runtime tree-building, preprocessing or environment-building callback.
`Op` and `Tst` are the closed signatures of permitted operations and queries. Each source call
names one of those operations. Index expressions have only the arithmetic constructors in
`IExp`; statements have only the constructors in `Stmt`.

`AccessModel` declares a `Contract` for every operation and a `QueryContract` for every query.
`AccessModel.contracts` is defined to be exactly satisfaction of those contracts. There is no
field for arbitrary additional interpreter assumptions, whole-program success or desired outputs.
The model must provide a joint realization of those exact contracts at every admitted input.
`Problem` requires an admitted size and an input at every admitted size. The model supplies an
actual word, so universal tape quantification cannot be vacuous.

Canonical `exec p I resources formats tape sizes memory` always elaborates index arithmetic,
operand addressing, control and allocations into explicit structural counters. Original operations,
structural instructions and queries have distinct keys. Allocation and release carry
`[format.bytes, elementCount]`, so weights can account for both width and capacity.
The interpretation cannot turn accounting off. `exec_mem` proves exact agreement with the memory
semantics `run`, including failures. Structural elaboration is an internal part of the evaluator,
not an optional wrapper around a different certification API.

The counters have abstract operation meaning. `Count.totalWeight` requires explicit weights for
operations, queries and structural instructions. `Count.original` explicitly projects only the
original-operation/query coordinates; it does not replace a full canonical budget.
Storage is format-aware. `allocAs format n` charges `format.bytes*n` modeled payload bytes;
`alloc n` means abstract `.cell` width1. `Problem.formats` declares the initial layout.
`ResourceModel` fixes permitted formats and primitive/query operand signatures, and canonical
execution checks the entire lexical format discipline, including aliases and frames. Explicit
conversion uses a declared operation with distinct input/output formats. No implicit retyping
or smaller forged representation can satisfy a different signature.

Certificates separately bound scratch, initial-plus-scratch payload, work, span and full counts.
Primitive workspace is in the same modeled byte units; queries reserve the largest workspace
among actual executed query keys, conservatively added to the allocation/primitive peak.
`stmtPeak_instrument` proves the allocation/primitive part is unchanged by elaboration.
`ResourceModel.work` and `span` weight the full count. Work and span use the same cost units;
FLOPs and seconds cannot be mixed in the span<=work comparison. Span permits internal primitive
parallelism but adds across sequential calls; no fork/scheduler/work-P speedup is inferred.
The per-key span<=work laws imply `ResourceModel.span_le_work` for the entire execution.

Format widths are model declarations, not a proof that arbitrary K values fit those bits.
Tagging exact real-valued words fp64 does not establish a physical 64-bit representation.
Physical byte/time claims require faithful storage encodings and justified primitive resource
models. Payload accounting excludes metadata, allocator headers/alignment, code and tape.
Oracle or backend storage included in a memory claim is declared as input payload or covered
by its resource model; an opaque matvec does not automatically account for a stored matrix.
See [resource design](../../docs/design/Ops-Resources.md) and `Examples/Resources.lean`.

## Certification

`Runs p model specification`, also written `p.Certifies model specification`, requires successful
canonical execution at every admitted size and input, under every interpretation satisfying
exactly the declared contracts and every tape. The budget, peak workspace and postcondition refer
to that same execution. `Specification` fixes all resource budgets and the postcondition
independently of the program. `Algorithm model specification` packages one fixed program and
this total proof.

`Algorithm.ofWp` uses the total statement logic and full structural bounds to construct the
certificate. `Algorithm.link` takes a fixed implementation table and verifies the entire lower
program against a separately realized lower model and specification, including introduced frames
and allocations. `Algorithm.runsLaw` observes the output of the same certified execution.

`Impl.program` adapts a fixed implementation with fixed operand syntax, preserving aliases.
A wrong operand arity elaborates to failure. Canonical `Impl.Meets` certifies this fixed program;
it has no liberal mode or success-companion convention.

Operation meanings and primitive costs, the declared input representation, and the relevance of
the specified postcondition remain properties of the chosen problem and operation model.

## Proof construction

The statement interpreters `eval` and `evalCounted`, judgments `ConditionalRuns`,
`ConditionalRunsW`, `ConditionalRunsL`, and conditional implementation relation `Impl.Triple`
form the proof calculus. `Wp` and its constructor rules can express total or liberal correctness.
`Profile.Refines` transfers conditional contracts and resource bounds through a fixed table.
These constructions do not assert model realizability or uniformity of a runtime tree family.
They are useful ingredients for a canonical certificate, not substitutes for one.

`ConditionalRuns` is a total execution theorem under its explicit input and interpretation
hypotheses. It does not assume that execution succeeds. The liberal form `ConditionalRunsL`
is partial correctness and is useful only as an internal proof step toward a total result.

The named builder in `Logic/Builder.lean` elaborates to the same statement trees. Use
`let t ← allocAs format n` for explicitly formatted scratch. The legacy `alloc n` helper
allocates abstract one-unit cells; it does not select a floating-point representation.
`Logic/Writes.lean` provides format-aware single and chained allocation rules, and
`Logic/Tactic.lean` supplies `alloc as`, `loop_inv`, `keep`, and `checkpoint` for block proofs.

The catalog supplies exact and standard-error scalar contracts, exact and error-bounded BLAS1,
and matrix-vector and comparison contracts. Sequential and pairwise BLAS profiles prove their
contracts through `Profile.Refines`. The CG, PCG, and Lanczos developments use this conditional
proof layer; a canonical certificate additionally fixes the problem, realized model, and full
resource specification.
The existing BLAS profiles allocate abstract `.cell` scratch. A format-specific specialization
uses explicitly formatted allocation and workspace measured in the same modeled byte units.

## Standard collections and stored implementations

`Profiles/Standard.lean` supplies exact, sequential-rounded and pairwise-rounded numerical
models for Krylov analysis. `Profiles/ExactBlas.lean` generates the exact scalar/vector
collection for real or complex words. `ExactLinear` adds explicitly stored operators,
sampling and dimension literals; `ExactScalarLinear` replaces BLAS by scalar conjugation;
`ScalarOnly` contains no vector or matrix-operation names. `Catalog/Functional.lean`
generates exhaustive local contracts and a joint realization from the declared functions
and spatial admissions. Primitive meanings, admissions, weights and word encodings remain
explicit model choices.

`Profiles/RCLikeScalar.lean` implements the six BLAS operations using scalar arithmetic and
conjugation. `StoredDense` and `StoredCOO` implement matrix application from declared matrix
words; `StoredScalar` composes their tables into the scalar-only signature. Linking retains
the complete lower instruction tree and its temporaries.

`Context.lean` forwards fixed extra input capabilities through procedure frames.
`Logic/ContextLink.lean` transfers an existing total word proof using local primitive laws
and a protected raw-data snapshot. `ContextProblem.lean` prefixes supplied raw buffers and
proves their reads, capacities and resident payload. Stored CG/PCG and Lanczos use these
rules to expose actual matrix and preconditioner data to scalar loops. The proof-side
source guard never becomes an omitted runtime operation. See the
[current program guide](../../docs/contributing/programs.md) and
[context design](../../docs/design/Ops-Context-Linking.md).

## Files

| File | Role |
| --- | --- |
| `Syntax.lean` | Index/operand/control syntax, fixed `Program`, structural elaboration |
| `Exec.lean` | Canonical `run`/`exec`, statement interpreters, memory projection |
| `Contract.lean` | Contracts, `Problem`, declared query contracts, closed `AccessModel` |
| `Static.lean` | Full `staticCost`/`staticPeak`, `Runs`, static soundness |
| `Cert.lean` | `Algorithm`, canonical `Impl.Meets`, conditional `Impl.Triple`, constructors |
| `Link.lean`, `Transfer.lean` | Fixed implementation tables, count projections and explicit weights |
| `Logic.lean`, `Rules.lean`, `Counted.lean` | Conditional proof rules |
| `Store.lean`, `Frame.lean` | Buffer memory, liveness, shape preservation and frames |
| `Tape.lean`, `TapeLaw.lean`, `Law.lean` | Tape locality, laws and output observations |
| `Catalog/`, `Blas/`, `Profiles/` | Operation contracts and conditional implementations |
| `Examples/Certification.lean` | Repeated-addition certificate and adversarial regressions |
| `Examples/Resources.lean` | Mixed-format storage, workspace, and work/span certificates |

The regressions address the canonical interfaces directly: impossible joint models, vacuous
inputs/tapes, runtime tree factories, failed execution, undeclared calls, omitted structural work,
and index arithmetic in a zero-round loop. No test invokes a linter to establish rejection.

Design: [Ops-Certification](../../docs/design/Ops-Certification.md).
Breaking API changes: [rename map](../../docs/renames/Ops-certification.md).
