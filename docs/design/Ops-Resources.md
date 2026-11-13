# Format-aware storage and operation resources

Requested by the maintainer after canonical certification, 2026-11-11. Preserve the closed
contract boundary; no new arbitrary interpreter assumptions or linter dependency.

## Objects and statements

`StorageFormat` describes a fixed-width representation by identity and positive payload byte
size. Standard formats include binary16, bfloat16, binary32 and binary64. `Stmt.allocAs f n s`
allocates n words with format f, charging f.bytes*n bytes; the old `alloc` is the one-byte
cell abbreviation for conditional scalar-word proofs. Numerical interpretation remains a
specified contract over opaque K; format and arithmetic/accumulator precision are separate.

`ResourceModel Op Tst` fixes permitted representations, operation input/output signatures,
Boolean/index query input signatures, primitive/query workspace bytes, and explicit work/span
weights for operations, queries and core instructions. All costs are nonnegative. One model
represents one configuration, including any internal parallel implementation tradeoffs.

`Stmt.wellTyped` computes the lexical buffer format discipline. Input formats come from the
Problem; allocation adds a format, frames inherit operand formats (including aliases), and
all calls/queries must match their model signatures. There is no retyping operation. Explicit
conversion is an ordinary declared operation with differing input/output formats and a
count/workspace charge. Canonical execution rejects an ill-typed tree before interpreting it.
Formats need not be duplicated in raw Mem: lexical buffer typing is fixed by input declarations
and allocAs and preserved by every constructor; primitive callS already forbids store-shape
changes. Bare Mem and the conditional calculus are representation-erased construction tools.

`Problem.formats` declares initial buffer formats. `initialBytes` measures their actual supplied
capacities. Canonical certificates bound scratch payload bytes, total resident payload bytes
(initialBytes+peak scratch), full instruction counts, and model-weighted work and span.
All budgets and models are fixed independently of the program's proof.

Canonical `exec` takes the fixed resource model and input formats, checks typing, then uses
mandatory structural elaboration. Builtin allocation counts retain format size and length.
Queries gain declared workspace charges as well as work/span charges.

## Parallelism and scope

Work is total weighted work. Work and span use the same normalized cost units;
FLOPs and seconds cannot be mixed in the span<=work comparison. Span is the sum of modeled primitive spans along this sequential
program, permitting parallelism inside a primitive. No fork/join or scheduler is introduced;
work divided by processor count is not a certified elapsed-time bound. Different parallel
configurations have separate resource models, including their workspace tradeoffs.
Payload bytes exclude evaluator metadata, allocator headers/alignment and code/tape storage;
physical claims require a representation/implementation model covering those quantities.
No finite encoding/representability theorem is supplied for opaque K. For example, tagging
exact real-valued words fp64 does not prove those reals fit64bits. These are modeled payload
bytes; a physical byte claim requires a separate faithful representation bridge. The .cell
legacy configuration is an abstract unit1, not a physical one-byte real representation.
Queries reserve the maximum declared workspace among actually executed query count keys;
the canonical bound adds this to the allocation/primitive peak. It may overestimate temporal
overlap, never summing queries as simultaneously live. Allocation/release instruction dimensions
are [format.bytes, elementCount]. Query work/span/workspace for the same q/d key must cover
both Boolean and index uses, or use distinct query names.

## Placement and shared proof machinery

Store.lean: StorageFormat and representation sizes, before syntax uses them.
Syntax.lean: allocAs, model signatures, lexical typing and fixed-program typing.
Exec.lean: weighted allocation, query workspace accounting, mandatory typing at entry,
count weights and semantic projection. Raw memory semantics erases format annotations.
Contract.lean: Problem formats/initialBytes, AccessModel.resources; semantic contracts remain
exactly primitive contracts. Static.lean: typed static bounds and count/byte/work/span specs.
Cert.lean: ofWp/link constructors require typed source/lower trees and all resource bounds.
Transfer.lean: count-weight algebra is reused, not duplicated. Existing scalar conditional
proofs remain one-byte instantiations; generic constructor induction handles allocAs.
Examples/Resources.lean: mixed32/64 allocation20n, conversion/alias format rejection,
query workspace, operation work/span tradeoff and actual canonical certificates.
Examples/Certification.lean migrates the earlier positive/negative canonical fixtures.

Searches: existing Count.lift/totalWeight, staticPeak, Counted rules and Mathlib Finsupp
additive-map monotonicity provide cost summation. No existing format-aware allocation model
or buffer typing checker was found in Ops. No protected check or target file is changed.
