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
field for arbitrary additional interpreter assumptions or whole-program success. The contracts
themselves are unconstrained by this type: see "What the model must also satisfy" below.
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
to that same execution. `Specification` has no program argument, but nothing prevents its
budgets from being defined as the static count of the certified program (a manifest); such a
bound says only that the program runs. `Algorithm model specification` packages one fixed
program and this total proof.

## What the model must also satisfy

The types accept a contract that depends on the whole input, reads cells that are not operands,
or has zero work; a unit-cost primitive can then write the answer (`Examples/Oracles.lean`).
`Confined.lean` names the properties that exclude this, as classes on the model:

* `AccessModel.Confined`: every primitive contract is in operand form (`BlockRel.spec`) and
  every query reads its operand blocks only. `Contract.Confined.frame`: a confined call changes
  no buffer that is not an output operand.
* `AccessModel.Uniform`: the contracts do not depend on the sizes or the input. A model with a
  declared oracle (the matrix-free operator) is confined and not uniform.
* `AccessModel.Charged`: every primitive, query and structural instruction has positive work.
  `AccessModel.Charged.size_le_work`: work is then at least the number of instructions.

`Profiles/Confined.lean` proves these for the standard collections. `scripts/OpsPrograms.lean`
computes one line for every certificate and compares it with `scripts/ops_certificates.txt`: a
recorded certificate may not get weaker in any field, and a new one must have a confined model,
closed-form work and a derived problem, or be added to that file. A family of certificates
indexed by a parameter that fixes the admitted size is not one certificate; the check lists
parametrised programs.

**The line of a certificate.**

| Field | Values | Meaning |
|---|---|---|
| `hyps` | a number | the hypotheses of the declaration |
| `uniform`, `confined`, `charged` | `yes`, `no`, `unknown` | an instance for the model was found; none exists once the model is unfolded to the end; the search stopped at its limit |
| `budget`, `work`, `scratch` | `closed`, `manifest`, `unknown` | see below |
| `problem` | `derived`, `handwritten` | the problem is that of a `Routine.Domain`, or a hand-written `Problem` |
| `derived` | a number, `?`, `-` | the operands whose buffer holds words computed from the inputs |
| `unstored` | `yes`, `no`, `-` | the domain declares inputs that no buffer holds |
| `oracles` | `declared`, `related`, `missing`, `none` | for a model that is not uniform, a `Routine.Domain.Oracles` declaration unifies with this domain and model (`declared`), or exists only for another instance of the domain (`related`); `none` for a uniform model |
| `claim` | names, `related:` names, `exempt`, `none`, `required-missing` | the `RandomizedClaim`s that are about this certificate at its own parameters; `related:` for claims about the same declaration at other arguments |

A resource field is classified by everything it depends on, through every definition of the
library (proofs are not searched):

* `manifest`: it depends on a function that reads a number or a count off a tree (`staticCost`,
  `staticPeak`, a coefficient or a polynomial computed from the program). The bound is the
  program's own syntax, not a statement a reader can evaluate;
* `closed`: the search finished and found no such function and nothing it cannot inspect. Every
  library definition under the field was opened; what is left is arithmetic and functions of
  Mathlib and of Lean's core, which are taken to be what their names say;
* `unknown`: the search met an axiom, an opaque constant or a non-constructive choice
  (`Classical.choose`, `Nat.find`, a supremum over a set, …), or the specification did not unfold
  to its fields. `unknown` counts as `manifest` wherever `closed` is required, and the reason is
  printed.

A scratch bound that adds the query reserve of the static count
(`resources.queryReserve (staticCost program d)`) is a manifest, although it names no peak.

**Reading what a certificate states.** `OPS_CERTIFICATES_REPORT=1` (or `=Name` for the
certificates whose name contains `Name`) prints, for each certificate and without writing
anything: its line with the reason of every `manifest` or `unknown`; the admitted sizes and the
acceptance predicate as written; the slots, with the formulas of the derived ones; the unstored
inputs; the model, with the contracts of its operations and of its queries and the three
weights (`operationWork`, `queryWork`, `coreWork`), whether the model is uniform or not; every
binder of the certificate, parameters and hypotheses; its resource fields and its output
condition.

For oracle declarations and randomized claims the report distinguishes two levels. A
declaration *applies to this instance* when its binders can be instantiated so that its type is
about this certificate: `RandomizedClaim A` with `A` this certificate at its own parameters,
`Oracles D M` with `D` the domain of the problem and `M` the model. Only then does the line of
the certificate say `claim=<name>` or `oracles=declared`. A declaration about the same
certificate declaration at other arguments (a claim for the real field only, or for operations
taken from a bundle) is *related*: the line says `claim=related:<name>` or `oracles=related`,
which satisfies neither the rule for termination-only certificates nor the ratchet, and the
report prints the instance it is about and the arguments where it differs. For a declaration
that applies the report prints the binders this instance fixes, the parameters that remain,
the hypotheses it shares with the certificate, and the hypotheses that are **not** hypotheses
of the certificate; for a claim, also the law of the tape (its realizability is a field of the
claim, so it is proved), `admits`, `interprets`, the event and the bound.
`OPS_CERTIFICATES_REPORT_FILE=path` writes the report to a file.

```
OPS_CERTIFICATES_REPORT=HSCG.Certification.algorithm lake env lean scripts/OpsPrograms.lean
```

`OperationCount.lean` gives the closed forms. `Program.countPoly` computes from the fixed
instrumented tree a polynomial in the sizes, one variable per size, that bounds the number of
instructions of every run (`Program.exec_work_le_countPoly`); the kernel evaluates it to an
explicit list of terms. Under a model whose weights are at most one it bounds the work, and
`Algorithm.withCountPoly` restates a certificate with it. The scalar conjugate gradient, PCG
and Lanczos certificates are stated this way, e.g. `33 n² k + 157 n k + 242 k + 50 n + 127`
instructions for conjugate gradient of order `n` with cap `k`.

`Algorithm.ofWp` uses the total statement logic and full structural bounds to construct the
certificate. `Algorithm.link` takes a fixed implementation table and verifies the entire lower
program against a separately realized lower model and specification, including introduced frames
and allocations. `Algorithm.runsLaw` observes the output of the same certified execution.

## Writing a routine and certifying it

A routine (`Routine.lean`) is a fixed tree with an interface, and is the unit that is written,
called, linked and certified. It is written with `routine%` (`RoutineSyntax.lean`), whose header
is the interface:

```lean
/-- Sum two vectors by two calls of `sum` and one addition. -/
def sum2 : Routine Op Tst := routine% [n] (x : n, y : n) → (z : 1, unreported w : 1) {
  run sum [n] (x, z);
  run sum [n] (y, w);
  call (Has.inj ScalarOp.add) [] (z, w) → (z)
}

def sum2Spec (dec : K → ℝ) (u : ℝ) : Routine.Spec K :=
  spec% [n] (xs, ys) → ([v]) ensures |dec v - …| ≤ …

theorem sum2_meets … : sum2.Meets I (sum2Spec dec u) := by
  routine_intro [n] (x, y, z, w) reads (xs, ys)
  have hsum := sum_meets hI hM hu
  call hsum [n] (x, z) as ν hfr hpos (zs) hpost
  obtain ⟨v₁, hv₁, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
  call hsum [n] (y, w) as ν₂ hfr₂ hpos₂ (ws) hpost₂
  obtain ⟨v₂, hv₂, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  step (hI .add) as ν₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
  routine_exit
  exact sum2_error hM hu hpost hpost₂
```

(`Examples/Routine.lean`.) In the header an operand named only on the left of `→` is read, only
on the right written, on both sides updated in place; each is declared once with its length, an
index expression in the dimensions or a Lean term `↑(…)`. An operand named again on the left,
without its length, is one more buffer variable of the tree on the same operand, as when a tree
written for distinct operands runs with two of them equal. Marks (`isolated`, `unreported`)
and clauses (`draws e`, `draws unspecified`, `by blocks`, `one variable`) state
what the header cannot infer. The body is a block of the builder, or `:= t` for a tree defined
elsewhere.

**Routines and fragments.** A tree is a routine when it has operands of its own and something
calls it through its interface: a `run` in another tree, a linking table, or a certificate. It is
then written with `routine%` and has one judgment. A tree that is a piece of one routine's tree,
working on buffers that routine allocates or at offsets computed inside that routine's operands,
is a fragment: a plain `Stmt` written with `ops%`, with one statement of its run in operand form
(`X_writes`), used only inside the proof of the routine that contains it. Its docstring names
that routine.

The library does not yet follow this rule everywhere. Kernels that several routines run, each on
operands of its own, are by the rule routines. The fill (`fillRoutine`), the batch of draws
(`sampleRoutine`) and the matrix copy, identity and real trace (`PairMatrix.copyRoutine`,
`PairMatrix.identityRoutine`, `PairMatrix.traceReRoutine`) are, and their callers run them by
interface. The others are still plain trees with operand-form statements, from before routines
existed: the row and column rotations and the Givens coefficient kernels of shifted QR, the
small-eigenvalue solver and Hessenberg reduction, and these kernels of `Blas/`: `unaryMap`,
the `Hermitian` family, `scalarBroadcast`, `normSq`, `Pair.multiply`,
`Pair.linearCombination`, `copyStrided`, `clamp`. They address sub-blocks of
one matrix buffer at computed offsets, and several have a word-level and a decoded statement;
they are to become routines, separated by block, with one judgment each. Until then every
statement in operand form says in its docstring what it is: a fragment of one named tree, shared
by the named trees, a step in the proof of a named theorem, or an end statement that nothing is
proved from. The Krylov families, Hutch++, MGS and the level-1 leaves follow the rule.

**One statement per routine.** A routine has one correctness statement, `XRoutine_meets`. A
caller uses it with `call`; it is not restated in operand form, and no lemma lists which
operands are apart (`routine_intro` puts those facts in the context, `routine_sep` proves them at
a call). Two derived statements exist where another consumer needs them: the contract of an
operation the routine implements (`Routine.Meets.satisfies_ofRel`, with `implements`), and the
counted run used to account a linked operation (`Routine.Meets.runs_ofRel`). A routine with
either states its specification as `Routine.Spec.ofRel` of the block relation of that contract;
every other routine states it with `spec%`.

Three situations keep an operand-form lemma beside a judgment, each for a stated reason at the
lemma:

- **One tree, several routines or table entries.** An operation whose contract admits several
  operand layouts (an output apart from an input, or that input itself) is implemented by one
  routine per layout, all with the same tree; the tree's lemma, stated for every layout, is the
  common proof of those routines (`RCLikeScalar.copy_writes`, `writes_scal`, `writes_axpy`). A
  tree that is the body of two table entries is proved once for both
  (`StoredDense.impl_writes_word`, used by `implRoutine` and the context-forwarded
  `ContextDense.impl`).
- **A judgment read on a loop invariant.** A loop over a routine keeps an invariant stated on
  the memory (the state of a recurrence held in the operands). The judgment of the body, read on
  that invariant, is a corollary used by the loop rule and by nothing else
  (`Carried.Rounded.step_writes`, `HSPCG.Rounded.step_writes_function`, `MGS.sweep_writes`).
- **An empty block past the end of a buffer, or a block whose length is not a dimension.** A
  judgment requires room for every written block, of a length its interface computes from the
  dimensions; a statement that must also hold for a block of length zero placed anywhere, or
  whose invariant is on a log of a slot count the tree does not take, stays in operand form
  (`hessenbergReduceLast_writes_word`).

A routine may have several judgments, for several specifications. A leaf whose result is a
definite list of words states it once, for any machine, as an exact-output judgment
(`axpyLoopRoutine_meets_exact`, `scalLoopRoutine_meets_exact`, `sumSeqRoutine_meets_exact`), and
each error model's judgment applies that one at its operands and reads its bound off the words
(`axpyLoopRoutine_meets` under the standard model, `axpyLoopRoutine_meets_mixed` under a mixed
relative/absolute model, the fixed-point example).

There are two proof styles for a judgment. The default opens the goal with `routine_intro` and
proves the `Writes` statement of the tree. `Routine.meets_ofRel_of_post` is for a run computed as
an exact final memory (a `Wp` ending in the `BlockRel.Post` of the relation): it supplies the
frame and the blocks read back, so the proof states only the memory. The draw examples (`Noisy`,
`Hutch`, `NoisyLinked`) and `Split` use it.

The tactics (`Logic/RoutineIntro.lean`):

- `routine_intro [n, k] (b, x, r, p) reads (bs, xs)` opens a goal `R.Meets I S`: the
  dimensions, the operands and the blocks read are named, and the context holds liveness
  (`hlive : m.Live [b, x, r, p]`, and `hl`, the same fact one operand at a time), room for the
  written blocks (`hrooms` as lists, `hroom` one block at a time), the precondition `hpre`, and
  the separation: for a routine separated by buffer one fact `hxr : x.1 ≠ r.1` for each pair the
  interface requires apart (operands that continue another are part of its region and have no
  name of their own), for a routine separated by block the disjointness `hblocks` of the blocks
  at the named operands. The goal is the `Writes` statement of the tree. `memory μ` names the
  memory `μ` instead of `m`, for a routine with a dimension called `m`.
- `call h [n] (x, z) as ν hfr hpos (zs) hpost` uses the judgment `h` of a routine at a frame of
  its tree, proves the side conditions from the context, and names the memory after the call,
  its frame, the tape position, the blocks written (`hzs`) and the postcondition at those
  blocks. `(pre := t)` supplies the precondition when it is not in the context.
- `routine_exit` closes the proof at the final memory and leaves the postcondition.
- `implements [n] (x) → (z) with hadm` proves `R.Implements B adm port`: it names the operands
  of the contract, splits the admission, substitutes an output that the admission makes equal to
  an input (`implements [n] (a, x, y) → (y) with hadm` for an operation in place), checks the
  interface by computation and proves separation from the inequalities of buffers the admission
  gives. Separation by block, or an admission that does not state it buffer by buffer, is left
  as a goal.
- Inside a rule that wants the body of a loop in operand form, the judgment is applied to the
  named operands directly: `hstep [n] [x, r, p] τ m' _ rfl rfl …` (`Krylov/CG/HSCG/Rounds.lean`).

The interface in detail:

- **Operands.** `Routine.ports` lists the operands, each with its mode and its length in the
  dimensions: `Port.read len` (left unchanged), `Port.write len` (initial contents not read),
  `Port.update len` (read and written in place), `Port.isolated len` (read-only and apart from
  every other operand, as stored data forwarded to a linked operation must be). `routine%`
  produces them from the header; the value is a plain structure
  `{ nd := …, ports := […], body := … }` whose other fields have defaults (no draws, no layout,
  separation by buffer).
- **Unreported operands.** `(Port.write len).unreported` is a written operand whose final
  contents the judgment does not report: caller-supplied scratch, or a matrix destroyed by a
  factorization. Nothing outside it changes; nothing is claimed of what it holds.
- **Separation.** `Routine.sep` names one of two fixed rules, and `Routine.SeparatedAt` is what
  the judgment requires. Under `.buffers` (`Routine.Separated`) two operands are in different
  buffers unless both are merely read (`Access.apart`, `Routine.separated_iff_pairwise`); an
  `isolated` operand is therefore in a buffer of its own. Under `.blocks`
  (`Routine.SeparatedBlocks`) the same holds of the blocks instead of the buffers, so operands
  may be disjoint blocks of one buffer. Operands separated by buffer satisfy both
  (`Routine.separatedAt_of_separated`). An author chooses between the two rules and cannot state
  another admission of operands.
- **Continuation.** `(Port.write len).continuing` continues the operand before it: its
  block is in the same buffer and starts where that block ends at the dimensions of the call.
  It is written in an explicit list of operands, not in a `routine%` header, because it must
  directly follow the operand it continues, which is not the order of a header.
  A basis of `k` columns read and the next `b` columns written is two operands, the second
  continuing the first (`Catalog/OrthRoutine.lean`, `extendRoutine`). The position is fixed by
  the interface, so a call supplies one operand per region (`Port.regions`, `Routine.arity`),
  and `Routine.operands` gives the positions of all operands. Separation is stated on the
  regions: an operand and those that continue it are one block, written if any of them is.
- **Layout.** By default buffer variable `i` of the tree is operand `i`. `binds := some l` makes
  buffer variable `i` operand `l[i]`; the tree is not changed. The buffer variables of a tree
  are its inputs and then its outputs, the form of the contract of an operation, so a block
  updated in place is two buffer variables and one operand: `routine%` generates that layout
  from the header. A tree written for its operands directly, with one buffer variable for an
  operand it updates, takes the clause `one variable` and has no layout; its program is then the
  tree with no frame around it, which is why the top-level routines of shifted QR are written so. A tree that is correct
  on several aliasing patterns of its operands is one routine per pattern, each written with
  `routine%` by naming the shared operand in several positions (`Profiles/RCLikeScalar.lean`:
  `(a : 1, x : n, x) → (x)` runs `axpy` with one vector). A layout is written by hand in two
  places, each documented at the definition: where the written blocks must follow the output
  order of an operation contract rather than the macro's order (`Examples/CgsQR.lean`), and
  where a continuation must directly follow the operand it continues (`extendRoutine`).
- **Draws.** `Routine.draws d` is `some k` when the routine consumes exactly `k` tape positions at
  the dimensions `d`, and `none` when that number depends on the data (a rejection loop, an
  early stop); the judgment then makes no claim on the final tape position.
- **Specification.** `Routine.Spec` is a precondition on the dimensions, the draws and the blocks
  read, and a postcondition relating them to the blocks written. The draws are the tape seen
  from the position of the call, on any stream. It mentions no memory, operand or tree.
  `spec% [n, k] (bs) → (xs, rs, ps) requires P ensures Q` writes one on named dimensions and
  blocks; `Routine.Spec.ofRel` reads one off the block relation of an operation contract.
- **Judgment.** `Routine.Meets R I S`: at every memory, on live separated operands with the read
  blocks in the precondition and room for the written blocks, the tree terminates, changes only
  the written blocks, advances the tape by the declared draws, and the written blocks satisfy
  the postcondition. It is the only judgment of routines, and it holds on every tape.
- **Probability.** A guarantee that holds only with high probability over the draws is not a
  `Meets`. Its statement is `PWrites` (`Logic/Probabilistic.lean`): in operand form, the run
  writes only its footprint and ends in the postcondition on a good set of tapes, and the good
  set fails with probability at most $\varphi$ under the stream laws. Its rules mirror those of
  `Writes`, with failure probabilities that add; a deterministic step enters with
  `PWrites.of_writes`, inside which `call` applies as usual. A routine with such a guarantee
  states `Routine.Spec.terminates` as its judgment (termination and footprint on every tape) and
  its accuracy as a `PWrites` statement or a probability theorem about the same run (the
  small-eigenvalue solver, rounded shifted QR). There is no routine-level form of `PWrites`
  yet: its statements name operands.
- **Calling.** A caller runs a routine by its interface, `run R [dims] (operands)`, one operand
  per operand of the routine (an operand updated in place is named once; the layout is applied
  by the builder). A fragment's tree is run by its buffer variables, `run t [dims] (vars)`. The
  caller uses the routine's judgment with the tactic `call` (the rule is `Routine.Meets.call`); it learns the
  footprint and the postcondition, and nothing of the tree. The cost of the caller includes the
  callee because the callee's tree is in the caller's tree.
- **Linking.** A routine implements an operation contract of a model when the admitted operands
  of the contract are separated operands of the routine (`Routine.Implements`,
  `RoutineLink.lean`); the contract of the operation is then a corollary of the judgment
  (`Routine.Meets.satisfies_ofRel`), and linking grounds it under the induced interpretation
  (`Interp.link_satisfies`). `Routine.link` is a routine with its tree linked through a table, and
  `Routine.Meets.of_link` transfers the judgment. The level-1 loops (`Blas/Sum.lean`, `Dot.lean`, `Level1.lean`), the stored
  matrix-vector leaves (`Profiles/StoredRoutine.lean`, `StoredDense.lean`, `StoredCOO.lean`),
  the exact reductions of `Profiles/RCLikeScalar.lean`, the vector draw (`Profiles/Random.lean`)
  and the examples `Gemm`, `GramSchmidt`, `CgsQR`, `Bilinear`, `Hutch`, `Noisy`, `NoisyLinked`
  are proved this way. An operation contract that admits several layouts of its operands (an
  output apart from a vector input or exactly that input: `copy`, `scal`, `axpy`, the real
  conjugation) is implemented by one routine for each layout, all with the same tree: separate
  operands, or the vector updated in place with its buffer variables bound to one operand. The
  contract follows by cases on the admission (`Routine.Meets.writes_ofRel`;
  `Profiles/RCLikeScalar.lean`, `Profiles/RealStar.lean`).
- **Certifying.** `Routine.close` is the program of a routine on a problem: the tree, with the
  sizes as dimensions and the supplied buffers as operands. The initial environment of a
  program has one buffer variable per supplied buffer, at its start. The program of a routine
  without a layout is its tree; the program of a routine with a layout is one frame of its tree
  on the supplied buffers in the layout, and that frame is counted like any other. A routine
  with an operand that continues another has no program (the position of the continuation is
  not the start of a buffer); it is called by a frame.
  `Routine.algorithm` is the one constructor: it certifies the program against any
  `Specification`, for any weights, from `Meets` under every interpretation of the model.
  Liveness and separation of the supplied buffers are not hypotheses; they hold for every
  problem. A counted certificate is a corollary of it: `(algorithm …).withCountPoly …` replaces
  the work by a bound on `Program.countPoly`, the instruction polynomial the kernel computes
  from the fixed instrumented tree (`countedAlgorithm` in each family). The closed form of the
  polynomial is checked by `kernel_rfl` (`Logic/KernelRfl.lean`), which leaves the reduction to
  the kernel (the elaborator's `rfl` can be slow when the tree has a free parameter), and
  evaluated at the sizes by `poly_eval`. It needs every weight of the model to be at most one,
  because a count of instructions bounds the work only then. `Routine.certify` is the same
  construction for a routine whose certificate states exactly its specification. No statement
  about cost is taken from the author of the routine.

- **The problem.** A certificate is about a problem: the sizes admitted, the inputs admitted
  and the buffers supplied. `Routine.Domain` (`RoutineProblem.lean`) builds it from the interface
  of the routine, and its author states mathematics only:
  - `valid`, the admitted sizes; `In d`, the type of the inputs (vectors, matrices, parameters);
    `accepts`, the admitted inputs;
  - a slot for every operand: `stored c get` (the buffer holds the encoding by the `Codec` `c`
    of the component `get` of the inputs), `derived len f` (the buffer holds words computed
    from the inputs, a threshold say), or `blank len` (uninitialised cells). A `Codec` (scalar,
    vector, matrix by an `EntryCodec`, pair, raw words) encodes and decodes bijectively at its
    length.

  The slots follow the interface (`fits`, proved by `domain_fits`): an operand that is read is
  `stored` or `derived`, an operand that is only written is `blank`, and the lengths are those
  of the ports. The inputs are determined by the stored buffers and the declared unstored part
  (`faithful`), so no other input is in no buffer; a quantity that is in no buffer and is not an
  input belongs in `accepts`, as an existential. A buffer depends on the inputs in no other way
  than these, and `Routine.Domain.derived` lists the operands whose buffer is computed from
  them.

  **Unstored inputs and oracles.** Data that is in no buffer can affect a run only through an
  operation whose contract mentions it. That is the oracle channel: a contract that mentions
  the data can hide any amount of work behind one call. A domain therefore declares the part
  of its inputs that is in no buffer (`Unstored`, `unstored`; none by default), and a
  certificate whose model reaches data outside memory states `Routine.Domain.Oracles`: the
  list `ops` of the operations that may depend on it, a proof that every other operation and
  every query has one contract at all sizes and inputs, and a proof that a declared operation
  sees the input only through its unstored part. A reviewer reads the contracts and the costs
  of the operations in `ops`; the work of such a certificate is counted in calls of them.
  Golub–Kahan declares its matrix as an unstored input reached through the two products
  (`GolubKahan.Band.Certification.oracles`); matrix-free conjugate gradient, with and without
  a preconditioner, takes its matrices as unstored inputs, with positive definiteness in
  `accepts`, and declares their products (`HSCG.Certification.oracles`,
  `HSPCG.Certification.oracles`). A standard model (`Profiles/Standard.lean`) reaches its
  operator only through its product: when it reads the operator of the unstored input
  (`Standard.Model.ReadsOperator`), the product is its one oracle (`Standard.Model.oracles`,
  `Profiles/StandardOracles.lean`). The carried and reorthogonalized conjugate gradient
  certificates take the matrix as an unstored input in this way; the Lanczos certificates in a
  standard model declare the product for an operator fixed by the sizes. A model with no
  declared oracle is uniform (`Oracles.uniform`).

  `D.problem` is the problem: exactly the buffers of the slots. An input of the problem is an
  admitted tuple of inputs and conversely (`Routine.Domain.inputEquiv`, `Routine.Domain.covers`):
  the certificate covers every input that satisfies `accepts`. `D.algorithm` is
  `Routine.algorithm` on that problem; that the supplied buffers hold the blocks read and have
  room for the blocks written is proved once (`readBlocks_initial`, `room_initial`), not by the
  author. `D.checked` states what a certificate says for the admitted inputs, in terms of the
  evaluator: for every admitted size and tuple of inputs, every interpretation satisfying the
  contracts and every tape, the run from the buffers of the slots (`D.memory`) succeeds within
  the resources of the specification — scratch, budget, work, span, and resident memory: the
  words of the inputs `D.bytes d` plus the peak of the run are at most `S.memory d` — and
  satisfies its output condition. `D.Checked A` is
  that statement as one proposition, and `D.checked_all` proves it of every certificate. A
  family's `_checked` theorem is either that proposition (`algorithm_checked`, `sign_checked`,
  `smallEig_checked`, …) or a form with the output written on values: `Mem.Holds c i a` says
  the buffer `i` holds the value `a` through the codec `c`, and `Mem.holds_decode` turns a block
  read from a buffer into the value it holds (`cg_checked`, `stored_checked`, `sum2_checked`).
  The docstring of a `_checked` theorem says what a reader must check beyond it: for an oracle
  certificate, which operations reach the unstored inputs; for a certificate whose
  deterministic claim is termination, which probability theorem carries the accuracy.
  `D.algorithmAt` is the same certificate when the specification depends on the input of the
  problem and not only on its data, as for a matrix-free solver whose matrix the model supplies.
  `D.certify` is the counted certificate (`Routine.certify` on the derived problem), with the
  payload `D.bytes` computed from the slots, and `D.checked_post` its evaluator-level statement:
  the reported operands hold blocks satisfying the postcondition. A domain depends on its
  routine only through the interface, so `D.cast` reads it at another routine with the same
  dimensions and operands, and the problem is the same (`problem_cast`).
  `Examples/RoutineProblem.lean` shows every kind of slot. Conjugate gradient, Lanczos,
  Golub–Kahan, Hutch++, MGS, the eigensolvers and the examples state their problems as
  domains. `Routine.algorithm` on a problem written by hand remains for a problem that is not
  derived from a routine: three examples keep one on purpose (`oracleProblem`,
  `capacityProblem`, `mixedProblem`), to show what a hand-written problem can hide.

A reviewer of a certified routine reads its `Routine.Spec`, the problem (`valid`, `accepts` and
any `derived` operand of its `Routine.Domain`), the
model (which operations exist and what each costs) and the stated work. `Examples/Routine.lean`
and `Examples/RoutineCertification.lean` are a complete small case, ending in a statement in
terms of the evaluator alone.

The names of routines, specifications, judgments, certificates and their files follow one
convention in every family, stated in
[Programs and certificates](../../docs/contributing/programs.md) ("Names of routines, files and
certificates").

### Operand footprints

An operand is a base cell `(buffer, offset)` and a footprint: which cells after the base are its
block. The footprint is three numbers, each an expression in the dimensions (`Port.len` and
`Port.stride`, read as a `View` of `Logic/View.lean`): `count` runs of `len` cells, one run
every `period` cells. Entry `k` of the block, in order, is the cell
`offset + period * (k / len) + k % len`.

| Operand | Header | `len` | `count` | `period` |
| --- | --- | --- | --- | --- |
| contiguous block (the default) | `x : n` | `n` | 1 | none |
| vector with increment `inc` | `x : n every inc` | 1 | `n` | `inc` |
| column of a matrix stored by columns | `x : m` | `m` | 1 | none |
| row of that matrix, leading dimension `lda` | `x : n every lda` | 1 | `n` | `lda` |
| `m × n` submatrix, leading dimension `lda` | `A : m × n every lda` | `m` | `n` | `lda` |

A port without `every` has `stride := none` and is one contiguous block. For a routine all of
whose operands are contiguous (`Routine.contiguous`, decided by `rfl`), every component of the
judgment is, by computation, the statement on contiguous blocks: `Routine.readAt` is
`Mem.readBlocks`, `Routine.RoomAt` is `Mem.Room`, `Routine.footprint` is `Fp.blocks`, and
separation by block is `Fp.Apart` of the blocks. `routine_intro`, `call` and `routine_exit`
state such goals in exactly those terms, so a proof about contiguous operands never mentions a
view. The constructions that read a routine as contiguous blocks (`Implements`, `withData`,
`close`, `algorithm`, `certify`) take `R.contiguous = true`, supplied by `rfl`.

With a periodic operand the same components are stated on the cells: the blocks read are
`Mem.readViews` (`Store.readView_eq_some_iff` gives each cell), room is `View.Fits`, the
footprint is `Fp.views`. The two separation rules are those of a contiguous routine:

- by buffer (the default): operands that must be apart are in different buffers;
- `by blocks`: their *cells* are disjoint (`Fp.ApartViews`). Two operands interleaved in one
  buffer are apart: two rows `i ≠ j` of one matrix, by `Fp.disj_inView_of_residues`, which
  derives disjointness from the arithmetic of offsets within one period.

A caller that holds a contiguous block reads a part of it as a view with
`Store.readView_of_readBlock`, and reads the block back from the views a call reports with
`Store.get_of_readView` and the frame.

Operation contracts are unchanged: an operation takes contiguous blocks. A tree with a periodic
operand reaches its cells by index arithmetic on the operand (`x[inc * i]`), so it applies
operations to runs: one cell at a time for a vector with increment or a row, one column of `m`
cells at a time for a submatrix. An operation on a whole periodic block (a level-1 operation
with increments, a matrix product with leading dimensions) would be an operation contract
stated on views; that is not done, and is the natural next step. Continuation (`cont`), which
places an operand at the end of the block before it, is meant for contiguous operands only.

The instruction count of a tree does not depend on the footprints of its operands.
`Examples/Strided.lean` has a scaling of a vector with increment, the exchange of two rows of a
matrix stored by columns (`swapRows`, `by blocks`), a caller that applies it to rows `i < j` of
one matrix held as one block (`swapMatrixRows_meets`), and their kernel-evaluated counts
(`34 n + 33` instructions for the caller, whatever the leading dimension).

### Three statements

Three statements have three roles. `Routine.Meets` is what an author states about a routine.
`Interp.Satisfies` says that an interpretation satisfies the contract of a primitive operation;
operation models are made of it. `Impl.Satisfies` says that an implementation of an operation
satisfies that contract; it is derived from the judgments of the routines that share the
entry's tree and consumed by linking.

An `Impl` is an implementation of an operation: the entry of a linking table, a tree with the
arity of the operation. It is the tree of a routine (`Routine.impl`). It is a separate type from
`Routine` because one tree may implement an operation whose contract
admits several layouts of the operands, which are several routines sharing that tree: the
`axpy` entry of `RCLikeScalar.table` is one tree, and its contract admits the output apart from
both vectors, on either vector in place and on both at once. `Impl.Satisfies` is then proved by
cases on the layout from the judgments of those routines (`Routine.Meets.satisfies_ofRel` when
there is one layout). An entry is written directly only where no routine can describe it: the
entry of a context table, whose first inputs are the context forwarded to every call
(`ContextDense.impl`); an implementation that does not always terminate, for liberal mode
(`Examples/Liberal.lean`); and the examples that prove a contract from the run of the entry
itself, the layer under routine judgments (`Examples/Dot.lean`, `MatMul.lean`, `Bits.lean`,
`StochRound.lean`). A tree that is not an implementation of an operation is a plain `Stmt`
(`ops%`), or a routine (`routine%`) when it has an interface of its own.

Operation meanings and primitive costs, the declared input representation, and the relevance of
the specified postcondition remain properties of the chosen problem and operation model.

## Randomized claims

A certificate (`Algorithm`) states what every run does, on every tape. The accuracy of a
randomized algorithm is a statement about the law of the tape; it is a separate theorem, and for
some solvers the certificate itself claims only termination (`Routine.Spec.terminates`). A
`RandomizedClaim A` (`Randomized.lean`) is the object that ties the accuracy to the certificate
`A`, so that a reader who has the certificate finds the guarantee and its assumptions. It holds:

* `law`: the law of the tape, as a `TapeModel` — the sample spaces, measures and random tapes
  the claim covers. Two forms are named. `TapeModel.streams [(s, ν), …]` says the entries of the
  tape are independent and an entry of the stream `s` has the law `ν` (`IsTapeLaw`); the
  stream identifiers of the list must be distinct, which is part of the law, so a list naming
  one stream twice describes no tape.
  `TapeModel.packed ν pack` says the tape is the packing `pack` of a random object with the law
  `ν`. A claim may also state its law directly, as Hutch++ does for two independent Gaussian
  matrices and spectral bisection for a rounded tape;
* `admits`: the hypotheses on the size and the input beyond admission to the problem (norm
  bounds, gaps, precision conditions), written on the typed input;
* `interprets`: the hypotheses on the interpretation beyond the contracts of the model
  (measurability, reading the tape only in its windows), where the proof needs them;
* `event`: the accuracy event, a property of the tape, the count and the final memory of the run;
* `bound`: the failure probability, a function of the size and the input;
* `realizable`: for every admitted size and input satisfying `admits`, the law is
  `TapeModel.Realizable`: some probability space carries a tape with it. Without this field a
  claim whose law no tape has would hold vacuously. `TapeModel.realizable_streams` (distinct
  streams, probability laws), `realizable_packed` and `realizable_uniform_gaussian` prove it
  for the named forms. The claims over a uniform and a Gaussian stream `sU`, `sG` take the
  hypothesis `sU ≠ sG` for it;
* `holds`: the statement `Algorithm.FailsAtMost`: for every admitted size and input satisfying
  `admits`, every interpretation satisfying the contracts and `interprets`, and every finite
  measure and tape with the law, the probability that the counted run of the program of `A`
  fails, exceeds a resource bound of the specification, or ends outside `event` is at most
  `bound`. The run is that of the certificate: the same program from the initial memory of the
  problem, so success and every resource bound are part of the event.

`admits` and `interprets` are not required to be satisfiable. They are numerical conditions in
the parameters of a claim (a unit roundoff below a threshold, a measurable interpretation
reading the tape in its windows); whether some input and some interpretation meet them depends
on those parameters, and a field demanding it could only be discharged by a further hypothesis
of the claim. They are stated in the claim and printed by the certificate report, where a
reader sees for which inputs and implementations the bound is claimed. `holds` quantifies over
every finite measure, of which the probability measures of `realizable` are instances.

`RandomizedClaim.ofReference` and `RandomizedClaim.ofWp` build a claim from the two transfers of
`Probability.lean`: from a reference event of the sample space, and from the probabilistic
program logic (`PWrites`, which bounds the probability that the tree misses a total
postcondition). `PWrites` is a statement about a tree; a randomized claim is the statement about
a certificate that a reader checks.

The claims of the library:

| Certificate | Claim | Law of the tape |
|---|---|---|
| `HutchPlusPlus.Certification.algorithm` over `ℝ` | `HutchPlusPlus.Certification.claim` | packing of two independent Gaussian matrices |
| `Deflation.deflateAlgorithm` with the product and QR of a `FloatMachine` | `Deflation.deflateClaim` | packing of a complex Gaussian matrix |
| any certificate of block Golub–Kahan | `BlockKrylov.gaussianClaim` | packing of a Gaussian start block |
| `SpectralBisection.countedBisectionAlgorithm` | `SpectralBisection.countedBisectionClaim` | rounding of independent uniform and Gaussian streams |
| `SmallEig.smallEigAlgorithm` | `SmallEig.smallEigClaim`; `smallEigGinibreClaim` at the Ginibre tails | independent uniform and Gaussian streams |
| `ShiftedQR.shqrSmallEigAlgorithm` | `ShiftedQR.shqrSmallEigClaim`; `shqrSmallEigGinibreClaim` at the Ginibre tails | independent uniform and Gaussian streams |
| `Schur.denseSchurAlgorithm` | `Schur.denseSchurClaim` | independent uniform and Gaussian streams |

**Every termination-only certificate has a claim.** The certificate check
`scripts/OpsPrograms.lean` finds the certificates whose definition uses
`Routine.Spec.terminates` (through the definitions of the certificates and specifications it is
built from), finds the declarations whose type is `RandomizedClaim A` with `A` an application
of that certificate, records them in the field `claim`, and fails if a termination-only
certificate has none and is not listed there (`exempt`) with its reason. The type of a claim
names its certificate, so no annotation is needed.

## What client code may depend on

The supported surface, which changes only with a recorded rename or a migration note:

* **Writing trees and routines**: `routine%`, `ops%`, `spec%` and their clauses and marks;
  `Routine`, `Port` through `Port.read`/`write`/`update`/`isolated` and `every`;
  `Routine.Spec`, `Spec.ofRel`, `Spec.terminates`.
* **The judgment and its use**: `Routine.Meets`; in a tree `run R [dims] (operands)`; in a proof
  `routine_intro`, `call`, `step`, `loop_inv`, `routine_exit`, `read_outputs`, `implements`,
  `kernel_rfl`, `poly_eval`.
* **Routines from routines**: `Routine.withData` with `Spec.onData` (stored data),
  `Routine.link` with `Meets.of_link` (linking through a table), `Routine.Implements` and
  `Meets.satisfies_ofRel` (a routine as the implementation of an operation).
* **Problems and certificates**: `Routine.Domain` (`In`, `valid`, `accepts`, the slots `stored`,
  `derived`, `blank`, `Unstored` and `Oracles`), `Codec`, `Domain.problem`, `Domain.covers`,
  `Domain.algorithm`, `Domain.certify`, `Algorithm.withCountPoly`, `Domain.Checked` with
  `checked_all`, `Mem.Holds`.
* **Randomized results**: `RandomizedClaim`, `TapeModel.streams`, `TapeModel.packed`,
  `Algorithm.FailsAtMost`.
* **Models**: `AccessModel`, `ResourceModel`, `Interp.Satisfies`, the operation contracts of
  `Catalog/`, the classes `Confined`, `Uniform`, `Charged`, and the standard collections of
  `Profiles/`.
* **The certificate check**: the fields of `scripts/ops_certificates.txt` and the report of
  `scripts/OpsPrograms.lean`.

Internal, and free to change without notice: the constructors of `Stmt` and how a tree is
represented (including `Note`); `Mem`, `Store`, footprints (`Fp`) and views; the evaluator, its
instrumentation and the form of `Count`; `Impl` and `Impl.Satisfies` beyond their use as table
entries; `Routine`'s fields other than through the constructors above (`binds`, `sep`,
`stride`); the rule set of the program logic in `Logic/` (`Wp`, `Writes`, `PWrites` and their
lemmas). A proof about a fragment uses those rules and may need changes when they change; a
proof that goes through `Meets`, `call` and the tactics should not.

## Notes: names that a tree carries

A tree has one constructor that does nothing: `Stmt.note n s` is the tree `s` with the metadata
`n : Note` (`Syntax.lean`). A note says which routine a frame runs (`Note.routine`), what a
bound variable is called in the source (`Note.var`), what the header of a tree names
(`Note.header`), or carries a label or a key and a value. The evaluator, the counted evaluator,
the static count and scratch, the storage check, linking and every judgment treat `note n s` as
`s` (`eval_note`, `stmtCost_note`, `stmtPeak_note`, `wp_note_iff`, `Writes.note_iff`,
`PWrites.note_iff`); the instrumented tree has no notes, so a note adds no instruction and no
certified count depends on one. Notes are the only place where a tree holds metadata, and a new
kind of metadata is a new constructor of `Note`; the type of trees does not change.
`Stmt.erase` removes every note, with the same run, count and scratch (`Notes.lean`).

The builder attaches notes to the trees written under `noted%`:
`def foo : Routine Op Tst := noted% routine% [n] (x : n) → (z : 1) { … }` records the names of
the header, of each loop variable, scratch buffer and index binding, and of the routine or tree
that each `run` frames. Without `noted%` a tree has no note. Proofs are the same in both cases:
`routine_intro`, `step`, `call` and `loop_inv` remove the notes of the goal first
(`strip_notes`, which is also the tactic to use after unfolding a noted tree by hand, before a
rule that matches the shape of the tree). The library's trees are written without `noted%`
where their proofs apply such rules by hand.

`Stmt.pretty` (`Notes.lean`) reads a tree back as pseudocode with those names, and shows a
noted `run` as `run name [dims] (operands)` in place of the tree of the routine;
`Examples/Notes.lean` checks its output on the integrator. It is a reading aid for people and
tools. It is not a code emitter, and nothing is proved about its output.

## Proof construction

The statement interpreters `eval` and `evalCounted`, judgments `ConditionalRuns`,
`ConditionalRunsW`, `ConditionalRunsL`, and conditional implementation relation `Impl.Satisfies`
form the proof calculus. `Wp` and its constructor rules can express total or liberal correctness.
`Profile.Refines` transfers conditional contracts and resource bounds through a fixed table.
These constructions do not assert model realizability or uniformity of a runtime tree family.
They are useful ingredients for a canonical certificate, not substitutes for one.

`ConditionalRuns` is a total execution theorem under its explicit input and interpretation
hypotheses. It does not assume that execution succeeds. The liberal form `ConditionalRunsL`
is partial correctness and is useful only as an internal proof step toward a total result.

The named builder in `Logic/Builder.lean` elaborates to the same statement trees. Use
`let t ← alloc n` for scratch of `n` cells of one byte each (`StorageFormat.cell`), the format of
every model that does not distinguish storage widths, and `let t ← allocAs format n` when the
model charges memory by a storage format (a floating-point width, say).
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
conjugation (the trees, routines and table are in `Profiles/RCLikeScalarTrees.lean`).
`StoredDense` and `StoredCOO` implement matrix application from declared matrix words;
`StoredScalar` composes their tables into the scalar-only signature, taking the leaf as a
routine. Linking retains
the complete lower instruction tree and its temporaries.

`RoundedBlas` supplies the sequential standard-error scalar/vector collection.
`RoundedScalarBlas` lowers that collection to `ScalarOp` alone and derives its contracts
from the supplied scalar machine. `StoredDense.rowWord` identifies the exact word recurrence
of streamed matrix products for that same machine; rowwise error follows from `StdModel`.
The Matrix layer converts the row bounds to a normwise allowance for the actual raw matrix.
Carried CG and both Lanczos variants combine these bridges into rounded stored scalar-only
certificates, with resources recomputed after lowering. Finite-format mixed-error models
remain separate from the unbounded-exponent standard relative model.

`Context.lean` forwards fixed extra input capabilities through procedure frames.
A routine written against an operation that only an oracle provides (a product with a matrix)
becomes a routine on stored data with `Routine.withData` (`RoutineData.lean`): the data blocks are
new leading `isolated` operands, forwarded to every call of the operation. Its specification is
`Spec.onData c P S₀`, the matrix-free specification `S₀` at the decoded data, for data that
satisfy `P`; `Routine.Meets.withData` gives its judgment from the judgment of the matrix-free
routine under the interpretation in which the operation reads the stored words, with no other
proof about the tree. Underneath, `Logic/IsolatedLink.lean` transfers a word proof through the
forwarding, the isolated buffers keeping their words (`Logic/Isolated.lean`).
The problem of a stored solver is the problem of its `Routine.Domain`: the stored matrices
are inputs like the others, held by the isolated operands. Stored CG/PCG and Lanczos are built
this way. The proof-side
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
| `Cert.lean` | `Algorithm`, `Impl.Satisfies` (a tree implements an operation contract), constructors |
| `RoutineInterface.lean` | The interface of a routine: access modes, ports, regions, the two separation rules |
| `Logic/View.lean` | Footprints of operands: `View` (runs at a period), reading, room, disjointness of views |
| `Examples/Strided.lean` | Operands that are not contiguous: a vector with increment, two rows of one matrix |
| `Routine.lean` | Routines: specifications, the judgment `Meets`, calls, programs and certificates |
| `Notes.lean` | `Stmt.erase` and its invariance; `Stmt.pretty`, a tree as pseudocode with the names of its notes |
| `RoutineSyntax.lean` | `routine%` and `spec%`: a routine and a specification on named dimensions and operands |
| `Logic/RoutineIntro.lean` | The tactics of routine proofs: `routine_intro`, `call`, `routine_exit`, `read_outputs`, `implements`, `routine_sep` |
| `Logic/KernelRfl.lean` | `kernel_rfl`: closed computations (instruction polynomials) checked by the kernel |
| `Certification.lean` | Adapters for certificates: reading supplied buffers, counts without structural instructions |
| `RoutineLink.lean` | A routine as the implementation of an operation contract; specifications read off a contract |
| `Randomized.lean` | Randomized claims about a certificate: the law of the tape (`TapeModel`), the accuracy event, the failure bound and the proof on the counted run |
| `RoutineProblem.lean` | The problem of a routine: codecs of operands, slots, `Routine.Domain`, coverage, the certificate on the derived problem and its evaluator-level statement |
| `RoutineData.lean` | A routine on stored data (`Routine.withData`), its specification (`Spec.onData`) and judgment (`Meets.withData`) |
| `Link.lean`, `Transfer.lean` | Fixed implementation tables, count projections and explicit weights |
| `Logic.lean`, `Rules.lean`, `Counted.lean` | Conditional proof rules |
| `Store.lean`, `Frame.lean` | Buffer memory, liveness, shape preservation and frames |
| `Tape.lean`, `TapeLaw.lean`, `Law.lean` | Tape locality, laws and output observations |
| `Catalog/`, `Blas/`, `Profiles/` | Operation contracts and conditional implementations |
| `Examples/Certification.lean` | Repeated-addition certificate and adversarial regressions |
| `Examples/Resources.lean` | Mixed-format storage, workspace, and work/span certificates |
| `Confined.lean`, `Profiles/Confined.lean` | Confined, uniform and charged models |
| `Examples/Oracles.lean` | Misleading certificates the types accept and these properties reject |
| `Examples/Integrator.lean`, `IntegratorLink.lean` | The integrator of the *Programs, models and certificates* page: routines, model, certificate, linking |

The regressions address the canonical interfaces directly: impossible joint models, vacuous
inputs/tapes, runtime tree factories, failed execution, undeclared calls, omitted structural work,
and index arithmetic in a zero-round loop. No test invokes a linter to establish rejection.

This file is the current design of the layer. An earlier design, with a different vocabulary, is
recorded in [Ops-Certification](../../docs/design/Ops-Certification.md) (history only).
Breaking API changes: [rename map](../../docs/renames/Ops-certification.md) and the JSON maps in
`docs/renames/`.
