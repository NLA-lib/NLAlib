# `NLAlib/Ops/Tools`: running, linting and auditing the new core

Diagnostic and compute support, included by the library umbrella. Formal certification in the
core is independent of linter results and diagnostic output. The tools follow the public module template, with exposed
computable support for `#eval` commands. Every Lean command below runs through
`scripts/ops/lean_gated.sh` (waits for no other `lean` and workers-slice anon memory < 6 GB, then
runs in `nlalib-workers.slice` with two threads). Gated commands share a per-user lock across
worktrees.

## 1. Runnable evaluator and cost profiler (`Exec`, `Program`, `Machines`, `Tables`, `Run`, `Demo`)

```lean
import NLAlib.Ops.Tools.Run
open NLAlib.Ops NLAlib.Ops.Tools
#eval profileProgram p I R formats τ d m -- checked fixed Program, full resource accounting
#eval profile I W τ s ρ m          -- any s : Stmt Op Tst, any I : Interp Op Tst K, memory m
#eval profileFrame I W τ s dims args bufs   -- whole buffers as operands
```

`profileProgram` uses the same format/arity checks, mandatory instrumentation, byte-sized
allocations, primitive workspace and query reservation as canonical `exec`. It reports the full
operation/query/bookkeeping log, explicitly weighted work and sequential modeled span, scratch
payload bytes, and initially resident plus scratch payload bytes. Sequential calls add spans;
primitive-internal parallelism comes only from the supplied model. These are modeled resources,
not measurements of elapsed time or a certificate of successful execution on every input.

`profile` and `profileFrame` are explicitly **RAW CONDITIONAL diagnostics**. They accept any
statement, interpretation and environment and omit mandatory instrumentation and format checks.
They print raw counts next to `stmtCost`, scratch payload bytes next to `stmtPeak`, and a bounds
comparison that is false on failed execution. A raw report is not a canonical certificate.

* `Exec.lean`: raw `execC` equals `evalCounted` after converting its log to a `Count`;
  `staticAt_eq` identifies the computable per-key bound with `stmtCost`, and `staticKeys` is
  complete for those keys. `allocAs` charges format width times length in payload bytes.
* `Program.lean`: `execProgramC` is the computable canonical wrapper.
  `map_toSt_execProgramC` proves equality with canonical `exec`; `profileProgram_work` and
  `profileProgram_span` prove that reported resources use the core's full count.
* `ProgramFixtures.lean`: kernel-checked computations with unequal operation/query/core weights,
  `[width,length]` allocation keys, query scratch, format/arity rejection, and raw failure.
* `Machines.lean`: carriers `ℚ` (exact; `sqrt` is `Rat.sqrt`, exact on squares) and `Float`;
  `blas1Fn`, `blasFn` (level 1 and scalar), `randFn A` (`ROp` with a matrix by rows),
  `withQueries` (comparisons `CmpTst`, `IdxTst.toNat`), `cmpOpFn` (flag-writing comparisons),
  `withFlagTest` (`FlagTst.isSet`), tapes `signTape seed`, `listTape`, memories `memOf`, `vals`,
  `blank`, `frameOf`; `ShowKey` names for the report.
* `Tables.lean`: computable tables of the profiles, each proved equal to the profile's table:
  `seqTable` (`Blas.seq`), `pairwiseTable k`, `gaussTable`, `noisyTable σ`, `noisyDrawsTable σ`.
* `Demo.lean`: branching on a comparison flag, gemm (algorithm, `Blas.seq`, `Blas.pairwise 3`
  in `Float`), pairwise summation
  (depths 4 and 1 against sequential, in `Float`), MGS, CGS, Girard–Hutchinson with a tape of
  signs (algorithm and `Rand.gaussLoop`), the noisy power iteration (algorithm and
  `noisyDraws`). Run: `scripts/ops/lean_gated.sh lake env lean NLAlib/Ops/Tools/Demo.lean`.

## 2. Target linter (`LintRegistry`, `Lint`, `LintFixtures`, `LintAll`)

```lean
import NLAlib.Ops.Tools.Lint
#ops_lint NLAlib.Ops.Examples.runs_gemm_link_seq   -- an error per violation, info if it passes
#ops_lint_scan                                      -- every headline of the imported modules
```

This is heuristic guidance, not a certification boundary. Canonical `Runs`, `Program.Certifies`,
and `Impl.Meets` have structural guarantees enforced by the core. The linter recognizes those
schemas and explicitly reports `UNSUPPORTED` because conditional heuristics do not inspect them;
it never marks
them as passing (a)-(f). `Profile.Refines` is also recognized and diagnosed as conditional profile
refinement, not canonical certification. An explicit request on an unrecognized statement gives
a schema diagnostic rather than an empty-check pass.

Conditional headlines contain `ConditionalRuns`, `ConditionalRunsW`, `ConditionalRunsL`,
`ConditionalRunsLaw`, or `Impl.Triple` (under `∀`, `∧`, `∃`). Rules, on the statement only:
(a) the program, tables of `Stmt.link` set apart, mentions only sizes (`ℕ`), rationals, types
and instances, and reaches no noncomputable definition; (b) the interpretation is a variable of
the statement (or `Interp.link` of one, or `ops_register_model`), not under `∃`, not fixed by an
equation, constrained by a hypothesis; (c) one witness covers the contract set jointly;
(d) counts and workspace reach no `Count.push`/`stmtCost`/`stmtPeak`/
`staticCost`/`staticPeak`/`Count.upper`/
`Profile.cost`; (e) a liberal statement has a positive success theorem in its module or named
`<name>_success`, with the same program and table arguments up to parameter renaming; (f) the
algorithm's tree reaches no ξ-taking primitive.

**Conventions proposed** (the linter reads them; no core change needed):
* *Witness*: a theorem named `exists_…` whose statement is `∃ …, C₁ … ∧ C₂ … ∧ …`; it covers
  the `NLAlib` predicates `Cᵢ` and their parent structures under a single leading existential
  telescope. `ops_register_witness` admits other names. The checker compares declaration
  predicate heads, including exported theorem interfaces represented by axiom metadata. It does
  not validate proof or axiom provenance; core certification and independent safety/axiom audits
  supply the formal guarantees.
  Review the shared arguments and parameter range in the witness statement.
  The *contract set* of a target is the `NLAlib` predicates of its hypotheses on the
  interpretation, closed under the parameters they share (machine, decoding, law, …).
* *ξ-taking primitive*: a constructor named `…Xi`, or `ops_register_xi c`.
* *Model primitive*: `ops_register_model c`.
* *Implementation*: an `Impl` used in the value of a `Table`/`Profile` definition ((f) exempt).

`LintFixtures.lean`: one true theorem per cheat (memory-dependent program, existential and
specific interpretation, contract without witness, liberal headline over a table of aborts,
`sraddXi` in an algorithm), each with its `#guard_msgs`, and accepted headlines of the examples.
`LintAll.lean`: imports every `NLAlib.Ops` module and runs `#ops_lint_scan`
(`scripts/ops/lean_gated.sh lake env lean NLAlib/Ops/Tools/LintAll.lean`).

## 3. Audit (`scripts/ops/audit.py`, `scripts/ops/Audit.lean`)

`python3 scripts/ops/audit.py [--no-times]`: source scan of `NLAlib/Ops/**/*.lean` (comments
and strings removed) for `sorry`, `admit`, `native_decide`, raised `maxHeartbeats`/
`maxRecDepth`, `implemented_by`, `extern`, `unsafe`, `axiom`; environment scan of every constant
of `NLAlib.Ops.*` (axioms only `propext`, `Classical.choice`, `Quot.sound`; no unsafe/partial;
no `implemented_by`); per-file elaboration time. The environment scan builds Ops modules with
`--wfail`. The audit exits nonzero on a violation.
