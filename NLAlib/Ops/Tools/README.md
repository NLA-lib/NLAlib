# `NLAlib/Ops/Tools`: running, linting and auditing the new core

Outside the trusted base: nothing in `NLAlib/Ops` imports these files, no theorem of the library
depends on them, and they are not in `NLAlib.lean`. They are plain (non-`module`) files so that
`#eval` can run the library's programs. Every Lean command below runs through
`scripts/ops/lean_gated.sh` (waits for no other `lean` and workers-slice anon memory < 6 GB, then
runs in `nlalib-workers.slice` with two threads). Gated commands share a per-user lock across
worktrees.

## 1. Runnable evaluator and cost profiler (`Exec`, `Machines`, `Tables`, `Run`, `Demo`)

```lean
import NLAlib.Ops.Tools.Run
open NLAlib.Ops NLAlib.Ops.Tools
#eval profile I W τ s ρ m          -- any s : Stmt Op Tst, any I : Interp Op Tst K, memory m
#eval profileFrame I W τ s dims args bufs   -- whole buffers as operands
```

The entry point takes a tree, an interpretation, a workspace function, a tape, an environment and
an initial memory, so it runs a tree from any producer (hand-written, the logic lane's builder,
`Stmt.link`). It prints the final memory (or `FAILED`), the counts per (operation, dimensions)
of the run next to `staticCost` of the tree, the peak of scratch cells next to `staticPeak`, and
`within static bounds: true/false`.

* `Exec.lean`: `execC`, the counted run with counts as a log, and `map_toSt_execC`: it **is**
  the core's `exec` (`exec` is noncomputable only because counts are `Finsupp`); `staticAt`
  with `staticAt_eq` (= `staticCost` at a key) and `staticKeys` with `staticAt_eq_zero` (complete
  list of keys). The core is unchanged.
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

A headline is a theorem whose conclusion has `Runs`, `RunsW`, `RunsL`, `RunsLaw` or
`Impl.Meets` (under `∀`, `∧`, `∃`). Rules, on the statement only:
(a) the program, tables of `Stmt.link` set apart, mentions only sizes (`ℕ`), rationals, types
and instances, and reaches no noncomputable definition; (b) the interpretation is a variable of
the statement (or `Interp.link` of one, or `ops_register_model`), not under `∃`, not fixed by an
equation, constrained by a hypothesis; (c) one witness covers the contract set jointly;
(d) counts and workspace reach no `Count.push`/`staticCost`/`staticPeak`/`Count.upper`/
`Profile.cost`; (e) a liberal statement has a success statement about the same program in its
module (or a theorem `<name>_success`); (f) the algorithm's tree reaches no ξ-taking primitive.

**Conventions proposed** (the linter reads them; no core change needed):
* *Witness*: a theorem named `exists_…` whose statement is `∃ …, C₁ … ∧ C₂ … ∧ …`; it covers
  the `NLAlib` predicates `Cᵢ` and their parent structures. Others: `ops_register_witness`.
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
