# `NLAlib/Ops`: the new core of the model of computation

Status: first build, 2026-11-10, branch `feat/ops-core`. Self-contained: every file imports only
Mathlib and other files of this directory. Nothing of `NLAlib/Computation` is used. Design:
`docs/design/Computation-Operations.md` (revision 3) on branch `design/operations-redesign`.
No registry, no targets, no ports yet.

## The pieces

| File | Content |
|---|---|
| `Store.lean` | Stack of buffers of possibly uninitialised cells; total updates `upd`, `updBlock` and guarded writes; `Mem` = store and tape position; read-after-update, scratch-on-top and block lemmas |
| `Syntax.lean` | `IExp`, `Operand`, `Env`, and `Stmt Op`: `skip`, `abort`, `seq`, `call`, `ite`, `whileFuel`, `bindIdx`, `alloc`, `loop`, `frame`. First-order: variables are positions in the environment, one tree for all sizes |
| `Exec.lean` | `Interp` (call, test, index); `run` (memory) and `exec` (memory, counts per `(operation, dimensions)`, live and peak scratch cells); `map_mem_exec`; `shape_store_of_run` |
| `Static.lean` | `staticCost`, `staticPeak` and their soundness `exec_within`; `Runs` (total, with counts and workspace), `RunsL` (liberal); `Runs.of_run` |
| `Contract.lean` | `Mode`, `Mode.Needs`, `OpSpec`, `Contract`, `Interp.Meets`; `BlockFn`, `BlockFn.spec`, `Interp.IsFn`; `Interp.ofFns`; `Interp.IsTest`, `Interp.IsIndex` |
| `Link.lean` | `Impl`, `Table`, `Stmt.link`, `Interp.link`; `run_link` (refinement transfer, both modes, no certificate) |
| `Transfer.lean` | `Count.push` (push-forward, weights), `Table.Accounts`, `Table.accounts_of_static`, `exec_link`, `Runs.link`, `link_total`, `RunsL.link`, `link_liberal`, `exec_link_weight`, `fail_subset` |
| `Tape.lean` | `Interp.TapeLocal`, `run_follows`, `staticWindow`, `pos_of_run_of_straight`, the window lemma `Interp.TapeLocal.link` |
| `Logic.lean` | `Wp` and one rule per constructor (`wp_seq`, `wp_call`, `wp_call_fn`, `wp_loop`, `wp_alloc`, `wp_frame`, `wp_ite`, `wp_bindIdx`), cell-level call rules, grounding (`Interp.link_meets`, `Interp.link_isFn`) |

Import graph: `Store → Syntax → Exec → {Static, Contract, Link} → {Transfer, Tape, Logic} →
Examples`.

## How they fit

* An algorithm is a `Stmt Op`. Its theorem is proved for every `Interp Op K` meeting contracts:
  the value part with the logic (`Wp`), the counts and the workspace by evaluating
  `staticCost` and `staticPeak` (`Runs.of_run`).
* A table gives each operation a tree over the lower operations or keeps it. `Stmt.link` turns a
  call into the `frame` of its implementation. `Interp.link` is the induced interpretation.
* "The implementation meets the contract" is `(I.link T).Meets md o C`, proved by
  `Interp.link_meets` (a `Wp` statement about the tree) or `Interp.link_isFn` (the exact
  certificate of a functional contract).
* The corollary about the linked program is `Runs.link` (total; counts pushed forward by
  `Count.push`, same workspace; needs `Table.Accounts`, which `Table.accounts_of_static` gives by
  `simp`) or `RunsL.link` (liberal; nothing needed). A tower is two applications.
* The evaluator fixes the charge (one per use, keyed by operation and dimensions); the workspace
  `W` is an argument of `exec`; what may read the tape is `Interp.TapeLocal`. None of them is in
  a contract.

## Examples (`Examples/`)

| File | What | Abstract theorem | Corollary by linking |
|---|---|---|---|
| `Arith`, `Dot`, `Blas`, `Krylov`, `GramSchmidt` | Tower: scalar arithmetic (functional, `StdModel u`) → `dot`, `axpy` (relational) → `nrm2` → modified Gram–Schmidt | `runs_mgs` | `runs_mgs_link` (two `Runs.link`), counts `push_blasCost_push_krylovCost_mgsCount` |
| `MatMul` | Functional contract: `mm` by a triple loop, exact certificate `mm_cert` | `runs_sq2` | `runs_sq2_link`, `push_mmCost_mm` |
| `StochRound` | `sradd` given its random word, and `sraddD` that draws; `SrModel` (sure bound, unbiasedness) | `runs_srsum` | `isSrAddD_link`, `sraddD_tapeLocal`, `runs_srsum_link` |
| `Liberal` | `div` by `recip` (may fail) and `mul`; mode-generic contract | `runsL_scale` | `runsL_scale_link` (`link_liberal`) |
| `Bits` | `wadd` over `xor3`, `maj`: ripple-carry adder, exact certificate `ripple_cert` | `runs_add3` | `runs_add3_link`, `push_wordCost_wadd`; a run checked by `rfl` |
| `Control` | `whileFuel`, `bindIdx`, `ite` on a concrete interpretation, runs checked by `rfl` | | |

Witnesses, one per contract, over the whole parameter range: `exists_arith`, `exists_isBlas`,
`exists_isKrylov`, `exists_isMM`, `exists_isSrAdd`, `exists_isRecipMul`, `exists_isWAdd`.

## Measurements (2026-11-10)

Elaboration, `lake env lean <file>`, two threads, Mathlib import included, seconds:
Store 2.1, Syntax 1.7, Exec 3.2, Static 2.6, Contract 2.6, Link 2.3, Transfer 2.0, Tape 2.2,
Logic 1.7; Arith 2.1, Dot 4.1, Blas 3.0, Krylov 2.2, GramSchmidt 4.6, MatMul 4.4, StochRound 3.5,
Liberal 2.7, Bits 4.1, Control 1.7. Core 2,892 lines in 9 files, examples 2,518 lines in 10 files.

Lines per example, statements included:

| Example | Mathematics | Program logic | Linking |
|---|---|---|---|
| Tower (two tables) | 85 | 348 | 72 |
| Matrix product | 24 | 109 | 27 |
| Stochastic rounding | 60 | 81 | 29 |
| Liberal | 30 | 59 | 8 |
| Bits | 27 | 137 | 30 |

The linking column is the accounting certificates (`simp` on static costs), the "induced
interpretation meets the contracts" lemmas (3 to 7 lines) and the corollaries (proof terms of 2
to 3 lines). Checks run on these modules only: `lake build --wfail`, the axiom audit (0
violations), `#lint` (0 errors), the rules check (left: E6 and P1, which are keyed to the old
core and the layer table, and P9 for three general lemmas kept here because the core imports only
Mathlib).

## Deviations from the design note

* No precision tags: one carrier `K`; a precision is part of the operation name. One tape stream.
* `Stmt` is first-order itself (positions in the environment), so there is no separate compiled
  form; `frame` replaces `named`, and linking is done on the tree, before the sizes.
* The charge is not a field: the evaluator counts one per use. The accounting is the workspace.
* `whileFuel` fails when the fuel is exhausted (otherwise a test of an implemented operation
  would make `run_link` false at fuel `0`).
* `Interp.IsFn` is conditional on admitted operands; it does not say the call fails elsewhere.
* A block function has one output block. Peaks are in cells, above the cells live at the start.
* Not built: conditional accounting (`AccountsLe`), recursion by iterated linking, registry.

## Found while proving the examples

* Reads after updates with a scratch buffer on top are done by hand (`change …; rw
  [Store.get_append_of_lt …, Store.get_updBlock_of_buf_ne …]`, about 25 times; `mgsStore_*`).
  Missing: a normal form and automation for stores, and named states.
* A relational contract is used by destructuring its postcondition and identifying its operands
  and reads again (`cases hd; cases hi; cases ho; obtain rfl := Option.some.inj …`). Missing: a
  call rule for contracts stated on given operands.
* Each block function needs its `…_apply` and `…_apply_of` lemmas. Missing: combinators for the
  common shapes (two blocks to one block).
* An operand handle outside the store can alias the scratch of an implementation, so even a
  liberal contract must assume its operand handles are in the store. The evaluator could reject
  such calls.
