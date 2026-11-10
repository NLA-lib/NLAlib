# `NLAlib/Ops`: the new core of the model of computation

Status: fourth build (base edits after the two reviews), 2026-11-10, branch `feat/ops-core`.
Self-contained: every file imports only Mathlib and other files of this directory. Nothing of
`NLAlib/Computation` is used. Design: `docs/design/Computation-Operations.md` (revision 3) on
branch `design/operations-redesign`; layout and profiles after
`docs/design/Library-Organization.md` (branch `design/library-organization`, approved). Reviews:
`Review-Fable-OpsCore.md`, `Review-COMPDYN-OpsCore.md`. No registry, no targets, no ports yet.

## What this step changed

The nine base edits that both reviews asked for before anything is built on the core.

1. **Arithmetic contract** (`Catalog/Scalar.lean`). `StdModel.div` assumes `dec b ≠ 0`: nothing
   is said of a division by zero, so no theorem goes through one. `StdModel.lit` rounds every
   literal (`StdModel.zero` is a corollary). `IsScalErr` is guarded the same way. A witness that
   is not exact: `inflMachine u` multiplies every result by `1 + u` and attains the bounds
   (`stdModel_infl`).
2. **One contract structure** (`BlockRel.lean`, `Blocks.lean`, `Rules.lean`). `BlockRel` has any
   number of input and output blocks, a tape window, a domain and a relation. Relational,
   functional (`BlockFn.rel`, the graph of a function) and window contracts are instances.
   **One call rule**, `wp_call_rel`, in every mode, with `wp_call_rel_liberal` for partial
   correctness; the rules for one cell, one block, two blocks and for the scalar functions are
   corollaries. The three forms of the third build (`BlockFn.spec`, the one-output `BlockRel`,
   `WinRel`) and their rules and certificates (`MeetsRel`, `MeetsWin`, `wp_call_win`) are
   replaced by this one.
3. **One certificate** (`Cert.lean`, `Law.lean`). `Impl.Meets R I md C`: the implementation `R`
   meets the contract `C` over `I`. An algorithm is stated in this form, like an implementation
   of a level-1 operation. `Interp.link_meets` grounds it (the algorithm becomes an operation);
   `Impl.Meets.runs`, `runs_rel`, `runsL`, `runsLaw` are the bridge to `Runs`, `RunsL`,
   `RunsLaw`. `gemm`, `mgs`, `cgs`, `hutch`, `npow` are restated as certificates, and their
   abstract theorems are one application of the bridge.
4. **The call step** (`Tactic.lean`): `wp_call h [facts] with v hv`.
5. **Counts that depend on the data** (`Static.lean`, `Counted.lean`, `Transfer.lean`,
   `Syntax.lean`, `Exec.lean`). `RunsW` and `RunsFromW`: the postcondition is given the counts.
   One rule per constructor. `Table.AccountsW`: a weighted accounting certificate.
   `whileFuel` binds the round index, stops at the cap without failing and passes the number of
   rounds to a continuation. `Catalog/Compare.lean`: comparison queries.
6. **`IsIndex` is `Option`-valued** (`Contract.lean`): a conversion fails exactly where its
   function does. `IdxTst.toNat` fails on a negative value (`IsToNat.index_neg`).
7. **Precision tags** (`Catalog/Tagged.lean`): `Tagged π G`, `CastOp π ρ`.
8. Per-block operands and strides: **not done** (see "Not done").
9. **Liberal statements, the tape, the README.** `wp_abort_liberal`,
   `Impl.meets_liberal_abort`, `Interp.link_meets_liberal_of_abort` and the fixture
   `runsL_scale_link_abort`: a liberal corollary holds for a table that fails, so it is never a
   result without a statement of success. A `Contract` no longer receives the tape: it declares
   a stream and a window and is given the entries of that window (`Contract.on`). Timings and
   counts below are measured.

## The pieces

| File | Content |
|---|---|
| `Store.lean` | Stack of buffers of possibly uninitialised cells; total updates `upd`, `updBlock` and guarded writes; `Mem` = store and tape position; `Mem.Live` |
| `Syntax.lean` | `IExp`, `Operand`, `Env`, and `Stmt Op Tst`: `skip`, `abort`, `seq`, `call`, `ite`, `whileFuel` (round index, early exit, continuation), `bindIdx`, `alloc`, `loop`, `frame`; `Stmt.ifZero`, `Stmt.ifPos`, `Stmt.whileStrict` |
| `Exec.lean` | `Interp` (call, test, index); `run` and `exec` (counts per operation or query and dimensions, live and peak scratch cells); `map_mem_exec`, `shape_store_of_run`, `cost_le_of_exec` |
| `Static.lean` | `staticCost`, `staticPeak`, soundness `exec_within`; `Runs`, `RunsW`, `RunsL`; `Runs.of_run` |
| `Contract.lean` | `Mode`, `Contract` (stream, window, specification given the window), `Interp.Meets`, `Interp.IsTest`, `Interp.IsIndex` |
| `BlockRel.lean` | `Mem.updBlocks`, `Mem.Room`, `Mem.writes`; **`BlockRel`**, `BlockRel.Post`, `BlockRel.spec` |
| `Blocks.lean` | `BlockFn` (with `nd`, `outLens`, several outputs), `BlockFn.rel`, `BlockFn.apply`, `Interp.IsFn`, `Interp.ofFns`; shapes `const`, `un`, `bin`, `tern`, `draw`, `drawVec`, `of1`, `of2`, `of3` |
| `Link.lean` | `Impl`, `Table`, `Stmt.link`, `Interp.link`, `run_link`; `Table.comp`, `Table.iter` |
| `Transfer.lean` | `Count.push`, `Count.weight`, `Table.Accounts`, **`Table.AccountsW`**, `Count.upper`, `exec_link` (one induction for counts and weights), `Runs.link`, `link_total`, `RunsW.link`, `exec_link_weight`, `RunsL.link`, `link_liberal`, `fail_subset` |
| `Stream.lean`, `Tape.lean`, `TapeLaw.lean` | The tape, `Interp.TapeLocal`, the window lemma, `IsTapeLaw` and the conditional law of a window |
| `Logic.lean` | `Wp`, one rule per constructor, `wp_whileFuel`, `wp_ifZero`, `wp_ifPos`, `wp_abort_liberal` |
| `Rules.lean` | **The call rule** `wp_call_rel`, `wp_call_rel_liberal`, and the corollaries `wp_call_rel_cell`, `wp_call_rel1`, `wp_call_rel2`, `wp_call_fn`, `wp_call_fn_liberal`, `wp_call_const`, `wp_call_un`, `wp_call_bin`, `wp_call_tern`, `wp_call_draw` |
| `Cert.lean` | **`Impl.Meets`**, `Interp.link_meets`, `Interp.link_isFn`, `Impl.meets_rel`, `Impl.meets_fn_of_run`, the bridge `Impl.Meets.runs`, `runs_rel`, `runsL`; `Interp.IsFn.meets_rel`; liberal vacuity |
| `Tactic.lean` | **`wp_call`**, with `wp_adm`, `wp_side`, `wp_read`, `wp_shape`, `wp_dom`, `wp_intro` |
| `Frame.lean`, `StoreSimp.lean`, `Attr.lean` | Reads through updates; footprints (`Store.EqOff`, `peel`, `eq_updBlock₂`, `isSome_readBlock`); `store_simp`, `store_side`; simp sets `storeNF`, `admNF` |
| `Counted.lean` | **`RunsFromW`** with a rule per constructor |
| `Window.lean` | `drawRel`, `wp_loop_fill` |
| `Law.lean` | `RunsLaw`, `Impl.Meets.runsLaw`, `Profile.Certifies.runsLaw`, failure probabilities, `runVal` |
| `Profile.lean` | Groups (`Has`, `Apart`), `Profile`, `Profile.Certifies`, `over`, `iter` |
| `Catalog/` | `Scalar` (`ScalarOp`, `Machine`, `IsScalar`, `StdModel`), `Blas1`, `Compare` (`CmpTst`, `IdxTst`, `IsCmp`, `IsToNat`), `Tagged` (`Tagged`, `IsScalarAt`, `CastOp`), `Isotropic`, `Random` |
| `Blas/`, `Profiles/` | The level-1 implementations and the profiles `Blas.seq`, `Blas.pairwise k`, `Rand.gaussLoop` |

## The contract, the rule, the certificate

```lean
structure BlockRel (K : Type) where
  nd : ℕ                                   -- number of dimensions
  stream : ℕ := 0                          -- tape stream of the window
  win : List ℕ → ℕ := fun _ => 0           -- length of the window
  inLens : List ℕ → List ℕ                 -- lengths of the input blocks
  outLens : List ℕ → List ℕ                -- lengths of the output blocks
  dom : List ℕ → List (List K) → List K → Prop := fun _ _ _ => True
  rel : List ℕ → List (List K) → List K → List (List K) → Prop   -- dims, inputs, window, outputs

def BlockRel.spec (R : BlockRel K) (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) :
    Contract K

theorem wp_call_rel (hI : I.Meets md o (R.spec adm))
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some b) (hnd : d.length = R.nd) (hk : R.win d = k)
    (hls : R.outLens d = ls) (hadm : adm d a b) (hlive : m.Live (a ++ b))
    (hr : m.readBlocks a (R.inLens d) = some xs) (hdom : R.dom d xs (τ.window R.stream m.pos k))
    (hz : m.Room b ls)
    (hQ : ∀ ys, ys.map List.length = ls → R.rel d xs (τ.window R.stream m.pos k) ys →
      Q ((m.updBlocks b ys).advance k)) : Wp md I τ (.call o ds ins outs) ρ Q m

def Impl.Meets (R : Impl Op Tst) (I : Interp Op Tst K) (md : Mode) (C : Contract K) : Prop

theorem Interp.link_meets (hT : T o = .inl R) (h : R.Meets I md C) : (I.link T).Meets md o C

theorem Impl.Meets.runs_rel (h : R.Meets I .total (B.spec adm)) (W) (hnd) (hadm) (hl) (hr)
    (hdom) (hz) :
    Runs I W τ R.body (Env.frame d (ins ++ outs)) m (staticCost R.body _) (staticPeak W R.body _)
      (B.Post d xs outs (τ.window B.stream m.pos (B.win d)) m)
```

A functional operation is `I.IsFn md o f adm := I.Meets md o (f.rel.spec adm)`; under it a call
is the equation `BlockFn.apply` (`Interp.IsFn.callS_eq`), which exact certificates use
(`wp_call_fn`, `Interp.link_isFn`).

Examples of the forms: `dotRel` (two inputs, one cell), `axpyRel` (in place), `mgsRel` and
`cgsRel` (**two output blocks**), `drawRel` (the output is the window), `nmvRel`, `hutchRel`,
`npowRel` (hidden randomness: the output is a function of the inputs and the window).

## How a block is proved (playbook, short)

* **A call is one line**: `wp_call hJ.dot with v hv`, `wp_call hJ.axpy [hH.eq_iff] with zs hzl hzs`,
  `wp_call (hS .neg)`. The tactic applies the sequence rule and the call rule, evaluates the
  operands, finds the blocks read from the facts in the context, discharges admissibility, live
  handles, the domain and room, and introduces the outputs with their relation in reduced form.
  A functional scalar call introduces nothing: the memory after it is `m.upd z (g a b)`. A side
  goal that is not discharged is left under its name (`hadm`, `hlive`, `hr`, `hdom`, `hz`).
* A catalog contract is declared `@[simps (attr := storeNF)] def fooRel : BlockRel K`, and a
  predicate on admitted operands `@[admNF] def`. (Tagging the definition itself with `storeNF`
  makes `simp` use the conditional equations of its `match`, with the expensive discharger.)
* The state after a call is the state before with one more update; nothing is renormalised.
  `store_simp [facts]` pushes reads through the updates.
* A loop invariant says what the written blocks hold and that the rest is untouched:
  `S.EqOff F s'`. A write keeps it by `EqOff.upd` / `EqOff.updBlock`, a fact about the initial
  store is kept by `hfr.readBlock_of fact (by store_side)`, and at the end `EqOff.eq_updBlock`
  (one block), `EqOff.eq_updBlock₂` (two blocks) or `EqOff.peel` give the equation of a contract;
  `EqOff.pop` frees a scratch buffer.
* **A certificate**: `refine Impl.meets_rel fun d ins outs τ m X hnd hadm hl hr _ hz => ?_`, then
  the dimensions and operands are destructured (`List.length_eq_two`, `Mem.readBlocks_two`,
  `Mem.room_one`, …) and the run lemma is applied. The abstract theorem is
  `(foo_spec hJ).runs_rel W …` with the static counts by `simp`.
* A loop with early exit: `wp_whileFuel rfl Inv h0 (fun i hi m hinv => holds_testAt rfl rfl hb ?_)
  hcap`. Counts that depend on the data: the same proof with `RunsFromW.whileFuel`,
  `RunsFromW.bindIdx`, `RunsFromW.seq`, `RunsFromW.call`, and `RunsFromW.of_wp` for the parts
  whose counts are static.
* A law-level theorem: the certificate against a contract with a window, then
  `(foo_spec hJ).runsLaw W ξ obs …`, whose last argument is the mathematics: a property of the
  random variable from the relation, sample by sample, and the law of the tape.

## Counts that depend on the data

* `RunsW I W τ s ρ m M Q`: the run succeeds within the workspace `M` and `Q` holds of the final
  **counts** and memory. `Runs` is the case `Q c m' := c ≤ B ∧ …` (`runs_iff_runsW`). A weighted
  clause `∀ T` monotone superadditive, `weight T c ≤ …` is such a `Q`.
* `RunsFromW I W τ s ρ st p Q`: from a state, `Q` holds of the counts **added** and the memory.
  Rules: `skip`, `seq` (the continuation is proved from the state and counts reached), `call`
  (from any `Wp` of the call), `ite`, `bindIdx` (charged at the value read), `alloc`, `loop`
  and `whileFuel` (an invariant on the counts so far and the memory), `frame`, `of_wp`, `mono`,
  `runsW`, `runs`.
* `Table.AccountsW T I W₂ w₂ t W₁`: `w₂` is an additive weight of the lower counts with values
  in an ordered monoid and every run of the implementation of `o` at `d` adds at most `t o d`
  to it. The counts of the run need not be a function of `(o, d)`. `Table.Accounts` is the case
  of the counts themselves (`Accounts.toW`), and `exec_link` is one induction for both.
  `RunsW.link` and `exec_link_weight` transfer a bound on the weight that may depend on the
  final memory.
* Fixture `Examples/Split.lean`: a split `k₊` read from the store, kernels at `k₊` and
  `k - k₊`. `runsW_split` gives the exact counts; `weight_split_le` gives
  `T k₊ + T (k - k₊) ≤ T k` for every superadditive `T`; `splitTable_accountsW` certifies the
  split as an implementation; `runsW_twice_link` gives `2 T k` for a linked algorithm.
* What is missing: a counted judgment for partial correctness. `AccountsW.impl` speaks of every
  successful run, so the fixture proves it by unfolding `exec` on its small tree. For a large
  implementation with data-dependent counts this needs `RunsFromWL` ("if the counted run
  succeeds, …") with the same rules.

## Loops and queries

`whileFuel fuel q dims ins body k`: round `i` (a new index variable in `dims`, `ins`, `body`)
evaluates the test and runs the body if it holds; the loop ends at the first round whose test
fails, or after `fuel` rounds without a further test; then `k` runs with the index variable
bound to the number of rounds done. `Stmt.whileStrict` is the loop that fails if the test still
holds after the fuel (`Examples/Control.lean`, `Examples/Loops.lean`). The static count is the
sum over the rounds and the supremum over the exits.

Queries: `CmpTst` (`lt`, `le`, `eq`, `isZero`, `isPos`; `IsCmp dec`, exact on decoded values) and
`IdxTst.toNat` (`IsToNat dec`: the floor of a nonnegative value, failure otherwise), with
`IsCmp.test_lt`, … and `IsToNat.index_eq`, `index_neg` for use in `wp_ite`, `holds_testAt`,
`wp_bindIdx`. Witness `exists_isCmp`.

## Precision tags

A tag is a copy of a group: `Tagged π G` (`π` a type used as a name). A call at a tag is
`Tagged.inj π ScalarOp.add`. Counts are per tag because the operations of two tags are different
names (`Tagged.inj_ne`); contracts are per tag (`IsScalarAt π M I`: one machine, one standard
model per tag); a cast is `CastOp π ρ` with `IsCast` and `CastModel`.

**Nothing is rewritten for a tag**: an algorithm, implementation or table written for
`[Has G Op]` is used at a tag with the instance `Tagged.has π`, and its certificate is the same
theorem (`sumSeq_spec_at` is `sumSeq_spec` applied). This departs from the spelling
`Blas1Op π` of the organisation note: the tag is not a parameter of every group but a wrapper,
so the untagged group stays the default and no table changes when a second precision appears.
`Examples/Mixed.lean`: `z := x y + w` with the product at `Lo` and the sum at `Hi`,
`|ẑ - (x y + w)| ≤ u_hi |x y + w| + (1 + u_hi) u_lo |x y|`, counts
`one (mul at Lo) + one cast + one (add at Hi)`, witness with two different machines.

## Randomness

Unchanged in content since the third build; the forms are now instances of `BlockRel`.

* The tape `Tape K = ℕ → ℕ → K`, one position for all streams; the law `IsTapeLaw law P ξ` is a
  clause of the access model; the interpretation is fixed before the sample.
* *Visible* randomness: `gauss [n] [] [g]` with the contract `drawRel` (the output block is the
  window). *Hidden* randomness: the operation has no random operand and its contract has a
  window (`nmvRel`, `drawBin`); the implementation draws into scratch that it allocates.
  `hutch` and `npow` are themselves operations with hidden randomness for their callers
  (`hutchRel`, `npowRel`).
* *Nobody else reads the window*: `Interp.TapeLocal`, a clause of the access model for the
  bottom operations and a field of every profile certificate.
* A law-level theorem is `RunsLaw`; it is obtained from the certificate by
  `Impl.Meets.runsLaw` and for a linked program by `Profile.Certifies.runsLaw`.

## Test cases (`Examples/`)

| File | What | Certificate | Abstract theorem and corollaries |
|---|---|---|---|
| `Gemm` | `C = A B`, `m p` calls of `dot` | `gemm_spec` against `gemmRel` | `runs_gemm_rounded`; `runs_gemm_link_seq`, `runs_gemm_link_pairwise`, `push_seq_gemmCount`, `push_pairwise_gemmCount` |
| `GramSchmidt` | modified Gram–Schmidt of one vector, **two outputs** `w`, `R` | `mgs_spec` against `mgsRel` | `runs_mgs_rounded`; `runs_mgs_link_seq`, `push_seq_mgsCount` |
| `CgsMath`, `Cgs`, `CgsQR`, `CgsLinked` | classical Gram–Schmidt, **two outputs** `Q`, `R`; `R` is also an input (only its upper triangle is written) | `cgs_spec` against `cgsRel` | `runs_cgs_rounded` (postcondition `CgsFactored`), `CgsOut.backward`, `CgsOut.backward_std`; `runs_cgs_link_seq`, `runs_cgs_link_pairwise`, `push_seq_cgsColCount` |
| `Hutch`, `HutchLinked` | Girard–Hutchinson, visible draws inside, a window of `N n` for the caller | `hutch_spec` against `hutchRel` | `runsLaw_hutch` (by `Impl.Meets.runsLaw`); `runsLaw_hutch_link`, `push_gaussLoop_hutchCount` |
| `NoisyMath`, `Noisy`, `NoisyLinked` | noisy power iteration, in place, a scratch block | `npow_spec` against `npowRel`; `nmvImpl_spec` | `runsLaw_npow`; `noisy_certifies`, `runsLaw_npow_link`, `push_noisyDraws_npowCount` |
| `StochRound` | stochastically rounded sum | `srAdd_cert`, `isSrAdd_link` | `runsLaw_srsum`, `sr_certifies`, `runsLaw_srsum_link` |
| `Split` | data-dependent sizes, weighted counts | `splitImpl_spec`, `splitTable_accountsW` | `runsW_split`, `weight_split_le`, `runsW_twice_link` |
| `Mixed` | two precisions and a cast | `sumSeq_spec_at` | `runs_mulAddMixed`, `exists_isMixed` |
| `Loops` | halving with early exit; a hundred buffers | | `wp_halve`, `runs_halve` (counts `Nat.size v`), `wpL_halveStrict`, `read_of_hundred` |
| `Control` | `whileFuel` at the cap, `whileStrict`, the round count in the continuation, `bindIdx` | | examples by `rfl` |
| `Liberal` | liberal mode, and its vacuity | `div_link_liberal` | `runsL_scale`, `runsL_scale_link`, `runsL_scale_link_abort` |
| `Dot`, `MatMul`, `Bits`, `RandomWitness` | exact certificates, bit level, witnesses | `dot_cert`, `mm_cert`, `ripple_cert` | unchanged in content |

`srsum`, `halve`, `sq2`, `add3`, `scale` keep their statement on an explicit environment: they
were not in the list to restate.

Witnesses: `exists_isScalar`, `stdModel_infl`, `Blas.exists_isBlas1`, `exists_isCmp`,
`exists_isMixed`, `exists_isHalving`, `exists_isRecipMul`, `exists_isTapeLaw`,
`exists_isRandLin`, `isNoisyMv_noiseFn`, `exists_isSrLo`, `memLp_quadForm_gaussian`. The
level-1 witness is still exact arithmetic; `stdModel_infl` gives a machine that is not exact for
the scalar model.

## Measurements (2026-11-10)

All numbers are measured on this branch and on the reviewed commit `e6b29eb0` with the same
script (`lake env lean <file>`, two threads, one process at a time, Mathlib import included).

**Declarations**, from a scan of the environment (constants declared in the modules
`NLAlib.Ops.*`, without internal and auto-generated names): 857 theorems (628 written as `theorem` in the source, the others generated by `@[simps]` for the contracts in operand form), 67 fields of `Prop` structures, 673 definitions, in 56 files and 13,700 lines. The reviewed commit
had 652 theorems by the same scan, of which 82 fields of `Prop` structures; a `grep` for
`theorem` gives 570 there.

**Elaboration**, seconds, before → after (files of the reviewed commit):

| | before → after |
|---|---|
| Core | `Store` 2.0 → 2.1, `Syntax` 2.1 → 2.0, `Exec` 3.3 → 3.5, `Static` 2.7 → 2.9, `Contract` 1.8 → 1.6, `Blocks` 2.9 → 2.3, `Link` 2.6 → 2.7, `Transfer` 2.1 → 2.4, `Tape` 2.3 → 2.4, `TapeLaw` 2.8 → 2.8, `Logic` 1.7 → 1.8, `Rules` 1.7 → 1.7, `Frame` 1.8 → 1.9, `StoreSimp` 2.3 → 2.4, `Counted` 1.7 → 2.0, `Window` 1.7 → 1.6, `Law` 2.3 → 2.4, `Profile` 1.7 → 1.8 |
| Catalog, level 1, profiles | `Catalog/Scalar` 2.6 → 2.6, `Catalog/Blas1` 2.2 → 2.2, `Catalog/Random` 2.2 → 2.3, `Blas/Sum` 3.5 → 4.2, `Blas/Dot` 3.3 → 2.6, `Blas/Level1` 2.8 → 2.9, `Profiles/Blas` 3.5 → 3.5, `Profiles/BlasCert` 3.0 → 3.0, `Profiles/Random` 2.4 → 2.6 |
| Examples | `Gemm` 2.7 → 3.2, `GramSchmidt` 4.0 → 5.1, `Cgs` 5.0 → 5.7, `CgsQR` 3.8 → 4.1, `CgsLinked` 2.4 → 2.4, `Hutch` 5.5 → 6.1, `HutchLinked` 3.5 → 3.5, `Noisy` 3.7 → 3.8, `NoisyLinked` 7.5 → 8.7, `StochRound` 4.9 → 4.9, `Loops` 2.1 → 2.6, `Control` 1.8 → 2.0, `Liberal` 2.7 → 2.8, `Dot` 4.2 → 4.2, `MatMul` 4.5 → 4.7, `Bits` 4.2 → 4.3, `RandomWitness` 3.5 → 3.8 |
| New files | `BlockRel` 2.0, `Cert` 1.7, `Tactic` 2.5, `Catalog/Compare` 2.2, `Catalog/Tagged` 2.1, `Examples/Split` 3.0, `Examples/Mixed` 3.4 |

The 49 files of the reviewed commit: 143.5 s before, 150.0 s after; all 56 files: 166.8 s. The
slowest file is `NoisyLinked` (8.7 s). A call by `wp_call` costs about 0.2 s more than the
hand-written rule application it replaces (the examples with many calls are 0.5 to 1.2 s
slower); the cost is the general `simp` on the admissibility side goal.

**Program-logic lines.** The lines of a call drop from five or six to one. The total moves
little, for two reasons: calls are a small part of a run proof (frames, invariants, lengths and
index facts are the rest, and are not touched by this step), and every algorithm now also has a
contract in operand form and a certificate. Lines of the declarations, docstrings included:

| | Run proofs (`wp_*`) before → after | Calls | Lines of the calls before → after | Contract and certificate (new) |
|---|---|---|---|---|
| `gemm` | 51 → 43 | 1 | 5 → 1 | 38 |
| modified Gram–Schmidt | 84 → 72 | 4 | 22 → 4 | 45 |
| classical Gram–Schmidt | 217 → 202 | 7 | 39 → 9 | 81 |
| Girard–Hutchinson | 79 → 54 | 4 | 21 → 5 | 35 |
| noisy power iteration, with `nmvImpl_spec` | 120 → 86 | 7 | 40 → 8 | 29 |

The reviews' baseline counts the whole program-logic part of a file (`gemm` 105, modified
Gram–Schmidt 160, classical Gram–Schmidt 400). By the same count of declarations the program
logic of `gemm` is 94 → 96 lines plus 38 for the contract and the certificate, modified
Gram–Schmidt 136 → 127 plus 45, classical Gram–Schmidt 333 → 329 plus 81 (which includes the
readability of `R`). The mathematics is unchanged. So this step makes a call procedural and
gives one statement form; it does not yet make the program part short. What dominates now is
listed under "For the logic layer".

Checks on these modules: `lake build --wfail` clean; no `sorry`, no `set_option`; axioms
`propext`, `Classical.choice`, `Quot.sound` only (checked for every theorem by the scan); files
under 600 lines, proofs under 80.

## Not done, and why

* **Item 8, per-block operands and strides.** Not cheap. Admissibility by block needs the
  certificates of `axpyLoop`, `scalLoop`, `copyLoop` proved again with frames by block instead
  of by buffer, and then `cgs` rewritten without its work vector; strides change the dimensions
  of `dot` and every profile cost. `OutApart` and `InPlace` are still by buffer. The contract
  form does not stand in the way: `adm` sees the operands, and a block-level predicate can read
  the lengths from the `BlockRel`.
* **Memory per tag.** The workspace is counted in cells of one size. A workspace per tag needs
  the tag on `alloc` and in the state of the counted run: a change of the evaluator.
* **A counted judgment for partial correctness** (see "Counts that depend on the data").
* **`AccountsW` whose bound depends on the data of the call.** The bound `t o d` is a function
  of the operation and the dimensions; a kernel whose weight depends on its data takes the
  bound as a dimension.
* **The level-1 witness with rounding.** `Blas.exists_isBlas1` is by exact arithmetic.
* Not restated as certificates: `srsum`, `halve`, `sq2`, `add3`, `scale`.
* `scal` still divides (review item 12), `ROp` still duplicates the catalog (item 13), the
  layout is not yet that of the organisation note (item 14).

## Deviations and open points

* **Trusted base, changed in this step**: `whileFuel` has a new meaning (round index, no failure
  at the cap, continuation); `Contract` is a structure that is given a window and not the tape;
  `BlockRel.spec` is the one contract form (its postcondition also says that there was room for
  the outputs, so that a liberal certificate of a functional operation is the equation `apply`);
  `IsIndex` is `Option`-valued; `StdModel.div`, `StdModel.lit`. Added templates: `RunsW`,
  `Table.AccountsW`.
* An output block is a list of words, so a program that writes only part of a block (`cgs`
  and the upper triangle of `R`) takes the block as an input too, readable, and its contract
  says nothing of the part it does not write.
* An operand that is updated in place appears twice in the frame of an implementation, once as
  input and once as output (`mgs`: `[Q, w, w, R]`), as for `axpy`.
* The window lemma needs an implementation without tests (`Stmt.Straight`).
* Draws are exact: the hypothesis on the law is on the decoded stream.
* A recursive program is a tree per depth (`Table.iter T k`).
* A block of length zero is readable at a dangling offset, so room for an output is a separate
  hypothesis of a contract (`Mem.Room`).

## For the logic layer

What a run proof still does by hand, in the order of the lines it costs in the test cases:

1. **Frames**: the `EqOff` of a chain of updates (`((hfr.mono …).upd (Or.inl (Or.inr ⟨rfl, by
   omega, by omega⟩)) _).updBlock …`), and footprint membership. Build on `Store.EqOff`,
   `EqOff.peel`, `eq_updBlock₂`, `EqOff.pop`.
2. **Scratch**: the lengths of the pushed buffers after `wp_alloc` and the frame after the
   pops (`hlen`, `hlR`, `hlt`, `hlw` in every proof).
3. **Index facts**: `i * n + n ≤ k * n`, `(i * p + j) / p = i`, positions of the tape.
4. **Certificates**: the destructuring of dimensions and operands in `Impl.meets_rel` (four to
   six lines each) is the same every time; a builder per shape, or a tactic.
5. **Named states**: a checkpoint that generalises the current store with its facts.
6. **A program notation with named variables**: the trees are positional, and an operand that
   is updated in place shifts the positions.
7. **Counts**: `RunsFromW` has the rules; it has no tactic and no partial-correctness form.

What to build on: `BlockRel` and `BlockRel.spec` for every contract; `wp_call_rel` (the other
call rules are corollaries, and the tactic uses only the rules for one cell, one block, two
blocks and the general one); `Impl.Meets` for every statement about a program; `RunsFromW` for
counts; `storeNF` and `admNF` for what the tactics unfold. The tactic is a macro over
`store_simp` and `store_side`: an index tactic or a footprint tactic plugged into `store_side`
is used by `wp_call` at once.
