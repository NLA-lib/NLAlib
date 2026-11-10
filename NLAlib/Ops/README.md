# `NLAlib/Ops`: the new core of the model of computation

Status: third build (randomness), 2026-11-10, branch `feat/ops-core`. Self-contained: every file imports only
Mathlib and other files of this directory. Nothing of `NLAlib/Computation` is used. Design:
`docs/design/Computation-Operations.md` (revision 3) on branch `design/operations-redesign`;
layout and profiles after `docs/design/Library-Organization.md` (branch
`design/library-organization`, approved). No registry, no targets, no ports yet.

## The pieces

| File | Content |
|---|---|
| `Store.lean` | Stack of buffers of possibly uninitialised cells; total updates `upd`, `updBlock` and guarded writes; `Mem` = store and tape position; `Mem.Live` |
| `Syntax.lean` | `IExp` (sum, product, truncated difference, quotient), `Operand`, `Env`, and `Stmt Op Tst`: `skip`, `abort`, `seq`, `call`, `ite`, `whileFuel`, `bindIdx`, `alloc`, `loop`, `frame`; `Stmt.ifZero`, `Stmt.ifPos` (branches on a size). Calls take operation names `Op`; tests and index uses take query names `Tst` |
| `Exec.lean` | `Interp` (call, test, index); `run` and `exec` (counts per operation or query and dimensions, live and peak scratch cells). A call or a frame whose operand handle is not a buffer of the store fails |
| `Static.lean` | `staticCost`, `staticPeak`, soundness `exec_within`; `Runs`, `RunsL`; `Runs.of_run` |
| `Contract.lean`, `Blocks.lean` | `Mode`, `Contract`, `Interp.Meets`, `Meets.mono`; functional contracts `BlockFn`, `Interp.IsFn` with the shapes `const`, `un`, `bin`, `tern`, `draw`, `of1`, `of2`, `of3`; relational contracts in operand form `BlockRel`, `BlockRel.spec` |
| `Link.lean` | `Impl`, `Table`, `Stmt.link`, `Interp.link`, `run_link`; `Table.comp`, `Table.iter`, `Stmt.link_comp`, `Interp.link_comp` |
| `Transfer.lean` | `Count.push`, `Count.weight`, `Table.Accounts`, `accounts_of_static`, `exec_link`, `Runs.link`, `link_total`, `RunsL.link`, `link_liberal`, `exec_link_weight`, `fail_subset` |
| `Stream.lean` | `Tape K`: at each position one entry of each stream; stream names; `Tape.window` |
| `Tape.lean` | `Interp.TapeLocal`, the window lemma `Interp.TapeLocal.link`; `Interp.TapeLocal.link_zero` (linking preserves tape independence, for every implementation) |
| `TapeLaw.lean` | No program. `IsTapeLaw law P ξ` (independent entries, one law per stream), the filtration `Tape.past`, `indepFun_of_measurable`, `map_windowFn`, the conditional law of a window given the past (`integral_future`, `integrable_future`, `condExp_future`, `integral_window`, `integral_entry`), `condLaw`, `integral_hidden`, `exists_isTapeLaw` |
| `Window.lean` | `WinRel`: relational contracts with a tape window (visible draws `drawRel`, hidden randomness); `wp_call_win` (hands over reduced shapes), `Impl.MeetsWin`, `Interp.link_meets_win`; the fill-loop rule `wp_loop_fill` |
| `Law.lean` | `RunsLaw` (the shape of a law-level theorem), `Profile.Certifies.runsLaw`, `measureReal_not_runs_le`, `measureReal_not_runs_le_of`, `runVal`, `integral_runVal` |
| `Logic.lean`, `Rules.lean` | `Wp`, one rule per constructor; calls on given operands (`wp_call_rel`, `wp_call_rel_cell`, `wp_call_fn_read`); `wp_whileFuel` (total, bound on the rounds from the mathematics), `wp_whileFuel_liberal`; `wp_ifZero`, `wp_ifPos`; grounding (`Interp.link_meets`, `Interp.link_isFn`, `Impl.MeetsRel`, `Interp.link_meets_rel`) |
| `Frame.lean`, `StoreSimp.lean`, `Attr.lean` | Reads through updates and scratch buffers; footprints and the frame of a run (`Store.EqOff`); the tactics `store_simp` and `store_side` |
| `Counted.lean` | `RunsFrom`: counts in the logic, used only where they depend on the data (`RunsFrom.whileFuel`) |
| `Profile.lean` | Groups of operations (`Has`, `Apart`); `Profile` (with tape windows `win`, `winLo`), `Profile.Certifies` (with `tapeLocal`), `tapeLocal_noDraw`, `Certifies.runs`, `Profile.over`, `Profile.iter` |
| `Catalog/Scalar.lean`, `Catalog/Blas1.lean` | The groups `ScalarOp` (functional contract `IsScalar`, standard model `StdModel u`, `u` a parameter, unbounded exponent) and `Blas1Op` (`sum`, `dot`, `axpy`, `nrm2`, `scal`, `copy`; error predicates, parameter record `Blas1Err`, contract set `IsBlas1`) |
| `Blas/Sum.lean`, `Blas/Dot.lean`, `Blas/Level1.lean` | Implementations with their mathematics and certificates: `sumSeq`, `sumPairwise` (recursive), `dotSum`, `nrm2Sum`, `axpyLoop`, `scalLoop`, `copyLoop` |
| `Catalog/Isotropic.lean`, `Catalog/Random.lean` | Mathematics of probes (`IsStdLaw`, `IsIsotropic`, their moments, `probeLaw`); the group `ROp` (scalar and vector Gaussian draw, `matvec`, exact `dot`, `add`, `nrm2`, `mulc q`, `axpy`), contract sets `IsRandBase`, `IsRandLin`, windows `randWindow` |
| `Profiles/Random.lean` | `Rand.gaussLoop`: the vector draw by scalar draws, with its certificate |
| `Profiles/Blas.lean`, `Profiles/BlasCert.lean` | `Blas.seq`, `Blas.pairwise k`: tables, costs, workspaces, constants, certificates, costs of `dot`, witness `Blas.exists_isBlas1` |

## What changed since the first build

1. **Operand handles** (design suggestion 1): the evaluator rejects a call or a frame whose
   operand is not a buffer of the store, so a dangling handle cannot alias the scratch of an
   implementation and liberal contracts assume nothing about handles.
2. **Counts** (suggestion 2): `Wp` carries no counts; the static cost gives them. `RunsFrom`
   carries them through a `whileFuel` loop, where the static cost (the fuel) is only a bound.
3. **Queries** (suggestion 3): tests and index uses have names of their own type `Tst`, which no
   table maps. An implemented operation cannot be used as a test, by typing; linking never
   produces `abort` for a test. A test that should be implemented is a call that writes a flag
   cell followed by a primitive test of that cell (not built).
4. **Loops**: `wp_loop` (counted, both modes), `wp_whileFuel` (invariant on the memory indexed by
   rounds, bound `J` on the rounds from the mathematics, fuel `≥ J`), `wp_whileFuel_liberal`,
   `RunsFrom.whileFuel` (counts `J` bodies and `J + 1` tests), sizes with difference and
   quotient, branches on a size.
5. **Recursion**, by iterated linking, with no addition to the trusted base. A recursive
   implementation is a tree that calls the operation it implements (`sumPairwise` calls `sum`
   on the two halves). The program is the algorithm linked through `Table.iter T k`, the
   `k`-fold composition of the table with itself; `k` bounds the depth and is a size. The
   contract is indexed by the lengths it covers (`ok n := ⌈log₂ n⌉ < k`), one level is one
   certificate (`Blas.sumPairwise_certifies : Certifies (C k) (C (k + 1))`), and
   `Profile.Certifies.iter` gives correctness and cost transfer for every `k` by induction,
   whatever `sum` means below. The cost is the `k`-fold push-forward, evaluated in closed form
   (`Blas.sumPairwise_iter_cost_sum`). The transfer theorems are the ones of the first build.
6. **Profiles**: a table with costs and workspaces and one certificate; any (algorithm, profile)
   corollary is one application of `Profile.Certifies.runs`.
7. **Program-logic infrastructure**: see the next section.

## Randomness (third build)

**The tape.** `Tape K = ℕ → ℕ → K`: the entry at a position and a stream. The memory has one
position; an operation with window `k` reads `k` positions (in the stream its contract names)
and advances by `k`. The law is a clause of the access model: `IsTapeLaw law P ξ` says the
entries of the random tape `ξ : Ω → Tape K` are independent and those of the stream `s` have the
law `law s` (a measure on words; `Examples.stdLaw` has the uniform law on `[0, 1]` and the
standard Gaussian for real words). The interpretation is fixed before the sample.

**Two kinds of randomness** (maintainer's rules R1–R4, 2026-11-10).

* *Visible* (R1a, R4): the algorithm calls a draw (`gauss [n] [] [g]`, contract `drawRel`: the
  output block is the window) and the values are in its store. `Examples.hutch`.
* *Hidden* (R1b, R3): the operation has no random operand (`nmv [n] [x] [y]`,
  `srAdd [x, y] [z]`). Its contract is a `WinRel` (or a block function with a window): the
  output is a function of the operands and of the window at the position, which the call
  consumes. The signature of the algorithm has no draw, so its tree cannot contain one, and no
  cell of the algorithm ever holds the window. The implementation draws into scratch that it
  allocates and that the evaluator frees; its certificate (`Impl.MeetsWin`) says the final
  memory is the initial one with the output block written and the position advanced. The
  primitive that is given its random word (`sraddXi [x, y, ξ] [z]`) is an operation of the lower
  signature only.
* *Conditional contracts* (R2). The contract holds at every memory, hence for inputs that are
  any function of the history. With the law of the tape, the window of a call at the position
  `p` is independent of `Tape.past ξ p`, the σ-algebra of all entries below `p` (it contains
  everything the algorithm has seen, and the hidden noise of earlier calls), and has the product
  law: `IsTapeLaw.integral_hidden` is "given the history, the output has the law
  `condLaw μ N x`", `condExp_future` the same as a conditional expectation. The mathematical
  half of a contract is a statement about `condLaw` (`IsNoisyMv`: the law of `A v + σ ‖v‖ g`;
  `SrModel`: unbiased and within `2 u`).
* *Nobody else reads the window*: `Interp.TapeLocal` with the registered windows, a clause of
  the access model for the bottom operations and a field of every profile certificate
  (`Certifies.tapeLocal`; by the window lemma for an implementation that draws, by
  `TapeLocal.link_zero` for one that does not).

**The shape of a law-level theorem**: `RunsLaw J W ξ s ρ m B M Q Φ`: for every sample the run
succeeds within the counts `B` and the workspace `M` with an output `X ω` (`Q (X ω)` of the
final memory), and `Φ X` (an expectation, a variance, a tail). The corollary for a linked
program is one application of `Profile.Certifies.runsLaw`.

## How a block is proved (playbook, short)

* Handles are an injective family `H : ι → ℕ` with `hH : Function.Injective H` and
  `hl : ∀ i, H i < s.length`; a scratch handle is `s.length`.
* A call: `wp_call_rel hJ.dot rfl rfl rfl rfl ⟨hok, by simp [hH.eq_iff]⟩ ?_ (xs := […]) ?_ ?_
  fun ys hlen hrel => ?_`; the three goals (handles in the store, the blocks read, room for the
  output) are closed by `store_simp`. Scalar calls: `wp_call_un`, `wp_call_bin`.
* The state after a call is the state before with one more update; nothing is renormalised.
  `store_simp [facts]` pushes reads through the updates.
* A loop invariant says what the written blocks hold and that the rest is untouched:
  `S.EqOff F s'`. A write keeps it by `EqOff.upd` / `EqOff.updBlock`, a fact about the initial
  store is kept by `hfr.readBlock_of fact (by store_side [hH.eq_iff])`, and at the end
  `EqOff.eq_updBlock` gives the equation of a contract or `EqOff.pop` frees a scratch buffer.
* Write offsets as `base + index` in the tree, so that they meet the lemmas as they are.
* Counts: `Runs.of_run` and `simp` on `staticCost`.
* A call with a window: `wp_call_win hJ (k := n) (l := n) rfl rfl rfl rfl rfl rfl ⟨adm⟩ ?_
  (xs := […]) ?_ ?_ fun ys hlen hrel => ?_`; the state after it is
  `(m.updBlock z ys).advance n`. After a visible draw, `obtain rfl : ys = τ.window s p n := hrel`.
* A loop that fills a block: `wp_loop_fill v pos rfl (fun i hi s' hfr hr => one call) hlen
  fun s' hfr hr => ?_`.
* A law-level theorem: (1) the run for every tape, with the result written as an explicit
  function `F τ` of the tape entries (program logic); (2) measurability of `ω ↦ F (ξ ω)` with
  respect to `Tape.past ξ (p + …)` by induction on the steps; (3) one step by
  `IsTapeLaw.integral_hidden` / `integral_entry` / `integral_window` and the conditional law of
  the contract (mathematics); (4) `RunsLaw` is the pair.

## Test cases (`Examples/`)

| File | What | Abstract theorem | Corollaries |
|---|---|---|---|
| `Gemm` | `C = A B`, `m p` calls of `dot` (`A` by rows, `B` by columns) | `runs_gemm_rounded`: `|ĉ_ij - Σ a_ik b_kj| ≤ ε.dot n · Σ |a_ik| |b_kj|` | `runs_gemm_link_seq` (`ε = (1+u)^n - 1`), `runs_gemm_link_pairwise` (`(1+u)^(⌈log₂ n⌉+1) - 1`), counts `push_seq_gemmCount`, `push_pairwise_gemmCount` |
| `CgsMath`, `Cgs`, `CgsQR`, `CgsLinked` | classical Gram–Schmidt of an `n × p` matrix | `runs_cgs_rounded`: every column satisfies `CgsCol` (local errors); `CgsRounded.backward`: `|a_j - Σ_{i≤j} r̂_ij q̂_i| ≤ ((1+ε_scal)(1+ε_axpy)^j - 1)(|a_j| + Σ_{i<j} |r̂_ij||q̂_i|)` entrywise when `r̂_jj ≠ 0` | `runs_cgs_link_seq`, `runs_cgs_link_pairwise`, `CgsRounded.backward_std` (constant `(1+u)^(2j+1) - 1`), `push_seq_cgsColCount` |
| `GramSchmidt` | modified Gram–Schmidt (the example of the first build, proved again) | `runs_mgs_rounded` | `runs_mgs_link_seq`, `push_seq_mgsCount` |
| `Loops` | halving while not zero; a hundred buffers | `wp_halve`, `runs_halve` (counts `Nat.size v`), `wpL_halve` | `read_of_hundred` |
| `NoisyMath`, `Noisy`, `NoisyLinked` | hidden randomness: `nmv [n] [x] [y]` with the conditional law of `A v + σ ‖v‖ g`; the noisy power iteration, `2 k` products | `runsLaw_npow`: `2 k` calls, workspace of one; `𝔼 x = A^(2k) x₀` and `𝔼 ‖x‖² ≤ (a + n σ²)^(2k) ‖x₀‖²` (each step: mean zero and variance `σ² ‖v_j‖² n` given the history) | `nmvImpl_spec` (exact product, probe drawn into scratch, `nrm2`, `mulc σ`, `axpy`), `noisy_certifies`, `runsLaw_npow_link` through `noisy` over `Rand.gaussLoop`: `n + 1` scratch cells, counts `push_noisyDraws_npowCount` |
| `Hutch`, `HutchLinked` | visible randomness: the Girard–Hutchinson estimator, `N` probes drawn by the algorithm into its scratch | `runsLaw_hutch`: `N` calls of each operation, `2 n + 1` scratch cells; `𝔼 est / N = tr A`, `Var (est / N) = Var (gᵀ A g) / N` (independent probes) | `runsLaw_hutch_link` (probes by scalar draws), `push_gaussLoop_hutchCount` |
| `StochRound` | hidden randomness: `srAdd [x, y] [z]`; `sraddXi` only inside the implementation; the stochastically rounded sum | `runsLaw_srsum`: `n` calls, sure bound `(1 + 2u)^n - 1` for every sample, and `𝔼 ŝ = s` | `sr_certifies`, `runsLaw_srsum_link`: `n` draws, `n` `sraddXi`, one scratch cell |
| `RandomWitness` | witnesses: `stdLaw`, `exists_isTapeLaw_stdLaw`, `exists_isRandLin`, `memLp_quadForm_gaussian`, `sqNorm_mulVec_le` | | |
| `Dot`, `MatMul`, `Liberal`, `Bits`, `Control` | first build: exact certificates, liberal mode, bit level | unchanged in content | |

Not proved for classical Gram–Schmidt: a bound on `|Q̂||R̂|` by the columns of `A`, and the loss
of orthogonality in terms of `κ(A) u`. `CgsCol` records the accuracy of the coefficients and of
the norm that they need.

Witnesses: `exists_isScalar` (exact arithmetic meets the standard model for every `u ≥ 0`),
`Blas.exists_isBlas1`, `exists_isHalving`, those of the first build, and for the randomized
examples `exists_isTapeLaw`, `exists_isRandLin` (exact real arithmetic, tape-local at the
registered windows), `isNoisyMv_noiseFn` with `isStdLaw_stdLaw_gauss`, `exists_isSrLo` (for
every law of the uniform stream), `memLp_quadForm_gaussian`.

Not in the programs: the division of the Hutchinson sum by `N` (a constant of a tree is a
rational and `N` is a size; the statement divides). Not proved: `Var (gᵀ A g) = 2 ‖A‖_F²` for
Gaussian probes and symmetric `A`; a tail bound.

## Measurements (2026-11-10)

Elaboration, `lake env lean <file>`, two threads, Mathlib import included, seconds: every file
under 5.2; core files 1.1 to 3.3; `Blas/*` 2.6 to 3.6; `Profiles/*` 2.9 to 3.6; `Gemm` 2.8,
`CgsMath` 3.4, `Cgs` 5.1, `CgsQR` 3.8, `CgsLinked` 2.4, `GramSchmidt` 4.0, `Loops` 2.2.

Third build: `Stream` 1.4, `Tape` 2.3, `TapeLaw` 2.8, `Window` 1.8, `Law` 2.3, `Profile` 1.7,
`Catalog/Isotropic` 2.8, `Catalog/Random` 2.2, `Profiles/Random` 2.5, `StochRound` 4.8,
`Hutch` 5.5, `HutchLinked` 3.6, `NoisyMath` 3.0, `Noisy` 3.8, `NoisyLinked` 7.6,
`RandomWitness` 3.7.

Lines, statements and docstrings included:

| | Mathematics | Program logic | Linking |
|---|---|---|---|
| Level-1 implementations (seven, once) | 146 | 475 | |
| Profiles `Blas.seq`, `Blas.pairwise` (once) | | | 350 |
| `gemm` | 15 | 105 | 51 |
| classical Gram–Schmidt | 177 | 400 | 45 |
| modified Gram–Schmidt | 12 | 160 | 27 |
| law of the tape, windows, law-level transfer (once) | 310 (`TapeLaw`) | 150 (`Window`) | 110 (`Law`), 60 (`Tape`, `Profile`) |
| probes: `Catalog/Isotropic`, `Catalog/Random`, `Rand.gaussLoop` (once) | 195 | 130 | 80 |
| noisy product and power iteration | 200 | 205 (algorithm 120, implementation 85) | 85 |
| Girard–Hutchinson | 90 | 120 | 60 |
| stochastically rounded sum | 100 | 125 | 75 |

Modified Gram–Schmidt, program logic of the algorithm (store description, step, run): 192 lines
in the first build, 109 now, with no lemma about a named store and no hand-written store
rewriting.

Checks on these modules: `lake build --wfail` clean; no `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`; the rules check leaves E6 and P1 (keyed to the old core and
the layer table) and P2 for `Attr.lean` (a simp attribute has to be registered in its own
file).

## Deviations and open points

Third build:

* **Trusted base, added**: the tape has streams (`Tape K`, an argument of the evaluator);
  `BlockFn.stream`, `BlockFn.drawVec`; the templates `IsTapeLaw` and `RunsLaw`; the contract
  form `WinRel.spec`; the registered windows (`randWindow`, `srWindow`).
* The design note has one position per distribution; here all streams share one position (a
  position holds an entry of every stream). The law is the same product, locality needs one
  number, and nothing else changes.
* A hidden-randomness contract is *functional in the window*: the decoded output is a function
  `N` of the decoded input and the window (`WinRel` with such a relation), or the output word
  is a function of the operand words and the window (`drawBin`). The form "any output with this
  law, at every memory" is not built: it needs measurability across memories.
* `R1b`/`R3` hold by typing in the examples (the algorithm's signature has no draw and no
  `sraddXi`). In a library with one composed signature they need a registry rule: a primitive
  that takes a random operand may occur only in implementation trees. `R4` is a convention.
* The window lemma needs an implementation without tests (`Stmt.Straight`); a rejection sampler
  needs a version with a bound.
* Draws are exact: the hypothesis on the law is on the decoded stream
  (`IsStdLaw ((law gauss).map dec)`). Rounded draws are another law, not studied.
* `Profile.Certifies.of_accounts` takes the tape clause; `Certifies.over` and `iter` need the
  windows to match (`P.winLo = Q.win`).

* `Profile.Certifies` has the field `transfer` (a run under the linked interpretation is a run
  of the linked program) where the organisation note has `accounts`. `Certifies.of_accounts`
  gives it from the accounting certificate; stated this way certificates compose (`over`,
  `iter`) without a lemma that shifts a counted run. `Profile.par` is not built: profiles of a
  signature over itself that keep each other's operations are stacked with `over`.
* Groups are joined by a class `Has G Op` with a partial inverse; tables are written for any
  `Op` with the groups they use. Definitions need `(Op := Op) (Tst := Tst)` in statements.
* A recursive program is a tree per depth (`Table.iter T k`), of size `2 ^ k` for pairwise
  summation; the depth is a Lean-level size.
* `dot` has no strides, so `gemm` takes `A` by rows and `B` by columns.
* Admitted operands are told apart by buffer, not by block. An in-place update of a column by
  another column of the same matrix buffer is not admitted; `cgs` uses a work vector and two
  copies. The catalog needs block-level disjointness.
* No precision tags; one tape stream; `nrm2` keeps the two-stage error form.
* A block of length zero is readable at a dangling offset, so room for an output is a separate
  hypothesis (`hwl` in `mgs`).

## Found while proving the test cases (missing infrastructure)

Third build (the first item of the list below is now `wp_loop_fill`, used by `gaussLoopImpl`;
the six older loops are not rewritten; `wp_call_win` hands over reduced shapes, `wp_call_rel`
still does not):

* Scratch buffers of an algorithm or an implementation: the lengths of the pushed buffers
  (`hlg`, `hly`, `hlt`, `hle` in `wp_hutch`, `nmvImpl_spec`) and the frame after the pops (an
  `EqOff` chain written by hand, ten lines in `nmvImpl_spec`) are derived by hand. Missing: an
  `alloc` rule that hands over the lengths and a "frame of a chain of updates" automation.
* Positions `p + (2 i + 1) n = p + 2 i n + n` by `ring`, and the invariant carries the position
  as an existential with an equation. Missing: the index tactic, also for positions.
* The bridge between blocks and vectors (`decv`, `vec_window`, `Fin n` against `range n`) is
  written per example. Missing: a small library of decoded blocks.
* Witnesses of relational contracts by functions: `Interp.IsFn.meets_rel` is new; each operation
  still destructures its blocks by hand.
* Measurability with respect to a σ-algebra that is not the instance (`Measurable[Tape.past ξ p]`)
  works with `.comp`, `.prodMk`, `.mono`; `fun_prop` is not usable there.

* The loop that fills a block cell by cell (frame, prefix read, `readBlock_upd_concat`) is
  written six times. Missing: one rule `wp_loop_fill`.
* Index facts `i * n + n ≤ m * n` are derived by hand (`Nat.mul_le_mul_right`, `Nat.succ_mul`)
  about ten times; `omega` does not see them. Missing: an index tactic.
* The output length given by `wp_call_rel` is `R.outLen d`, not reduced
  (`replace hzl : zs.length = n := hzl`). The rule should hand over reduced shapes.
* Each certificate of an implementation destructures its dimensions and operands by hand (six
  lines). Missing: `MeetsRel` builders for the common shapes.
