# `NLAlib/Ops`: the new core of the model of computation

Status: second build, 2026-11-10, branch `feat/ops-core`. Self-contained: every file imports only
Mathlib and other files of this directory. Nothing of `NLAlib/Computation` is used. Design:
`docs/design/Computation-Operations.md` (revision 3) on branch `design/operations-redesign`;
layout and profiles after `docs/design/Library-Organization.md` (branch
`design/library-organization`, not yet approved). No registry, no targets, no ports yet.

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
| `Tape.lean` | `Interp.TapeLocal`, the window lemma `Interp.TapeLocal.link` |
| `Logic.lean`, `Rules.lean` | `Wp`, one rule per constructor; calls on given operands (`wp_call_rel`, `wp_call_rel_cell`, `wp_call_fn_read`); `wp_whileFuel` (total, bound on the rounds from the mathematics), `wp_whileFuel_liberal`; `wp_ifZero`, `wp_ifPos`; grounding (`Interp.link_meets`, `Interp.link_isFn`, `Impl.MeetsRel`, `Interp.link_meets_rel`) |
| `Frame.lean`, `StoreSimp.lean`, `Attr.lean` | Reads through updates and scratch buffers; footprints and the frame of a run (`Store.EqOff`); the tactics `store_simp` and `store_side` |
| `Counted.lean` | `RunsFrom`: counts in the logic, used only where they depend on the data (`RunsFrom.whileFuel`) |
| `Profile.lean` | Groups of operations (`Has`, `Apart`); `Profile`, `Profile.Certifies`, `Certifies.runs`, `Profile.over`, `Profile.iter` |
| `Catalog/Scalar.lean`, `Catalog/Blas1.lean` | The groups `ScalarOp` (functional contract `IsScalar`, standard model `StdModel u`, `u` a parameter, unbounded exponent) and `Blas1Op` (`sum`, `dot`, `axpy`, `nrm2`, `scal`, `copy`; error predicates, parameter record `Blas1Err`, contract set `IsBlas1`) |
| `Blas/Sum.lean`, `Blas/Dot.lean`, `Blas/Level1.lean` | Implementations with their mathematics and certificates: `sumSeq`, `sumPairwise` (recursive), `dotSum`, `nrm2Sum`, `axpyLoop`, `scalLoop`, `copyLoop` |
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

## Test cases (`Examples/`)

| File | What | Abstract theorem | Corollaries |
|---|---|---|---|
| `Gemm` | `C = A B`, `m p` calls of `dot` (`A` by rows, `B` by columns) | `runs_gemm_rounded`: `|ĉ_ij - Σ a_ik b_kj| ≤ ε.dot n · Σ |a_ik| |b_kj|` | `runs_gemm_link_seq` (`ε = (1+u)^n - 1`), `runs_gemm_link_pairwise` (`(1+u)^(⌈log₂ n⌉+1) - 1`), counts `push_seq_gemmCount`, `push_pairwise_gemmCount` |
| `CgsMath`, `Cgs`, `CgsQR`, `CgsLinked` | classical Gram–Schmidt of an `n × p` matrix | `runs_cgs_rounded`: every column satisfies `CgsCol` (local errors); `CgsRounded.backward`: `|a_j - Σ_{i≤j} r̂_ij q̂_i| ≤ ((1+ε_scal)(1+ε_axpy)^j - 1)(|a_j| + Σ_{i<j} |r̂_ij||q̂_i|)` entrywise when `r̂_jj ≠ 0` | `runs_cgs_link_seq`, `runs_cgs_link_pairwise`, `CgsRounded.backward_std` (constant `(1+u)^(2j+1) - 1`), `push_seq_cgsColCount` |
| `GramSchmidt` | modified Gram–Schmidt (the example of the first build, proved again) | `runs_mgs_rounded` | `runs_mgs_link_seq`, `push_seq_mgsCount` |
| `Loops` | halving while not zero; a hundred buffers | `wp_halve`, `runs_halve` (counts `Nat.size v`), `wpL_halve` | `read_of_hundred` |
| `Dot`, `MatMul`, `StochRound`, `Liberal`, `Bits`, `Control` | first build: exact certificates, stochastic rounding, liberal mode, bit level | unchanged in content | |

Not proved for classical Gram–Schmidt: a bound on `|Q̂||R̂|` by the columns of `A`, and the loss
of orthogonality in terms of `κ(A) u`. `CgsCol` records the accuracy of the coefficients and of
the norm that they need.

Witnesses: `exists_isScalar` (exact arithmetic meets the standard model for every `u ≥ 0`),
`Blas.exists_isBlas1`, `exists_isHalving`, and those of the first build.

## Measurements (2026-11-10)

Elaboration, `lake env lean <file>`, two threads, Mathlib import included, seconds: every file
under 5.2; core files 1.1 to 3.3; `Blas/*` 2.6 to 3.6; `Profiles/*` 2.9 to 3.6; `Gemm` 2.8,
`CgsMath` 3.4, `Cgs` 5.1, `CgsQR` 3.8, `CgsLinked` 2.4, `GramSchmidt` 4.0, `Loops` 2.2.

Lines, statements and docstrings included:

| | Mathematics | Program logic | Linking |
|---|---|---|---|
| Level-1 implementations (seven, once) | 146 | 475 | |
| Profiles `Blas.seq`, `Blas.pairwise` (once) | | | 350 |
| `gemm` | 15 | 105 | 51 |
| classical Gram–Schmidt | 177 | 400 | 45 |
| modified Gram–Schmidt | 12 | 160 | 27 |

Modified Gram–Schmidt, program logic of the algorithm (store description, step, run): 192 lines
in the first build, 109 now, with no lemma about a named store and no hand-written store
rewriting.

Checks on these modules: `lake build --wfail` clean; no `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`; the rules check leaves E6 and P1 (keyed to the old core and
the layer table) and P2 for `Attr.lean` (a simp attribute has to be registered in its own
file).

## Deviations and open points

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

* The loop that fills a block cell by cell (frame, prefix read, `readBlock_upd_concat`) is
  written six times. Missing: one rule `wp_loop_fill`.
* Index facts `i * n + n ≤ m * n` are derived by hand (`Nat.mul_le_mul_right`, `Nat.succ_mul`)
  about ten times; `omega` does not see them. Missing: an index tactic.
* The output length given by `wp_call_rel` is `R.outLen d`, not reduced
  (`replace hzl : zs.length = n := hzl`). The rule should hand over reduced shapes.
* Each certificate of an implementation destructures its dimensions and operands by hand (six
  lines). Missing: `MeetsRel` builders for the common shapes.
