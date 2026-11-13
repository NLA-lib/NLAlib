# Programs

Part of the [contributor guide](../../CONTRIBUTING.md).

Algorithms analysed for their cost are programs over memory buffers (`NLAlib/Computation`,
`docs/design/Computation.md`). A program `<spec>Prog` is written with the builder in its topic
file, next to its specification, and compiled once, at symbolic sizes, into one first-order tree
for all sizes, `<spec>Prog.compiled : Computation.Prog P ι r b` (a registered tree).

A program reaches its matrix only through oracles, and may call black-box kernels
(`Computation.Stmt.kcall`, `docs/design/Computation-DynamicPrograms.md`). A finite-precision
result about a program assumes contracts of what it calls: of the arithmetic
(`Computation.IsRelErrSem`), of an oracle (`Computation.IsMatvecErr`), of a kernel
(`Computation.IsMatMulErr`, `Computation.IsQRErr`). A routine used inside a larger one is
certified once, by a theorem concluding its certificate (`Computation.IsMatvecRoutine`,
`Computation.IsOrthRoutine`, `Computation.ImplementsKernel`), and the larger analysis takes the
certificate as a hypothesis.
A program proof states a `Computation.RoutineSpec` per block, mode-generic (the total mode gives
success, the liberal mode refinement), proves it by the call rule (`Computation.RoutineSpec.wp_bind`) and the rules of `NLAlib/Computation/RoutineSpec.lean`, one
named state per step, and derives the block's success and refinement lemmas from it
(`Computation.Triple.exists_exec`, `Computation.Triple.holds_of_exec`); a certificate enters
through its bridge (`Computation.IsMatvecRoutine.routineSpec`).

Results may be proved autonomously, so the statement of a published cost result is the
library's, not the prover's: it is a **target**.

- A target is a library definition of type `Prop`, written and reviewed by the library, in a
  file of its own, `<Topic>/<Spec>Targets.lean`, and registered in `docs/targets.toml`. It states
  an access model about a registered tree: `Computation.MatrixFree`, `Computation.MatrixFreeProb`
  or `Computation.StoredEntries`, which bind the program before the sizes and quantify over the
  matrix, the tape and the declared inputs afterwards, so the counts and the memory are functions
  of the sizes by the statement itself. Its name is the model, then the specification
  (`MatrixFreeHutchpp`).
- A result is `theorem matrixFreeHutchpp : MatrixFreeHutchpp`: its type is the target constant,
  with no hypothesis, parameter or postcondition of the prover's, and each registered target has
  exactly one such proof. A `Result:` theorem whose statement reaches a run or a budget proves a
  registered target; a lemma about a program family is proof infrastructure and has no result id
  [E3]. The exception is a **rounded program theorem** (approved by the maintainer 2026-11-07): a
  theorem about runs under every interpretation satisfying the standard model. Its conclusion
  may assert a rounded access model (`Computation.MatrixFreeRounded` or
  `Computation.MatrixFreeRoundedProb`). It may also assert an execution or budget under a bound
  interpretation `I` with a leading hypothesis `Computation.IsRelErrSem … I.sem`. The checker
  inspects the interpretation supplied to each execution clause, including clauses grouped with
  numerical postconditions. A separate exact execution in the same conclusion requires the
  ordinary target review [E3]. Qualifying theorems may carry a result id for the explorer.
- The registry records each target's closure hash (every library constant its statement reaches,
  proofs erased and hygienic names numbered, the registered trees as leaves hashed by their
  constructor normal forms, which the kernel checks are the trees), its printed statement, each
  tree's printed normal form, the toolchain, the Mathlib revision and the SHA-256 of
  `lake-manifest.json` and `lakefile.toml`; `docs/targets.approved` holds the registry's SHA-256. A
  change of a target, of a definition it unfolds to, or of a tree changes a hash and needs a
  maintainer's approval: they review the diff that `TARGETS_UPDATE=1 lake env lean
  scripts/Targets.lean` writes and approve it with `sha256sum docs/targets.toml >
  docs/targets.approved`. A declared input computed from the sizes carries the registry flag
  `precomputed` and a `Precomputed:` docstring sentence [E3].
- Every `<spec>Prog` has a registered tree, named by a registered target, whose definition calls
  it [E4]. This is completeness, not soundness. So a new program lands in `NLAlib` together with
  its registered target, and only a maintainer registers targets: a PR that needs one proposes the
  target statement in its description. `docs/targets.toml` is the list of current targets.
- What the models prove and what they trust is listed in `docs/design/Computation.md`,
  "Guarantees: what is proved and what is trusted". A reader of a target
  still reads its size condition, its declared inputs, its postcondition and its bound: the model
  guarantees that the program meets exactly that statement, not that the statement is the
  interesting one.

The other rules are hygiene: the guarantees do not rest on them.

**Finite formats and successful executions.** Pure relative arithmetic with every exact
result in range is an idealized assumption, not a binary64 certificate. Underflow needs an
absolute error term, and overflow needs an input-range invariant. The scalar success predicate
does not restrict the error clause: it constrains every successful arithmetic operation.
The global matvec contract has a separate range problem: it requires success on every word
vector. `Computation.IsMatvecErrOn` instead requires success and mixed normwise error only
on a specified decoded input domain. `Computation.IsMatvecErrOn.exec_apply` discharges one
actual stored oracle call once that input-domain condition has been proved.
`Computation.exec_apply_of_finiteFloatDoubleOracle` instantiates this rule with checked
binary64 addition and an input-only range bound. A complete solver additionally needs an
invariant that proves the domain and scalar range conditions at every call.

An error bound for successful runs is distinct from a bound on failure or inaccurate output.
The former can hold when all executions fail. Read the event in a probabilistic headline:
the bounded-format eigensolver program theorem bounds successful-but-inaccurate executions;
its separate shallow binary128-layout witnesses do not prove finite-word program success.
Numerical examples obtained by substituting a format's unit roundoff in a pure-relative
theorem quantify its sufficient precision assumptions, and are not format instantiations.

- Programs, kernels, implementations and compiled trees are computable: not `noncomputable`,
  `partial`, `opaque` or `unsafe`, and they run no code other than their definition (no
  implemented-by attribute) [E2]. It matters for the emitter and the `Float` runner.
- An `alloc` is live for the rest of the enclosing block, so a program that another program calls
  wraps its allocations in `scope` (a kernel is closed by its `named` node) [E9]. An open `alloc`
  is still counted, in the target's `mem`, so the rule is a warning: it keeps the peak the author
  intends.
- Only `NLAlib/Computation` defines a value semantics (`Computation.ScalarSem`) or an
  interpretation (`Computation.Interp`), each with its certificate [E6].
- `Stmt.named`, which the NumPy emitter prints as a call into its prelude, is constructed only in
  the BLAS and implementation files; a theorem may mention it [E8].

A builder need not be generic in its variable sorts: the theorem is about the compiled tree, and
a handle forged from a number does not compile. `scripts/Targets.lean` checks E3 and
`scripts/Programs.lean` checks E2, E4 and E9, each against fixtures of the ways a proof or a
program could cheat (an axiom of a target's type, a vacuous hypothesis, a claim wrapped in a
structure, an edit that must change a hash, a forged handle, a callee with an open `alloc`, …;
each script lists its fixtures). `scripts/AccessModelFixtures.lean` proves that the model forms
of known cheating programs are false. `scripts/check_rules.py` checks E5, E6 and E8. The tools
library `NLAlibTools` ([proofs](proofs.md)) is not part of the library and is not held to its rules.

## Proving a program

A program proof is the mathematical proof replayed one call at a time. Write the mathematics
first, then one routine specification per block, each proved by the skeleton below; reuse the
specifications that exist (the catalog: `SPEC_CATALOG=out.md lake env lean
NLAlibTools/SpecCatalog.lean` lists every theorem concluding a `Computation.RoutineSpec`,
`Computation.Spec` or `Computation.Triple`, with its pre, footprint and post).

**1. The mathematics, as named lemmas.** What the block computes is a function on matrices and
scalars, stated and proved apart from the program: a loop is the iterate of its step
(`NLAlib.newtonSchulzLoop_eq_iterate`), a clamp is a formula (`NLAlib.toNat_eighClamp`), a
nonzero divisor is a lemma on the model (`Computation.IsRelErrSem.dec_ne_zero_of_mul_eq_some`).
The block proof then only moves these values through the store.

**2. The statement.** One theorem per block, for every mode `md`:

```lean
theorem spec_fooBlock (md : Mode) … (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧
      (∀ p x, safe p x) ∧ u p < 1)) (A₀ : Matrix …) (hXY : X ≠ Y) … :
    RoutineSpec md I
      (fun st => pairLayout.Holds st.store p X xo.eval A₀ ∧ st.store.read p c 0 = some z ∧
        md.Needs (dec p z ≠ 0 ∧ Writable st.store p Y 0 (n * n * 2)))   -- pre
      (fooBlock p (.const n) X xo c Y)                                   -- the program
      [matBlock Y 0 n n 2, (t, 0, 5)]                                    -- footprint
      fun st st' => pairLayout.Holds st'.store p Y 0 (fooMath M A₀ z) ∧ PosKept st st'
```

- Footprint: an explicit list of `matBlock b off rows cols 2` blocks and `(b, off, len)` cells,
  never a `List.range` map; a window several blocks share is a named list
  (`NLAlib.eighSplitWindow`). A data-dependent size is a parameter with an equation
  (`(kp) (hkp : kp = …)`).
- Pre: input values, then the success-only facts (writable blocks, nonzero divisors, defined
  literals) under `md.Needs`. A correctness-only fact goes in the post as a guard (`A → Q`) or in
  the pre as `md = .liberal → …`. The range of the standard model is a parameter `safe`.
- Index arguments are index expressions, `(xo : IExp ℕ)`, and the statement uses only their values
  (`xo.eval`), so one spec serves a loop body at `.var k` and a call at `.const k` (the default;
  `Computation.spec_scalarBlock` is of this form). **Never** state a block's spec at `.const k`
  for a body that a loop runs at `.var k`: the unifier then compares the two programs and the
  kernel can time out (25 min lost in the shifted-QR test).
- A comparison whose outcome only the values decide (`ifThenElse` on stored words) takes the
  semantics' comparison as a mode-independent hypothesis, outside `md.Needs`:
  `(hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))`
  (`NLAlib.spec_eighClampBlock`); the outcome is then fixed in every mode and
  `Computation.RoutineSpec.ifThenElse` applies. The standard model gives it
  (the cmp_le clause of `Computation.IsRelErrSem`), so the liberal corollary pays nothing.
- No `let` in the statement; give each declaration its own `omit … in`.
- In the proof, `md.Needs` facts are used without a case split: `hN.mono fun h => …`
  (`Computation.Mode.Needs.mono`), `Computation.Mode.Needs.elim`, `Computation.Mode.needs_and`,
  `Computation.Mode.needs_of` for a fact that always holds.

**3. The proof skeleton.** One step per call, each spec elaborated in its own `have` (machine
arguments by name: `toNat`, `qrR`, `unif`, `normal`, `mmR`, and `pairLayout (K := K)`), then
one `refine` of the call rule naming the next state:

```lean
  refine ⟨by exec_composable, fun st ⟨hX, hc, hc1, hN⟩ => ?_⟩
  have s₁ := spec_zhermShift (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
    (normal := normal) md hs p n (X := X) (Y := T) (xo := xo) (yo := 0) (c := ⟨c, 0⟩) z A₀
    (by fp_omega [hXT])
  refine s₁.wp_bind_keep ((readsOnly_pairLayoutHolds p X xo.eval A₀).and
      (readsOnly_cellsHold [(p, c, 1, some w)])) (by fp_omega [hXT, hcT])  -- kept, disjoint
    ⟨hX, hc, hN.mono (·.1)⟩ ⟨hX, (cellsHold_nil _).cons hc1⟩                -- pre, bundle
    fun st₁ hm₁ h₁ ⟨hX₁, hC₁⟩ => ?_                                        -- next state
  have s₂ := …
  refine s₂.wp_run_keep … fun st₂ hm₂ h₂ hF₂ => ?_                        -- last call
  exact ⟨(hm₁.trans hm₂).of_sub (by simp [matBlock]), h₂.1, h₂.2.trans h₁.2⟩
```

`Computation.RoutineSpec.wp_bind` / `Computation.RoutineSpec.wp_run` are the same without a
bundle. The closing `exact` gives `Modifies` of the block's footprint (by
`Computation.Modifies.of_sub` with the witness blocks explicit), the post, and `PosKept` by
`.trans` along the steps. A scalar instruction is `RoutineSpec.ins (spec_bin_getD …)`
(`Computation.RoutineSpec.ins`, `Computation.spec_lit`, `Computation.spec_bin_getD`,
`Computation.spec_un_getD`, `Computation.spec_litIdx_getD`, `Computation.spec_copy`; the getD
forms need `Inhabited K`, from the model's lit_ok field). A conditional is
`Computation.RoutineSpec.ifThenElse`; an index binder is `Computation.RoutineSpec.bindIdx_of_read`
with `(pre := fun s => s = stᵢ)`, closed by `.wp_run rfl`.

**4. Values across calls (keep bundles).** A fact read by a later call rides in the bundle `F`
of `Computation.RoutineSpec.wp_bind_keep`: scalar cells as `Computation.CellsHold` (built by
`Computation.CellsHold.cons` from `Computation.cellsHold_nil`; `.head` is the cell consed last,
read by `hC.read (.tail _ (.head _))`), matrices as `pairLayout.Holds`
(`Computation.readsOnly_pairLayoutHolds`), joined by `Computation.ReadsOnly.and`. Its read set
must be disjoint from the call's footprint (one fp_omega): a bundle holds only what the next
call does not write, so split bundles, re-bundle the output of a call when a later call needs
it, drop a cell after its last read (`Computation.CellsHold.sub`). Across allocations, transfer
a whole bundle with `Computation.ReadsOnly.of_read_eq_below`.

**5. Sub-blocks.** Write a long block as nested sub-builders, `(do A₁ … Aₖ) >>= fun _ => (do B₁
…)`, so `r >>= f` matches the call rule syntactically; prove each sub-block as its own spec with
the footprint form its consumer uses. A spec stated about a different but run-equal builder is
moved by `Computation.RoutineSpec.congr`, built in a separate `have`. Prove composability once
per block, with general arguments (`NLAlib.executionComposable_eighCompressBlock`).

**6. Allocations.** Nest `Computation.Spec.allocBind_named` for buffers of different lengths,
then one `refine spec_allocBind_iterate j hb (fp := G) (post := Q) ?_` per further buffer of
one length (`Computation.spec_allocBind_iterate`), and wrap in `Computation.RoutineSpec.scope`.
The body's hypotheses are about the allocated state, its conclusion about the released state
(`NLAlib.spec_eighNodeBlock_of_body`, `NLAlib.spec_eighSplitBlock_of_body`).

**7. Loops.** `Computation.RoutineSpec.forRange` (or `Computation.Spec.loop`) with the
invariant "the store holds the iterate": `fun st₀ k st => State ((step)^[k] A) st.store ∧ … ∧
PosKept st₀ st`; the step is the one-iteration spec, and the math lemma rewrites the iterate to
the algorithm's function. A loop that runs while a comparison holds (`whileFuel`):
`Computation.RoutineSpec.whileFuel` / `Computation.Spec.whileFuel`, with the invariant before
each test; the total mode needs fuel for the first test (`hf0`), the comparison defined, and fuel for each test that holds.

**8. Old lemma pairs become corollaries.** A refinement lemma is `(spec_eighSignBlock .liberal
… trivial …).spec.holds_of_exec hpre hrun` (`Computation.Triple.holds_of_exec`), a success lemma
`(spec_eighSignBlock .total …).spec.exists_exec hpre` (`Computation.Triple.exists_exec`), with dummy
`u`, `dec`, `safe` at `liberal`; pass the start state explicitly after an index binder. Facts
of every run (memory, shape) join by `Computation.RoutineSpec.and_liberal`. An old lemma
without a spec is adapted by `Computation.Triple.of_exec`.

**9. Frames.** Every frame holds in every mode, unconditionally: if an old refinement lemma
gives a frame only under value hypotheses, use the kernel's `*_frame` spec
(`Computation.spec_zhermShift_frame`, `Computation.spec_kcall_frame`) or build one with
`Computation.Spec.seq_frame`, `Computation.Spec.loop_frame`, `Computation.Spec.frame_of_sub`.

**10. Straight-line blocks.** A block of scalar instructions without loops or branches (a
rotation, a norm, a coefficient update) is a list of `Computation.ScalarOp` run by
`Computation.scalarBlock p ops`, specified once by `Computation.spec_scalarBlock md p ops`:
footprint one cell per operation (`Computation.opsFootprint`), post `storeFn p st'.store =
evalOps I.sem p ops (storeFn p st.store)` and each written cell reads its evaluated word, with the
count and `PosKept`. The liberal mode needs nothing; the total mode needs
`Computation.OpsDefined` (cells read hold words when read: temporaries written earlier need no
initialisation; `Computation.opsDefined_of_forall` when all are present), `Computation.OpsOk`
(`Computation.opsOk_of_plain` with `Computation.WordTotal` for add, sub, mul, neg and copies;
`Computation.IsRelErrSem.wordTotal`) and `WritableBlocks` of the footprint. Read inputs into the
word function with `Computation.storeFn_of_read`, coarsen the footprint with
`Computation.RoutineSpec.sub`. Evaluate one output word per lemma (`evalOps … g (B, xo.eval) =
…`, by `simp only [evalOps_cons, ScalarOp.step, ScalarOp.value, Function.update_apply, …]`):
one `simp` over all outputs of a 36-operation block exhausts the heartbeats.

**Pitfalls.**
- A nested `exact` chain of calls leaves metavariables, and a spec inlined in a `refine` can take
  18 s a step: always `have sᵢ := …` first.
- fp_omega clears the context: pass every bound and disequality it needs (fp_omega [hi, hlen]).
  It unfolds `Computation.matBlock`, `Computation.cellBlocks`, `List.Nodup` and normalises
  products. If slow: `Computation.blockDisjoint_of_fst_ne`, or `Computation.blockDisjoint_iff`
  then nlinarith. Peel `x ∈ H.handles` with List.mem_append before omega.
- Never use `pairLayout.width` or a `List.range` map in a footprint.
- Close `x = x` components with trivial; split_ifs cases equal up to defeq by `absurd h1 h2`.
- Proofs at most 80 lines: split by sub-block, not by tactic tricks; default heartbeats.
- Long do-blocks: matching `r >>= f` against a long block with `r` a named head def is slow
  (bind associativity is defeq but expensive). Put the continuation into the def (a head def
  taking `rest`) and state that piece in `Wp` form.
- A builder argument written `.var k` where the callee's spec has `.const k` (an old spec that is
  not index-generic): `Computation.RoutineSpec.of_runEquiv` with `Computation.RunEquiv` built by
  the tactic run_equiv after unfolding the block's definitions; values equal only by arithmetic
  are left as goals (`Computation.Cell.normIdx_eq_of_eval_eq`). Do not compare whole statements
  by `exec_eq_of_normIdx_eq I rfl`: it can exhaust the kernel on a large block.
- A loop whose iterations all modify inside one fixed list: `Computation.RoutineSpec.forRange_const`
  (one footprint); keep per-iteration footprints for the post only.
- A conditional whose outcome the proof only learns by cases: case on the comparison and build the
  untaken arm with `NLAlib.routineSpec_of_false`; `Computation.RoutineSpec.ifThenElse` needs the
  outcome fixed in the precondition.
- `Computation.RoutineSpec.bind` forgets the second routine's `Modifies`; rebuild as
  `⟨composable, spec.with_modifies⟩` when a later frame needs it.
- Old statements may allow a scratch buffer to alias an input (`Su = t`): take the aliasing case
  as a conditional hypothesis and derive what the case forces from the reads that exist.
- omega sees `IExp.eval e` as an atom: simp the evals first or pass explicit indices.
- The naming rules N1–N18 and T13 run only in stage_check (they need the extraction), not in
  the per-file rules check: a name's part before `_of_` must occur in the conclusion, a conclusion
  must not start with `let`, names ending in `Tail` are registry bounds.
- `Computation.IsMatMulKernel.spec_kcall` states its footprint and post with `pairLayout.width`:
  `simp only [Computation.matBlock, Computation.pairLayout]` before fp_omega. A kernel call written
  with `.var k` against a spec at `.const k`: `Computation.RunEquiv.kcall`.
- Dispatch on a stored kind (an index binder, then guarded blocks `eighWhen (eighEqInd c i)`): one
  spec per kind, chaining `NLAlib.spec_eighWhen` for the taken guard and
  `NLAlib.routineSpec_eighWhen_of_eval_eq_zero` for the others (`NLAlib.spec_eighUpNode_one`).
- Allocations of different lengths: `Computation.spec_allocBind_chain`. A footprint block that
  runs past its buffer: `Computation.Modifies.of_sub_shape` (cells past the buffer read `none`).
  A statement with `.var k` against a spec at `.const k`: `Computation.Spec.of_exec_eq`, with the
  run equation from `Computation.RunEquiv.exec_run_eq` in its own `have`. A postcondition that
  is a metavariable is not a pattern: name it first (`obtain ⟨Post, hPost⟩`).
- `omega` fails on a hypothesis or goal of the form `False ∨ P` (left by `simp` on a membership):
  simp the `False` disjunct away first. A name that fp_omega or `omega` must see through (a
  cell list, a register count, a footprint window) is an `abbrev`, not a `def`, or is unfolded
  before the call.
- An error without a line (a kernel error such as a deterministic timeout or deep recursion,
  reported at the declaration) comes from the proof term, not a tactic: replace halves of the
  proof by `sorry` (locally, never committed) until it compiles, then look in the removed half for a whole-statement `rfl`,
  a `decide`, or a unification of `.var k` with `.const k`.
- Spec lookup: the catalog `NLAlibTools/SpecCatalog.lean` writes every specification with its
  pre, footprint, post and file:line (`SPEC_CATALOG=<out.md> lake env lean NLAlibTools/SpecCatalog.lean`).

**Fast check loop.** Most of a job's time goes to waiting on Lean, so:
1. Iterate on the edited file against the modules already built:
   `flock <lock> lake lean <file>`, or a scratch file that imports it (seconds per check).
2. After an edit, rebuild only that module and its direct dependents: `lake build <Module>`
   through the lock.
3. Once per job, at the end and before the final commit: one `lake build --wfail NLAlib`, one
   `bash scripts/stage_check.sh` and the Targets dry run. Never per iteration, never in a polling
   loop. The naming rules run only in stage_check; the rules check's `--partial` mode on an
   extraction runs them earlier.

**Worked examples.** Scalar steps, a nested conditional, frame by `Modifies`:
`NLAlib.spec_eighClampBlock` (`NLAlib/Matrix/Computation/SpectralBisectionClamp.lean:70`).
A loop as an iterate: `NLAlib.spec_eighSignIter` and `NLAlib.spec_eighSignLoop`
(`NLAlib/Matrix/Computation/SpectralBisectionNode/SignStep.lean:79`, `:158`); scalar prologue and
calls with keep bundles: `NLAlib.spec_eighSignBody` (same file, `:200`); corollaries:
`NLAlib.holds_of_exec_eighSignBlock` (`:427`). The cleanest chain of kernel calls with `have sᵢ`:
`NLAlib.spec_eighNodeProjectors` (`NLAlib/Matrix/Computation/SpectralBisectionNode/Setup.lean:207`).
A split with a named window, allocation prefix and `congr`: `NLAlib.spec_eighSplitBody`,
`NLAlib.spec_eighSplitBlock`
(`NLAlib/Matrix/Computation/SpectralBisectionNode/Split.lean:522`, `:679`). A loop over slots
with an invariant, a head def with its continuation, and both old lemmas from one spec:
`NLAlib.spec_eighDownLevel` (`NLAlib/Matrix/Computation/SpectralBisectionProgram/DownLevel.lean:1140`). A whole program with
ten allocations of different lengths and two level loops: `NLAlib.spec_eighProg`
(`NLAlib/Matrix/Computation/SpectralBisectionProgram/Refinement.lean:872`).
