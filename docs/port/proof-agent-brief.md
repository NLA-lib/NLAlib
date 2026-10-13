# Brief for a proof agent

You own one file (occasionally two or three small ones, named in your task). Its statements and
docstrings are already written; every proof is `sorry`. Your job is to replace every `sorry` with
a proof, so that the file compiles with no errors, no `sorry` and no linter warnings.

## Read first

1. `CONTRIBUTING.md`, in full. §3 (file template), §5 (statements), §6 (docstrings), §7 (proofs),
   §10 (memory) and §11 (agent rules) bind you.
2. The stage's design note, named in your task (`docs/design/Matrix-<Stage>.md`).
3. Your file.
4. The prototype files named in your task, under `~/Documents/prove2me/lean/`. They are read-only
   proof material. Never edit anything there and never build there.

## Rules

- **Statements are fixed.** Do not change a statement's meaning, add a hypothesis, or weaken a
  conclusion. You may, and should, do what the linters ask: drop or weaken unused instance
  arguments (`[Fintype m]` to `[Finite m]`, removing an unused `[DecidableEq _]`), add `omit … in`,
  reorder or regroup `variable` lines, change binder names. If you believe a statement is false,
  not provable as written, or badly shaped, do not repair it silently: leave it `sorry`, and say
  so in your report with the counterexample or the obstruction.
- **Search before proving**: Mathlib (`grep -rn` under `.lake/packages/mathlib/Mathlib`, `exact?`,
  `apply?`, `rw?`, `simp?` in the file while working), then the already-built `NLAlib/`, then the
  prototype. If Mathlib already has a statement outright, say so in your report; the orchestrator
  decides whether to delete it.
- **Proof style** (CONTRIBUTING §7): tactic proofs; `simp only [...]` on large goals, no
  `simp_all`; no terminal `exact?`/`apply?`/`simp?` left in the file; a proof over about 80 lines is
  split into `private` lemmas (or public ones if a second file could want them, with a docstring);
  no `set_option maxHeartbeats` at file level (per declaration with a comment if unavoidable); no
  `open Classical` at file level; no `axiom`, `native_decide`, `admit`.
- **Helpers.** A `private` helper needs no docstring. A public helper you add needs a docstring and
  a Mathlib-style name (CONTRIBUTING §4). Do not add theorems beyond what the proofs need.
- **Docstrings** stay as written, except that you correct anything a proof shows to be inaccurate
  and report it.
- **Budget.** If one declaration resists for about an hour, stop on it. Move it, with its full
  docstring and a `sorry` body, to the same path under `NLAlibScaffold/` (creating the file from
  the template if needed, with `public import` of your `NLAlib` file), and add to its docstring a
  line `Proof: <what the argument is, where it broke, estimated difficulty>`. Then go on.

## Building

Two agents may be working on this machine at once, each on its own file. Memory is the limit.

- Check your file with
  `LEAN_NUM_THREADS=2 lake lean <path/to/File.lean> -- -M 8000 > /tmp/<name>.log 2>&1`
  and read the log. Run it from the repository root. Use `lake lean`, not `lake env lean`: only
  `lake lean` applies the options and linters of `lakefile.toml`.
- To run the environment linters (`simpNF`, `docBlame`, `unusedArguments`, …) on your file once
  it has no `sorry`: build its module with
  `LEAN_NUM_THREADS=2 lake build NLAlib.<Module.Name>`, then check a scratch file in `/tmp`
  containing `import NLAlib.<Module.Name>`, `import Batteries.Tactic.Lint` and
  `#lint in NLAlib` with `LEAN_NUM_THREADS=2 lake env lean -M 8000 /tmp/<name>_lint.lean`. Do this
  when your file has `@[simp]` lemmas or new definitions.
- Never run `lake build` without `LEAN_NUM_THREADS=2`, never build `NLAlib` as a whole, never run
  `lake exe cache get` or `lake update`, never `import Mathlib`.
- Scratch files go in `/tmp`, not in the repository.
- Do not edit any file but your own (and its `NLAlibScaffold` counterpart if needed). Do not edit
  `NLAlib.lean`, `docs/port/status.md` or `docs/port/ledger.json`; the orchestrator does.
- Do not commit.

## Done means

`lake lean` on your file prints nothing: no errors, no warnings (including "declaration uses
sorry" and the `unusedFintypeInType`, `unusedArguments`, `unusedSectionVars`, style and long-line
linters). Lines are at most 100 characters.

## Report (your final message)

1. State: every declaration proved, or the list of what went to `NLAlibScaffold` and why.
2. Ledger entries: for each prototype declaration you used or that your file replaces, a line
   `old name → new name`, or `old name → null (reason)`.
3. Statements you think are wrong, weak, misnamed or missing a companion lemma, with reasons.
4. Instance or signature changes you made, one line each.
5. Anything Mathlib already had.

Keep the report under 400 words. Do not paste proofs into it.
