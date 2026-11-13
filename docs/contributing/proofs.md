# Proofs and what each library may contain

Part of the [contributor guide](../../CONTRIBUTING.md).

- `import NLAlib` is sorry-free; `scripts/Audit.lean` checks every reachable declaration against
  `propext`, `Classical.choice`, `Quot.sound` only.
- `lakefile.toml` has two libraries that matter to contributors. `NLAlib` is the library: proved,
  documented and checked by every rule here. `NLAlibTools` holds tools that are not part of the
  library: canonical Ops execution diagnostics and smoke tests. Its files import retained
  `NLAlib` modules and are plain (non-`module`) files so that `#eval` runs the
  library's programs, may contain `sorry` and are not held to the library's rules; CI builds
  them, checks their root file and replays them, non-strictly.
- A library docstring has no `Proof:` sketch line [D8]: what is merged is proved.
- Proofs are free to differ from any source. Choose the argument that is shortest in Lean and
  reuses the most library API; a clever proof from the literature is worth nothing if a
  three-line one through Mathlib exists.
- Proof style: tactic proofs, `simp only` with named lemmas rather than bare `simp` on large
  goals, no `simp_all` [S1], no `decide` on anything but tiny finite goals (review list: [S3]),
  `nlinarith`/`positivity`/`gcongr` welcome. A proof over 80 lines is split into named lemmas
  [S4]; this counts the proof body, excluding type-level `let` bindings in the statement.
  Terminal `exact?` and `apply?` do not appear in committed code [S2].
- Nothing in `NLAlib/` (or the `leanOptions` of `lakefile.toml`) is
  `unsafe`, `partial`, `implemented_by` or `extern`, or sets a `debug.` option or a kernel option
  (`set_option debug.skipKernelTC true in` makes the elaborator skip the kernel, and an `unsafe`
  definition then inhabits any type with no axiom) [S9]. The checks
  behind it: `scripts/Replay.lean` sends every constant of the package's `.olean` files (every
  library of `lakefile.toml`) to the kernel again (Lean core's `Environment.replay`, as
  `lean4checker` does), trusts as its base only modules read from `.lake/packages/` and the
  toolchain, and in `NLAlib` (and any library it imports) fails on an `unsafe` or `partial`
  constant, an axiom or a use of `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or
  `Lean.trustCompiler`; `scripts/Audit.lean` fails on an `unsafe` or `partial` constant.
- `NLAlib`, every file and the root `NLAlib.lean`, imports no other library of the package:
  neither `NLAlibTools` nor any other library of `lakefile.toml` [P3, P12]. It imports itself,
  Mathlib and Mathlib's dependencies only.
- Instances: no global instance on a Mathlib type unless it is the one Mathlib would add
  (`Matrix.instMeasurableSpace`, in `ForMathlib`, is one); each is allowlisted with its reason
  [S6]. No `attribute [instance]` at file level [F9].
