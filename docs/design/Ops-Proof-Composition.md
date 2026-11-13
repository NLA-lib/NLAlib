# Reusable proof composition trials

Requested 2026-11-12: test whether established mathematical analyses transfer to programs
without repeated bookkeeping. Work on the migrated resource branch; preserve canonical
accounting and all existing statements. No target/check/approval changes.

## First trial: state iteration

Existing CG.HSCG.rounds_writes and CG.HSPCG.rounds_writes independently rebuild the same
constant-footprint invariant, frame dimensions/operands, liveness and capacity preservation,
position chaining and Function.iterate step. The transition/state/validity differ; the program
composition does not. Mathlib Function.iterate supplies the mathematical iteration.

Add to Ops.Logic.Loop:
- evaluation of existing operand lists after an index is appended (using IExp.eval_append),
- reuse existing Store.EqOff transport of Mem.Live and Mem.Room,
- writes_loop_frame_iterate, parameterized by arbitrary mathematical state S, state predicate,
  transition, validity, footprint and a framed total round proof. It forwards an initial-store
  frame to the round, so clients preserve any other input facts without restating a chain.

Both CG and PCG consume this rule, preserving exactly their current hypotheses and conclusions.
The purpose is to expose the mathematical transition and nonbreakdown, not raw store equations.

## Second trial: contract-to-stored-state composition

Inspect duplicated step_writes adapters and the bridge from total block contracts to fixed
Program certificates. Add shared rules only where at least two concrete programs use them.
Use existing Writes/Impl.Triple.writes and Algorithm.ofWp rather than introduce another
certification layer. Where actual canonical solver certification remains cumbersome, record
specific missing machinery and implement shared infrastructure before repeating it.

## Validation and assessment

Compile the two original solver endpoints, compare proof bodies before/after, prove new
mathematical output consequences using existing pure CG/PCG mathematics, and check reuse under
zero rounds, aliases, abstract words and arbitrary dimensions. New canonical certificates, if
constructed, must use jointly realized primitive maps and independent full resource budgets.
No conditional proof is relabeled canonical. Run the unchanged full build/stage plus scoped
kernel/axiom checks, report legacy check failures explicitly.

## Implemented trials

`Impl.Triple.writes_blocks` turns a block contract into the stored-output relation and an
unchanged-store frame. Output blocks must be pairwise apart; inputs may alias outputs as
permitted by the original contract. It preserves the actual random-tape window and position.
CG, PCG, residual reorthogonalization and Lanczos normalization all use the same rule.
The original theorem statements are unchanged. Together with framed iteration, the first four
CG/PCG proof bodies lose 26 lines of repeated execution bookkeeping.

Three new consequences test mathematical reuse:

- `CG.HSCG.runs_solve_polynomial`: a polynomial energy-error bound on the stored CG iterate.
- `CG.HSPCG.runs_solve_polynomial`: the corresponding preconditioned bound.
- `Lanczos.runs_solve_basis`: the stored basis agrees with the pure Arnoldi matrix, including
  the existing zero/breakdown convention.

The two polynomial proofs take six tactic lines each; the basis proof takes three. They apply
existing pure mathematics after the existing solver result, without unfolding instructions.
They retain exactly the original conditional run budgets and hypotheses. In particular the
fixed-horizon CG/PCG results retain the Krylov-grade restriction and exact-operation contracts.
These are not floating-point accuracy claims or new canonical solver certificates.

`Algorithm.mapPost` separately tests the same pattern on the canonical core. It changes only
`Specification.good` and forwards the same program, jointly realized model, actual run, counts,
work, span, scratch and total modeled memory bounds. `Examples.Consequences` applies it to both
repeated addition and mixed-format scratch cleanup. No execution or cost proof is repeated.

## Assessment and remaining friction

Once the mathematical output interface exists, the new consequences are short and reusable.
There was duplicated buffer readback and loop framing rather than a need to reprove CG math.
The shared rules remove that duplication across different state sizes and routines.

The low-level solver statements still have long buffer-layout, liveness, capacity and model
hypotheses. This trial does not establish easy end-to-end canonical certification for a new
solver. The next useful authoring work is shared adapters from problem initial buffers to block
contracts and from declared primitive models to the existing implementation certificates,
followed by full canonical CG/Lanczos certificates with independent resource budgets. Avoid
copying those adapters into each solver or treating a conditional theorem as a certificate.

## Validation log

- `LEAN_NUM_THREADS=2 lake build --wfail NLAlib`: passed, 4,635 jobs.
- Source rules on every modified/new Lean file: zero errors, 27 warnings on existing code.
- Reference check: zero problems. Generated root updated with `mk_all`.
- Individual axiom checks on all three new solver results, both generic rules, canonical
  consequence transport and both canonical consumers: only Lean's standard logical axioms.
- Unchanged `scripts/stage_check.sh`: all 952 proved modules build with zero warnings;
  global audit checks 35,586 declarations with zero violations. The stage then stops at the
  existing `CastOp` deriving-instance unused-argument findings in the environment linter.
  No checks, exceptions, targets or baselines were changed.
- `lake build --no-build --rehash NLAlib`: all targets current, 4,635 jobs.
- Unmodified `scripts/Replay.lean` with `REPLAY_ROOTS=NLAlib REPLAY_STRICT=NLAlib`:
  35,587 constants of 953 modules replayed through Lean's kernel; zero violations. Only the
  83 standard compiler `_unsafe_rec` auxiliaries are exempted by the existing checker.
  This is the `NLAlib` library replay, not an assertion that every stage step passed.

## Stored-output Chebyshev corollaries

The explorer consumes explicit convergence bounds for recomputed-rho and carried-rho CG.
No objects or hypothesis interfaces are added. Both use the existing exact scalar, BLAS and
matvec contracts, positive definiteness, ordinary readable input buffers and writable output
capacity. The spectral input is `0 < a` and `spectrum ℝ A ⊆ Set.Icc a a'`, with a supplied
solution of the input system. The conclusion is the existing total `ConditionalRuns` budget
with stored output energy error at most `4 * rho ^ (2 * q)` times initial energy error,
where `rho = (Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)`.

`CG/HSCG/Bounds.lean` adds `runs_solve_chebyshev` with `q = k` and the existing grade
restriction. `CG/HSCG/Carried/Bounds.lean` adds the same name with
`q = min cap (krylovGrade A (b - A *ᵥ x₀))`, accepting every cap and exact comparisons.
The full signatures follow the existing `runs_solve` buffer and model arguments, adding
`{a a' : ℝ} (ha : 0 < a) (hspectrum : spectrum ℝ A ⊆ Set.Icc a a')` and
`{solution : Fin n → ℝ} (hsolution : A *ᵥ solution = decv dec n bs)`.
The existing `ConditionalRuns.mono` transfers stored-output equality and retains counts and
scratch; `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow` supplies all mathematics.
Mathlib was searched for CG bounds; NLAlib's existing pure theorem is reused directly.
No execution, frame or convergence argument is duplicated. The generated root imports the
new carried bounds module. These exact-operation consequences do not extend the rounded model
or constitute new canonical resource certificates. No open design questions.
