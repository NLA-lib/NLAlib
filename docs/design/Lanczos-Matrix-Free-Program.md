# Matrix-free Lanczos program

> Archived execution-system design. The former evaluator, programs, target registry and
> emission tooling are retired. The current interfaces are documented in
> [the Ops migration](Ops-Migration.md) and [the program guide](../contributing/programs.md).
> Mathematical analysis is retained; program and registry names below describe the historical system.

Approved and integrated 2026-11-04; rounded oracle execution completed 2026-11-05. The
stored Lanczos program, compiled tree, targets and closed count formulas remain unchanged.

## Concrete program

`proposals/krylov/LanczosOracle.lean` (a draft, since removed; `git log -- proposals` finds it)
contains `lanczosOracleProg tag o N q` and its single
compiled first-order tree with six declared buffers: retained input, all basis columns, alpha,
beta, input norm, previous vector. Scoped slot 6 is an empty allocation, slot 7 has N work cells,
and slot 8 has two scalar registers. There is no ROM load and no stored matrix. Each Paige step
begins with the actual one-column `.apply o tag work 0 V (N*j) 1`. Every remaining scalar,
normalization and copy operation is in the same order as the dense program. Exact zero input,
zero dimension, zero requested steps and terminal zero continuation are included.

The proposed count has q oracle loads and q matvecs; multiplication/addition N+4qN each,
conjugation N+2qN, division N(q+1), sqrt/comparison q+1, negation 2q, literal
2N+3+q(N+2), and copy N+2qN. All other kinds have zero upper counts. The per-tag peak-cell bound
is N(q+4)+2q+5 at the program tag, zero at other tags. It covers the declared buffers and
workspace, and excludes hidden storage/internal arithmetic of the oracle backend. `MatrixFree`
uses the existing oracle abstraction and does not claim the oracle's own implementation cost.

## Exact proposed target

`MatrixFreeLanczos` quantifies types/tags/oracle first and then uses the existing `MatrixFree`
model on the fixed tree. It has no matrix symmetry, definiteness, nonzero-input or nonbreakdown
premise. For every real A, input b, tape and natural sizes, execution succeeds within the count
and memory formulas. Its actual final declared buffers hold b, `lanczosMatrix A b (q+1)`, all
q alpha values, all q+1 beta values, exact input norm, and final previous vector. The exact
postcondition is the dense analogue, including b preservation, with no ROM matrix encoding.

## Shared proof interface, proposed before mutation

Canonical `LanczosProgramState.lean` will expose

```lean
def workspaceShape (tag : P) (N q : ℕ) (storedMatrix : Bool := true) : Array (P × ℕ)

structure State (tag : P) (N q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (st : St P ℝ (OpCount P ι))
    (storedMatrix : Bool := true) : Prop where
  shape : st.store.shape = workspaceShape tag N q storedMatrix
  matrix : if storedMatrix then Holds st.store tag 6 0 A else True
  -- Existing input, basis, alpha, beta, norm, prev and persistent-zero fields unchanged.
```

The true specialization has exactly the existing capacities and loaded-matrix requirement.
The false specialization has length-zero slot 6 and no matrix read premise. Shared frame,
projection, next-norm, commit and initialization theorems receive an optional implicit
`storedMatrix` parameter, defaulting to true. Existing dense matvec, step, loop and target
specializations remain true; no target closure changes. There is no new arithmetic contract.
Only the matrix-vector execution prefix and outer oracle loop need new proofs. The scalar and
guarded normalization phases are reused rather than copied. The proposal exact proof uses the
existing exact interpreter/oracle execution semantics and generic scoped allocation helpers.

StaticCost analyzes the actual proposed tree for resources. Its proof is independent of the
exact output induction, and counts and memory do not follow from an exact-correctness target.
New proposal proofs remain outside NLAlib until the new target/tree is approved. Root owns
registration, packaging, umbrella/vocabulary integration and the full stage.

## Approved implementation amendment, 2026-11-04

The user approved both exact matrix-free targets. Canonical Lanczos files are
`LanczosOracleProgramTree.lean`, `LanczosOracleTargets.lean`, `LanczosOracleStaticCost.lean`,
`LanczosOracleExecution.lean` and `LanczosOracleProgram.lean` in `Krylov/Processes`.
The approved program/tree/count/target bodies are copied unchanged from the proposal.
The oracle execution file groups the prefix, step and loop in one topic-sized module; the
outer realization is independently owned for integration.

`State.shape` retains a literal conditional array, definitionally equal to `workspaceShape`,
so the existing dense postcondition's restricted simplification remains valid. Its default true
specialization has exactly the original dense capacities and matrix-read premise. Shared
scalar phases infer the matrix-storage flag from `State`, with `optParam Bool true` preserving
the default. Raw initializer APIs instead expose explicit `_of_workspace (storedMatrix : Bool)`
variants and retain all four original dense signatures as true-specialization wrappers. The
existing dense `LanczosProgram` proof has been rechecked with warnings fatal.

`Computation.exec_apply_exactInterp_offset` generalizes the existing exact oracle execution
lemma to arbitrary source and destination offsets. The old helper's statement is unchanged and
its proof is now the zero-offset specialization. This handles the actual basis offset N*j
without a second semantics or assumed oracle-output premise.

The canonical resource analysis proves the approved operation counts, additional cells N+3
at the program tag (zero at other tags), and additional bits `(N+3)*width tag`, conditional only
on actual successful execution and standard charges. Initial declared storage is added once;
there is no ROM storage in the oracle model.

## Shared rounded implementation, 2026-11-05

`LanczosOracleProgramRounded.lean` proves actual compiled execution, all six declared decoded
outputs, input norm/direction errors, the active `LanczosRun` and original static resources.
Scalar roundoff u and oracle accuracy eta are separate contracts; a chosen allowance v >= u
makes the common local run budget cover eta. No accumulated horizon is needed for completion.
The zero-input/dimension/budget and terminal continuation cases remain covered. Dense and
oracle products supply the same `IsMatvecRoutine` certificate to one Paige-step, normalization
and prefix/loop proof; the prior dense backward statements are preserved. Every mathematical
`LanczosRun` theorem also applies to the extracted oracle run.
See [the common design](Krylov-Rounded-Oracles.md).
