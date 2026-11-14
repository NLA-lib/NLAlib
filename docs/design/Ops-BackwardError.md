# Backward error in the operation core

Requested 2026-11-14 (board T136) as a prerequisite of the finite-precision shifted QR algorithm
[BanksGarzaVargasSrivastava2022, Part II], and of any backward-stable algorithm after it.
No targets, checks or approvals change.

## Problem

Every contract of `NLAlib/Ops` is **forward**. An operation's `Contract`/`BlockRel` relates its
output words to its input words; rounding enters per operation (`StdModel`, `RelErr`,
`AbsRelErr`, `Blas.seq.err`). Nothing states "the output is the exact result of a perturbed
input". The rounded Krylov and PCG developments therefore prove `Writes` theorems that return
word recurrences, then thread an error invariant through their own proofs by hand (about a
thousand lines each). For a unitary eigenvalue algorithm this is the wrong shape: each step is a
unitary similarity of a perturbed matrix, and the perturbations simply add,

$$\mathbf{U}_2^{\mathsf{H}}\bigl(\mathbf{U}_1^{\mathsf{H}}(\mathbf{H} + \mathbf{E}_1)\mathbf{U}_1 +
\mathbf{E}_2\bigr)\mathbf{U}_2 = (\mathbf{U}_1\mathbf{U}_2)^{\mathsf{H}}(\mathbf{H} + \mathbf{E}_1 +
\mathbf{U}_1\mathbf{E}_2\mathbf{U}_1^{\mathsf{H}})(\mathbf{U}_1\mathbf{U}_2),\qquad
\|\mathbf{U}_1\mathbf{E}_2\mathbf{U}_1^{\mathsf{H}}\|_2 = \|\mathbf{E}_2\|_2 .$$

The exact shifted QR development (`origin/feat/ops-exact-shifted-qr`) hard-codes exact
equalities `H' = Uᴴ * H * U` in `IterationContract`, `DecoupleInv` and `DecouplingContract`;
only its `DeflationInv` carries a perturbation `E`.

## Objects

Mathematics (`NLAlib/Matrix/Perturbation/UnitarySimilarity.lean`, any `RCLike 𝕜`, any
`Fintype` index):

```lean
def IsPerturbedUnitarySimilar (A B : Matrix n n 𝕜) (ε : ℝ) : Prop :=
  ∃ U E : Matrix n n 𝕜, HasOrthonormalCols U ∧ specNorm E ≤ ε ∧ B = Uᴴ * (A + E) * U
```

The shape is that of `DeflationInv` (`M = Uᴴ * (H + E) * U`, `specNorm E ≤ ε`), so the two
compose without a transport. `IsQRErr`/`IsMatMulErr` (`Matrix/FinitePrecision/Machine.lean`) are
backward statements about one factorization or product, not about a similarity; they are not
restated. Mathlib has `Matrix.unitaryGroup` but no perturbed similarity (searched, none);
`HasOrthonormalCols` is the library's spelling of unitarity (vocabulary, V1).

Operation core (`NLAlib/Ops/Logic/Backward.lean`; Ops imports only Mathlib and Ops, so this layer
is generic in the notion of perturbation):

```lean
structure IsBackwardErrorRel (R : ℝ → α → α → Prop) : Prop where
  refl  : ∀ a, R 0 a a
  trans : R ε₁ a b → R ε₂ b c → R (ε₁ + ε₂) a c
  mono  : ε ≤ ε' → R ε a b → R ε' a b

def BackwardStep md I τ c ρ F (R : ℝ → α → α → Prop) (S S' : α → Mem K → Prop) (ε : ℝ) :=
  ∀ a m, S a m → Writes md I τ c ρ F (fun m' => ∃ b, R ε a b ∧ S' b m') m
```

`S`/`S'` say which state the memory holds, together with everything a step needs and keeps
(parameter words, live and separated views, a Hessenberg form, a position). A backward step is an
ordinary `Writes` statement, so it is used by every existing rule (`Writes.seq`, `in_frame`,
`Impl.meets_of_writes`, `Algorithm.ofWp`, `mapPost`), and implementations are still substituted
under fixed contracts by `Profile.Refines.runs`/`Algorithm.link`. Nothing in `Contract`,
`Profile`, `Cert` is forked.

The bridge (`NLAlib/Matrix/FinitePrecision/OpsUnitarySimilarity.lean`) proves
`isBackwardErrorRel_isPerturbedUnitarySimilar` and the exact case.

## Rules

| declaration | statement |
|---|---|
| `IsPerturbedUnitarySimilar.refl`, `.trans`, `.symm`, `.mono`, `.nonneg` | the algebra; errors add |
| `isPerturbedUnitarySimilar_zero_iff` | error `0` ↔ `∃ U, HasOrthonormalCols U ∧ B = Uᴴ * A * U` |
| `HasOrthonormalCols.isPerturbedUnitarySimilar` | `IsPerturbedUnitarySimilar A (Uᴴ * A * U) 0` |
| `isPerturbedUnitarySimilar_add`, `.add_right` | a perturbation `F` of the output adds `specNorm F` |
| `.sub_single`, `specNorm_single_le` | zeroing an entry of modulus `≤ δ` adds `δ` (deflation) |
| `.exists_fromBlocks₁₁`, `.exists_fromBlocks₂₂` | a step on a diagonal block of a block upper triangular matrix is a step on the matrix, same error |
| `.specNorm_le` | `specNorm B ≤ specNorm A + ε` |
| `BackwardStep.writes_add` | continue from an accumulated error `e`: error `e + ε` |
| `BackwardStep.skip`, `.of_exact` | exact steps have error `0` |
| `BackwardStep.mono` | footprint, error, final predicate |
| `BackwardStep.seq` | errors add, footprints join |
| `BackwardStep.loop` | `N` rounds `i ↦ ε i`: error `∑ i ∈ range N, ε i` |
| `BackwardStep.ite` | both arms with `ε`, test succeeds on `S`: error `ε` |
| `BackwardStep.whileFuel` | rounds with `ε i ≥ 0`, continuation `ε'`: `∑ i ∈ range N, ε i + ε'` |
| `Ops.BackwardStep.of_unitarySimilar` | a `Writes` returning `∃ U B, HasOrthonormalCols U ∧ B = Uᴴ * A * U ∧ S' B m'` is a `BackwardStep … 0` |

Relative budgets ($\varepsilon \le \nu\|\mathbf{A}\|_2$) become additive by carrying a norm
bound `specNorm A ≤ M` in `S`, which `specNorm_le` re-establishes with `M + ε`.

Example (`NLAlib/Ops/Examples/Backward.lean`): three abstract steps with errors `u, v, w` in a
loop of `N` rounds give `N * (u + v + w)`, in three lines from `loop`, `seq`, `mono`.

## Exact arithmetic is ν = 0

Codex's exact contracts end with `∃ U H', HasOrthonormalCols U ∧ H' = Uᴴ * H * U ∧ … ∧
HoldsMatrix w H' μ'.store`. Taking `S H μ` to be the preconditions (`IsUpperHessenberg H`,
`HoldsMatrix w H μ.store`, the parameter words, the geometry) and `S'` the remaining conjuncts,
`BackwardStep.of_unitarySimilar` turns `IterationContract` and `DecouplingContract` into
`BackwardStep … (fun ε A B => IsPerturbedUnitarySimilar A B ε) S S' 0` with no mathematics.
`DecoupleInv`'s `H = Uᴴ * H₀ * U` is `IsPerturbedUnitarySimilar H₀ H 0`
(`isPerturbedUnitarySimilar_zero_iff`), and `DeflationInv`'s witness is
`IsPerturbedUnitarySimilar H M ε` verbatim. The bridge is stated generically on `main`, since
that branch is not merged; it does not modify it.

## How the rounded shifted QR will use it

1. **Kernels.** The Givens coefficient and rotation kernels are proved over a generic `Machine`
   (as rounded Krylov does), with a rounding model; one sweep of rotations of an
   `(n+1)×(n+1)` Hessenberg matrix is shown a `BackwardStep` with
   `ε = c(n)·u·specNorm H` (the Givens backward-error analysis, below).
2. **Iteration.** `IterationContract` is weakened from `HoldsMatrix w (shqrAcceptStep …)` to a
   backward step: the stored matrix is a perturbed unitary similarity of the input, within
   `ν·M`, and is Hessenberg. The exact proof gives the `ν = 0` instance through
   `of_unitarySimilar`.
3. **Decoupling.** `DecouplingContract` becomes a backward step with budget
   `F · ν · M` by `BackwardStep.loop` (or `whileFuel`), where `F` is the iteration cap and `M`
   the norm bound carried in `S`. The potential-contraction part of `DecoupleInv` stays a
   separate conjunct of `S`; whether it survives rounding is the rounded convergence question.
4. **Deflation.** `DeflationInv`'s `ε` accumulates `sub_single` (each zeroed subdiagonal adds
   `≤ τ`) and the backward errors of the block steps, lifted to the whole matrix by
   `exists_fromBlocks₁₁`/`₂₂` (after reindexing the range to a `Sum` split). The final theorem's
   `(N-1)·δ·frobNorm H` becomes `(N-1)·δ·frobNorm H + (blocks)·F·ν·M`.

## What is left

- The Givens backward-error analysis (a rounded rotation is the exact rotation of a perturbed
  pair, a sweep a perturbed unitary similarity, `c(n)` explicit), over a generic `Machine`.
- Rounded convergence: that the potential still contracts with rounding (BGS Part II), which
  needs the shift-strategy analysis under perturbation, not just backward errors.
- Lifting a step on a contiguous range of `Fin (n+1)` to the whole matrix through the `Sum`
  reindexing (`specNorm_submatrix_equiv` exists; `DeflationInv.conj` does the exact case).

## Open questions

1. **Norm.** Spectral only. The deflation bound of [BanksGarzaVargasSrivastava2022] is stated in
   the Frobenius norm. Recommendation: keep `specNorm` (it is what Bauer–Fike and `DeflationInv`
   use); add a Frobenius twin only when a consumer needs it.
2. **State-dependent budgets.** `BackwardStep` takes an additive `ε`; relative bounds go through a
   norm bound in `S`. Recommendation: keep it additive; a budget `ε : α → ℝ` complicates the loop
   rule and every consumer bounds the norm anyway.
3. **Frame forwarding in the loop rule.** `BackwardStep.loop` asks each round for a
   `BackwardStep` from any memory, so facts relative to the loop's initial memory (its position,
   its parameter words) must be stated in `S` with fixed values. Recommendation: accept; add a
   framed variant (as `writes_loop_frame_iterate`) only if a second consumer needs it.
4. **Operation-level backward contracts.** A `BlockRel` whose relation is "the output decodes to a
   perturbed similarity of the decoded input" would let a whole kernel be a declared primitive
   with a backward contract. Recommendation: not now; the shifted QR kernels are actual code, and
   a call already meets `BackwardStep` through `writes_call`.
5. **Placement of the generic relation.** `IsBackwardErrorRel` is pure order theory but lives in
   Ops because Ops imports only Mathlib and Ops. Recommendation: keep it there.
