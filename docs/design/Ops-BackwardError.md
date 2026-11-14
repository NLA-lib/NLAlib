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
| `.of_specNorm_sub_le` | `specNorm (B - Uᴴ * A * U) ≤ ε`, `U` unitary: error `ε` (kernel entry point) |
| `.of_near_unitary` | `specNorm (Û - U) ≤ η`, `U` unitary: `Ûᴴ * A * Û` with error `(2η + η²)·specNorm A` |
| `.sub_single`, `specNorm_single_le` | zeroing an entry of modulus `≤ δ` adds `δ` (deflation) |
| `.exists_submatrix` | a step on the principal block `A.submatrix e e` (`e` injective, e.g. a range of a partition) is a step on `A`, same error; entries off the block kept; block triangularity kept for any labelling constant on the block |
| `.submatrix_equiv` | relabelling the indices by a bijection |
| `.exists_fromBlocks₁₁`, `.exists_fromBlocks₂₂` | the two-block `Sum` case |
| `.specNorm_le` | `specNorm B ≤ specNorm A + ε` |
| `BackwardStep.writes_add` | continue from an accumulated error `e`: error `e + ε` |
| `BackwardStep.skip`, `.of_exact` | exact steps have error `0`; `skip` to any predicate implied by `S` |
| `BackwardStep.mono` | footprint, error, final predicate |
| `BackwardStep.seq` | errors add, footprints join |
| `BackwardStep.loop` | `N` rounds `i ↦ ε i`: error `∑ i ∈ range N, ε i` |
| `BackwardStep.loop_rel` | per-round error `ν·M` from `g a ≤ M`, `g` growing by at most the error: error `(1+ν)^N M₀ - M₀`, final `g ≤ (1+ν)^N M₀` |
| `BackwardStep.ite` | the test's outcome `T c` is passed to the arm `c`; both arms with `ε` |
| `BackwardStep.whileFuel` | outcome `T i true` to the round, `T i false` to the exit at round `i < N`, `S N` to the exit at the cap; rounds `ε i ≥ 0`, exit `ε'`: `∑ i ∈ range N, ε i + ε'` |
| `Ops.BackwardStep.of_unitarySimilar` | a `Writes` returning `∃ U B, HasOrthonormalCols U ∧ B = Uᴴ * A * U ∧ S' B m'` is a `BackwardStep … 0` |
| `Ops.BackwardStep.of_specNorm_sub_le` | a `Writes` returning `∃ U B, HasOrthonormalCols U ∧ specNorm (B - Uᴴ * A * U) ≤ ε ∧ S' B m'` is a `BackwardStep … ε` |

**Relative budgets (worked lemma `loop_rel`).** Part II charges each step
$\nu\,\boldsymbol{u}\,\|\mathbf{H}_k\|_2$. With `g := specNorm` and `hg :=
IsPerturbedUnitarySimilar.specNorm_le`, a kernel stated as `∀ M, BackwardStep … (S ∧ specNorm ≤
M) S' (ν * M)` composes over `N` rounds to error `((1+ν)^N - 1)·M₀` from `specNorm H ≤ M₀`,
and the final matrix keeps `specNorm ≤ (1+ν)^N M₀`. No consumer re-derives the geometric sum.

Examples (`NLAlib/Ops/Examples/Backward.lean`): three abstract steps in a loop of `N` rounds give
`N * (u + v + w)`; `backwardStep_loop_ite` (the shape of `decoupleRound` in a counted loop) and
`backwardStep_whileFuel_skip` (the shape of `worklistLoop`) give `N * u`, the skipped arm and the
exit using the outcome of the test.

**Do the revised rules reproduce Codex's exact loops?** Checked against 4e46b269 (read only).
`decoupleRound_writes` splits on `IsDecoupledAbs τ H`, feeds `I.test … = some b` to `writes_ite`,
and in the skip arm re-establishes `DecoupleInv … (j+1)` by `DecoupleInv.stopped … hdec`. With
`T j b H μ := ScanHolds H (τ^2) n r μ.store ∧ (b = true ↔ ¬IsDecoupledAbs τ H)` (obtained from
`hC.test_isZero` and `ScanHolds.flag_iff`), `htest` is `holds_testAt`, the true arm is
`IterationContract` + scan (via `of_unitarySimilar` after `shqrAcceptStep_exists_unitary`), and
the false arm is `skip` with `DecoupleInv.stopped` from `T j false`: exactly
`backwardStep_loop_ite`, error `0`. `worklistLoop_writes` exits through `writes_whileFuel` with
`get stack = some 0`: with `T j b μ := ∃ count, get stack = some count ∧ (b = true ↔ 0 < count)`,
the false exit gives `count = 0`, and the cap uses the invariant's progress measure (`hcap` from
`S N`): exactly `backwardStep_whileFuel_skip`. This is checked on paper and by the two examples,
not by re-proving Codex's files, which are not on `main`.

## Exact arithmetic is ν = 0

Codex's exact contracts end with `∃ U H', HasOrthonormalCols U ∧ H' = Uᴴ * H * U ∧ … ∧
HoldsMatrix w H' μ'.store`. Taking `S H μ` to be the preconditions (`IsUpperHessenberg H`,
`HoldsMatrix w H μ.store`, the parameter words, the geometry) and `S'` the remaining conjuncts,
`BackwardStep.of_unitarySimilar` turns `DecouplingContract` into
`BackwardStep … (fun ε A B => IsPerturbedUnitarySimilar A B ε) S S' 0` with no mathematics
(after moving its `μ'.pos = μ.pos` conjunct into `S'` with the position pinned).
`IterationContract` returns `HoldsMatrix w (shqrAcceptStep τ B θ α γ m H ss)`, not `Uᴴ H U`; it
needs `shqrAcceptStep_exists_unitary` (DeflationHypotheses.lean, with `U := 1`) first, one line.
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
   `≤ τ`, from the true outcome of the deflation test) and the backward errors of the block
   steps, lifted to the whole matrix by `exists_submatrix` with `e := blockIndex n r` (it keeps
   the other blocks and `BlockTriangular (rangeLabel …)`; the perturbed form of Codex's private
   `exists_embed_conj`). Better still, the hidden `M` of `DeflationInv` becomes the
   `BackwardStep` state and the rest of the invariant `S M m`, so the worklist is one
   `BackwardStep`. The final theorem's `(N-1)·δ·frobNorm H` gains the summed block errors.

## What is left

1. **Next step: the rounded Givens sweep as a `BackwardStep` over a generic `Machine`** with
   `StdModel`: coefficients from rounded data are a nearly unitary rotation (`of_near_unitary`),
   their application to two rows or columns gives componentwise errors bounded in `specNorm`
   through `frobNorm` (`of_specNorm_sub_le`), `n` rotations compose by `trans`, and the relative
   budget `c(n)·u·specNorm H` goes through `loop_rel`. This is the main mathematical work of the
   backward side; Codex's kernels are proved under `ExactModel id Mch` and have to be re-proved
   under a rounding model.
2. Retargeting `DeflationInv` onto `IsPerturbedUnitarySimilar` (and moving its spectral
   consequences, the characteristic polynomial and Bauer–Fike, onto the relation), with a
   vocabulary row, when the exact branch lands.
3. Rounded convergence: shifts and acceptance under rounding, the potential contraction absorbing
   the perturbation (BGS Part II). This is forward-error analysis, outside this design.

## Open questions (answered by review, Fable, 2026-11-14)

1. **Norm.** Keep `specNorm`: `trans` needs a unitarily invariant norm, a Frobenius twin would copy
   the file, and Part II's `δ·frobNorm H` is a scalar threshold, not a norm on `E`. No
   generalization over gauges.
2. **State-dependent budgets.** Keep `ε : ℝ` additive; relative budgets go through the ℕ-indexed
   `S` and a norm bound, now the worked lemma `loop_rel`.
3. **Frame forwarding.** Accept: Codex's posts already pin `pos` in `S`, and parameter words are
   read-only views pinned by value.
4. **Operation-level backward contracts.** Not now. The replacing pattern is a kernel's
   `BackwardStep` as a `Prop` parameter of the convergence theorem, as `IterationContract` is a
   parameter of the decoupling theorem (BGS Part II assumes a black-box backward-stable QR
   step); the Givens analysis and the rounded convergence proof are then independent.
5. **Placement of `IsBackwardErrorRel`.** Keep it in Ops; Mathlib has no graded relation to host it.

Watch item: when the first Ops kernel is proved as a `BackwardStep`, state once its implication to
an `IsQRErr`-style black box, so "backward-stable kernel" keeps one spelling.
