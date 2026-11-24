# A verified dense Schur solver (Las Vegas)

The dense Schur solver of [Eigensolvers-DenseSchur](Eigensolvers-DenseSchur.md) is Monte Carlo:
on a bad draw it may store flag $0$ with an inaccurate $\widehat{\mathbf{U}}$,
$\widehat{\mathbf{T}}$. A Schur form can be checked a posteriori, so this stage adds a residual
check whose acceptance is **sound on every tape**, and composes it with any Schur solver. The flag
then means "verified": flag $0$ implies the accuracy, with no probability. Only the chance of a
nonzero flag is probabilistic.

**Status: built** (single-shot). Every statement below is proved with no `sorry`. The retry loop
of §5 is designed, not built. Nothing in the checks, CI, the lakefile, the allowlists,
`*Targets.lean`, `docs/targets.*` or `scripts/ops_certificates.txt` changed. The check and the
certified solver are routines ([routines](../contributing/routines.md)); the pieces of the check
are fragments of its tree.

## 1. The check (a stage contract, solver-agnostic)

The routine `schurResidualCheck : [N] (A0 : read, U : read, T : update, P : read 2) →
(Fl : write 1)` with `P = [θ, κ]` (`Eigensolvers/Schur/ResidualCheck.lean`; blocks apart, draws
not declared because the norm-estimate contract does not state the tape position) runs four
fragments of its tree:

1. `zeroStrictLower [N] (T) → (T)`: the routine `fillRoutine` of the literal $0$ on each entry of
   the strict lower triangle, so the stored
   $\widehat{\mathbf{T}}$ is exactly upper triangular **whatever the solver did**
   (`zeroStrictLower_writes`: the block holds `upperPart T`);
2. `residualWords [N] (A0, U, T) → (D)`: $\mathbf{D} = \mathrm{fl}(\mathbf{A}_0 -
   \mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})\mathbf{U}^{\mathsf H}))$ with two `matMulOn`, the
   conjugate transpose `PairMatrix.conjTranspose` and an entrywise `sub` loop
   (`residualWords_writes`: `subWord M A₀ (matMulWord M (matMulWord M U T) Uᴴ)`);
3. `checkNorms [N] (A0, U, T, D) → (S)`: four `frobNormStage` norms
   $\hat r, \hat a, \hat w, \hat t$ (`checkNorms_writes`, from any `FrobNormEstimateContract`);
4. `checkDecide [] (S, P) → (S, Fl)`: the guard $\hat g = \mathrm{fl}(\mathrm{fl}(\mathrm{fl}(\hat
   w\hat w)\hat t)\kappa)$ (`checkGuard`), and flag $0$ iff $\mathrm{fl}(\hat r + \hat g) \le
   \mathrm{fl}(\hat a\theta)$ by the exact comparison `CmpTst.le`, else $1$.

**Every tape** (the judgment `schurResidualCheck_meets` against `schurResidualCheckSpec`, whose
postcondition is `ResidualCheckPost`; `schurResidualCheck_writes` reads it on the final memory for
the proofs of the verified solver): on a scalar machine with the standard model, index
literals and exact comparisons, from any stored $\mathbf{A}_0$, $\mathbf{U}$, $\mathbf{T}$ (no
hypothesis on them), the run writes only $\mathbf{T}$ and the flag and ends in
`ResidualCheckOutcome M c₁ c₂ θ κ A₀ U T t f`: the block holds `upperPart T`, and there are
estimates within $(c_1, c_2)$ of the four norms with the flag the literal $0$ iff the comparison
holds. With $(c_1, c_2) = (15/16, 17/16)$ (`frobNormStage_frobNormEstimateContract_check`):

```lean
theorem ResidualCheckOutcome.frobNorm_sub_le (hM : StdModel u id M)
    (h : ResidualCheckOutcome M (15 / 16) (17 / 16) θ κ A₀ U T t f μ')
    (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) (hκ : 32 * ((N : ℝ) + 1) ^ 2 * u ≤ κ) (hθ : 0 ≤ θ)
    (h0 : μ'.store.get f.1 f.2 = some 0) :
    frobNorm (A₀ - U * upperPart T * Uᴴ) ≤ 2 * θ * frobNorm A₀

theorem ResidualCheckOutcome.flag_eq_zero (hM : StdModel u id M)
    (h : ResidualCheckOutcome M (15 / 16) (17 / 16) θ κ A₀ U T t f μ')
    (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 64 * ((N : ℝ) + 1) ^ 2 * u)
    (hθ1 : θ ≤ 1) (huθ : 4096 * ((N : ℝ) + 1) ^ 3 * u ≤ θ) (hUU : specNorm (Uᴴ * U - 1) ≤ 1 / 2)
    (hR : frobNorm (A₀ - U * upperPart T * Uᴴ) ≤ θ / 8 * frobNorm A₀) :
    μ'.store.get f.1 f.2 = some 0
```

Soundness accounts for every rounding of the check: the product error is at most
$24(N + 1)^2\boldsymbol{u}\|\mathbf{U}\|_{\mathsf F}^2\|\mathbf{T}\|_{\mathsf F}$
(`StdModel.frobNorm_matMulWord_conjTranspose_sub_le`) and the guard dominates it; the subtraction
errs by $\boldsymbol{u}\|\cdot\|_{\mathsf F}$ (`StdModel.frobNorm_subWord_sub_le`). Completeness uses
$(1 - e)^2\|\mathbf{T}\|_{\mathsf F} \le (1 + e)\|\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F}$
for $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e \le 1$
(`frobNorm_le_of_specNorm_conjTranspose_mul_self_sub_one_le`).

Junk values. $N = 0$: empty matrices, all norms $0$, the comparison $0 \le 0$ holds, the bound is
$0 \le 0$. $\mathbf{A}_0 = 0$: $\hat a = 0$, the flag is $0$ only if $\hat r = \hat g = 0$, and then
$\mathbf{U}\mathbf{T}'\mathbf{U}^{\mathsf H} = 0$ exactly; the comparison is exact and non-strict,
so the exact zero output of the solver on $\mathbf{A} = 0$ passes. No division anywhere.

**Cost** (`size_stmtCost_schurResidualCheck_le`): $1619(n + 1)^3$; the monomial computed by
`kernel_rfl` is $1616(n + 1)^3$.

## 2. The verified solver (generic)

`verifiedSchurWith Solve : [N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`
(`Eigensolvers/Schur/Verified.lean`, a tree over the stage `Solve`, as the pipeline is): copy
$\mathbf{A}$ into scratch by the routine `PairMatrix.copyRoutine`, run `Solve` on its
$n_r + n_q$ words `P[0]`, …, then the check on the copy, $\widehat{\mathbf{U}}$,
$\widehat{\mathbf{T}}$ and the words $\theta, \kappa$ at `P[nr + nq]`. The check's words come
**after** the solver's, so the solver runs at the offsets of its own work bounds.

**(a) Every tape** (`verifiedSchurWith_writes`): for any `Solve` with
`TerminatingSchurSolver eU n d qs Solve I` (terminates on every tape, frame of the pipeline,
`SchurOrth`), $64(n + 2)^3\boldsymbol{u} \le 1$, $\kappa \ge 32(n + 2)^2\boldsymbol{u}$,
$\theta \ge 0$, $2\theta\sqrt{n + 1} \le \delta$ and `qs.length = nr + nq`, from
`SchurPipelineInput (qs ++ [θ, κ])`, the run terminates on every tape in
`VerifiedSchurOutput M a uo f A δ eU`: `SchurOrth`, the flag $0$ or $1$, and flag $0$ ⇒
`SchurOutput a uo f A δ eU` ($\widehat{\mathbf{T}}$ upper triangular,
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$, orthogonality $e_U$). No probability.

**(b) Probability, for any solver postcondition** (`verifiedSchurWith_measureReal_not_flag_le`,
the form requested by the eigendecomposition design, O9): if from every input the solver ends in a
postcondition `Post` except with probability $\varphi$, where `Post` is measurable with its frame,
implies `SchurOutput a uo f A δ' eU`, is kept when only the flag is rewritten to $0$ and is kept by
the release of scratch, then $\mathbb{P}[\neg(\text{flag } 0 \wedge \texttt{Post})] \le \varphi$,
under $e_U \le 1/2$, $\sqrt{n + 1}\,\delta' \le \theta/8$, $0 \le \kappa \le
64(n + 2)^2\boldsymbol{u}$, $\theta \le 1$, $4096(n + 2)^3\boldsymbol{u} \le \theta$. A later stage
that needs more of the solver's output (the regularized matrix) instantiates `Post`.

**(c) Work** (`size_stmtCost_verifiedSchurWith_le`): the solver's count plus
$1619(n + 1)^3 + 32(n + 1)^2 + 64$.

## 3. The instance

`verifiedSchur sG = verifiedSchurWith (denseSchur sG)` (`VerifiedDense.lean`), with
`verifiedSchurParams u n δ φ = denseSchurParams n δ_int φ ++ [θ, κ]`,
$\delta_{\mathrm{int}} = \delta/(16(n + 1))$, $\theta = \delta/(2\sqrt{n + 1})$,
$\kappa = 32(n + 2)^2\boldsymbol{u}$ (the word depends on the machine's unit roundoff), and
`uVerifiedSchur n δ φ = min (uDenseSchur n δ_int φ) (θ/(4096(n + 2)^3))`.

* `verifiedSchur_writes` (Result: verified-schur-every-tape): on every tape, flag $0$ ⇒
  $\widehat{\mathbf{T}}$ upper triangular, $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
  \widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2$, and always
  $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}$.
* `verifiedSchur_measureReal_not_schur_le` (Result: verified-schur-failure):
  $\mathbb{P}[\text{flag} \ne 0 \text{ or no Schur output at } \delta_{\mathrm{int}}] \le \varphi$.

The budget: the internal run has $\|\mathbf{R}\|_2 \le \delta_{\mathrm{int}}\|\mathbf{A}\|_2$, so
$\|\mathbf{R}\|_{\mathsf F} \le \sqrt{n + 1}\,\delta_{\mathrm{int}}\|\mathbf{A}\|_{\mathsf F} =
(\theta/8)\|\mathbf{A}\|_{\mathsf F}$ and the check passes; a pass gives
$\|\mathbf{R}\|_2 \le \|\mathbf{R}\|_{\mathsf F} \le 2\theta\|\mathbf{A}\|_{\mathsf F} \le
2\theta\sqrt{n + 1}\|\mathbf{A}\|_2 = \delta\|\mathbf{A}\|_2$. The completeness constant against
the 2-norm tolerance is $c = 1/(16(n + 1))$ (two Frobenius/2-norm conversions); the bits grow by
$O(\log(n/\delta))$.

## 4. The certificate (`VerifiedCertificate.lean`)

The routine `verifiedSchurRoutine sG` (`verifiedSchurWithRoutine` around `denseSchur sG`) meets
`verifiedSchurSpec` (`verifiedSchurRoutine_meets`, whose postcondition `VerifiedSchurPost` is the
flag-conditional Schur form on the blocks written). `verifiedSchurAlgorithm Mch hM admitted sU sG`
is `Routine.Domain.algorithm` of that judgment over `smallEigModel`, with
`StdModel u id Mch` a parameter of the certificate. The problem is derived from
`verifiedSchurInputs`, which accepts an input
$(\mathbf{A}, \delta, \varphi)$ with $0 < \delta, \varphi \le 1$ and $\boldsymbol{u} \le$
`uVerifiedSchur` (the acceptance predicate) and holds the words computed from
$(\delta, \varphi)$ in a derived slot. `verifiedSchur_checked` states the certificate. `S.good` is
**the flag-conditional statement**: the frame, and flag $0$ ⇒ `SchurOutput` of the input matrix at
its $\delta$. Work and span `verifiedSchurWork` $= 384547(n+1)^3(k+1)^4(n_r+n_q+1)(F+1)(T+1)^2 +
1619(n+1)^3 + 32(n+1)^2 + 128$ (`verifiedSchur_work_le`,
`size_staticCost_verifiedSchurProgram_le`). The probability on one counted run:
`verifiedSchur_algorithm_measureReal_not_accepts_le` (Result: verified-schur-certificate), and as
the randomized claim of the certificate `verifiedSchurClaim` (independent tape entries, uniform
on $s_U$ and standard Gaussian on $s_G$, realizable for $s_U \ne s_G$; failure at most $\varphi$).

## 5. Retries (designed, not built)

`verifiedSchurRetryWith Solve : [N, …, R]`: set the flag to $1$; `whileFuel R (isPos Fl)` of
(copy back, solve, check). (a) holds on every tape by the same invariant. The product bound
$\mathbb{P}[\text{flag} \ne 0] \le \varphi^R$ needs a new Ops rule: the existing
`PStep.measure_exists_bind_bad_le` bounds $\mathbb{P}[\text{second step bad}]$ by $\varphi_2$ via the
strong Markov property at the random end position $q$ of the first step; restricting each event of
that proof to the past-measurable event "first step ended with flag $\ne 0$" gives
$\mathbb{P}[\text{first bad} \wedge \text{second bad}] \le \varphi_2\,\mathbb{P}[\text{first bad}]$,
and induction over the `whileFuel` rounds gives $\varphi^R$. Independence comes from the tape law
(fresh windows after the random stopping position), not from the program. The existing
`PWrites.whileFuel` only gives the union bound, useless here.

## 6. Changes to merged material

* `SchurOrth` gains the matrix block: `SchurOrth a uo eU` also states that the block of
  $\mathbf{A}$ holds a matrix (`Pipeline.lean`: `schurPipeline_pos_terminates`,
  `schurPipelineWith_terminates`; `Dense.lean`: `denseSchur_writes_orth`, `denseSchur_terminates`).
  A strengthening; the check needs the words of $\widehat{\mathbf{T}}$ initialized.

## 7. Shared machinery added

`PWrites.of_measureReal_le` (a per-memory failure bound with a measurable outcome is a
`PWrites` from that memory; candidate for `Ops/Logic/ProbabilisticFamily`, placed in
`Verified.lean` to avoid rebuilding the library low in the graph), `StdModel.mul_bounds`,
`StdModel.add_bounds`, `StdModel.frobNorm_subWord_sub_le`,
`StdModel.frobNorm_matMulWord_conjTranspose_sub_le`, `conjTranspose_writes_holdsMatrix`,
`writes_loop_sub_cells`, `HoldsMatrix.get_eq`, `SchurPipelineInput.of_below`,
`SchurPipelineInput.head`, `upperPart`, `subWord`.
