# A verified dense Schur solver (Las Vegas)

The dense Schur solver of [Eigensolvers-DenseSchur](Eigensolvers-DenseSchur.md) is Monte Carlo:
on a bad draw it may store flag $0$ with an inaccurate $\widehat{\mathbf{U}}$,
$\widehat{\mathbf{T}}$. A Schur form can be checked a posteriori, so this note adds a residual
check whose acceptance is **sound on every tape**, and composes it with any Schur solver. The flag
then means "verified": flag $0$ implies the accuracy, with no probability. Only the chance of a
nonzero flag is probabilistic.

## 1. The check (a stage contract, solver-agnostic)

`schurResidualCheck : [N] (A0, U, T, P) → (T, Fl)`, with `P = [θ, κ]`:

1. zero the strict lower triangle of $\mathbf{T}$ (`zeroStrictLower`), so the stored
   $\widehat{\mathbf{T}}$ is exactly upper triangular **whatever the solver did**;
2. $\mathbf{D} = \mathrm{fl}(\mathbf{A}_0 - \mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})
   \mathbf{U}^{\mathsf H}))$ (`residualWords`: two `matMulOn`, the conjugate transpose
   `PairMatrix.conjTranspose`, an entrywise `sub` loop);
3. the rounded Frobenius norms $\hat r, \hat a, \hat w, \hat t$ of $\mathbf{D}, \mathbf{A}_0,
   \mathbf{U}, \mathbf{T}$ (`frobNormStage`);
4. the guard $\hat g = \mathrm{fl}(\mathrm{fl}(\mathrm{fl}(\hat w\hat w)\hat t)\kappa)$, a
   computed upper bound for the rounding of the two products;
5. flag $0$ iff $\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\hat a\theta)$ (exact comparison
   `CmpTst.le`), else $1$.

Cost $O(N^3)$ (the two products), scratch $6N^2 + 4$ words.

**Contract, every tape** (`schurResidualCheck_writes`). Standard model at $\boldsymbol{u}$ with
$64(N + 1)^3\boldsymbol{u} \le 1$, $32(N + 1)^2\boldsymbol{u} \le \kappa$, $0 \le \theta$; any
stored $\mathbf{A}_0, \mathbf{U}, \mathbf{T}$ (no hypothesis on them):

```lean
Writes .total I τ schurResidualCheck.body (Env.frame [N] [a0, uo, t, p, t, f])
  (Store.inBlock t.1 t.2 (2 * (N * N)) ⊔ Store.inBlock f.1 f.2 1)
  (fun μ' => ∃ T' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix t T' μ'.store ∧
    T'.IsUpperTriangular ∧ (∀ i j, i ≤ j → T' i j = T i j) ∧
    (μ'.store.get f.1 f.2 = some 0 ∨ μ'.store.get f.1 f.2 = some 1) ∧
    (μ'.store.get f.1 f.2 = some 0 →
      frobNorm (A₀ - U * T' * Uᴴ) ≤ 2 * θ * frobNorm A₀)) μ
```

The soundness accounts for every rounding of the check: $\|\mathbf{R}\|_{\mathsf F} \le
(\hat r + \hat g)/(c_1(1 - \boldsymbol{u}))$ up to constants, since the product error is at most
$24(N+1)^2\boldsymbol{u}\|\mathbf{U}\|_{\mathsf F}^2\|\mathbf{T}\|_{\mathsf F} \le \hat g$.

**Completeness** (`schurResidualCheck_flag_zero`): if moreover $\|\mathbf{U}^{\mathsf H}\mathbf{U}
- \mathbf{I}\|_2 \le 1/2$, $\mathbf{T}$ is upper triangular, $\theta \le 1$,
$\kappa \le 64(N+1)^2\boldsymbol{u}$, $2048(N + 1)^3\boldsymbol{u} \le \theta$ and
$\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F} \le
(\theta/8)\|\mathbf{A}_0\|_{\mathsf F}$, the flag is $0$ (and $\mathbf{T}' = \mathbf{T}$).

Junk values. $N = 0$: empty matrices, all norms $0$, flag $0$, the bound is $0 \le 0$.
$\mathbf{A}_0 = 0$: $\hat a = 0$; the flag is $0$ only if $\hat r = \hat g = 0$, and the soundness
then gives $\mathbf{U}\mathbf{T}'\mathbf{U}^{\mathsf H} = 0$ exactly. The comparison is exact and
non-strict, so the exact zero output of the solver on $\mathbf{A} = 0$ passes.

## 2. The verified solver

`verifiedSchurWith Solve : [N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`: copy $\mathbf{A}$ into a
scratch $\mathbf{A}_0$, run `Solve` on `P[2]` (any program with the interface of the pipeline), run
the check on `(A0, U, A, P[0])`. `verifiedSchur sG` is the instance with `denseSchur sG` run at the
internal tolerance $\delta_{\mathrm{int}} = \delta/(16(n+1))$.

**(a) Every tape** (`verifiedSchurWith_writes`, generic): any solver that terminates on every tape
writing only $\mathbf{A}$, $\widehat{\mathbf{U}}$, the flag and storing $\widehat{\mathbf{U}}$ with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le e_U$ (`SchurOrth`);
then the verified run terminates and, if it stores flag $0$, `SchurOutput a uo f A δ eU`
($\widehat{\mathbf{T}}$ upper triangular, $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2$, orthogonality $e_U$), with
$\theta = \delta/(2\sqrt{N})$. No probability.

**(b) Probability** (`verifiedSchurWith_measureReal_flag_ne_zero_le`): if the solver also
satisfies `SchurOutput a uo f A δ' eU` with probability $\ge 1 - \varphi$, $\delta' \le
\theta/(8\sqrt N)$, $e_U \le 1/2$ and the precision condition of completeness, then
$\mathbb{P}[\text{flag} \ne 0] \le \varphi$.

**Retries** (`verifiedSchurRetryWith Solve : [N, …, R]`): the attempt (copy back, solve, check) runs
in a `whileFuel` loop of at most $R$ rounds while the flag is positive. (a) holds on every tape.
$\mathbb{P}[\text{flag} \ne 0] \le \varphi^R$, by a new Ops rule (`PStep` with a product bound): the
attempt $i + 1$ starts at the random end position of attempt $i$, and by the strong Markov
property of the tape (`IsTapeLaw.measure_past_shift_mem`) its failure is independent of the past;
the failure events multiply, not add.

**Precision.** `uVerifiedSchur n δ φ = min (uDenseSchur n δ_int φ) (δ/(4096 √(n+1) (n+2)^3))`,
$\delta_{\mathrm{int}} = \delta/(16(n+1))$: the internal run has $\|\mathbf{R}\|_2 \le
\delta_{\mathrm{int}}\|\mathbf{A}\|_2$, hence $\|\mathbf{R}\|_{\mathsf F} \le \sqrt N
\delta_{\mathrm{int}}\|\mathbf{A}\|_{\mathsf F} = (\theta/8)\|\mathbf{A}\|_{\mathsf F}$, and the
check passes. The bits grow by $O(\log(n/\delta))$ only. The completeness constant is
$c = 1/(16N)$ relative to the 2-norm tolerance (the two Frobenius/2-norm conversions).

**(c) Work.** Static count of the verified program = the solver's + $O(N^3)$ (the products) per
attempt; with retries, $R$ times that.

**(d) Certificate** (`verifiedSchurAlgorithm`): `Algorithm.ofWp` over `smallEigModel`, with
`S.good` the flag-conditional statement `flag = 0 → SchurOutput …`. Its every-tape proof needs the
standard model of the machine, which the specification takes as a parameter (`StdModel u id Mch`)
with $64(N+1)^3\boldsymbol{u} \le 1$ among the admitted sizes.

## 3. Placement and shared machinery

* `Eigensolvers/Schur/ResidualCheck.lean`: `zeroStrictLower`, `residualWords`,
  `schurResidualCheck`, their writes lemmas, soundness and completeness.
* `Eigensolvers/Schur/Verified.lean`: the generic verified solver, the instance, the bounds.
* `Ops/Logic/Probabilistic...`: the repetition rule.
