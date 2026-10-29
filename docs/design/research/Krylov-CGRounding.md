# Design note (research): the Hestenes–Stiefel CG program in finite precision

2026-10-29. Branch `research/hscg-fp` (from `design/lanczos-fp` @ 8ec9b88). **Status: RESEARCH**
(open question for the maintainer; nothing goes to `main` until the whole chain is proved).
Mathematical source: `docs/design/research/HSCG-FiniteP.md` (= harness
`reports/HSCG-FP-Research.md`, "the report" below). Precedent:
`docs/design/Krylov-LanczosRounding.md`. Decision sheet: harness `state/decisions/CG-FP.json`
(ids CG1–CG7 below).

## Summary

* **Program** (§1): textbook HSCG from $\mathbf x_0=\mathbf 0$ in the model of computation, product a
  parameter (oracle `cgProg` / `gemv` twin `cgDenseProg`), exact test $\nu_j = \mathrm{fl}(\|\mathbf r_j\|^2) = 0$
  before each step (stop; $k$ = steps taken, read off the outputs), **no test on
  $\mu_j=\mathrm{fl}(\mathbf p_j^{\mathsf T}\mathbf A\mathbf p_j)$**: its positivity is a theorem.
  Exact spec against `cgState` (§1.4).
* **Headline** (§2, §8): for symmetric $\mathbf A$ with spectrum in $[a,a']$, $a>0$,
  $\kappa=a'/a$, standard model, $\varepsilon=\max(\varepsilon_{\rm mv},\gamma_{N+2}(u))$, and
  $$\text{(H)}\qquad q^3\,\varepsilon\,\kappa^2\le 10^{-5},$$
  the run **succeeds** (every division is by a positive number), and with $k\le q$ the steps taken
  there is a symmetric $\tilde{\mathbf H}$ of size $N(k+1)$, spectrum in $[a/2,\,a'+a/2]$,
  $$\|\tilde{\mathbf H}-\mathbf I_{k+1}\otimes\mathbf A\|_F\le 4\cdot10^4\,k^3\,\varepsilon\,\kappa\,a'\ (\le a/2),$$
  on which exact CG from $(\mathbf b,\mathbf 0,\dots)$ computes the computed step lengths
  $\gamma_j$ **exactly** and residuals of **exactly** the computed residual norms
  $\|\mathbf r_j\|$; exact Lanczos computes $\mathbf T_k=\mathbf L\,\mathrm{diag}(\gamma^{-1})\mathbf L^{\mathsf T}$.
  The report's (H′) $\varepsilon k^5\kappa^2\le 1/(8.4\cdot10^5)$ and bound $4.2\cdot10^5k^5\varepsilon\kappa\|\mathbf A\|$
  improve to $k^3$ through the slimmer interface (§4.3): the CG recurrence residual does not grow
  with $j$.
* **Range** (§8): (H) restricts $k\le(10^{-5}/\varepsilon\kappa^2)^{1/3}$; in double precision this is
  $k\lesssim30$–$100$ for $\kappa=10$ and vacuous for $\kappa=10^3$ (constants unoptimised; $\kappa^2$
  intrinsic). The a posteriori form has no such limit.
* **A posteriori theorem** (§6) kept: the same model with explicit run certificates
  $\Pi,K,B$, no $\kappa$; it is the induction engine.
* **Errors** (§9, new part): exact CG on the model has $\tilde{\mathbf H}$-norm error decrements
  *exactly* $\sum\gamma_i\|\mathbf r_i\|^2$ (the Strakoš–Tichý estimator is exact for the model), its
  error at $k$ is $\|\mathbf x_\star\|_{\mathbf A}^2-\|\mathbf b\|^2(\mathbf T_k^{-1})_{00}$ up to
  $2\|\mathbf b\|^2c/a^2$, and the computed residual norms converge at the Chebyshev rate of
  $2\kappa+1$. Residual gap (local, $\kappa$-free) this round. The computed run's own
  $\|\mathbf x_\star-\mathbf x_k\|_{\mathbf A}$ (a rigorous Strakoš–Tichý Thm 10.1) recommended
  **next round**, statements in §9.4.
* **Skeleton**: 6 scaffold files, 61 sorried statements (all typecheck; `check_rules` clean;
  `check_constants` clean). Size estimate ≈ 5.3k lines (§10). Revised after the Fable review
  (harness `reports/CG-FP-Review.md`, accept with changes): dispositions in §12.

---

## 1. The program

### 1.1 Step (0-based $j$; vectors in five slots of length $N$)

| line | operation | kernel | `CGRun` clause |
|---|---|---|---|
| 1 | $\mathbf s\leftarrow\mathbf A\mathbf p_j$ | `mv` (oracle `apply` / `gemv`) | `s_eq`, `norm_es_le` |
| 2 | $\mu\leftarrow\mathbf p_j^{\mathsf H}\mathbf s$ | `dot` | `μ_eq`, `abs_eμ_le` ($\gamma_N$, Cauchy–Schwarz) |
| 3 | $\gamma_j\leftarrow\nu/\mu$, copy out | `bin .div` | `γ_eq`, `abs_eγ_le` ($u$) |
| 4 | $\mathbf x\leftarrow\gamma_j\mathbf p_j+\mathbf x$ | `axpy` | `x_succ`, `norm_ex_le` ($\gamma_2$) |
| 5 | $t\leftarrow-\gamma_j$; $\mathbf r\leftarrow t\mathbf s+\mathbf r$ | `un .neg` (exact), `axpy` | `r_succ`, `norm_er_le` |
| 6 | $\nu'\leftarrow\mathbf r^{\mathsf H}\mathbf r$ | `dot` | `ν_eq`, `abs_θ_le` (product form, $\gamma_N$) |
| 7 | $\delta_j\leftarrow\nu'/\nu$, copy out | `bin .div` | `δ_eq`, `abs_eδ_le` |
| 8 | $\mathbf p'\leftarrow\mathbf r$; $\mathbf p'\leftarrow\delta_j\mathbf p_j+\mathbf p'$ | `copyv` (exact), `axpy` | `p_succ`, `norm_ep_le` |
| 9 | $\nu\leftarrow\nu'$, copy out | `copy` | — |

Start: $\mathbf x\leftarrow\mathbf 0$ (literals), $\mathbf r\leftarrow\mathbf b$, $\mathbf p\leftarrow\mathbf b$
(`copyv`, exact), $\nu_0\leftarrow\mathbf b^{\mathsf H}\mathbf b$. Loop $j<q$: **if $\nu=0$** (exact
`cmp .eq` against a literal 0) write $\gamma_j=\delta_j=\nu_{j+1}=0$, else the step. Output
$\mathbf x$. Direction slots rotate ($3N+N(j\bmod2)$). Memory $5N+7$. The direction update is
copy-then-axpy (two roundings, $\gamma_2$) because `axpy` updates its second argument; a
`scal`+`axpy` variant would cost $\gamma_3$.

Why $\mathbf x_0=\mathbf 0$ (CG5): $\mathbf r_0=\mathbf b$ is then exact, the model's start is exactly
$\mathbf b/\|\mathbf b\|$ (Lanczos had $c\mathbf v_1=\mathbf b+\boldsymbol\delta_0$), the gap starts at $0$,
and `cgState A b 0` / `cgIterate A b 0` are the exact objects. A general $\mathbf x_0$ adds one
`gemv` and an initial gap term; nothing else changes.

### 1.2 Lean shape (`NLAlibScaffold/Krylov/LinearSystems/CGProgramTree.lean`, typechecks)

```lean
def cgStepWith (mv) (p) (N) (W) (pc pn) (sc) (gamCell delCell nuCell) := do
  mv W pc (2 * N);  dot p ⟨sc,1⟩ W pc W (2 * N) N
  ins (.bin p .div ⟨sc,2⟩ ⟨sc,0⟩ ⟨sc,1⟩);  ins (.copy p gamCell ⟨sc,2⟩)
  axpy p ⟨sc,2⟩ W pc W 0 N;  ins (.un p .neg ⟨sc,6⟩ ⟨sc,2⟩);  axpy p ⟨sc,6⟩ W (2 * N) W N N
  dot p ⟨sc,4⟩ W N W N N;  ins (.bin p .div ⟨sc,5⟩ ⟨sc,4⟩ ⟨sc,0⟩);  ins (.copy p delCell ⟨sc,5⟩)
  copyv p W N W pn N;  axpy p ⟨sc,5⟩ W pc W pn N
  ins (.copy p ⟨sc,0⟩ ⟨sc,4⟩);  ins (.copy p nuCell ⟨sc,0⟩)
def cgProgWith (mv) (p) (N q) (b X gam del nu) := …  -- init, forRange q (ifThenElse ν = 0 …), copy x
def cgProg (p) (o) := cgProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p
def cgDenseProg (p) (N q) (A …) := cgProgWith (fun W src dst => gemv p N N A 0 W src W dst) p N q …
```
Placement (CG7): `Krylov/LinearSystems/` (CG is a solver; the Lanczos program is in
`Krylov/Processes/`). Moves to `NLAlib/` when targets are registered (rule E4), as for Lanczos.

### 1.3 Breakdown (CG1, maintainer requirement 1)

The only partial operations are the two divisions (`IsRelErrSem.bin_ok` needs a nonzero
divisor; `safe = True`, no overflow).

* **Division by $\nu_j$**: tested. $\nu_j=\|\mathbf r_j\|^2(1+\theta_N)$ with $1+\theta_N\ge(1-u)^N>0$
  (product form of `dot`), so $\nu_j=0\iff\mathbf r_j=\mathbf 0$ (`CGRun.ν_eq_zero_iff`): the program
  stops exactly when the *updated* residual is exactly zero, and later outputs are $0$ (as
  `cgStep`'s junk values).
* **Division by $\mu_j$**: not tested. **Theorem**: under (H) and $\nu_j>0$, $\mu_j>0$. Chain:
  (i) $\|\mathbf r_j\|\le2\|\mathbf p_j\|$ (`CGRun.norm_r_le_two_mul_norm_p`, from the line-search
  defect $|\mathbf p_{j-1}^{\mathsf T}\mathbf r_j|$ of Lemma B′ and
  $\|\mathbf r_j+\delta\mathbf p_{j-1}\|^2=\rho_j^2+\delta^2\|\mathbf p_{j-1}\|^2+2\delta\tau_{j-1}$, certificates of
  steps $<j$ only); (ii) $\mu_j\ge(a-2.1\varepsilon a')\|\mathbf p_j\|^2>0$
  (`dotProduct_add_pos_of_spectrum_subset_Icc`). Hence $\gamma_j>0$, $\delta_j\ge0$.
* So the bridge is an **induction over iterations interleaved with the analysis of the prefix
  run**. The invariant is built forward (it must not presuppose the final run): for $m=0$ the
  state decodes to $\mathbf x_0=\mathbf 0$, $\mathbf r_0=\mathbf p_0=\mathbf b$, $\nu_0$ (there is no
  `CGRun N 0`: `k_pos`), and $\mathbf p_0=\mathbf b\ne\mathbf 0$ gives $\mu_0>0$ directly; for $m\ge1$
  there is `R : CGRun N (min m k)` decoding the state, extended each iteration by re-packaging
  its ~30 fields with the step-$m$ data and re-proving `k_mul_ε_le`; the a priori certificates of
  `R` give $\mathbf p_m\ne\mathbf 0$, so iteration $m$ succeeds.

Alternatives. (b) Add a guard `if μ ≤ 0 then stop` (`cmp .le` is exact): the bridge becomes
unconditional and independent of the analysis (exactly the Lanczos pattern), and the analysis
proves the guard never fires under (H). Costs one comparison and departs from textbook HSCG.
Fallback if the interleaved induction is awkward in Lean (trigger: it costs > 300 lines over the
Lanczos template); statement unchanged except a "stop reason" conjunct. Decision CG1 = (a),
with (b) kept as the named fallback. (c) Hypothesis "no breakdown" — rejected (a condition on the run). (d)
`whileFuel` with $k$ written out — same as Lanczos L1(b), not needed.

### 1.4 Exact specification

`exec_cgProg_exactInterp` (sorry): for `A.PosDef` over $\Bbbk$ and every $\mathbf b$, the run
succeeds, `X` $=\mathbf x_q$ of `cgState A b 0`, `gam[j]` $=$ `cgAlpha A (cgState A b 0 j)`,
`del[j]` $=\|\mathbf r_{j+1}\|^2/\|\mathbf r_j\|^2$, `nu[j]` $=\|\mathbf r_j\|^2$. Positive definiteness is
needed (division by $\mathbf p^{\mathsf H}\mathbf A\mathbf p$); at and past the grade both skip with zeros.
New name `cgAlpha` (the `let α` of `cgStep`, made a definition; `cgStep_x` is `rfl`). ≈600 lines
(loop invariant over five slots, rotation as in Lanczos).

## 2. The bridge (`CGRounding.lean`)

### 2.1 Statements

```lean
noncomputable def cgSteps (ν : ℕ → ℝ) (q : ℕ) : ℕ   -- first j < q with ν j = 0, else q
noncomputable def cgRoundingEps (N : ℕ) (u εmv : ℝ) : ℝ := max εmv (roundingFactor (N + 2) u)
def CGOutputs st p dec X gam del nu q x γ δ ν : Prop      -- buffers decode
def HasCGRunOutputs st p dec ε X gam del nu q A b : Prop :=
  ∃ x γ δ ν, CGOutputs … ∧ (outputs after the stop are 0) ∧
    ∃ R : CGRun N (cgSteps ν q), R.A = A ∧ R.b = b ∧ R.ε = ε ∧ (γ, δ, ν agree) ∧
      R.x k = x ∧ (k < q → R.r k = 0)
theorem IsRelErrSem.exists_cgRun_of_cgProg (I p o) (h : IsRelErrSem u dec ⊤ I.sem)
    (hz : AddsZeroExactly dec I.sem) (q) (A) (hA : Aᵀ = A) (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (hmv : IsMatvecErr I o dec p A (εmv * specNorm A))
    (b) (hb : dec ∘ b ≠ 0) (hq : 0 < q) (hu : (N + 2) u < 1)
    (hsmall : q ^ 3 * cgRoundingEps N u εmv * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ st', exec I (cgProg …).run (inputState …) = some st' ∧ HasCGRunOutputs st' … q A (dec ∘ b)
```
plus `cgProg_matrixFreeRounded` (instance of `MatrixFreeRounded`, decision L7 of Lanczos),
`exists_cgRun_of_cgDenseProg` ($\varepsilon_{\rm mv}=\sqrt N\gamma_N$, every hypothesis on data, sizes,
$u$), `HasCGBackwardModel` and `exists_cgBackwardModel_of_cgDenseProg` (end to end).

Unlike Lanczos the bridge needs the spectral hypothesis: it is what makes $\mu_j>0$ (success)
provable. Without it success is false in general (indefinite $\mathbf A$).

### 2.2 Clause by clause

| clause | bound | from | status |
|---|---|---|---|
| `s_eq`, `norm_es_le` | $\varepsilon_{\rm mv}\|\mathbf A\|\|\mathbf p\|$ / $\sqrt N\gamma_N$ | `IsMatvecErr` / `exec_gemv_abs_mulVec_sub_le` + `norm_toLp_map_abs_mulVec_abs_le` | exists |
| `μ_eq`, `abs_eμ_le` | $\gamma_N\|\mathbf p\|\|\mathbf s\|$ | `exec_dot_abs_sum_mul_sub_le` + C–S (`sum_abs_mul_abs_le_norm`, LanczosStep) | exists |
| `γ_eq`, `δ_eq` | $u$ | `IsRelErrSem.bin_err` (`.div`) | immediate |
| `ν_eq`, `abs_θ_le` | $\gamma_N$ | `exec_dot_eq_sum_mul_one_add_isRoundingProduct` + weighted mean (`exists_isRoundingProduct_sum_mul_one_add_eq`), as Lanczos' near-unit proof | exists |
| `x_succ`, `r_succ`, `p_succ` | $\gamma_2$ | `IsRelErrSem.exec_axpy`, `exec_neg_axpy` (LanczosStep), `exec_copyv` | exists |
| `ν_pos` | $j<k$: $\nu_j\ne0$ by def. of $k$, $\ge0$ | `cgSteps` | immediate |
| `μ_pos` | §1.3 | analysis of the prefix | **interleaved** |
| `k_mul_ε_le` | (H) ⇒ $q\varepsilon\le10^{-5}$ | — | immediate |

Reused from the Lanczos scaffold: `LanczosMvSpec` (rename `MvSpec` on integration),
`StoreFrame`, `DecVec`, `DecCell`, `BlockUpd`, `SeqShape`, `exec_dot_re_copy`-style lemmas,
`exec_neg_axpy`. New run lemmas: `bin .div` with a decoded nonzero divisor (S), the skip branch
writing literal zeros (S).

## 3. The interface `CGRun` (`FinitePrecision/CGRun.lean`)

0-based, as `cgState` and the program: fields $\mathbf A,\mathbf b,\mathbf x,\mathbf r,\mathbf p,\mathbf s,\nu,\mu,\gamma,\delta$,
the eight errors ($\mathbf e^s,\theta,e^\mu,\eta^\gamma,\mathbf e^x,\mathbf e^r,\eta^\delta,\mathbf e^p$), $\varepsilon$, and the
clauses of §2.2; `k_pos`, `k_mul_ε_le`, `x_zero`, `r_zero = b`, `p_zero = b`, `ν_pos`, `μ_pos`. The
iterate and its error are fields now (they are not used by the backward model, only by §9) so
that the error-relation part needs no refactor. `CGRun.take m` (prefix, proved) restricts
every field.

Lanczos data of the run (`toLanczosData`, 1-based as `LanczosData`):
$\bar{\mathbf v}_{j+1}=(-1)^j\mathbf r_j/\rho_j$ ($\rho_j=\|\mathbf r_j\|$; $\mathbf b/\|\mathbf b\|$ if $\mathbf r_j=\mathbf 0$, only at $j=k$),
$\alpha_{j+1}=\gamma_j^{-1}+(\rho_j/\rho_{j-1})^2\gamma_{j-1}^{-1}$, $\beta_{j+1}=\rho_{j+1}/(\gamma_j\rho_j)$, i.e.
`tridiagonal = cgTridiagonal γ ρ k` (report §2.6′ convention: the **exact** $\mathbf L\mathbf D\mathbf L^{\mathsf T}$ of
the computed pivots and the computed residuals' norm ratios; the computed
$\gamma_j^{-1}+\delta_{j-1}/\gamma_{j-1}$ differs by $\le3.2\varepsilon\delta_{j-1}/\gamma_{j-1}$, absorbed in
$\bar{\mathbf f}_j$). With this convention $\mathbf T_m\succ0$ for every $m$ (`posDef_cgTridiagonal`).

## 4. The interface refactor (maintainer requirement 5)

### 4.1 What the backward proof uses

Audit of `Backward.lean` / `BackwardSpectral.lean` (every `L.` occurrence): the data
`L.normalized : LanczosData` with unit columns $1..k+1$ (`norm_normalizedV`), `transpose_H`,
`k_pos`, `β_zero`, `β_nonneg`, `β_pos`, `ε_nonneg`, and two bounds:
`frobNorm_normalized_residual_le` ($\|\bar{\mathbf F}_k\|_F\le12k\sqrt k\varepsilon\|\mathbf H\|$) and
`specNorm_normalized_gramCommutator_le` ($40k^2$); the latter is
`LanczosData.specNorm_gramCommutator_le` with $g=0$ (unit columns), where the $\beta$ bound is
multiplied by $g$ and **drops out**: $\|\bar{\mathbf M}_k\|_2\le2p+2\|\bar{\mathbf V}\|_F\|\bar{\mathbf F}\|_F\le2p+2kf$.
`k_mul_ε_le` and `β_le` are not used by the backward model itself.

### 4.2 The slim interface (`FinitePrecision/NormalizedBackward.lean`, CG2)

```lean
structure NormalizedLanczosData (n k) extends LanczosData n k where
  norm_v : ∀ j, 1 ≤ j → j ≤ k + 1 → ‖toLp 2 (v j)‖ = 1
  β_nonneg : ∀ j ≤ k, 0 ≤ β j
  β_pos : ∀ j, 1 ≤ j → j < k → 0 < β j
def normalizedBackwardBound (k) (f p) := 102 k³ f + 96 k² p
theorem NormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le
    (hf : ∀ j < k, ‖toLp 2 (D.recurrenceError j)‖ ≤ f) (hp : ∀ j < k, |D.adjacentInner j| ≤ p) :
    frobNorm (D.backwardH - D.dilatedH) ≤ normalizedBackwardBound k f p
```
plus `transpose_backwardH`, `backwardH_mul_dilatedBasis`,
`lanczosTridiagonal_backwardH_dilatedStart`, `lanczosState_…_beta`, `lanczosMatrix_…`,
`spectrum_backwardH_subset_Icc` (Weyl, the form CG needs), `abs_dotProduct_cfc_mulVec_sub_le`
(bounded by $\|\tilde{\mathbf H}-\hat{\mathbf H}\|_F$). The residual bounds are **hypotheses**, not fields
(the report proposed a `PerturbedLanczos` structure with factor-function fields): the model is
a function of the data only, so `CGRun.backwardH` does not depend on which certificates are
used to bound it, and the a priori and a posteriori theorems are about the same matrix.

Constant check: $\|\mathbf\Delta\|_F\le2\|\hat{\mathbf E}\|_F\le4\sqrt{k(k+1)}f+8(k+1)(2k+1)(2p+2kf)$ and
$(k+1)(2k+1)\le6k^2$ give $102k^3f+96k^2p$. Lanczos ($f=12k\varepsilon\|\mathbf H\|$, $p=8k\varepsilon\|\mathbf H\|$):
$1224k^4+768k^3\le1992k^4\le2000k^4$, so **`lanczosBackwardFactor` and every Lanczos statement
are unchanged** (`LanczosRun.frobNorm_toNormalizedLanczosData_backwardH_sub_dilatedH_le`).

### 4.3 Why $k^3$ for CG (vs $k^5$ in the report)

The report fed CG into the *Lanczos-shaped* interface with $\varepsilon_{\rm CG}=210k\varepsilon\kappa$ and
the Lanczos factor $2000k^4$, which already contains one $k$ from Lanczos' $\|\bar{\mathbf f}_j\|\le12(j+1)\varepsilon\|\mathbf H\|$
(itself from $\beta_j\le\frac54j\|\mathbf H\|$). For CG, $\|\bar{\mathbf f}_j\|$ does **not** grow with $j$
($\beta_j\le1.6a'$ a priori from the model), only $|\bar p_j|$ accumulates ($\propto j$). With the slim
bound: $f=O(\varepsilon\kappa a')$, $p=O(k\varepsilon\kappa a')$, $\|\mathbf\Delta\|=O(k^3\varepsilon\kappa a')$.

### 4.4 Statement changes on integration (none for users)

* Structure → `LanczosData.lean`; theorems replace the bodies in `Backward.lean`,
  `BackwardSpectral.lean`.
* `LanczosRun.backwardH := L.toNormalizedLanczosData.backwardH` (and `dilatedH`, `dilatedBasis`,
  `dilatedBasisSucc`, `dilatedStart`, `dilatedResidual`, `backwardPerturbation` likewise), so every
  `LanczosRun.*` theorem keeps name and statement and becomes a one-line corollary
  (`backwardH_eq_toNormalizedLanczosData_backwardH` is then `rfl`).
* `LanczosRun.frobNorm_dilatedResidual_le` (the $1000k^4$ intermediate): keep, derived the same
  way ($\le\frac12$ of the bound, $996k^4$).
* `LanczosRun.exchangeDefect*`, `specNorm_exchangeDefect_*`: move to `NormalizedLanczosData`;
  their LanczosRun versions are internal and may be dropped (not headlines). Docs: Lanczos note
  §3.6 table gains one row ("via `NormalizedLanczosData`").
* New named bound `normalizedBackwardBound` → `docs/constants.toml`.

## 5. Exact CG layer (`LinearSystems/CGTridiagonal.lean`)

| statement | content | source | status |
|---|---|---|---|
| `cgAlpha`, `cgStep_x` | named step length | — | def, `rfl` |
| `cgBidiagonal`, `cgTridiagonal`, `cgTridiagonal_eq_mul` | $\mathbf T=\mathbf L\,\mathrm{diag}(\gamma^{-1})\mathbf L^{\mathsf T}$, $\mathbf L_{i+1,i}=\rho_{i+1}/\rho_i$ | MeSt06 §3.1 | new, easy |
| `posDef_cgTridiagonal` | $\gamma>0\Rightarrow\mathbf T\succ0$ | — | new, easy |
| `sq_mul_inv_cgTridiagonal_zero_zero` | $\rho_0^2(\mathbf T_{k+1}^{-1})_{00}=\sum_{i\le k}\gamma_i\rho_i^2$ | MeSt06 §3.3, ST02 (4.4) | new, easy |
| (E0) `PosDef.lanczosTridiagonal_eq_cgTridiagonal` | exact CG ⇒ Lanczos $\mathbf T$ | MeSt06 §3.1 | new, moderate (via `lanczosState_eq_of_orthonormal_recurrence`, exists) |
| (E0′) `…cgAlpha_cgState_eq_of_lanczosTridiagonal_eq`, `…norm_cgState_r_eq_of_…` | converse: uniqueness of LDLᵀ | classical | new, moderate |
| HS decrement `re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ` | $\|\mathbf e_j\|_A^2-\|\mathbf e_{j+1}\|_A^2=\gamma_j\|\mathbf r_j\|^2$ | HS52 Thm 6:1 | new, easy |
| (E1) `PosDef.norm_cgState_r_le` | $\|\mathbf r_j\|\le\sqrt{a'/a}\|\mathbf r_i\|$, $i\le j$ | ST02 (7.20) | new, easy (`isMinOn_cgIterate`, exists) |
| (HS) `PosDef.norm_cgState_p_sq_eq` | $\|\mathbf p_j\|^2=\|\mathbf r_j\|^4\sum_{i\le j}\|\mathbf r_i\|^{-2}$ (no hypothesis on $\mathbf r$) | HS52 Thm 5:5 | new, easy ($\mathbf r_j\perp\mathbf p_{j-1}$, induct) |
| (E2) `PosDef.norm_cgState_p_sq_le` | $\|\mathbf p_j\|^2\le(a'/a)\|\mathbf r_j\|^2$ | HS52 Thm 5:5 | new, easy (conjugacy, exists) |
| (E3) `PosDef.cgAlpha_le`, `…norm_cgState_r_succ_sq_div_le` | $\gamma_j\le1/a$; $\delta_j\le a'\gamma_j$ | report (E3) | new, easy |

Existing and used: `cgState`, `cgStep`, `cgIterate`, `PosDef.cgState_x_eq`,
`star_cgState_r_dotProduct_eq_zero`, `star_cgState_p_dotProduct_mulVec_eq_zero`,
`isMinOn_cgIterate`, `IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`,
`re_quadForm_sub_cgIterate_eq_integral_sub` (Gauss quadrature form), `cgIterate_eq_lanczosMatrix`.
`CGRecurrence.lean`'s private `star_p_dotProduct_r` and `r_eq_zero_of_p_eq_zero` are to be made
public. Placement: `cgAlpha` and (E1)–(E3) to `CGRecurrence.lean`, the rest a new
`NLAlib/Krylov/LinearSystems/CGTridiagonal.lean`.

## 6. Lemmas A–C, a posteriori (report §§2.4–2.6)

Certificates (hypotheses, computable from the run): $\|\mathbf p_j\|\le\Pi\rho_j$;
$\|\mathbf A\|_2\gamma_j\|\mathbf p_j\|^2\le K\rho_j^2$ ($j<k$); $\beta_{j+1}\le B$ and $\delta_j\le B\gamma_j$
($j+1<k$: step $j$ uses $\beta_j$ and $\delta_{j-1}/\gamma_{j-1}$ only; $\beta_{j+1}$ enters $\bar{\mathbf f}_j$
through the exact cancellation $\beta_{j+1}\bar{\mathbf v}_{j+2}=(-1)^{j+1}\mathbf r_{j+1}/(\gamma_j\rho_j)$). In
Lean: `hB : ∀ j, j + 1 < k → lanczosβ (j+1) ≤ B ∧ δ j ≤ B * γ j`. With it the three statements below
assume `hB0 : 0 ≤ B` (automatic for $k\ge2$ from $0<\beta_1\le B$; needed for $k=1$, see §13).

* **Lemma A** `CGRun.norm_recurrenceError_le`: $\|\bar{\mathbf f}_j\|\le8\varepsilon(\|\mathbf A\|_2(1+\Pi)^2+B)$.
  The report's $\varepsilon\|\mathbf A\|(5.1\pi_j+4.1)+\varepsilon(1/\gamma_j+4.2\beta_j)+3.2\varepsilon\delta_{j-1}/\gamma_{j-1}$,
  with $1/\gamma_j\le1.05\|\mathbf A\|\pi_j^2$ (`ρ_sq_le`, a posteriori, no $\kappa$).
* **Line search** `abs_p_dotProduct_r_succ_le`: $|\mathbf p_j^{\mathsf T}\mathbf r_{j+1}|\le5(j+1)\varepsilon(1+\Pi+K)\rho_j^2$
  — the rigorous, $\kappa$-free, $O(\varepsilon^2)$-free form of ST02 Thm 9.1.
* **Lemma B** `abs_adjacentInner_le`: $|\bar p_j|\le16(j+1)\varepsilon(\|\mathbf A\|_2(1+\Pi)^2+B(1+\Pi+K))$.
  The structure that must survive formalisation: in $L_j$ the factor $K$ multiplies only
  $\delta_{j-1}/\gamma_{j-1}$ (bounded by the model), never $1/\gamma_j$ (which is $O(\kappa)$); a
  single coefficient certificate covering $1/\gamma_j$ would give $\kappa^2$ in $p$ and $\kappa^3$ in (H).
  That is why $B$ is not allowed to bound $1/\gamma_j$.
* **Lemma C** (coefficient growth) is not needed: replaced by $B\le1.6a'$ from the model (§7).
* `frobNorm_backwardH_sub_dilatedH_le_of_certificates`: the a posteriori model,
  $\|\mathbf\Delta\|_F\le$ `normalizedBackwardBound k (8ε(‖A‖(1+Π)²+B)) (16kε(‖A‖(1+Π)²+B(1+Π+K)))`.
  Kept as a public theorem (CG6): it is the induction engine and certifies much more than the a
  priori bound on a given run (report sanity runs: $\Pi\le0.42\sqrt\kappa$).
* `norm_r_le_two_mul_norm_p` (next direction not small) and the gap theorem (§9.3).

Constants carry a margin of 1.5–2 over the report's hand derivation and are to be re-derived;
the a priori constants below follow from these.

## 7. Prefix runs and the a priori induction

P(j), $1\le j\le k$: certificates $\Pi_j^2\le3.3\kappa$, $K_j\le1.05\kappa$, $B_j\le1.6a'$ for the steps
$<j$. Step P(j) ⇒ P(j+1):

1. **Model of the prefix.** `C.take j` with the P(j) certificates:
   $f\le8\varepsilon(a'(1+1.82\sqrt\kappa)^2+1.6a')\le89\varepsilon\kappa a'$,
   $p\le16j\varepsilon(8\kappa a'+1.6a'\cdot3.9\kappa)=227.8\,j\varepsilon\kappa a'\le230j\varepsilon\kappa a'$ (using $(1+1.82\sqrt\kappa)^2\le8\kappa$,
   $1+\Pi+K\le3.9\kappa$; the first draft's $322$ was an arithmetic slip), so
   $c_j:=\|\mathbf\Delta_j\|_F\le(102\cdot89+96\cdot230)j^3\varepsilon\kappa a'=31158\,j^3\varepsilon\kappa a'\le4\cdot10^4j^3\varepsilon\kappa a'\le0.4a$ by (H)
   (margin 28% on the constant for the re-derivation of Lemmas A and B; the review's recount of
   $L_j$, $\approx11\|\mathbf A\|(1+\Pi)^2+14.1B(1+\Pi+K)$ per $(j+1)$, stays under the 16). The model
   of `C.take j` needs $B$ only for the steps $i+1<j$.
   Weyl: spectrum of $\tilde{\mathbf H}_j$ in $[a/2,a'+a/2]$, condition number $\le2\kappa+1\le3\kappa$.
2. **Exact CG on the prefix model** reproduces $\gamma_i$ ($i<j$) and $\rho_i$ ($i\le j$) (§5 E0′ with
   `lanczosTridiagonal_backwardH`, `lanczosState_backwardH_dilatedStart_beta`).
3. **Step-$j$ certificates.** (S) $K$: direct ($\mu_j\ge(1-2.1\varepsilon\kappa)a\|\mathbf p_j\|^2$), no model.
   (P) $\pi_j^2\le(1+2\varepsilon)^2[1+(1+\eta)^2(\rho_j/\rho_{j-1})^2\pi_{j-1}^2+2(1+\eta)|\tau_{j-1}|/\rho_{j-1}^2]$;
   unrolled, the ratios telescope to $S_j=\sum_{i\le j}\rho_j^2/\rho_i^2=\|\tilde{\mathbf p}_j\|^2/\rho_j^2\le\kappa(\tilde{\mathbf H}_j)\le3\kappa$
   (the identity (HS) `norm_cgState_p_sq_eq` and (E2) on the model, with the reproduction of
   $\rho_i$: `CGRun.sum_ρ_sq_div_ρ_sq_le`, hypothesis spectrum of the model in $[l,l']$), so
   $\pi_j^2\le1.1\cdot3\kappa$. Without (HS) only (E1) termwise is available, $S_j\le1+j\kappa$,
   which costs a factor $k$ in $p$ and turns (H) into $k^4\varepsilon\kappa^2$. (B) $\beta_{j}$, $\delta_{j-1}/\gamma_{j-1}\le1.04\lambda_{\max}(\tilde{\mathbf H}_j)\le1.6a'$ (E3 on
   the model). The new step-$j$ index needs the model of `C.take (j+1)` for $\beta_{j+1}$,
   $\delta_j/\gamma_j$: they are proved after P(j+1)'s $\Pi,K$ part — the induction is on the
   triple (Π,K at $j$) → model of $j+1$ → (B at $j$); no circularity, since the model of
   $j+1$ steps needs $B$ only for steps $<j+1$ **as a bound on $\bar{\mathbf f},\bar p$**, and those for step $j$
   use $\delta_{j-1}/\gamma_{j-1}$, $\beta_j$ (step $<j$) and $1/\gamma_j$ (via $\pi_j$), the audit of report §2.6′(L).
4. **Next division.** $\rho_j\le2\|\mathbf p_j\|$ and $\mu_j>0$ (§1.3) — used by the bridge.

**Formal shape.** One private theorem `aprioriCertificates (j ≤ k) : ∀ i < j, Π_i ∧ K_i ∧ β_{i+1} ∧ δ_i`
by `Nat.rec` (skeletoned in `CGBackward.lean`), from which `norm_p_sq_le`,
`specNorm_mul_γ_mul_norm_p_sq_le`, `lanczosβ_succ_le`, `δ_le` follow at $j=k$. It uses only the
a posteriori engine `frobNorm_backwardH_sub_dilatedH_le_of_certificates` on `C.take j`, Weyl
(`NormalizedLanczosData.spectrum_backwardH_subset_Icc`), and the reproduction lemmas with
positive definiteness as a **hypothesis** (`cgAlpha_backwardH_of_posDef`,
`norm_cgState_backwardH_r_of_posDef`, `sum_ρ_sq_div_ρ_sq_le`); never the public a priori
`cgAlpha_backwardH` / `spectrum_backwardH_subset_Icc`, which depend on it (no file-level circle;
the docstrings say so). Step $j=0$ is direct ($\mathbf p_0=\mathbf r_0$, no `take 0`). The backward
model of every prefix is the *same construction* applied to `C.take j`, so the interface must be
a plain structure over `LanczosData` (it is).

**Arithmetic of (H).** $k^3\varepsilon\kappa^2\le10^{-5}$ gives $c_k\le0.4a$, $2.1\varepsilon\kappa\le10^{-5}$,
$20k\varepsilon(1+\Pi+K)\le80k\varepsilon\kappa\le10^{-3}$, $k\varepsilon\le1/100$. The $\kappa^2$ is natural (the
perturbation $\sim\varepsilon\kappa\|\mathbf A\|$ must stay below $\lambda_{\min}$: maintainer's point); the
$\kappa$ in $\varepsilon_{\rm CG}$ is unavoidable for the interface quantities in the normwise model
(report §2.7, attained by admissible error choices). Constants unoptimised.

**Future work (not this round).** A sharper a priori $1/\gamma_j\le1.02\|\mathbf A\|$ (instead of
$1.05\|\mathbf A\|\pi_j^2$), from $\mathbf p_j^{\mathsf T}\mathbf A\mathbf p_j=\mathbf r_j^{\mathsf T}\mathbf s_j+\delta_{j-1}\zeta_j+\dots$ with
$O(k\varepsilon\kappa\|\mathbf A\|)$ corrections from P(j), with Kantorovich on $e^\mu$, gives
$f=O(\varepsilon\sqrt\kappa a')$ and drops pieces (4), (7) of $L_j$; the total gain is only ~25% (the
$p$ term dominates), and $\gamma_j\le1.02/a$ likewise. Recorded, not pursued (review §B).

## 8. Headlines (`FinitePrecision/CGBackward.lean`)

Hypotheses throughout: `C : CGRun n k`, `0 < a`, `spectrum ℝ C.A ⊆ Icc a a'`,
`k^3 * C.ε * (a'/a)^2 ≤ 1/10^5`.

| statement | content |
|---|---|
| `frobNorm_backwardH_sub_dilatedH_le` | $\|\tilde{\mathbf H}-\mathbf I\otimes\mathbf A\|_F\le4\cdot10^4k^3\varepsilon\kappa a'$ |
| `spectrum_backwardH_subset_Icc` | model spectrum in $[a/2,a'+a/2]$ (PD, $\kappa\le2\kappa+1$) |
| `lanczosTridiagonal_backwardH` | exact Lanczos on $(\tilde{\mathbf H},(\mathbf b,\mathbf 0,..))$ gives `cgTridiagonal γ ρ k` (no (H)) |
| `cgAlpha_backwardH`, `norm_cgState_backwardH_r` | exact CG on the model: step lengths $=\gamma_j$, residual norms $=\rho_j$ |
| `norm_p_sq_le`, `specNorm_mul_γ_mul_norm_p_sq_le`, `lanczosβ_succ_le`, `δ_le` | a priori certificates |
| `ρ_le` | $\rho_j\le\sqrt{3\kappa}\rho_i$, $i\le j\le k$ (ST02 (7.20), import removed) |
| `ρ_le_chebyshev` | $\rho_j\le2\sqrt{\kappa_c}\,(\frac{\sqrt{\kappa_c}-1}{\sqrt{\kappa_c}+1})^j\|\mathbf b\|$, $\kappa_c=2\kappa+1$ |
| §9 statements | errors |

Program level: `HasCGBackwardModel` (output $\gamma_j$ exact; output $\nu_j$ within relative $\varepsilon$
of $\|\tilde{\mathbf r}_j\|^2$), `exists_cgBackwardModel_of_cgDenseProg`. Further corollaries for free
from §4: Ritz values of the computed $\mathbf T_k$ in $[a-c,a'+c]$, Paige-type localisation,
$W_1$-closeness of spectral measures of $(\mathbf A,\mathbf b/\|\mathbf b\|)$ and the model.

Validity range (honest): (H) bounds $k$, $k\le(10^{-5}/(\varepsilon\kappa^2))^{1/3}$. Double precision,
$\kappa=10$: dense $N=10^3$ ($\varepsilon\approx N^{3/2}u\approx3.5\cdot10^{-12}$) $k\le30$; oracle with $\varepsilon\approx Nu$,
$k\le97$. For $\kappa=10^3$: $k\le1$ (dense), $k\le4$ (oracle) — **the a priori theorem is vacuous for
ill-conditioned problems of practical size**, with these (unoptimised, ~$10^5$) constants and the
polynomial $k^3$. The a posteriori theorem (§6) has no $\kappa$ and holds for every $k$ with
$k\varepsilon\le1/100$. Lanczos is in the same position (its bound $2000k^4\varepsilon\|\mathbf H\|$ is informative
only for $k\lesssim(5\cdot10^{-4}/\varepsilon)^{1/4}\approx100$). Improving the constants by $10^2$–$10^3$ is
plausible (Lemma B and the exchange rule are crude) but does not change the picture for
$\kappa=10^3$; the $\kappa^2$ is intrinsic (§7). The range is stated in the docstrings of
`CGBackward.lean` (module docstring and `frobNorm_backwardH_sub_dilatedH_le`). Within it the
constants have a real margin: $31158\le4\cdot10^4$ (28%) and $c_k\le0.4a<a/2$ (20%).

## 9. Relating the errors of the model and of the computed run (maintainer requirement 3)

### 9.1 Literature, precisely

* **Exact arithmetic** [HS52 Thm 6:1; MeSt06 (3.17)–(3.20); ST02 (4.4), (4.9)]: with $\mathbf x_0=\mathbf 0$,
  $\|\mathbf x-\mathbf x_k\|_A^2=\|\mathbf r_0\|^2[(\mathbf T_n^{-1})_{11}-(\mathbf T_k^{-1})_{11}]$, $\|\mathbf r_0\|^2(\mathbf T_k^{-1})_{11}=\sum_{i<k}\gamma_i\|\mathbf r_i\|^2$,
  and $\|\mathbf x-\mathbf x_j\|_A^2-\|\mathbf x-\mathbf x_{j+d}\|_A^2=\nu_{j,d}:=\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf r_i\|^2$. Library: the Gauss
  quadrature form `re_quadForm_sub_cgIterate_eq_integral_sub` exists; the $\mathbf T^{-1}$ and
  decrement forms are new (§5).
* **Greenbaum 1989, Thm 3 (pp. 26–29)**, as summarised in MeSt06 §5.2 (full text not
  accessible here): for the perturbed CG recurrence, the $\mathbf A$-norm error is "reduced at
  approximately the same rate" as the energy norm of the error of exact CG on the model; "the
  situation is technically more complicated, since the definition of the norm depends on the
  matrix", and the maximal attainable accuracy is assumed far away. Hypotheses: Greenbaum's
  perturbed-recurrence assumptions, not derived from a rounding model for HSCG.
* **Strakoš–Tichý 2002, Thm 10.1** (read in full): under $\varepsilon(n+c)\kappa\ll1$,
  $$\|\mathbf x-\mathbf x_j\|_A^2-\|\mathbf x-\mathbf x_{j+d}\|_A^2=\nu_{j,d}+\nu_{j,d}E^{(1)}_{j,d}+\|\mathbf x-\mathbf x_j\|_AE^{(2)}_{j,d}+O(\varepsilon^2),$$
  $|E^{(1)}_{j,d}|\le O(d)\max_i|E^{(1)}_i|$, $|E^{(1)}_i|\le\varepsilon\kappa O(t^{(1)}(n))+O(\varepsilon^2)$,
  $|E^{(2)}_i|\le\varepsilon\|\mathbf A\|^{1/2}\kappa^{1/2}(\|\mathbf x\|+\max_{i'}\|\mathbf x_{i'}\|)O(t^{(2)}(n))+O(\varepsilon^2)$ (ST02
  (10.6)–(10.9)). Not fully rigorous: $O(\varepsilon^2)$ terms dropped throughout; (7.20)
  $\|\mathbf r_j\|/\|\mathbf r_i\|\lesssim\kappa^{1/2}$ imported from "monotonicity … preserved (with small
  additional inaccuracy) also in finite precision ([19],[22])"; (7.19) assumes the gap small
  ("final accuracy level has not been reached yet"). The estimate is trustworthy "until
  $\|\mathbf x-\mathbf x_j\|_A\gg|E^{(2)}_{j,d}|$" (10.11).
* **Residual gap** [Greenbaum 1997 SIMAX 18:535–551; Sleijpen–van der Vorst–Fokkema 1994;
  ST02 (7.15)–(7.18)]: $\|\mathbf b-\mathbf A\mathbf x_j-\mathbf r_j\|\le\varepsilon\|\mathbf A\|(\|\mathbf x\|+\max_i\|\mathbf x_i\|)O(jc)$, rigorous and
  local (two-term recurrences: no amplification; Gutknecht–Strakoš 2000 for the three-term
  contrast).
* Golub–Meurant / Golub–Strakoš (Gauss–Radau) bounds are exact-arithmetic statements;
  library: `re_quadForm_sub_cgIterate_le_integral_radauQuadrature_sub` and the lower twin.

### 9.2 What the model gives exactly (this round; ER1)

Everything below is exact CG on the SPD $\tilde{\mathbf H}$ plus §5 and the reproduction theorems:

* (ER1a) `quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`:
  $\|\tilde{\mathbf e}_j\|^2_{\tilde H}-\|\tilde{\mathbf e}_{j+d}\|^2_{\tilde H}=\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf r_i\|^2$ **exactly**, computed $\gamma_i$ and norms of
  the computed residuals. *The Strakoš–Tichý estimator $\nu_{j,d}$ computed from the run is
  the exact error decrement of exact CG on the model.* (Output-level: $\|\mathbf r_i\|^2=\nu_i(1+O(\varepsilon))$.)
* (ER1b) `quadForm_backwardH_sub_cgIterate_eq`: $\|\tilde{\mathbf e}_k\|^2_{\tilde H}=\|\tilde{\mathbf x}_\star\|^2_{\tilde H}-\|\mathbf b\|^2(\mathbf T_k^{-1})_{00}$,
  $\mathbf T_k$ = `cgTridiagonal γ ρ k` (the "formula in terms of the tridiagonal matrix"):
  $(\mathbf T_n^{-1})_{11}$ is replaced by $\tilde{\mathbf v}^{\mathsf T}\tilde{\mathbf H}^{-1}\tilde{\mathbf v}$.
* (ER1c) `abs_quadForm_backwardH_sub_quadForm_le`: $|\|\tilde{\mathbf x}_\star\|^2_{\tilde H}-\|\mathbf x_\star\|^2_{\mathbf A}|\le2\|\mathbf b\|^2c/a^2$
  (resolvent identity; the model start is exactly $\mathbf b/\|\mathbf b\|$ since $\mathbf r_0=\mathbf b$ is not rounded).
* (ER1d) `abs_quadForm_backwardH_sub_cgIterate_sub_le`: $|\|\tilde{\mathbf e}_k\|^2_{\tilde H}-(\|\mathbf x_\star\|_{\mathbf A}^2-\sum_{j<k}\gamma_j\|\mathbf r_j\|^2)|\le2\|\mathbf b\|^2c/a^2$;
  relative to $\|\mathbf x_\star\|^2_{\mathbf A}\ge\|\mathbf b\|^2/a'$ this is $\le2\kappa c/a=O(k^3\varepsilon\kappa^3)$.
* (ER1e) `ρ_le_chebyshev`, and Gauss–Radau two-sided bounds for $\|\tilde{\mathbf e}_k\|_{\tilde H}$ from the library
  on the model with the interval $[a/2,a'+a/2]$ (corollary, not skeletoned).

Recommendation: **this round** (≈300 lines, exact arithmetic, all inputs exist or are in §5).

### 9.3 The residual gap (this round; ER2)

`CGRun.norm_sub_mulVec_x_sub_r_le` (a posteriori, local, no $\kappa$, no $O(\varepsilon^2)$):
$\|(\mathbf b-\mathbf A\mathbf x_k)-\mathbf r_k\|\le\varepsilon\sum_{j<k}(\|\mathbf A\|_2(\|\mathbf x_j\|+4\gamma_j\|\mathbf p_j\|)+\|\mathbf r_j\|)$, from
$\mathbf g_{j+1}=\mathbf g_j+\gamma_j\mathbf e^s_j-\mathbf A\mathbf e^x_j-\mathbf e^r_j$, $\mathbf g_0=\mathbf 0$. A priori corollary (not skeletoned):
$\gamma_j\le2/a$, $\|\mathbf p_j\|\le3.2\kappa\|\mathbf b\|$ give $\|\mathbf x_j\|\le6.5j\kappa\|\mathbf b\|/a$ and a gap
$O(k^2\varepsilon\kappa^2\|\mathbf b\|)$ — crude; the a posteriori form is the useful one. True residual:
$\|\mathbf b-\mathbf A\mathbf x_k\|\le\rho_k+\text{gap}$, and with `ρ_le_chebyshev` an a priori true-residual bound.

### 9.4 The computed run's own $\mathbf A$-norm error (next round; ER3)

Provable in this framework with no import and no dropped $O(\varepsilon^2)$: one step,
$\mathbf e_j:=\mathbf x_\star-\mathbf x_j$, $\mathbf A\mathbf e_j=\mathbf r_j+\mathbf g_j$,
$$\|\mathbf e_j\|_A^2-\|\mathbf e_{j+1}\|_A^2=\gamma_j\rho_j^2(1+\zeta_j)+\xi_j,$$
$\gamma_j\rho_j^2\zeta_j=\gamma_j[2\delta_{j-1}\tau_{j-1}+2\mathbf e^{p\mathsf T}_j\mathbf r_j-\rho_j^2(\theta_j+\eta^\gamma_j+\theta_j\eta^\gamma_j)+\gamma_j\mathbf p_j^{\mathsf T}\mathbf e^s_j+\gamma_je^\mu_j]$, so
$|\zeta_j|\le C\,k\varepsilon\kappa$ by the line-search lemma and the a priori certificates;
$\mathbf e_{j+1}=\mathbf e_j-\gamma_j\mathbf p_j-\mathbf e^x_j$ and
$\xi_j=2\gamma_j\mathbf p_j^{\mathsf T}\mathbf g_j+2\mathbf e^{x\mathsf T}_j\mathbf A\mathbf e_{j+1}+\|\mathbf e^x_j\|_A^2$
(equivalently $+2\mathbf e^{x\mathsf T}_j\mathbf A(\mathbf e_j-\gamma_j\mathbf p_j)-\|\mathbf e^x_j\|_A^2$; the first draft had the
cross term with the wrong sign, harmless for $|\xi_j|$), so
$|\xi_j|\le2\gamma_j\|\mathbf p_j\|\|\mathbf g_j\|+2\|\mathbf A\|^{1/2}\|\mathbf e_{j+1}+\mathbf e^x_j\|_A\varepsilon(\|\mathbf x_j\|+\gamma_j\|\mathbf p_j\|)+\|\mathbf A\|\varepsilon^2(\cdot)^2$.
Proposed statements (shape):

```lean
theorem CGRun.quadForm_sub_x_sub_quadForm_sub_x_succ_eq (hx : C.A *ᵥ xs = C.b) (j < k) :
    quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j+1)) = C.γ j * C.ρ j ^ 2 * (1 + C.ζ j) + C.ξ j
theorem CGRun.abs_ζ_le (H) : |C.ζ j| ≤ 50 * k * C.ε * (a'/a)                     -- a priori
theorem CGRun.abs_ξ_le : |C.ξ j| ≤ 2 γ_j ‖p_j‖ ‖g_j‖ + 3 ε ‖A‖^{1/2} ‖x_⋆ − x_{j+1}‖_A (‖x_j‖ + γ_j ‖p_j‖)
     + 2 ε² ‖A‖ (‖x_j‖ + γ_j ‖p_j‖)²                                           -- a posteriori
theorem CGRun.abs_errorDecrement_sub_modelDecrement_le (j + d ≤ k) :
    |(‖e_j‖²_A − ‖e_{j+d}‖²_A) − (‖ẽ_j‖²_H̃ − ‖ẽ_{j+d}‖²_H̃)| ≤ 50kεκ·ν_{j,d} + Σ_{i∈[j,j+d)} |ξ_i|
```
The last is the rigorous Greenbaum/Strakoš–Tichý statement: **the computed run's error
decrements match those of exact CG on the backward model** (which equal $\nu_{j,d}$ by ER1a)
to relative accuracy $O(k\varepsilon\kappa)$, plus a term that matters only near the attainable
accuracy. Comparing *absolute* errors $\|\mathbf e_k\|_A$ vs $\|\tilde{\mathbf e}_k\|_{\tilde H}$ adds ER1c's
$2\|\mathbf b\|^2c/a^2$ (relative $O(k^3\varepsilon\kappa^3)$), meaningful only down to error level $\sqrt{k^3\varepsilon\kappa^3}\|\mathbf x_\star\|_A$;
the decrement form avoids it (recommended headline).

Why next round: (i) it needs the a priori bound on $\|\mathbf x_j\|$ and the gap bookkeeping across
steps (two more inductive quantities); (ii) the choice between the decrement form, the
absolute form, and a "trust until $\|\mathbf e_j\|_A\gg|\xi|$" form (ST02 (10.11)) is a maintainer
decision (CG4); (iii) nothing in ER3 is needed by the rest of the chain. The `CGRun` fields for
$\mathbf x$, $\mathbf e^x$ are already in place, so no refactor.

**Done (2026-10-29, branch `research/cg-error-tracking`, `Krylov/FinitePrecision/CGErrorTracking.lean`,
all proved).** Shape as proposed, with $\zeta,\xi$ not named as fields: the exact identity
`quadForm_sub_x_sub_quadForm_sub_x_succ_eq` (terms $2\gamma_j(\mathbf p_j^{\mathsf T}\mathbf r_j-\rho_j^2)$,
$\gamma_j^2\mathbf p_j^{\mathsf T}\mathbf A\mathbf p_j-\gamma_j\rho_j^2$, $2\gamma_j\mathbf p_j^{\mathsf T}\mathbf g_j$,
$2\mathbf e^{x\mathsf T}_j\mathbf A\mathbf w_j$, $\|\mathbf e^x_j\|_A^2$); relative terms $26k\varepsilon\kappa\rho_j^2$ and
$6\varepsilon\kappa\gamma_j\rho_j^2$; one step $|\Delta E^2-\gamma_j\rho_j^2|\le60k\varepsilon\kappa\gamma_j\rho_j^2+(36j+16)\varepsilon\kappa\|\mathbf b\|^2/a$
(a priori, via `norm_x_le` and the gap bound, so no a posteriori $\xi$ form); $d$ steps
$|\Delta_{j,d}E^2-\nu_{j,d}|\le60k\varepsilon\kappa\nu_{j,d}+(36(j+d)+16)d\varepsilon\kappa\|\mathbf b\|^2/a\le200k^2\varepsilon\kappa\|\mathbf b\|^2/a$;
the decrement form against the model (no model distance); Gauss quadrature
$|E_{j+1}^2-(\|\mathbf x_\star\|_A^2-\|\mathbf b\|^2(\mathbf T_{j+1}^{-1})_{00})|\le200k^2\varepsilon\kappa\|\mathbf b\|^2/a$;
absolute $|E_j^2-\tilde E_j^2|\le10^5k^3\varepsilon\kappa^2\|\mathbf b\|^2/a$ (model distance dominant).

## 10. Files, dependency order, size

| # | file (scaffold path = future path, except where noted) | content | sorry | est. lines |
|---|---|---|---|---|
| 1 | `Krylov/FinitePrecision/NormalizedBackward.lean` | §4 refactor (→ `LanczosData.lean`, `Backward*.lean`) | 10 | 300 (mostly moves) |
| 2 | `Krylov/LinearSystems/CGTridiagonal.lean` | §5 exact layer | 12 | 680 |
| 3 | `Krylov/FinitePrecision/CGRun.lean`, `CGRunModel.lean` | §3, §6, gap | 15 | 1300 |
| 4 | `Krylov/FinitePrecision/CGBackward.lean` | §7–§9.2 | 19 | 1050 |
| 5 | `Krylov/LinearSystems/CGProgramTree.lean` | §1 | 1 | 650 |
| 6 | `Krylov/LinearSystems/CGRounding.lean` | §2 (+ step/run files like `LanczosStep`/`LanczosProgramRun`) | 4 | 1400 |

Total ≈ 5.3k lines (the bridge raised from 1100 to 1400: the forward invariant re-packages a
`CGRun` per iteration, review M3); next round ER3 ≈ 500. Imports: 1 ← `BackwardSpectral`; 2 ← `CGLanczos`,
`CGRecurrence`; 3 ← 1, 2; 4 ← 3; 5 ← `Computation.BLAS`, `Computation.Exact`, 2; 6 ← 4, 5,
`BLAS.RoundingErrors`, `Matrix.Norms.Compare` (proof will also import
`NLAlibScaffold.Krylov.Processes.LanczosStep` for `LanczosMvSpec`, decided at proof time). Every
name a `Proof:` line cites elaborates in the file's import closure, except the forward
reference in 3/`CGRounding` docstrings to lemmas of 4 (named, not used).

Dependency order for proving: 1 and 2 (parallel) → 3 (Lemma A, line search, Lemma B, gap) →
4 (induction, then reproduction and ER1) → 5 (exact spec, parallel with 1–4) → 6 (bridge needs 4).
Risky steps: Lemma B (structure of $L_j$, §6) and the induction bookkeeping (§7).

Exists vs new: exists — the whole Lanczos backward chain, `cgState`/`cgIterate`/orthogonality/
conjugacy/Chebyshev/quadrature, the FP toolkit (`IsRelErrSem`, product-form `dot`, `axpy`,
`gemv`, `IsMatvecErr`, `MatrixFreeRounded`), the Lanczos program/step infrastructure. New —
everything in the table. Bibliography to add: `StrakosTichy2002`, `MeurantStrakos2006`,
`GreenbaumLiuChen2021`, `Greenbaum1997SIMAX` (the SIMAX attainable-accuracy paper; the existing
`Greenbaum1997` is the book).

## 11. Open questions (each with a recommendation)

* **Q1 (CG1) Breakdown.** No $\mu$-test, positivity a theorem, bridge interleaved with the
  analysis (recommended, maintainer's suggestion) vs guard `μ ≤ 0 → stop` (decoupled bridge,
  non-textbook). Recommend the first; switch to the guard only if the interleaved induction
  costs > 300 extra lines. **Decided (a)**, (b) the named fallback.
* **Q2 (CG2) Interface.** `NormalizedLanczosData` + bounds as hypotheses (recommended) vs the
  report's `PerturbedLanczos` with factor fields. Hypotheses keep one model per run and keep
  every Lanczos statement.
* **Q3 (CG3) Hypothesis form.** $q^3\varepsilon\kappa^2\le10^{-5}$ with $\kappa=a'/a$ for any enclosing interval
  $[a,a']$ (recommended; the maintainer's $(\lambda_{\max}+c)/(\lambda_{\min}-c)$ appears inside as $\le2\kappa+1$) vs
  eigenvalue-API form with `eigenvalue A 0`/`eigenvalue A (n-1)`. Intervals compose with
  `spectrum_subset_Icc_of_le` and the CG Chebyshev API.
* **Q4 (CG4) Error part scope.** ER1 + gap now, ER3 (computed $\mathbf A$-norm error, decrement form)
  next round (recommended).
* **Q5 (CG5) Start.** $\mathbf x_0=\mathbf 0$ (recommended) vs general $\mathbf x_0$.
* **Q6 (CG6) A posteriori theorem public.** Yes (recommended): the engine, and the sharper
  certificate in practice.
* **Q7 (CG7) Placement.** CG program in `Krylov/LinearSystems/` (recommended) vs
  `Krylov/Processes/` next to Lanczos.
* Still open mathematically (not for this round): whether another construction avoids the
  $\kappa$ in the model distance (report §2.7(3)); optimality of $k^3$ and $\kappa^2$.

## 12. Review dispositions (Fable review 2026-10-29, `reports/CG-FP-Review.md`; CG1–CG7 = (a))

| item | disposition |
|---|---|
| MF1 `hB` one index too strong | **fixed**: `hB : ∀ j, j + 1 < k → …` in `norm_recurrenceError_le`, `abs_adjacentInner_le`, `frobNorm_backwardH_sub_dilatedH_le_of_certificates`; conclusions unchanged. Downstream: the a priori headline and the induction (P(1) needs no $B$); no other use. §6, §7 updated. |
| MF2 HS direction-norm identity | **fixed**: `Matrix.PosDef.norm_cgState_p_sq_eq` (§5, `CGTridiagonal.lean`) and `CGRun.sum_ρ_sq_div_ρ_sq_le` (on the model, `CGBackward.lean`), wired into step (P) of §7 and the docstring of the engine. |
| MF3 induction engine | **fixed**: private `aprioriCertificates` skeletoned; the four a priori certificate docstrings cite it, not `cgAlpha_backwardH`; new hypothesis-form reproduction lemmas `cgAlpha_backwardH_of_posDef`, `norm_cgState_backwardH_r_of_posDef` (and `lanczosTridiagonal_backwardH` moved before the induction) break the file-level circle. Bridge invariant has an explicit $m=0$ case (§1.3, `exists_cgRun_of_cgProg` docstring). |
| M1 constants margin | **fixed**: $p\le230j\varepsilon\kappa a'$ (§7 step 1); $102\cdot89+96\cdot230=31158\le4\cdot10^4$; the statement keeps $4\cdot10^4k^3\varepsilon\kappa a'$ and (H) $q^3\varepsilon\kappa^2\le10^{-5}$ (so $c_k\le0.4a$). Range in §8 and the docstrings. |
| M2 ER3 $\xi_j$ sign | **fixed** in §9.4. |
| M3 bridge cost | **accepted**: forward invariant (§1.3); estimate 1100 → 1400 lines; CG1 (b) kept as fallback. |
| L1, L3 | verified by the review; no change. |
| L2 `norm_r_le_two_mul_norm_p` | quadratic-mean hint added to the docstring. |
| L4 scaling of `lanczosState` | cited in the `Proof:` lines of `lanczosTridiagonal_backwardH`, `cgAlpha_backwardH_of_posDef` (lemma to be added with the proof). |
| L5 literals; underflow | underflow caveat added (`ν_eq_zero_iff`, bridge docstring). Named constants (`cgBackwardFactor`, `cgSmallness` in `docs/constants.toml`) deferred to integration: research branch, `check_constants` passes. |
| §B Kantorovich / $1/\gamma_j\le1.02\|\mathbf A\|$ | **not done**, recorded as future work (§7). |
| CG1–CG7 | approved (a); CG1 fallback (b) as in §1.3. |

## 13. Statement changes during the proofs (batches 1–4)

| statement | change | reason |
|---|---|---|
| `CGRun.norm_recurrenceError_le` (Lemma A), `CGRun.abs_adjacentInner_le` (Lemma B), `CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` | **hypothesis `hB0 : 0 ≤ B` added** (names kept; the interim `…_of_nonneg` variants removed) | false as stated for $k=1$, $B<0$: `hB` is vacuous and the right side is negative for $B$ negative enough, while the left side is positive (counterexample $n=1$, $\mathbf A=\mathbf b=1$, $\varepsilon=1/100$, $\mathbf e^r_0=0.005$, $\Pi=1$, $B=-100$). For $k\ge2$, $0<\beta_1\le B$ gives $B\ge0$, so nothing is lost. Only downstream use: the a priori engine in `CGBackward.lean`, where $B=1.6a'>0$. |
| `Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq`, `Matrix.PosDef.norm_cgState_r_eq_of_lanczosTridiagonal_eq` | unused hypothesis `hk : 0 < k` removed | generalisation (the $k=0$ case is vacuous or $
ho_0=\|\mathbf b\|$) |
| `Matrix.PosDef.norm_cgState_p_sq_eq` | unused instance `[DecidableEq n]` omitted | linter; no change of meaning |
| `CGRun.lean` | split: Lemma B, the a posteriori model, the next division and the residual gap moved to `CGRunModel.lean` (F10); helper lemmas of `CGRun` used across the seam (`ρ_pos`, `δ_bounds`, `norm_s_le`, …) made public | file size |

## References

As in the report (`HSCG-FiniteP.md`), plus: Strakoš, Tichý, ETNA 13 (2002) 56–80, §§7–10
(Thm 9.1, Thm 10.1, (7.14)–(7.20), (10.6)–(10.11), read in full); Meurant, Strakoš, Acta
Numerica 15 (2006) §§3.1–3.3, 5.2; Greenbaum, SIMAX 18 (1997) 535–551; Hestenes, Stiefel
(1952) Thms 5:5, 6:1, 18:3.
