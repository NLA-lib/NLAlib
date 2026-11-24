# Iterative refinement in three precisions

Design, 2026-11-20; revised 2026-11-23 for the routine core and the folder
`NLAlib/LinearSystems`, on `main` at `833cee56`.
Requested as the library's example of mixed precision. All four stages below are implemented and
checked. The note was written
with the code, not reviewed before it: the interface questions in section 8 are open.

## Why this algorithm

Refinement for $Ax = b$ computes $r_j \approx b - Ax_j$, $d_j \approx A^{-1}r_j$,
$x_{j+1} \approx x_j + d_j$. Carson and Higham [CarsonHigham2018] run the three operations at
three unit roundoffs: the residual at $u_r$, the correction with factors computed at $u_f$, the
update at the working $u$. Their result cannot be stated with one unit roundoff: if the
effective solve accuracy is sufficiently less than one the iteration contracts, and the limiting
accuracy $4pu_r\operatorname{cond}(A, x) + u$ depends on $u$ and $u_r$ and not on the solve. One theorem covers fixed precision ($u_f = u = u_r$), traditional refinement
($u_r = u^2$) and "factor in single, solve to double" ($u_f > u$).

## 1. Objects

| Object | Kind | Mathlib bridge |
|---|---|---|
| `RefinementRun A b θ η ζ ε k` | run model (structure, data in `x r d`) | none needed: stated with `specNorm`, `‖WithLp.toLp 2 ·‖`, `A⁻¹` |
| `RefinementRun.start`, `RefinementRun.extend` | constructors | — |
| `refinementContractionFactor κ θ η ζ ε`, `refinementAccuracyBound κ θ η ε` | named bounds, in `docs/constants.toml` | — |
| `Ops.RefinementOp` (`residual`, `solve`, `update`) | operation group | — |
| `Ops.residualRel`, `Ops.solveRel`, `Ops.updateRel`, `Ops.IsRefinement` | contracts | — |
| `LinearSystems.Refinement.solve`, `LinearSystems.Refinement.solveSpec` | routine and its specification | — |
| `LinearSystems.Refinement.Model.model` | operation model | — |
| `LinearSystems.Refinement.Certification.inputs`, `problem`, `program`, `algorithm`, `oracles` | certificate | — |

The parameters are accuracies of operations, not unit roundoffs: `θ` is the relative error of
the correction, `η` the residual error relative to $\|b\| + \|A\|_2\|x_j\|$, `ζ` the residual
error relative to the exact residual, `ε` the relative error of the update. In three precisions
`η` is of order $u_r$, `ζ` and `ε` of order $u$, `θ` of order $\kappa(A)u_f$. `ζ` is there
because the residual is rounded to the working precision after it is computed: that error is
relative to the residual itself and must not be charged to `η`.

No Mathlib deviation. `A`, `b` and the four accuracies are parameters of the type, unlike
`CGRun`, which bundles them: a program proof extends a run one executed step at a time, and
with parameters in the type the loop invariant is `∃ R : RefinementRun A b θ η ζ ε j, …` with
no field equalities.

## 2. Interfaces

`RefinementRun` is the hypothesis interface of the mathematics; its raw-condition constructors
are `start` (no steps) and `extend` (three local bounds at the last iterate).
`Ops.IsRefinement dec A θ η ζ ε α I` is the hypothesis interface of the routine: the three
operations satisfy their contracts. `α` is the matrix-norm allowance of the residual contract,
since a file of `NLAlib/Ops` may not name `specNorm`; the judgment and the model take
`α = specNorm A`, as `IsMatvec` is used with `em * specNorm A`.

The residual and the solve contracts name the matrix and fix the dimension to its order. The
update contract does not: it is stated at the length given by the dimension of the call, so it
is one contract at every size and input, and the model declares only `residual` and `solve` as
oracles.

## 3. Statement shapes

```lean
theorem RefinementRun.norm_sub_x_succ_le (R : RefinementRun A b θ η ζ ε k) {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (xs - R.x (j + 1))‖ ≤
      refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε * ‖WithLp.toLp 2 (xs - R.x j)‖ +
        refinementAccuracyBound (pseudoConditionNumber A) θ η ε * ‖WithLp.toLp 2 xs‖

theorem RefinementRun.norm_sub_x_le (R : RefinementRun A b θ η ζ ε k) {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b)
    (hφ : refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε < 1) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (xs - R.x j)‖ ≤ φ ^ j * ‖WithLp.toLp 2 (xs - R.x 0)‖ + ξ / (1 - φ) * ‖WithLp.toLp 2 xs‖

theorem norm_inv_mulVec_sub_le_of_add_mulVec_eq {A E : Matrix n n 𝕜} (hA : IsUnit A) {ω : ℝ}
    (hE : specNorm (A⁻¹ * E) ≤ ω) (hω : ω < 1) {d r : n → 𝕜} (hd : (A + E) *ᵥ d = r) :
    ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤ ω / (1 - ω) * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖

def solveSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (θ η ζ ε : ℝ) : Routine.Spec K :=
  spec% [m, k] (bs, xs) → (xs')
    requires m = n
    ensures ∃ R : RefinementRun A (decv dec n bs) θ η ζ ε k,
      R.x 0 = decv dec n xs ∧ R.x k = decv dec n xs'

theorem solve_meets (hI : IsRefinement dec A θ η ζ ε (specNorm A) I) (hA : IsUnit A)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec dec A θ η ζ ε)
```

with `φ`, `ξ` the two named bounds: `φ = (1+ε)(θ + (1+θ)κ(ζ+η))`, `ξ = (1+ε)(1+θ)·2κη + ε`.
General over `[RCLike 𝕜]` and a finite index type for the mathematics; real, `Fin n` for the
routine, as every Ops contract. `norm_sub_x_le` carries
`Result: iterative-refinement-forward-error`.

The specification of the routine gives the run, not a bound: every statement about a run
(the forward error now, a backward error later) is then a statement about the stored output,
and the routine has one judgment. The certificate is built with `Routine.Domain.certify`, so it
states exactly that specification, and `Certification.algorithm_checked` reads it on values:
for every invertible $A$ with $\varphi < 1$, every $b$ and $x_0$, the run succeeds within
`25 k + 15` instructions and the second buffer holds $\hat x$ with
$\|x_\star - \hat x\| \le \varphi^k\|x_\star - x_0\| + \xi\|x_\star\|/(1 - \varphi)$.

Relation to the source: [CarsonHigham2018, Theorem 3.2, Corollary 3.3] work componentwise in
the $\infty$-norm and reach $4pu_r\operatorname{cond}(A, x) + u$, with $p$ the largest number of
nonzeros in a row of $[A\ b]$. Here everything is normwise in the 2-norm, so $\kappa_2(A)$
replaces $\operatorname{cond}(A, x)$: weaker for badly scaled systems, and the form the
library's `specNorm` perturbation lemmas produce. Two further differences: the rate $\varphi$
here also contains $\kappa(\zeta + \eta)$, while theirs depends only on the solve; and the
limiting term $\xi/(1 - \varphi)$ depends on $\theta$ through $1 + \theta$ and $1 - \varphi$, a
constant factor when $\varphi$ is bounded away from one. The paper's
refinement through $\mu_i$ (convergence up to $\kappa_\infty(A)u_f < 1$ only through the
residual) is not reproduced. The backward-error results (their sections 4 and 5) are not
covered.

## 4. Consumers

`RefinementRun` is consumed by `solve_meets` now, and by any refinement routine later: each
ends a round in `R.extend`. `IsRefinement` is consumed by `solve`, and its three fields are what
the stage 3 implementations prove. `norm_inv_mulVec_sub_le_of_add_mulVec_eq` turns a backward
error of a factorization into `θ`. `solveSpec` is what a caller of `solve` uses.

## 5. Files

| File | Contents |
|---|---|
| `NLAlib/Matrix/FinitePrecision/RefinementRun.lean` | the two bounds; `RefinementRun`, `start`, `extend`; the two error theorems |
| `NLAlib/Ops/Catalog/Refinement.lean` | `RefinementOp`, the three relations, `IsRefinement`, `exists_isRefinement` |
| `NLAlib/LinearSystems/Refinement/Solve.lean` | `solve`, `solveSpec`, `solve_meets` |
| `NLAlib/LinearSystems/Refinement/Model.lean` | `Model.signature`, `Model.resources`, `Model.model`, `Model.laws`, `Model.confined_model` |
| `NLAlib/LinearSystems/Refinement/Certification.lean` | `accepts`, `inputs`, `problem`, `program`, `model`, the count, `algorithm`, `oracles`, `algorithm_checked` |
| `NLAlib/LinearSystems/Refinement/Kernels.lean` | the residual, update and cast routines |
| `NLAlib/LinearSystems/Refinement/Rounded/` | `Signature`, `Bounds`, `Solve`, `Certification`: the three-precision program and certificate |
| `NLAlib/Matrix/Factorizations/Cholesky/Routine.lean`, `TriangularSolve/{Substitution,Routine}.lean` | the kernels |
| `NLAlib/Matrix/FinitePrecision/CholeskyRoundingError.lean`, `CholeskyTraceBounds.lean` | their rounding analysis |

Additions outside the new files:

* `norm_inv_mulVec_sub_le_of_add_mulVec_eq` in `NLAlib/Matrix/Perturbation/Inverse.lean`, after
  `norm_sub_le_of_add_mulVec_eq`: it is a statement about perturbed linear systems.
* `NLAlib/Ops/Tools/LintAll.lean` imports the new catalog file.
* `docs/rules/layers.toml` and `docs/contributing/layout.md`: the folder `LinearSystems`,
  layer 1, with its generated `NLAlib/LinearSystems/RULES.md`.
* `docs/references.bib` (`CarsonHigham2018`), `docs/constants.toml` (two entries),
  `docs/contributing/vocabulary.md` (two rows), `NLAlib.lean`.

The family has no exact member, so there is no `Rounded` namespace: the accuracies are
parameters, and the exact iteration is the instance with all four equal to zero.

## 6. Material

Consulted: [CarsonHigham2018], from the authors' copy, for the algorithm and the labels of the
statements cited (Algorithm 1.1, equation (2.3), Theorem 3.2, Corollary 3.3). The proofs here are
the normwise argument, written directly; they do not follow the paper's componentwise proof.
Reused in the library: `specNorm`, `pseudoConditionNumber_of_isUnit`, `norm_toLp_mulVec_le`;
the shape of `CGRun` and of `matvecErrorRel`/`IsMatvec`; `HSPCG.Model` and
`HSCG.Certification` as the pattern of a model and a certificate with an unstored matrix.
`richardsonIterate` is the exact iteration of which this is the rounded form; no bridge is
stated, because the run has no exact preconditioner matrix to compare with.
Searched and not found: a refinement run, a relative-error solve contract, a rounded
triangular-solve routine, a rounded factorization, [CarsonHigham2018] in the bibliography.

## 7. Shared proof machinery

The judgment is `routine_intro`, `loop_inv`, three `step`s and `R.extend`; the certificate is
`Routine.Domain.certify` and the readable statement `checked_post` with `read_outputs`.
Nothing was written by hand that a rule already does. Stage 3 will repeat one argument three
times, a componentwise rounding bound turned into a Euclidean one
(`|z_i - y_i| ≤ u|y_i|` for all `i` gives `‖z - y‖ ≤ u‖y‖`); `AbsRelErr.norm_sub_le` in
`Matrix/FinitePrecision/VectorErrors.lean` is the existing lemma for it.

## Stages

1. **Run model** (done). `Matrix/FinitePrecision/RefinementRun.lean`.
2. **Routine and certificate over three abstract operations** (done). `Refinement/Solve.lean`,
   `Model.lean`, `Certification.lean`: the matrix is an unstored input and the accuracies are
   assumptions. It remains as the statement for any other implementation of the operations.
3. **Rounding mathematics and kernels** (done).
   `Matrix/FinitePrecision/CholeskyRoundingError.lean` and `CholeskyTraceBounds.lean`: for
   positive definite $A$ read with relative error $v$ and $4(n+1)^2(u+v)\kappa(A) \le 1$, every
   computed pivot is positive and $\|A - \hat L\hat L^{\mathsf T}\|_2 \le 2(n+1)^2(u+v)\|A\|_2$;
   the solve with the factors has relative error at most $24(n+1)^2(u+v)\kappa(A)$; the rounded
   residual has a normwise bound. Routines: `Cholesky.leftLooking`, `TriangularSolve.forward`,
   `TriangularSolve.backward`, `Refinement.residualRows`, `addInPlace`, `castLoop`.
4. **The three-precision program** (done). `Refinement/Rounded/`: scalar arithmetic at three
   tags and four casts, the matrix stored, no oracle. `Rounded.solve` factors at $u_f$, computes
   residuals at $u_r$ and updates at $u$, with $\theta = 24(n+1)^2(2u_f)\kappa(A)$,
   $\eta = (1+u)(n+1)\gamma_{n+1}(u_r)$ and $\zeta = \varepsilon = u$.
   `Rounded.Certification.algorithm` is uniform and confined, with closed-form work
   $52n^3 + 104n^2k + 97n^2 + 125nk + 38n + 113k + 119$ instructions.

Limits of the result: normwise in the 2-norm; the standard model on all operands, so no overflow
or underflow; narrowing casts round and widening casts are exact; memory is one abstract cell
per word, so the three formats are not given different byte widths; positive definite $A$ only.
LU with pivoting, a stopping test and concrete IEEE formats are not covered.

## The port to the routine core (2026-11-23)

Written first on `edb7e0ee`, where the program was a plain tree with an operand-form theorem
`solve_writes`. On the routine core:

* `solve` is a routine (`routine%`), with `solveSpec` and the one judgment `solve_meets`; the
  operand-form theorems `solve_writes` and `solve_writes_norm_sub_le` are gone.
* The contracts are stated with `Interp.Satisfies` and the witness with
  `Interp.IsFn.satisfies_rel`.
* The update contract no longer names the order of the matrix (section 2).
* `Model.lean` and `Certification.lean` are new: the first version had no certificate.
* `norm_inv_mulVec_sub_le_of_add_mulVec_eq` moved to its intended home.
* The solver moved from `NLAlib/Krylov/Refinement` to `NLAlib/LinearSystems/Refinement`, the
  run model from `Krylov/FinitePrecision` to `Matrix/FinitePrecision`, and
  `docs/rules/layers.toml` and the layout guide gained the entry `LinearSystems`.

## 8. Open questions

1. **Home** (decided 2026-11-23). Solvers for linear systems built on factorizations are in
   the new top-level folder `NLAlib/LinearSystems`, layer 1 (it may import `Krylov` and be
   imported by it, for refinement with a Krylov inner solver). The factorizations and the
   triangular solves of stages 3 and 4 go in `NLAlib/Matrix/Factorizations/<Name>/`, as
   modified Gram–Schmidt does, and their rounding mathematics in `Matrix/FinitePrecision`,
   where `RefinementRun.lean` is: it needs only `Matrix`. `Krylov/LinearSystems` keeps the
   mathematics of CG, GMRES and Richardson.
2. **Norm.** The 2-norm loses the componentwise condition number of the source.
   Recommendation: keep the 2-norm for the run model, which is what `specNorm` lemmas feed, and
   add a componentwise residual contract in stage 3 only if a consumer needs
   $\operatorname{cond}(A, x)$.
3. **Operation group or tagged existing groups.** `solve` could be `Tagged _ OperatorOp.matvec`
   for $A^{-1}$, as the PCG preconditioner is, but `IsMatvec` bounds the error by $\|r\|$ and
   not by $\|A^{-1}r\|$, which costs a factor $\kappa(A)$ in the convergence condition
   ($\kappa^2 u_f < 1$). Recommendation: the dedicated relative contract, as implemented.
4. **Scratch.** `r` and `d` are caller-supplied unreported operands. Allocating them inside the
   routine is a small change; it would make the interface `(b, x) → (x)`.
5. **Hypotheses of the certificate.** The four nonnegativity hypotheses on the accuracies are
   arguments of the model (its joint realization needs them), so the certificate report counts
   them. Nonnegative-real parameters would remove them at the cost of coercions in every
   statement. Recommendation: keep the hypotheses.
6. **`accepts`.** It contains $\varphi < 1$, which the run does not need to succeed, only the
   forward-error reading of the certificate. Recommendation: keep it there, where
   `algorithm_checked` shows it as a hypothesis on the input, rather than as an extra
   hypothesis of the readable statement.
