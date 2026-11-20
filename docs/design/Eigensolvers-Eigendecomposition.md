# An eigendecomposition stage on the dense Schur solver (EIG)

*Design note, read-only against `origin/main` at `edb7e0ee` (2026-11-20). Destination:
`docs/design/Eigensolvers-Eigendecomposition.md`. It builds on
[Eigensolvers-DenseSchur](Eigensolvers-DenseSchur.md) (SCHUR, merged), the sizing study
`Sizing-Eigendecomposition.md`, and the verified Schur solver in progress (branch
`feat/schur-verified`, worktree `nlalib-schur-verified`: `Verified.lean`, `ResidualCheck.lean`). Every
Lean statement and definition of this note was elaborated with `sorry` proofs against
`feat/schur-verified` at `ba5ad537` (main, the verified Schur solver and `feat/schur-tighten`); the
fixes are listed in §13. Internal constants may move at proof time (O7). The headline's $K$, gap and
tolerances do not move.*

**Status.** The maintainer approved the stage on 2026-11-20, with options O1–O10 as recommended
(`state/decisions/RESEARCH-TRACK.json`, item 1). The design review
(`Review-Fable-EIG-Design.md`, verdict "revise, then skeleton") is applied in full. The changes are
listed in §12.

## 0. Summary

* **Headline (§1).** Take any $\mathbf{A} \in \mathbb{C}^{(n+1)\times(n+1)}$, $0 < \delta \le 1$,
  $0 < \varphi \le 1$ and $\boldsymbol{u} \le \boldsymbol{u}_E(n,\delta,\varphi)$. With probability
  $\ge 1 - \varphi$, the program `denseEig` stores the flag $0$, the Schur pair
  $(\widehat{\mathbf{U}}, \widehat{\mathbf{T}})$ of SCHUR, and a matrix $\widehat{\mathbf{V}}$. With
  $\widehat{\mathbf{D}} = \operatorname{diag}(\hat t_{11}, \dots, \hat t_{NN})$ and $N = n + 1$:
  1. **residual.** For every column, $\|\mathbf{A}\hat{\mathbf{v}}_j - \hat t_{jj}\hat{\mathbf{v}}_j\| \le
     \delta\|\mathbf{A}\|_2\|\hat{\mathbf{v}}_j\|$. For the whole matrix,
     $\|\mathbf{A}\widehat{\mathbf{V}} - \widehat{\mathbf{V}}\widehat{\mathbf{D}}\|_2 \le
     \delta\|\mathbf{A}\|_2\|\widehat{\mathbf{V}}\|_2$. Every column has norm in $[7/8, 9/8]$.
  2. **conditioning.** $\widehat{\mathbf{V}}$ is invertible and
     $\kappa(\widehat{\mathbf{V}}) \le 2\sqrt N B$. Here $B$ = `denseSchurB n δ φ`
     $\le 2^{36}N^4W^2/(\delta^2\varphi)$ and $W = 3 + \sqrt{\log(8/\varphi)}$ (EM5).
  3. **backward form.** $\|\widehat{\mathbf{V}}\widehat{\mathbf{D}}\widehat{\mathbf{V}}^{-1} - \mathbf{A}\|_2 \le
     \delta\|\mathbf{A}\|_2$.
  4. **separation.** $|\hat t_{ii} - \hat t_{jj}| \ge (\Gamma/4)\|\mathbf{A}\|_2$ for $i \ne j$. Here
     $\Gamma$ = `denseSchurΓ n δ φ` $\ge \delta^7\varphi^3/(2^{134}N^{29/2}W^7)$ (EM5, with the
     gap tail $(2048e, 11/3, 2/3, 2)$ of `feat/schur-tighten`).

  The bits satisfy $\log_2(1/\boldsymbol{u}_E) \le c_1L^4(\log_2L+1)^2 + c_2$. The static count is
  $\le C N^3 L^9(\log_2L+1)^6$. There is a certificate. The run terminates on every tape.
* **Theory first (§2).** These results do not mention programs:
  * **T1.** A componentwise backward solution has a small residual (Oettli–Prager, both
    directions). Applied to the shifted triangular systems, it gives each eigenvector's residual
    **without a gap**.
  * **T2.** Approximate eigenvectors of a matrix with $\kappa_V \le B$ and gap $\ge \Gamma$ are well
    conditioned: $\kappa \le \tfrac75\sqrt N B\cdot m'/m$. No van der Sluis step is needed.
  * **T3.** The column and matrix algebra from a Schur form plus triangular eigenvectors to an
    eigendecomposition residual. T3 also covers the backward form and the separation of the Schur
    diagonal.
  * **T4** (EM4). The whole composition as a matrix theorem, with items 1–4 from plain matrix
    hypotheses. It has a residual-only sibling.

  The program theorems are T4 plus plumbing.
* **A swappable stage (§3).** `EigenvectorStageContract` is stated normwise and is not tied to a
  method. It promises: per-column residuals of $\mathbf{Y}$ against $\mathbf{T}$, column norms,
  $\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|$, a flag that is complete under a gap $g_0$, and exact output
  at $\mathbf{T} = 0$. The stage owns its parameter slice. The instance is back substitution with a
  pivot floor (xTREVC). T1 and the triangular predicate are used only inside the instance.
* **Composition (§4).**
  * `eigSolverWith Solve Ev : (A, P, Pe) → (A, U, V, Fl)` runs any Schur solver and then the stage
    on its **own** operand `Pe`.
  * The pipeline exposes $\mathbf{X}$ (`RegularizedSchurOutput`, PP2X, with a split budget lemma).
  * The dense layer gets two tolerances (`…At n δR δC φ`).
* **Verification (§6).** With the verified Schur solver, flag $0$ certifies three things on every
  tape: the Schur output, the eigenvalue listing, and item 1. No new check is needed. A bound on
  $\kappa$ is certifiable in $O(N^3)$ (follow-up EIG-V). Item 3 on every tape needs a checkpoint of
  $\mathbf{X}$.
* **17 targets** (§8), about 6.5k lines, six waves.

## 1. The headline, in Lean (not elaborated)

```lean
namespace NLAlib.Schur

/-- The input of the eigen solver: the pipeline's input for the solver words `qs` in `P`, the
stage's words `qe` in `Pe`, and room for `V`; the six blocks live and pairwise apart. -/
def EigSolverInput {n : ℕ} (qs qe : List ℝ) (a p pe uo v f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  SchurPipelineInput qs a p uo f A μ ∧ μ.Live [pe, v] ∧
    μ.Room [pe, v] [qe.length, 2 * ((n + 1) * (n + 1))] ∧
    Fp.Apart [a, p, uo, f, pe, v] [2 * ((n + 1) * (n + 1)), qs.length,
      2 * ((n + 1) * (n + 1)), 1, qe.length, 2 * ((n + 1) * (n + 1))] ∧
    μ.store.readBlock pe.1 pe.2 qe.length = some qe

/-- The blocks the eigen solver writes. -/
def eigFp (n : ℕ) (a uo v f : ℕ × ℕ) : Fp :=
  schurFp n a uo f ⊔ Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))

/-- The part of an eigendecomposition that a certified Schur output certifies on every tape
(§6): column norms within `c` of `1`, the column residuals within `eC`, and the matrix residual
within `eM`, relative to `‖A‖₂`. -/
def EigResidual {n : ℕ} (a v : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c : ℝ) (μ' : Mem ℝ) : Prop :=
  ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
    HoldsMatrix v V μ'.store ∧ EigResidualOf A T V eC eM c

/-- The matrix content of `EigResidual` (shared with EM4; namespace `NLAlib`, file
`Matrix/Perturbation/ApproximateEigendecomposition`, shown here for reading). -/
def EigResidualOf {n : ℕ} (A T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c : ℝ) : Prop :=
  (∀ j, |‖WithLp.toLp 2 (V.col j)‖ - 1| ≤ c) ∧
  (∀ j, ‖WithLp.toLp 2 ((A - T j j • 1) *ᵥ V.col j)‖ ≤ eC * specNorm A * ‖WithLp.toLp 2 (V.col j)‖) ∧
  specNorm (A * V - V * Matrix.diagonal (fun i => T i i)) ≤ eM * specNorm A * specNorm V

/-- The matrix content of an eigendecomposition output: the residual part, `V` invertible with
$\kappa(\mathbf{V}) \le K$, the backward form (no `∃ E`, which keeps it measurable), and the
gaps of the diagonal. -/
def EigDecompOf {n : ℕ} (A T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) : Prop :=
  EigResidualOf A T V eC eM c ∧ IsUnit V ∧ pseudoConditionNumber V ≤ K ∧
    specNorm (V * Matrix.diagonal (fun i => T i i) * V⁻¹ - A) ≤ eE * specNorm A ∧
    ∀ i j, i ≠ j → g * specNorm A ≤ ‖T i i - T j j‖

/-- **An eigendecomposition output**: flag `0` and one stored pair `(T, V)` with `EigDecompOf`. -/
def EigOutput {n : ℕ} (a v f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix v V μ'.store ∧ EigDecompOf A T V eC eM c eE K g

/-- HE1: the dense eigendecomposition theorem. Result: dense-eigendecomposition -/
theorem denseEig_measureReal_not_eig_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseEig n δ φ)
    {a p pe uo v f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : EigSolverInput (denseEigSchurParams n δ φ) [denseEigFloor n δ φ] a p pe uo v f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseEig (O := O) (Q := Q) sG).body
      (Env.frame (denseEigDims n δ φ) [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOutput a uo f A δ (58 * denseEigRotations n δ φ * u) μ' ∧
        EigOutput a v f A δ δ (1 / 8) δ (2 * √((n : ℝ) + 1) * denseSchurB n δ φ)
          (denseSchurΓ n δ φ / 4) μ') μ} ≤ φ
```

Here `denseEig sG = eigSolverWith (denseSchurAt sG …) triEigvecStage`. The interface is
`[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`, with `Pe` holding the single word $\rho$ =
`denseEigFloor n δ φ` (`Algorithm: dense-eigendecomposition`).

Companions (namespace `NLAlib.Schur`):

* **HE2** `denseEig_terminates`. On every tape, for $\boldsymbol{u} \le \boldsymbol{u}_E$, the run
  is total. It writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the flag,
  and it keeps `SchurOrth`.
* **HE3** `logb_inv_uDenseEig_le`: $\log_2(1/\boldsymbol{u}_E) \le c_1L^4(\log_2L+1)^2 + c_2$.
  This uses $\log(1/\delta_C) = O(L)$, which follows from EM5.
* **HE4** `denseEig_work_le`, `denseEig_work_le_polylog`: the Schur count at $\delta_C$, plus
  $c_E N^3$, plus the glue; in polylog form $C N^3L^9(\log_2L+1)^6$, the merged dense Schur form at
  $\delta_C$ ($\log(1/\delta_C) = O(L)$).
* **CT** `denseEigAlgorithm`, `denseEig_algorithm_measureReal_not_accepts_le`.

The forward eigenvalue bound is not planned (O8): it is one line from item 3 and has no consumer.
O8 as revised (§12) does put the **column residual** and the **closed forms of B and Γ** in the
plan.

## 2. Theory: program-free numerical analysis

Index types are a general `[Fintype n] [DecidableEq n]` where the mathematics allows it, over an
`RCLike` field `𝕜` where it applies. `Fin (n + 1)` is used only where a merged lemma requires it.

### 2.1 Perturbed linear systems (T1)

```lean
namespace NLAlib

/-- `x` solves `M x = b` up to a componentwise relative perturbation `ε` of `M` and an absolute
perturbation of at most `σ` on its diagonal. -/
def IsComponentwiseBackwardSolution (ε σ : ℝ) (M : Matrix n n 𝕜) (b x : n → 𝕜) : Prop :=
  ∃ Δ : Matrix n n 𝕜, (∀ i k, ‖Δ i k‖ ≤ ε * ‖M i k‖ + if i = k then σ else 0) ∧
    (M + Δ) *ᵥ x = b

/-- T1a: the residual. -/
theorem IsComponentwiseBackwardSolution.norm_mulVec_sub_le
    (h : IsComponentwiseBackwardSolution ε σ M b x) (hε : 0 ≤ ε) (hσ : 0 ≤ σ) :
    ‖WithLp.toLp 2 (M *ᵥ x - b)‖ ≤ (ε * frobNorm M + σ) * ‖WithLp.toLp 2 x‖

/-- T1b (Oettli–Prager, the direction a program proof uses). -/
theorem isComponentwiseBackwardSolution_of_norm_sub_le (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (h : ∀ i, ‖(M *ᵥ x - b) i‖ ≤ ε * ∑ k, ‖M i k‖ * ‖x k‖ + σ * ‖x i‖) :
    IsComponentwiseBackwardSolution ε σ M b x
```

**T1a.** $Mx - b = -\Delta x$, so $|(\Delta x)_i| \le \varepsilon(|M||x|)_i + \sigma|x_i|$. Then
$\||M||x|\| \le \|M\|_{\mathsf F}\|x\|$ by Cauchy–Schwarz on each row.

**T1b.** Let $r = Mx - b$, $w_{ik} = \varepsilon|m_{ik}| + \sigma[i=k]$ and $S_i = \sum_k
w_{ik}|x_k|$. Put $\Delta_{ik} = -r_iw_{ik}\overline{\operatorname{sgn}x_k}/S_i$, and set row $i$ to
zero when $S_i = 0$. Mathlib has nothing like this (searched: Oettli, Rigal, componentwise).

### 2.2 Triangular eigenvectors: residual without a gap

```lean
/-- `Y` is an approximate eigenbasis of `T` by back substitution: each column has norm within `η`
of `1` and is a componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = 0$. -/
def IsTriangularEigenbasisApprox (ε σ η : ℝ) (T Y : Matrix n n 𝕜) : Prop :=
  ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ η ∧
    IsComponentwiseBackwardSolution ε σ (T - T j j • 1) 0 (Y.col j)

/-- The column residual: gap-free and structure-free. -/
theorem IsTriangularEigenbasisApprox.norm_mulVec_col_le
    (h : IsTriangularEigenbasisApprox ε σ η T Y) (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (j : n) :
    ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤
      (ε * (1 + √(Fintype.card n : ℝ)) * frobNorm T + σ) * ‖WithLp.toLp 2 (Y.col j)‖
```

The proof is T1a with $\|\mathbf{T} - t_{jj}\mathbf{I}\|_{\mathsf F} \le (1+\sqrt N)\|\mathbf{T}\|_{\mathsf F}$.
For $\mathbf{y}_j = (\mathbf{x};1;0)$, the shifted system with a perturbed matrix **and** a perturbed
right-hand side is exactly $(\mathbf{T} - t_{jj}\mathbf{I} + \Delta)\mathbf{y}_j = 0$. These all go
into $\Delta$:
* the rounding of the shift;
* the normalization, which multiplies by a real factor with complex rounding $\theta_i$. This makes
  $\sigma$ larger by a factor $1/(1-3\boldsymbol{u})$, inside the slack of $3s_{\min} \le
  4\rho\|\mathbf{T}\|_{\mathsf F}$;
* the pivot floor.

The matrix-level bound (Frobenius over the columns) is not a separate theorem. The contract and
EM4 use the column form (S2).

### 2.3 Approximate eigenvectors of a well-conditioned matrix (T2)

```lean
theorem IsConditionedDiagonalizable.smul (h : IsConditionedDiagonalizable B Γ A) (c : ℂ) :
    IsConditionedDiagonalizable B (‖c‖ * Γ) (c • A)

theorem IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual
    {B Γ η m m' : ℝ} {M V : Matrix n n ℂ} {ev : n → ℂ}
    (hM : IsConditionedDiagonalizable B Γ M) (hΓ : 0 < Γ) (hη : 0 ≤ η)
    (hsmall : 8 * √(Fintype.card n : ℝ) * B * η ≤ Γ) (hm : 0 < m)
    (hcol : ∀ j, m ≤ ‖WithLp.toLp 2 (V.col j)‖ ∧ ‖WithLp.toLp 2 (V.col j)‖ ≤ m')
    (hres : ∀ j, ‖WithLp.toLp 2 ((M - ev j • 1) *ᵥ V.col j)‖ ≤ η * ‖WithLp.toLp 2 (V.col j)‖)
    (hsep : ∀ i j, i ≠ j → Γ / 2 ≤ ‖ev i - ev j‖) :
    IsUnit V ∧ m * specNorm V⁻¹ ≤ 7 / 5 * B ∧
      pseudoConditionNumber V ≤ 7 / 5 * √(Fintype.card n : ℝ) * B * (m' / m)
```

The proof is about 250 lines; the review re-derived it. It has five steps:
1. Bauer–Fike puts each $\mathrm{ev}_j$ within $\kappa\eta \le \Gamma/8$ of some $d_{\pi(j)}$.
2. $\pi$ is injective, because $2B\eta \le \Gamma/4 < \Gamma/2$.
3. The off part of $\mathbf{W}^{-1}\mathbf{v}_j$ is $\le \tfrac87\|\mathbf{W}^{-1}\|\eta\|\mathbf{v}_j\|/\Gamma$.
   The main entry is $\ge \tfrac67\|\mathbf{v}_j\|/\|\mathbf{W}\|$.
4. $\mathbf{W}^{-1}\mathbf{V} = \mathbf{P}_\pi(\mathbf{I}+\mathbf{G})\boldsymbol\Lambda$ with
   $\|\mathbf{G}\|_{\mathsf F} \le 1/6$. Neumann applies (`Matrix/Perturbation/Inverse`).
5. Hence $\|\mathbf{V}^{-1}\| \le \tfrac75\kappa/m$ and $\|\mathbf{V}\| \le \sqrt N m'$.

The sizing's van der Sluis step (E1) is dropped. Both $0 < \Gamma$ and the separation hypothesis are
needed. T2 consumes **column** residuals in the units of $\mathbf{M}$.

### 2.4 A gap of T alone does not bound the conditioning

Take $\mathbf{T}$ with superdiagonal $1$ and diagonal $0, \Gamma, 2\Gamma, \dots$. Then
$\kappa(\mathbf{Y}) \gtrsim (\|\mathbf{T}\|/\Gamma)^{N-1}/(N-1)!$, which is $N^{\Theta(N)}$ at the
Ginibre gaps. So the conditioning has to come from the class of the regularized $\mathbf{X}$, and T2
is applied at $s^{-1}\mathbf{X}$. Reading T2 at the triangular level instead is not planned (O5).

### 2.5 From a Schur form to an eigendecomposition (T3)

```lean
/-- T3a, column form: for any `Z`, a column `y` of `Y` and the column `v` of `V`. -/
theorem norm_mulVec_sub_smul_le_of_schur (Z U T : Matrix n n ℂ) (y v : n → ℂ) (μ : ℂ) :
    ‖WithLp.toLp 2 ((Z - μ • 1) *ᵥ v)‖ ≤
      (specNorm (Z - U * T * Uᴴ) * specNorm U +
          specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * ‖WithLp.toLp 2 y‖ +
        specNorm U * ‖WithLp.toLp 2 ((T - μ • 1) *ᵥ y)‖ +
        (specNorm Z + ‖μ‖) * ‖WithLp.toLp 2 (v - U *ᵥ y)‖

/-- T3a, matrix form. -/
theorem specNorm_mul_sub_mul_diagonal_le_of_schur (Z U T Y V : Matrix n n ℂ) (d : n → ℂ) :
    specNorm (Z * V - V * Matrix.diagonal d) ≤
      (specNorm (Z - U * T * Uᴴ) * specNorm U +
          specNorm U * specNorm T * specNorm (Uᴴ * U - 1)) * specNorm Y +
        specNorm U * specNorm (T * Y - Y * Matrix.diagonal d) +
        (specNorm Z + specNorm (Matrix.diagonal d)) * specNorm (V - U * Y)

/-- Near-orthonormal `U`: $\|\mathbf{U}\mathbf{x}\| \ge \sqrt{1 - e}\,\|\mathbf{x}\|$ (search
`Residual.lean`, `OrthErr.lean` first). -/
theorem sqrt_one_sub_mul_norm_le_norm_mulVec (hU : specNorm (Uᴴ * U - 1) ≤ e) (he : e ≤ 1) (x) :
    √(1 - e) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (U *ᵥ x)‖

/-- T3b: the backward form. -/
theorem specNorm_mul_diagonal_mul_inv_sub_le {Z V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V) :
    specNorm (V * Matrix.diagonal d * V⁻¹ - Z) ≤
      specNorm (Z * V - V * Matrix.diagonal d) * specNorm V⁻¹

/-- T3c: the Schur diagonal of a perturbed class matrix is separated. -/
theorem IsConditionedDiagonalizable.le_norm_sub_diag_of_add_eq {n : ℕ} {B Γ : ℝ}
    {X E W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hX : IsConditionedDiagonalizable B Γ X)
    (hΓ : 0 < Γ) (hW : HasOrthonormalCols W) (hT : T.IsUpperTriangular)
    (hXE : X + E = W * T * Wᴴ) (hE : specNorm E ≤ Γ / (16 * (n + 1) * B)) :
    ∀ i j, i ≠ j → 7 / 8 * Γ ≤ ‖T i i - T j j‖
```

The column form has no $\sqrt N$ on its main term $\|\mathbf{Z} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|\|\mathbf{U}\|\|\mathbf{y}\|$
(S2). T3c follows from `exists_isEigenvalueListing_norm_sub_le_of_class` with $\mathbf{E}_1 = 0$, and
the listing of the diagonal (`isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul`).

### 2.6 The composition as a matrix theorem (T4, EM4)

```lean
/-- The column residual budget: the residual of a column of `V` against `Z`, in units of
$\|\mathbf{A}\|_2\|\mathbf{v}_j\|$, when the Schur error against `Z` is `e` (in units of `‖A‖₂`).
Valid under `e + eR ≤ 1/2`, `eU ≤ 1/8`, `cN + 2 eU + 2 cV N ≤ 1/8` (§2.6). -/
noncomputable def eigEta (n : ℕ) (e eU cR cV : ℝ) : ℝ :=
  2 * e + 3 * eU + 4 * √((n : ℝ) + 1) * cR + 8 * ((n : ℝ) + 1) * cV

/-- The column-norm tolerance of `V`. -/
noncomputable def eigColTol (n : ℕ) (eU cV cN : ℝ) : ℝ := cN + 2 * eU + 2 * ((n : ℝ) + 1) * cV

/-- T4 (EM4): an eigendecomposition from a Schur form of a regularized matrix, program-free. -/
theorem eigDecompOf_of_schur {n : ℕ} {A X U T Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {s c₁ B Γ eR eX eU cR cV cN : ℝ}
    (hT : T.IsUpperTriangular) (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hAX : specNorm (A - X) ≤ eR * specNorm A) (hXT : specNorm (X - U * T * Uᴴ) ≤ eX * specNorm A)
    (hs : c₁ * frobNorm A ≤ s) (hc₁ : 0 < c₁) (hA : A ≠ 0)
    (hC : IsConditionedDiagonalizable B Γ (s⁻¹ • X)) (hΓ : 0 < Γ)
    (hY : ∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
      ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤ cR * frobNorm T * ‖WithLp.toLp 2 (Y.col j)‖)
    (hV : specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y)
    (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR cV ≤ c₁ * Γ) :
    EigDecompOf A T V (eR + eigEta n eX eU cR cV) (eR + √((n : ℝ) + 1) * eigEta n eX eU cR cV)
      (eigColTol n eU cV cN) (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR cV)
      (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ)

/-- T4' (EM4, residual only, for the verified composition): from a Schur form of `A` itself. -/
theorem eigResidualOf_of_schur {n : ℕ} {A U T Y V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eA eU cR cV cN : ℝ} (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (hAT : specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A) (hY : …as above…) (hV : …as above…)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8) :
    EigResidualOf A T V (eigEta n eA eU cR cV) (√((n : ℝ) + 1) * eigEta n eA eU cR cV)
      (eigColTol n eU cV cN)
```

**Constants, re-derived.**
* Under the stated bounds, $\|\mathbf{U}\| \le \sqrt{9/8}$ and $\|\mathbf{T}\| \le \tfrac87(1 + e_R +
  e_X)\|\mathbf{A}\| \le 2\|\mathbf{A}\|$. Also $\|\mathbf{X}\| \le 2\|\mathbf{A}\|$,
  $\|\mathbf{y}_j\|/\|\mathbf{v}_j\| \le (1 + c_N)/(1 - c) \le 1.4$, and
  $\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F} \le 1.25N$.
* Each term of the column T3a at $\mathbf{Z} = \mathbf{X}$ is then at most its term in `eigEta`.
  The same estimate at $\mathbf{Z} = \mathbf{A}$ goes through $\mathbf{X}$: the column residual is
  $\le e_R + \eta$, and the matrix residual is $\le (e_R + \sqrt N\eta)$ (the $\sqrt N$ falls only on
  $\eta$, through the Frobenius sum).
* **Conditioning.** T2 at $s^{-1}\mathbf{X}$ with $\mathrm{ev}_j = s^{-1}\hat t_{jj}$ and
  $\eta_{T2} = \eta\|\mathbf{A}\|/s \le \eta/c_1$ (`hκ`) gives $\kappa \le \tfrac75\tfrac{1+c}{1-c}\sqrt NB
  \le 2\sqrt NB$ for $c \le 1/8 < 3/17$.
* **Separation.** T3c at $s^{-1}\mathbf{X}$, with $\|\mathbf{E}\| \le (e_X + 4e_U(1 + e_R + e_X))\|\mathbf{A}\|/s
  \le (e_X + 6e_U)/c_1$ (`hsep`), gives $\tfrac78 s\Gamma \ge \tfrac78c_1\Gamma\|\mathbf{A}\|$ (S3).
* **Backward form.** T3b with the matrix residual against $\mathbf{X}$ ($\sqrt N\eta\|\mathbf{A}\|\|\mathbf{V}\|$)
  gives $e_E = e_R + \sqrt N\eta\cdot2\sqrt NB$.
* `hA : A ≠ 0` is used because the class is impossible for $\mathbf{X} = 0$ when $N \ge 2$. The case
  $\mathbf{A} = 0$ is handled by the contract's clause for $\mathbf{T} = 0$ (B1, §4.3).

## 3. The eigenvector stage

### 3.1 The contract (normwise, not tied to a method; B1, B2, S1)

```lean
namespace NLAlib.Schur

/-- **The eigenvector stage** `[N, ne] (T, U, Pe) → (V, G)`, its `ne` words `ps` in `Pe`:
deterministic and total for any stored pair. It stores a flag `0` or `1`. For `T = 0` it stores
`V = U` exactly and the flag `0`. For an upper triangular `T` it stores `V` within
`cV‖U‖_F‖Y‖_F` of `U Y`, where the columns of `Y` have norm within `cN` of `1` and residual
$\|(\mathbf{T} - t_{jj})\mathbf{y}_j\| \le c_R\|\mathbf{T}\|_{\mathsf F}\|\mathbf{y}_j\|$ (`cR₀` when
the flag is `0`). The flag is `0` when the diagonal gaps exceed `g₀‖T‖_F`. -/
def EigenvectorStageContract (cR₀ cR cV cN g₀ : ℝ) (nmax : ℕ) (ps : List ℝ) (Ev : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a uo pe v g : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (U T : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsSchurPair a uo U T μ.store →
    μ.store.readBlock pe.1 pe.2 ps.length = some ps → μ.Live [a, uo, pe, v, g] →
    μ.Room [v, g] [2 * (N * N), 1] →
    Fp.Apart [a, uo, pe, v, g] [2 * (N * N), 2 * (N * N), ps.length, 2 * (N * N), 1] →
    Writes .total I tape Ev.body (Env.frame [N, ps.length] [a, uo, pe, v, g])
      (Store.inBlock v.1 v.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ V : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix v V μ'.store ∧
        (μ'.store.get g.1 g.2 = some 0 ∨ μ'.store.get g.1 g.2 = some 1) ∧
        (T = 0 → V = U ∧ μ'.store.get g.1 g.2 = some 0) ∧
        (T.IsUpperTriangular →
          (∃ Y : Matrix (Fin N) (Fin N) ℂ,
            (∀ j, |‖WithLp.toLp 2 (Y.col j)‖ - 1| ≤ cN ∧
              ‖WithLp.toLp 2 ((T - T j j • 1) *ᵥ Y.col j)‖ ≤
                (if μ'.store.get g.1 g.2 = some 0 then cR₀ else cR) * frobNorm T *
                  ‖WithLp.toLp 2 (Y.col j)‖) ∧
            specNorm (V - U * Y) ≤ cV * frobNorm U * frobNorm Y) ∧
          ((∀ i j, i ≠ j → g₀ * frobNorm T < ‖T i i - T j j‖) →
            μ'.store.get g.1 g.2 = some 0))) μ

/-- **A stage that completes** (no rounding model): total on every tape for any stored pair,
writing only `V` and the flag, and storing a matrix and a word. -/
def CompletingEigenvectorStage (nmax : ℕ) (ps : List ℝ) (Ev : Impl O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {N : ℕ} {a uo pe v g : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (U T : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsSchurPair a uo U T μ.store →
    μ.store.readBlock pe.1 pe.2 ps.length = some ps → μ.Live [a, uo, pe, v, g] →
    μ.Room [v, g] [2 * (N * N), 1] →
    Fp.Apart [a, uo, pe, v, g] [2 * (N * N), 2 * (N * N), ps.length, 2 * (N * N), 1] →
    Writes .total I tape Ev.body (Env.frame [N, ps.length] [a, uo, pe, v, g])
      (Store.inBlock v.1 v.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∃ V : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix v V μ'.store) ∧
        ∃ x : ℝ, μ'.store.get g.1 g.2 = some x) μ
```

These are the clauses EP3 and EP4 use: column residuals, column norms, $\|\mathbf{V} - \mathbf{U}\mathbf{Y}\|$,
flag completeness, and the case $\mathbf{T} = 0$.
* The two-tier residual (`cR₀` on flag $0$) is the soundness clause of S1. On flag $0$, EP4's
  residual does not depend on the floor.
* `IsTriangularEigenbasisApprox`, T1 and the pivot floor do not appear in the contract. They live
  in the instance.
* The stage owns its parameter slice `ps` (B2), as every merged stage does.

**Instances.**
* This stage: `triEigvecStage`, with
  `triEigvecStage_eigenvectorStageContract (hρ : 0 < ρ) : EigenvectorStageContract cR₀ (cR₀ + 4ρ) cV cN (4ρ) nmax [ρ] triEigvecStage I`.
  The constants are $c_{R,0} = 16(1 + \sqrt{n_{\max}})(n_{\max}+1)\boldsymbol{u}$, $c_V = 8(n_{\max}+1)\boldsymbol{u}$
  and $c_N = 4(n_{\max}+2)\boldsymbol{u}$, under $64(n_{\max}+1)\boldsymbol{u} \le 1$.
* Later: inverse iteration on $\widehat{\mathbf{T}}$ (a random variant of this contract), or any
  method with normwise column residuals. These are listed, not planned.

### 3.2 The program

`triEigvecStage : [N, ne] (T, U, Pe) → (V, G)`, with $\rho$ = `Pe[0]`:

1. $\hat s$ := `frobNormStage [N] (T)`.
2. If $\hat s \le 0$ (only $\mathbf{T} = 0$): $\widehat{\mathbf{V}} :=$ an exact copy of $\widehat{\mathbf{U}}$,
   and $G := 0$. This is the contract's clause for $\mathbf{T} = 0$.
3. Otherwise set $s_{\min} := \mathrm{fl}(\rho\hat s)$ and $G := 0$. For each $j < N$, run `triEigColumn`:
   * `shiftedTriSolve [N, j]`. For $i = j-1, \dots, 0$:
     * $\hat m := \mathrm{fl}(t_{ii} - t_{jj})$;
     * if $\mathrm{fl}(|\hat m|^2) \le \mathrm{fl}(s_{\min}^2)$, then $\hat m := s_{\min}$ and $G := 1$;
     * $\hat s_i := \mathrm{fl}(-t_{ij} - \sum_{i<k<j}t_{ik}\hat x_k)$;
     * $\hat x_i := \mathrm{fl}(\hat s_i/\hat m)$.
   * $\hat{\mathbf{y}}_j := (\hat{\mathbf{x}};1;0)$.
   * Normalize by $\mathrm{fl}(1/\mathrm{fl}\|\hat{\mathbf{y}}_j\|)$. The norm is $\ge 1$ because of the unit entry.
4. $\widehat{\mathbf{V}} := $ `matMulOn [N, N, N, N, N, N, 0] (U, Y)` (merged, error $8(N+1)\boldsymbol{u}\|\mathbf{U}\|_{\mathsf F}\|\mathbf{Y}\|_{\mathsf F}$).

**From the program to the contract.**
* EF2 proves a per-row residual bound for the chain:
  $\gamma_{cN}(|t_{ij}| + \sum|t_{ik}||\hat x_k|)$, plus the shift $\boldsymbol{u}$, the division
  $c_d\boldsymbol{u}$ (EF1) and the floor $\le 3s_{\min}$.
* T1b turns that bound into `IsComponentwiseBackwardSolution` (EF2).
* EF3 gets `IsTriangularEigenbasisApprox` after normalization.
* `IsTriangularEigenbasisApprox.norm_mulVec_col_le` gives the contract's normwise column residual, with
  $\varepsilon(1+\sqrt N) + 4\rho = c_R$ in general and $c_{R,0}$ when no pivot was floored (EF4).

**Cost.** About $N^3/6$ multiply–adds for the solves, $N^3$ for the product, $O(N^2)$ divisions and
$N$ square roots. The static count is $\le c_EN^3$.

## 4. Composition

### 4.1 The pipeline exposes X (PP2X, with a split budget; S4)

```lean
def RegularizedSchurOutput {n : ℕ} (C : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop)
    (a uo f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c₁ c₂ eR eX eU : ℝ)
    (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ U T X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix uo U μ'.store ∧ T.IsUpperTriangular ∧
    specNorm (Uᴴ * U - 1) ≤ eU ∧ specNorm (A - X) ≤ eR * specNorm A ∧
    specNorm (X - U * T * Uᴴ) ≤ eX * specNorm A ∧
    (A = 0 ∨ ∃ s : ℝ, c₁ * frobNorm A ≤ s ∧ s ≤ c₂ * frobNorm A ∧ C (s⁻¹ • X))

theorem RegularizedSchurOutput.schurOutput (h : RegularizedSchurOutput C a uo f A c₁ c₂ eR eX eU μ') :
    SchurOutput a uo f A (eR + eX) eU μ'

/-- The split budget: the regularizer's part and the rest, with the scale-back rounding kept as a
`u`-term in `eX` (not absorbed into `δR` as `schurPipeline_budget_round` does). -/
theorem schurPipeline_budget_split {a F s c₁ c₂ x u δR εHT εCT ε t₁ t₂ : ℝ} (ha : 0 ≤ a)
    (hF0 : 0 ≤ F) (hFa : F ≤ x * a) (hx : 1 ≤ x) (hxu : x * x * u ≤ 1 / 32) (hu : 0 ≤ u)
    (hc₁ : 0 < c₁) (hs : 0 < s) (hsl : c₁ * F ≤ s) (hsu : s ≤ c₂ * F)
    (ht₁a : s * t₁ ≤ a + 3 * u * F) (ht₁F : s * t₁ ≤ (1 + 3 * u) * F) (ht₂ : t₂ ≤ t₁ + δR)
    (ht₂0 : 0 ≤ t₂) (hδR0 : 0 ≤ δR) (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT)
    (hεHT : εHT ≤ 1 / 8) (hεCT : 0 ≤ εCT) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) :
    s * δR + 3 * u * F ≤ (c₂ * x * δR + 3 * x * u) * a ∧
    s * ((εHT * t₂ + εCT) + (2 * ε + ε ^ 2) * (t₂ + (εHT * t₂ + εCT))) +
        (1 + ε) ^ 2 * u * s * x * (t₂ + (εHT * t₂ + εCT)) ≤
      (2 * c₂ * x * (3 * εHT / c₁ + εCT + 8 * ε / c₁) + (8 + 2 * c₂ / c₁) * (x * x) * u) * a

noncomputable def schurPipelineEX (n : ℕ) (c₁ c₂ u εHT εCT ε : ℝ) : ℝ :=
  2 * c₂ * √((n : ℝ) + 1) * (3 * εHT / c₁ + εCT + 8 * ε / c₁) +
    (8 + 2 * c₂ / c₁) * ((n : ℝ) + 1) * u

/-- PP2X: the hypotheses of PP2; the pipeline's `PWrites` form and its `measureReal` form. -/
theorem schurPipelineWith_pwrites_regularizedSchur [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Impl O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} :
    PWrites law I (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurPipelineInput (qR ++ qC) a p uo f A)
      (RegularizedSchurOutput C a uo f A c₁ c₂
        (c₂ * √((n : ℝ) + 1) * δR + 3 * √((n : ℝ) + 1) * u)
        (schurPipelineEX n c₁ c₂ u εHT εCT ((1 + εHU) * (1 + εCU) - 1))
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) (φR + φC)
```

The scale-back rounding of the regularizer's part, $(1+\varepsilon)^2\boldsymbol{u}\sqrt N\cdot
c_2\sqrt N\delta_R\|\mathbf{A}\|_2 \le 1.27(c_2/c_1)N\boldsymbol{u}\|\mathbf{A}\|_2$, is a
$u$-term of $e_X$; hence the factor $N$ on $2c_2/c_1$ in `schurPipelineEX` (§13).

**PP2 is not a literal corollary** (S4). The merged budget absorbs the scale-back rounding into
$\delta_R$ through the slack $c_2\sqrt N\delta_R$. PP2 has no lower bound on $\delta_R$, so
$e_R + e_X \le$ merged $e_A$ cannot be proved in general. EP1 therefore:
* restructures the merged proof into one shared core, `schurPipeline_pos_run`: the good event with
  the stored pieces ($s$, $\mathbf{A}'$, $\mathbf{E}$, the tracked relation);
* proves PP2 from that core with the merged `schurPipeline_budget`, so its statement and numeral are
  unchanged;
* proves PP2X from the same core with `schurPipeline_budget_split`.

Both theorems are corollaries of one run lemma, and the run lemma is the shared machinery.
`RegularizedSchurOutput.schurOutput` gives the weaker PP2-style form with $e_A = e_R + e_X$. That
form is used by EP3, not by PP2.

### 4.2 Two tolerances in the dense layer (S7)

Each definition of `DenseParameters` is generalized to `…At n δR δC φ`. The tolerances are in the
headline's units: the regularizer runs at `denseSchurDelta n δR` and the core at `denseSchurDelta n δC`
(each $/(16\sqrt N)$), so that `…At n δ δ φ` is the merged definition by `rfl` (§13). The regularizer
runs at $\delta_R$; $B$, $\Gamma$ and `denseSchurDegree` depend on $\delta_R$ only. The terms of
`uDenseSchurWith` that enter $e_X$ move to $\delta_C$:
* term 2, the reducer's backward error, becomes `denseSchurDelta n δC`$/(3200N^2)$;
* term 4, the core, becomes `uShQR n k (2B) (Γ/2) 8 (denseSchurDelta n δC) (φ/2)`;
* term 6, the replays, is taken at $\delta_C$;
* term 7, the accumulator, becomes $\delta_C/(4096NR)$;
* term 8, the scaling, becomes $\delta_C/(64N)$.

The core's threshold, words, cap, leaf accuracy, leaf failure, leaf words and leaf cap, and the
rotation count, move to $\delta_C$ with it; the regularizer's words, $B$, $\Gamma$ and the degree $k$
stay at $\delta_R$.

Term 1 (regularizer) stays at $\delta_R$; terms 3 (class transfer, $t_1t_2$) and 5 ($1/100$) are
unchanged. At $\delta_R = \delta_C = \delta'$ every `…At` definition equals the merged one by `rfl`
(merged names are the diagonal instances). HD1X `denseSchurAt_measureReal_not_regularizedSchur_le`
holds with the class `IsConditionedDiagonalizable (denseSchurB n δ φ) (denseSchurΓ n δ φ)`. HD1 and
HD1' are reproved from PP2 at the diagonal, so their statements are unchanged. HD5 at two tolerances
(`logb_inv_uDenseSchurAt_le`) is a separate target: `DenseBits` is 817 lines of log bounds in one
$\delta$.

The eigen parameters:
* $\delta_R = \delta$ (the regularizer at $\delta' = \delta/(16\sqrt N)$, as merged);
* $\delta_C$ = `denseEigCoreDelta n δ φ` $= \min(\delta, \Gamma)/(2^{10}N^2B)$;
* $\rho$ = `denseEigFloor n δ φ` $= \delta_C/(64N)$;
* `uDenseEig n δ φ = min (uDenseSchurAt n δ' δC φ) (δC / (4096 * N^3 * R))`; the second term covers
  $c_{R,0}$, $c_V$ and $c_N$.

### 4.3 The eigen solver (B2) and the composition (EP3)

```lean
def eigSolverWith (Solve Ev : Impl O Q) : Impl O Q :=
  opsImpl% [N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl) {
    let G ← alloc 1;
    run Solve.body [N, nr, nq, k, F, T] (A, P, A, U, Fl);
    run Ev.body [N, ne] (A, U, Pe, V, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    } else { skip }
  }

/-- EP3: the generic Monte Carlo composition (plumbing around EM4). -/
theorem eigSolverWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Solve Ev : Impl O Q} {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p pe uo v f : ℕ × ℕ} {qs qe : List ℝ} {B Γ c₁ c₂ eR eX eU φ cR₀ cR cV cN g₀ : ℝ}
    (hSolve : PWrites law I Solve.body (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
      (schurFp n a uo f) (SchurPipelineInput qs a p uo f A)
      (RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU) φ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (hΓ : 0 < Γ) (hB : 1 ≤ B) (hc₁ : 0 < c₁) (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8)
    (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hfloor : 16 * g₀ * √((n : ℝ) + 1) < 7 * c₁ * Γ)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV ≤ c₁ * Γ) :
    PWrites law I (eigSolverWith Solve Ev).body
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (EigSolverInput qs qe a p pe uo v f A)
      (fun μ' => SchurOutput a uo f A (eR + eX) eU μ' ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) μ') φ
```

**Proof on the good event of `Solve`** (`PWrites.seq` with `PWrites.of_writes`):
* **$\mathbf{A} \ne 0$.** First check that the floor is not used. The gaps are $\ge \tfrac78c_1\Gamma\|\mathbf{A}\|_{\mathsf F}$
  (T3c inside EM4), and $g_0\|\widehat{\mathbf{T}}\|_{\mathsf F} \le 2g_0\sqrt N\|\mathbf{A}\|$. So `hfloor`
  gives flag completeness, hence $G = 0$ and the residual constant $c_{R,0}$. EM4 then gives
  `EigDecompOf` with the stated constants.
* **$\mathbf{A} = 0$.** Here $\mathbf{X} = 0$ and $\widehat{\mathbf{T}} = 0$. The contract's clause
  for $\mathbf{T} = 0$ gives $\widehat{\mathbf{V}} = \widehat{\mathbf{U}}$ and $G = 0$. All residuals are
  $0$, and $\widehat{\mathbf{U}}$ is invertible because $e_U \le 1/8$. The bound
  $\kappa(\widehat{\mathbf{U}}) \le \sqrt{(1 + e_U)/(1 - e_U)} \le 2 \le 2\sqrt NB$ needs $B \ge 1$,
  which is a hypothesis of EP3 (`hB : 1 ≤ B`; the instance has $2 \le B$ from
  `denseSchur_params_basic`). Gaps are $\ge 0 = g\cdot0$, and the backward form is
  $\|\widehat{\mathbf{U}}\cdot0\cdot\widehat{\mathbf{U}}^{-1}\| = 0$.

`eigSolverWith_terminates` is the every-tape form. `measurableSet_eigOutput` and
`measurableSet_eigResidual` use `measurable_pseudoConditionNumber`, `measurable_specNorm` and
`Measurable.matrix_inv` (on main).

## 5. Edge cases and junk values

* **$n = 0$.** There is no solve. $\hat{\mathbf{y}}_0 = (1)$ and $\kappa = 1$; the gap clauses are vacuous. If
  $\mathbf{T} = 0$, the copy branch applies.
* **$\mathbf{A} = 0$**, and $\mathbf{T} = 0$ in general. The stage copies $\widehat{\mathbf{U}}$ and
  stores flag $0$; this is now a **contract clause** (B1), not a property of the program alone.
  Without the branch, $s_{\min} = 0$ and the program would divide by $0$.
* **$\mathbf{T} = 0$ with $\mathbf{A} \ne 0$** does not occur on the good event when $N \ge 2$, since
  the gaps are positive.
* **Repeated or close diagonal entries.** On the good event no pivot is floored (`hfloor`). Off the
  event, pivots are floored to $s_{\min}$, $G = 1$, and the overall flag is $1$. The run stays total,
  and the column residual holds with $c_R$. $\widehat{\mathbf{V}}$ may be singular; nothing is
  claimed about it.
* **Non-triangular $\widehat{\mathbf{T}}$.** The stage reads only the upper triangle, so it is total.
  The analytic clause is conditional on triangularity.
* **Flags.** The solver's flag and $G$ are each in $\{0, 1\}$. The glue sets `Fl := 1` when $G > 0$.
* **Nat subtraction.** The reverse loop uses `j - 1 - i'` in program dims only.
* **Normalization.** $\|\hat{\mathbf{y}}_j\| \ge 1$, so the division is always defined.

## 6. Verification: what flag 0 certifies on every tape

### 6.1 With the verified Schur solver, no new check (EP4)

**Layout.** `verifiedSchurWith Solve` (worktree, `Verified.lean:143–149`) has the interface
`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`. It passes `P[nr + nq]` to `schurResidualCheck` as its
tolerance words $(\theta, \kappa)$. Because the stage's word now lives in its own operand `Pe` (B2),
`eigSolverWith (verifiedSchurWith Solve) Ev` reads no word of the solver. The solver's whole `P`
(`qs ++ [θ, κ]`) is its own slice.

```lean
/-- EP4: a certified Schur solver gives a certified eigenvector residual on every tape
(plumbing around EM4'). -/
theorem eigSolverWith_writes_residual {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) {Solve Ev : Impl O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {eA eU cR₀ cR cV cN g₀ : ℝ}
    (hSolve : ∀ τ μ, SchurPipelineInput qs a p uo f A μ →
      Writes .total I τ Solve.body (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
        (schurFp n a uo f) (fun μ' => (∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsSchurPair a uo U T μ'.store) ∧
          (μ'.store.get f.1 f.2 = some 0 → SchurOutput a uo f A eA eU μ')) μ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) :
    Writes .total I τ (eigSolverWith Solve Ev).body
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 →
        SchurOutput a uo f A eA eU μ' ∧
        EigResidual a v A (eigEta n eA eU cR₀ cV) (√((n : ℝ) + 1) * eigEta n eA eU cR₀ cV)
          (eigColTol n eU cV cN) μ') μ
```

Flag $0$ of the eigen solver implies $G = 0$, so the floor-free $c_{R,0}$ applies (the soundness
clause).

| claim | every tape, flag 0 (verified Schur + stage) | probability $\ge 1-\varphi$ | with EIG-V |
|---|---|---|---|
| Schur output against $\mathbf{A}$ | yes | | |
| $\operatorname{diag}\widehat{\mathbf{T}}$ lists the spectrum of $\mathbf{A} + \mathbf{E}$, $\|\mathbf{E}\| \le 2\delta\|\mathbf{A}\|$ | yes | | |
| item 1 (column and matrix residual), column norms | **yes**, a priori (EP4) | | |
| item 2: invertible, $\kappa \le 2\sqrt NB$ | no | yes | $\kappa \le \hat K$ |
| item 3: backward form | no | yes | only with the $\mathbf{X}$ checkpoint (§6.3) |
| item 4: gaps | checkable in $O(N^2)$, not planned | yes | |

**Probability with the verified solver** (O9). The verified stage's theorem (b) should take the inner
solver's postcondition `Q` as a parameter, with `Q μ' → SchurOutput …`, and keep it through the check:
the check writes the strict lower triangle and the flag, and $\mathbf{T}' = \mathbf{T}$ on the passing
branch. Then `RegularizedSchurOutput` passes through, and EP3 applies to
`eigSolverWith (verifiedSchurWith (denseSchurAt …)) triEigvecStage`. **This is not "unchanged"**: it
needs B2 (the stage's own operand), which is now in the design, and the generalization of (b) on
`feat/schur-verified`, which is requested from that stage.

### 6.2 Certifying κ in O(N³) (follow-up EIG-V, not counted)

Keep $\widehat{\mathbf{Y}}$. Compute $\mathbf{W} = \mathrm{fl}(\widehat{\mathbf{Y}}^{-1})\widehat{\mathbf{U}}^{\mathsf H}$
with `shiftedTriSolve` at shift $0$. Check $\mathrm{fl}\|\mathbf{I} - \mathbf{W}\widehat{\mathbf{V}}\|_{\mathsf F}$
plus a guard $\le 1/2$. Neumann then gives $\kappa(\widehat{\mathbf{V}}) \le \hat K =
2\|\widehat{\mathbf{V}}\|_{\mathsf F}\|\mathbf{W}\|_{\mathsf F}$, and the flag is $0$ iff $\hat K \le K$.
This is sound on every tape, about 4 targets, and changes the stage interface (keeping $\mathbf{Y}$),
which is decided then (O6).

### 6.3 Why item 3 needs a checkpoint of X

A check against $\mathbf{A}$ sees the regularizer's $\delta_R$ in the residual and multiplies it by
$\kappa \approx \sqrt NB$, with $B \propto 1/\delta_R^2$. An every-tape item 3 therefore needs the
stored $\widehat{\mathbf{X}}$: a copy before the reducer, a residual check against it, a rounded
$\|\mathbf{A} - \widehat{\mathbf{X}}\|$, and EIG-V.

## 7. Placement and shared machinery

### 7.1 Files

| file | declarations | new? |
|---|---|---|
| `Matrix/Perturbation/ComponentwiseBackward.lean` | `IsComponentwiseBackwardSolution`, T1a, T1b, `.mono` | new |
| `Matrix/Spectral/TriangularEigenvectors.lean` | `IsTriangularEigenbasisApprox`, `.norm_mulVec_col_le` | new |
| `Matrix/Perturbation/EigenvectorConditioning.lean` | T2 | new |
| `Matrix/Perturbation/EigenvalueBackward.lean` | `IsConditionedDiagonalizable.smul`, T3c | existing |
| `Matrix/Spectral/Schur.lean` | T3a (column, matrix), T3b, the $\sqrt{1-e}$ lemma (if absent) | existing |
| `Matrix/Perturbation/ApproximateEigendecomposition.lean` | `EigResidualOf`, `EigDecompOf`, `eigEta`, `eigColTol`, EM4, EM4' | new (program-free; `EigResidualOf`/`EigDecompOf` live here, not in `Schur/`) |
| `Eigensolvers/Schur/DenseParameters.lean` (EM5) | `denseSchurB_le`, `le_denseSchurΓ` | existing |
| `Ops/Logic/…` (where `Fp.Apart` lives) | list-generic `Fp.Apart` projection (`Fp.Apart.sublist` or similar; search first) | existing |
| `Matrix/FinitePrecision/StoredProducts.lean` | strided componentwise dot-product bound (if `norm_rowEntryWord_sub_le` does not cover it) | existing |
| `Ops/Blas/Pair.lean` (moved from `ShiftedQR/Division`, O10) | `complexDivideWithScratch` (deprecated alias), `Ops.StdModel.norm_complexDivide_sub_le` | existing |
| `Matrix/FinitePrecision/TriangularSolve.lean` | `shiftedTriSolve` and lemmas | new |
| `Eigensolvers/Schur/Contracts.lean`, `Completion.lean` | `EigenvectorStageContract`, `CompletingEigenvectorStage` | existing |
| `Eigensolvers/Schur/Eigenvectors.lean` | `triEigColumn`, `triEigenvectors`, `triEigvecStage`, instance, completion, count | new |
| `Eigensolvers/Schur/Pipeline.lean`, `Composition.lean`, `Residual.lean` | `RegularizedSchurOutput`, `schurPipeline_pos_run`, `schurPipeline_budget_split`, `schurPipelineEX`, PP2X; PP2 rerouted | existing |
| `Eigensolvers/Schur/DenseParameters.lean`, `Dense.lean`, `DenseBits.lean` | `…At` family, HD1X, HD5-At | existing |
| `Eigensolvers/Schur/EigSolver.lean` | `EigSolverInput`, `eigFp`, `EigResidual`, `EigOutput`, measurability, `eigSolverWith`, EP3, EP4, termination, count | new |
| `Eigensolvers/Schur/DenseEig.lean`, `Certificate.lean` | eig parameters, HE1–HE4, CT | new / existing |

**Vocabulary rows.** `IsComponentwiseBackwardSolution`, `IsTriangularEigenbasisApprox`,
`EigResidualOf`, `EigDecompOf`, `EigenvectorStageContract`, `CompletingEigenvectorStage`,
`RegularizedSchurOutput`, `EigResidual`, `EigOutput`, `EigSolverInput`. There are no Mathlib bridges
and no deviations.

### 7.2 Shared proof machinery

* **T1b** is the one conversion from rounding to backward form, reused by EIG-V and by inverse
  iteration.
* **EM4/EM4'** hold all the analysis. EP3, EP4 and EIG-V are plumbing around them.
* **The column T3a** serves item 1, `eigEta`, EP4 and EIG-V.
* **`schurPipeline_pos_run`** is the one run lemma behind PP2 and PP2X (S4).
* **The `Fp.Apart` projection lemma** removes the need for `apart_five`/`apart_six` (EF0).
* **The strided dot-product bound** keeps EF2 from re-deriving $(1+5\boldsymbol{u})^m - 1$ (EF0).
* **Loop rules** follow the invariant style of `RowSolveSubst`. Static counts use `stmtWorkMono` and
  `kernel_rfl`.

## 8. Targets

| id | target | size | deps | wave |
|---|---|---|---|---|
| EM1 | T1 (`IsComponentwiseBackwardSolution`, T1a, T1b); `IsTriangularEigenbasisApprox`, column residual | M (~250) | – | 0 |
| EM2 | T2, `IsConditionedDiagonalizable.smul` | M (~280) | – | 0 |
| EM3 | T3a (column and matrix), the $\sqrt{1-e}$ lemma, T3b, T3c | M (~300) | – | 0 |
| EM5 | closed forms `denseSchurB_le`, `le_denseSchurΓ` | S (~150) | – | 0 |
| EF0 | `Fp.Apart` list projection; strided componentwise dot bound | S (~200) | – | 0 |
| EF1 | rounded complex division (normwise relative $c_d\boldsymbol{u}$; move to `Ops/Blas/Pair`) | S (~150) | – | 0 |
| EP1 | `RegularizedSchurOutput`, `schurPipeline_pos_run`, `schurPipeline_budget_split`, PP2X (two forms), PP2 rerouted | M–L (~450, refactor) | – | 0 |
| EM4 | `EigResidualOf`, `EigDecompOf`, `eigEta`, `eigColTol`, EM4, EM4' | M (~350) | EM2, EM3 | 1 |
| EF2 | `shiftedTriSolve` + per-row residual + backward form + flag | L (~1000) | EF0, EF1, EM1 | 1 |
| EP2 | two-tolerance parameters, `denseSchurAt`, HD1X; HD1/HD1' rerouted | L (~600, refactor) | EP1 | 1 |
| EP2b | `logb_inv_uDenseSchurAt_le` (bits at two tolerances); HD5 rerouted | L (~700, refactor) | EP2 | 2 |
| EP3 | `EigSolverInput`, `eigFp`, `EigResidual`, `EigOutput`, measurability, `eigSolverWith`, EP3, termination | M (~350) | EM4, EP1, EF0 | 2 |
| EP4 | `eigSolverWith_writes_residual` | S (~120) | EM4, EP3 | 3 |
| EF3 | `triEigColumn`, `triEigenvectors`, `IsTriangularEigenbasisApprox`, flag completeness and soundness | M (~500) | EF2 | 2 |
| EF4 | contract, completion contract, `triEigvecStage`, instance, completion, count | M (~400) | EF3, EM1 | 3 |
| EP5 | eig parameters, `uDenseEig(_pos)`, `denseEig_errors_le`, HE1, HE2, HE3 | L (~500) | EP2b, EP3, EF4, EM5 | 4 |
| EP6 | HE4, `eigSolverAlgorithm`, `denseEigAlgorithm`, certificate theorem | M (~300) | EF4, EP5 | 5 |

**17 targets, about 6.5k lines.** Compared with the first draft:
* added EM4 (S5), EM5 (S8), EF0 (the machinery of §7.2) and EP2b (EP2 split, S7);
* EP1 grew (S4);
* EP3 shrank, because EM4 holds the analysis;
* EP4 now depends on EP3.

The definitions (the contracts, `EigOutput`, `eigEta`, `eigColTol`, `EigSolverInput`,
`RegularizedSchurOutput`, `schurPipelineEX`) are fixed in this note (S6) and go into the skeleton.

**Closed forms (EM5)**, from the definitions:
* $t_2 = \min(1, (\varphi/8)/s_2)$ with $s_2 = 128e\cdot N^3(K+1)^2\cdot9e$, where $K + 1 \le
  37W/\delta' = 592W\sqrt N/\delta$.
* $t_1 = (\gamma/2)\min(1, ((\varphi/32)/s_1)^3)$ with $s_1 = 2048e\cdot N^{11/3}(K+1)^2\cdot49e^{1/3}$
  (the gap tail $(2048e, 11/3, 2/3, 2)$ of `feat/schur-tighten`) and $\gamma = \delta/(64\sqrt NW)$;
  $32s_1 \le 2^{42}N^{14/3}W^2/\delta^2$ and $\Gamma = t_1/2$.

So:

```lean
theorem denseSchurB_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    denseSchurB n δ φ ≤ 2 ^ 36 * ((n : ℝ) + 1) ^ 4 * smallEigNoiseLevel (φ / 2) ^ 2 / (δ ^ 2 * φ)

theorem le_denseSchurΓ (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    δ ^ 7 * φ ^ 3 / (2 ^ 134 * ((n : ℝ) + 1) ^ (29 / 2 : ℝ) * smallEigNoiseLevel (φ / 2) ^ 7) ≤
      denseSchurΓ n δ φ
```

These are design arithmetic; only the powers of two may move at proof time. `le_denseSchurΓ` is at
the tightened gap tail (§13).

## 9. Merged statements that change

| merged | change | meaning |
|---|---|---|
| PP2 `schurPipelineWith_measureReal_not_schur_le` | reproved from the new run lemma `schurPipeline_pos_run` with the merged budget; **not** a corollary of PP2X | statement and numeral unchanged |
| `schurPipeline_budget`, `schurPipeline_budget_round` | unchanged; `schurPipeline_budget_split` is added next to them | – |
| the dense parameter definitions (`denseSchurParams`, `…Dims`, `…Cap`, `…Threshold`, `…ShQRParams`, `…LeafAccuracy`, `…LeafFailure`, `…LeafParams`, `…LeafCap`, `…ParamsWith`, `…DimsWith`, `…Rotations(With)`, `uDenseSchur(With)`) | diagonal instances of the `…At` family | definitional, values unchanged |
| HD1, HD1', HD5 | reproved through HD1X / HD5-At | statements unchanged |
| `complexDivideWithScratch` | moved to `Ops/Blas/Pair` with a deprecated alias (O10) | none |
| programs, contracts, certificates, check files | none; new `ops_certificates` lines need approval | – |

## 10. Material

* The sizing study.
* Higham 2002, Ch. 8 (Thm 8.5) and §7.2 (Oettli–Prager).
* LAPACK `xTREVC` (`smin`).
* Bauer–Fike and the class matching on main.
* `GinibreClass.lean` and `SmallEig/Parameters.lean`, for EM5.
* The verified Schur worktree (`Verified.lean`, layout of `P`).
* The review `Review-Fable-EIG-Design.md`.

## 11. Decisions

O1–O10 are approved as recommended. The review's agreements and partial disagreements are applied:
* **O1 (a):** the stage runs after the Schur solver.
* **O2 (a):** two tolerances, the merged names as diagonal instances (with S7).
* **O3 (a):** the pivot floor and a flag, with the soundness clause.
* **O4 (a):** $\widehat{\mathbf{D}}$ in place.
* **O5 (a):** T2 at $\mathbf{X}$.
* **O6:** do not anticipate $\mathbf{Y}$ in the contract (the contract does change now for S1, B1, B2).
* **O7:** internal constants may move; the headline's $K$, $\Gamma/4$ and $\delta$ stay.
* **O8:** no forward eigenvalue corollary; the column residual and the closed forms of $B$ and $\Gamma$
  are added.
* **O9:** request the general postcondition from the verified stage; the composition is not
  "unchanged" (§6.1).
* **O10:** move the division program to `Ops/Blas/Pair`.

## 12. Changes after review

From `Review-Fable-EIG-Design.md`, all applied.

* **B1.** The contract has a clause: `T = 0 → V = U ∧ flag = 0`. EP3's case $\mathbf{A} = 0$ is
  proved from the contract, with `1 ≤ B` as a hypothesis.
* **B2.** The stage has its own operand `Pe` and dimension `ne`: `eigSolverWith : (A, P, Pe) → (A, U, V, Fl)`.
  The collision with `verifiedSchurWith`'s use of `P[nr + nq]` is gone.
* **S1.** The contract is normwise and floor-free, with a parameter slice `ps`, a gap parameter `g₀`,
  and a two-tier residual (`cR₀` on flag $0$, the soundness clause). T1 and
  `IsTriangularEigenbasisApprox` are used only in the instance.
* **S2.** T3a has a column form. `eigEta` is columnwise. `EigResidual` states both the column and the
  matrix residual. $\sqrt N$ appears only where the Frobenius sum puts it.
* **S3.** The hypotheses are now `eigColTol ≤ 1/8` (which is $< 3/17$), `hfloor` with $c_1$, and
  `hsep` with $6e_U$. The gap conclusion is $\tfrac78c_1\Gamma$, which gives $\Gamma/4$ at $c_1 = 1/2$.
  The $/c_1$ in $e_E$ is dropped.
* **S4.** PP2X uses `schurPipeline_budget_split`, with the scale-back rounding as a $u$-term and
  $e_R = c_2\sqrt N\delta_R + 3\sqrt N\boldsymbol{u}$. PP2 is not a literal corollary. Both are proved
  from a new run lemma, and PP2's statement is unchanged. EP1 is about 450 lines.
* **S5.** EM4 is the matrix-level composition, with the residual-only sibling EM4'. EP3 and EP4 are
  plumbing.
* **S6.** `eigEta`, `eigColTol`, `EigSolverInput`, `CompletingEigenvectorStage`, `schurPipelineEX` are
  written out. `eigEtaA` is removed (EP4 uses `eigEta` at $e_A$).
* **S7.** The $u$-terms that move to $\delta_C$ (2, 4, 6, 7, 8) are named. EP2 is split into EP2
  (parameters + HD1X, about 600 lines) and EP2b (bits, about 700 lines).
* **S8.** EM5 adds closed forms of $B$ and $\Gamma$, and the headline quotes them.
* **Nits.**
  * `λ` is now `ev`.
  * `EigOutput` has one existential.
  * The headline's column tolerance is $1/8$, not $\delta$.
  * EF1 states a normwise relative bound: cancellation in $\operatorname{Re}(a\bar b)$ is allowed, with
    error $\le c\boldsymbol{u}|a||b|/|b|^2$.
  * The complex $\theta_i$ of the normalization is absorbed in $\sigma$'s slack.
  * EP4 depends on EP3.
  * $2 \le B$ comes from `denseSchur_params_basic`.
  * No new measurability lemma is needed (`Measurable.matrix_inv` exists).
* **Targets.** 13 became 17 (EM4, EM5, EF0, EP2b added), with status `planned`, as in
  `schur-targets.pre-skeleton.json`.

## 13. Changes at the typecheck (skeleton step 1)

Every statement and definition above was elaborated with `sorry` proofs (`lake env lean`, against
`ba5ad537`). All elaborate after these fixes; none changes the headline's meaning.

* **EP3.** `EigOutput … (7 / 8 * c₁ * Γ)` lacked its memory argument `μ'` (it did not elaborate).
* **Glue.** `if` in `opsImpl%` needs an `else` branch (`else { skip }`). The flag $1$ is written
  with `IndexOp.lit [1]`, the library's flag literal; EP3 and EP4 take `hL : IsIndexLit Mch I`.
* **EP4.** `hSolve` must also store the pair on every tape,
  `(∃ U T, HoldsSchurPair a uo U T μ'.store) ∧ (flag 0 → SchurOutput …)`. Otherwise the stage, whose
  contract needs `HoldsSchurPair`, cannot be run when the flag is not $0$, and the conclusion is a
  total `Writes`. `verifiedSchurWith_writes` gives it (`VerifiedSchurOutput` contains `SchurOrth`).
* **`schurPipelineEX`.** The $u$-term is $(8 + 2c_2/c_1)N\boldsymbol{u}$, not
  $(8N + 2c_2/c_1)\boldsymbol{u}$: the scale-back rounding of the regularizer's part is
  $\le 1.27(c_2/c_1)N\boldsymbol{u}\|\mathbf{A}\|_2$ under PP2's $\delta_R \le 1/c_1$, and the merged
  budget absorbed it in the slack of $2c_2\sqrt N\delta_R$, which $e_R = c_2\sqrt N\delta_R +
  3\sqrt N\boldsymbol{u}$ no longer has. `schurPipeline_budget_split` and PP2X are written out.
* **Two tolerances.** The `…At` family takes $\delta_R$, $\delta_C$ in the headline's units (each
  through `denseSchurDelta`), so that the merged names are `…At n δ δ φ` by `rfl`; with
  $\delta'$-units, $16\sqrt N\cdot\delta/(16\sqrt N)$ is not `rfl` to $\delta$. The eigen solver takes
  $\delta_R = \delta$.
* **EM5.** The branch has the tightened gap tail $(2048e, 11/3, 2/3, 2)$, so
  $\Gamma \ge \delta^7\varphi^3/(2^{134}N^{29/2}W^7)$ (was $\delta^9\varphi^4/(2^{188}N^{49/2}W^9)$, true but
  weaker). $B \le 2^{36}N^4W^2/(\delta^2\varphi)$ is unchanged ($16s_2 \le 4.8\cdot10^{10}N^4W^2/\delta^2$).
* **HE4.** The polylog form is $CN^3L^9(\log_2L+1)^6$, that of the merged dense Schur count after
  `feat/schur-tighten` (was $CN^3L^{15}$).
* **Edge cases checked.** $n = 0$: the gap clauses are vacuous and T2, EM4 hold with $\kappa = 1$.
  $\mathbf{A} = 0$: EM4 excludes it (`hA`), EP3 and the headline go through the contract's clause
  $\mathbf{T} = 0$; all residuals are $0$. `uDenseEig`, $B$ and $\Gamma$ are positive, so the headline
  is not vacuous.
