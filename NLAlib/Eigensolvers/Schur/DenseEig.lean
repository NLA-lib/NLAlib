/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.EigSolver
public import NLAlib.Eigensolvers.Schur.Eigenvectors
public import NLAlib.Eigensolvers.Schur.DenseBits

/-!
# A dense eigensolver

The dense eigensolver `NLAlib.Schur.denseEig` runs the dense Schur solver
(`NLAlib.Schur.denseSchur`) at two tolerances, the regularizer at $\delta$ and the core at
$\delta_C = \min(\delta, \Gamma)/(2^{10}(n + 1)^2B)$, and then the eigenvector stage
`NLAlib.Schur.triEigvecStage` with the floor $\rho = \delta_C/(64(n + 1))$. For every complex
$\mathbf{A}$ of order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, at a unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_E(n, \delta, \varphi)$ with $\log_2(1/\boldsymbol{u}_E) =
O(L^4\log^2L)$, $L = \log_2(4(n + 1)/(\delta\varphi))$, the run stores, except with probability
$\varphi$, the flag $0$, the Schur output of the dense Schur solver, and $\widehat{\mathbf{V}}$ with
column and matrix residuals at most $\delta\|\mathbf{A}\|_2$ (relative to the columns and to
$\|\widehat{\mathbf{V}}\|_2$), column norms in $[7/8, 9/8]$, $\kappa(\widehat{\mathbf{V}}) \le
2\sqrt{n + 1}\,B$, $\|\widehat{\mathbf{V}}\widehat{\mathbf{D}}\widehat{\mathbf{V}}^{-1} -
\mathbf{A}\|_2 \le \delta\|\mathbf{A}\|_2$ and diagonal gaps at least $(\Gamma/4)\|\mathbf{A}\|_2$,
$\widehat{\mathbf{D}}$ the diagonal of $\widehat{\mathbf{T}}$. The class $(B, \Gamma)$ is that of
the
regularizer (`NLAlib.Schur.denseSchurB`, `NLAlib.Schur.denseSchurΓ`; closed forms
`NLAlib.Schur.denseSchurB_le`, `NLAlib.Schur.le_denseSchurΓ`). The papers compute eigenvalues
only.

## Main definitions

* `NLAlib.Schur.denseEig`: the program.
* `NLAlib.Schur.denseEigCoreDelta`, `NLAlib.Schur.denseEigFloor`,
`NLAlib.Schur.denseEigSchurParams`,
  `NLAlib.Schur.denseEigDims`, `NLAlib.Schur.denseEigRotations`, `NLAlib.Schur.uDenseEig`: its
  parameters.

## Main results

* `NLAlib.Schur.denseEig_measureReal_not_eig_le`: the dense eigendecomposition theorem.
* `NLAlib.Schur.denseEig_terminates`: termination on every tape.
* `NLAlib.Schur.logb_inv_uDenseEig_le`: the bits of precision.
* `NLAlib.Schur.denseEig_work_le`, `NLAlib.Schur.denseEig_work_le_polylog`: the operation count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Schur

open Ops MeasureTheory ProbabilityTheory ShiftedQR SmallEig

/-! ### Parameters -/

/-- The core tolerance $\delta_C = \min(\delta, \Gamma)/(2^{10}(n + 1)^2B)$. -/
noncomputable def denseEigCoreDelta (n : ℕ) (δ φ : ℝ) : ℝ :=
  min δ (denseSchurΓ n δ φ) / (2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ)

/-- The floor parameter $\rho = \delta_C/(64(n + 1))$ of the eigenvector stage. -/
noncomputable def denseEigFloor (n : ℕ) (δ φ : ℝ) : ℝ :=
  denseEigCoreDelta n δ φ / (64 * ((n : ℝ) + 1))

/-- The words of the Schur solver: `NLAlib.Schur.denseSchurParamsAt` at $(\delta, \delta_C)$. -/
noncomputable def denseEigSchurParams (n : ℕ) (δ φ : ℝ) : List ℝ :=
  denseSchurParamsAt n δ (denseEigCoreDelta n δ φ) φ

/-- The dimensions of a run: those of the Schur solver at $(\delta, \delta_C)$ and the one word
of the stage. -/
noncomputable def denseEigDims (n : ℕ) (δ φ : ℝ) : List ℕ :=
  denseSchurDimsAt n δ (denseEigCoreDelta n δ φ) φ ++ [1]

/-- The rotation count $R$ of the Schur solver at $(\delta, \delta_C)$. -/
noncomputable def denseEigRotations (n : ℕ) (δ φ : ℝ) : ℕ :=
  denseSchurRotationsAt n δ (denseEigCoreDelta n δ φ) φ

/-- **The precision threshold** $\boldsymbol{u}_E(n, \delta, \varphi)$: the minimum of the Schur
solver's `NLAlib.Schur.uDenseSchurAt` at $(\delta, \delta_C)$ and $\delta_C/(4096(n + 1)^3R)$ (the
stage's residual, product and norm errors). -/
noncomputable def uDenseEig (n : ℕ) (δ φ : ℝ) : ℝ :=
  min (uDenseSchurAt n δ (denseEigCoreDelta n δ φ) φ)
    (denseEigCoreDelta n δ φ / (4096 * ((n : ℝ) + 1) ^ 3 * denseEigRotations n δ φ))

/-- **The precision threshold is positive** for $0 < \delta \le 1$ and $0 < \varphi \le 1$: the
headline is not vacuous. -/
theorem uDenseEig_pos {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uDenseEig n δ φ := by
  sorry

/-- **The errors of the dense eigensolver**: for $0 < \delta \le 1$, $0 < \varphi \le 1$,
$0 \le \boldsymbol{u} \le \boldsymbol{u}_E$ and the core rotation count $R_c$ with
$R = (n + 1)^2 + R_c$, the constants of the Schur solver at $(\delta, \delta_C)$ ($e_R$, $e_X$,
$e_U$ with $\varepsilon = (1 + 27(n + 1)^2\boldsymbol{u})(1 + 24\boldsymbol{u})^{R_c} - 1$) and of
the stage ($c_{R,0}$, $c_V$, $c_N$ at $N_{\max} = n + 1$, $g_0 = 4\rho$) meet the hypotheses of
`NLAlib.Schur.eigSolverWith_pwrites` at $(B, \Gamma)$ and $c_1 = 1/2$, and the errors of the
headline are at most $\delta$. -/
theorem denseEig_errors_le {n Rc : ℕ} {δ φ u eR eX eU cR₀ cV cN : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu0 : 0 ≤ u) (hu : u ≤ uDenseEig n δ φ)
    (hR : denseEigRotations n δ φ = (n + 1) ^ 2 + Rc)
    (heR : eR = 2 * √((n : ℝ) + 1) * (denseSchurDelta n δ / 2) + 3 * √((n : ℝ) + 1) * u)
    (heX : eX = schurPipelineEX n (1 / 2) 2 u (50 * ((n : ℝ) + 1) ^ 2 * u)
      (denseSchurDelta n (denseEigCoreDelta n δ φ))
      ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1))
    (heU : eU = 2 * ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1) +
      ((1 + 27 * ((n : ℝ) + 1) ^ 2 * u) * (1 + 24 * u) ^ Rc - 1) ^ 2)
    (hcR : cR₀ = 16 * (1 + √((n : ℝ) + 1)) * ((n : ℝ) + 2) * u)
    (hcV : cV = 8 * ((n : ℝ) + 2) * u) (hcN : cN = 4 * ((n : ℝ) + 3) * u) :
    eR + eX ≤ δ / 2 ∧ eU ≤ 58 * (denseEigRotations n δ φ : ℝ) * u ∧ eU ≤ 1 / 8 ∧
      eigColTol n eU cV cN ≤ 1 / 8 ∧
      16 * (4 * denseEigFloor n δ φ) * √((n : ℝ) + 1) < 7 * (1 / 2) * denseSchurΓ n δ φ ∧
      eX + 6 * eU ≤ 1 / 2 * denseSchurΓ n δ φ / (16 * (n + 1) * denseSchurB n δ φ) ∧
      8 * √((n : ℝ) + 1) * denseSchurB n δ φ * eigEta n eX eU cR₀ cV ≤
        1 / 2 * denseSchurΓ n δ φ ∧
      eR + eigEta n eX eU cR₀ cV ≤ δ ∧ eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV ≤ δ ∧
      eR + 2 * ((n : ℝ) + 1) * denseSchurB n δ φ * eigEta n eX eU cR₀ cV ≤ δ := by
  sorry

/-! ### The program -/

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The dense eigensolver**: `NLAlib.Schur.eigSolverWith` of the dense Schur solver
`NLAlib.Schur.denseSchur` on the Gaussian stream `sG` and the eigenvector stage
`NLAlib.Schur.triEigvecStage`. The interface is
`[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
Algorithm: dense-eigendecomposition -/
def denseEig (sG : ℕ) : Impl O Q :=
  eigSolverWith (denseSchur (O := O) (Q := Q) sG) (triEigvecStage (O := O) (Q := Q))

end Program

/-! ### The theorems -/

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The dense eigendecomposition theorem.** Let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_E$, index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, a measurable interpretation reading the tape only in its windows whose
draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on
it and a stream $s_G$ with the standard real Gaussian law. Let $0 < \delta \le 1$ and
$0 < \varphi \le 1$. Then for every complex $\mathbf{A}$ of order $n + 1$, from a memory holding
$\mathbf{A}$, the words of `NLAlib.Schur.denseEigSchurParams` and the floor
`NLAlib.Schur.denseEigFloor`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{denseEig}(\mathbf{A}) \text{ fails, writes outside } \mathbf{A},
  \widehat{\mathbf{U}}, \widehat{\mathbf{V}} \text{ and the flag, or stores no flag } 0 \text{ and
  Schur output with } \widehat{\mathbf{V}}:\ \|(\mathbf{A} - \hat
  t_{jj}\mathbf{I})\hat{\mathbf{v}}_j\|
  \le \delta\|\mathbf{A}\|_2\|\hat{\mathbf{v}}_j\|,\ \|\mathbf{A}\widehat{\mathbf{V}} -
  \widehat{\mathbf{V}}\widehat{\mathbf{D}}\|_2 \le
  \delta\|\mathbf{A}\|_2\|\widehat{\mathbf{V}}\|_2,\
  \lvert\|\hat{\mathbf{v}}_j\| - 1\rvert \le 1/8,\ \kappa(\widehat{\mathbf{V}}) \le
  2\sqrt{n + 1}\,B,\ \|\widehat{\mathbf{V}}\widehat{\mathbf{D}}\widehat{\mathbf{V}}^{-1} -
  \mathbf{A}\|_2 \le \delta\|\mathbf{A}\|_2,\ \lvert\hat t_{ii} - \hat t_{jj}\rvert \ge
  (\Gamma/4)\|\mathbf{A}\|_2\ (i \ne j)\bigr] \le \varphi\,,$$
the Schur output with $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2$ and
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}$.
Here $\widehat{\mathbf{D}} = \operatorname{diag}(\hat t_{jj})$, $\boldsymbol{u}_E$ is
`NLAlib.Schur.uDenseEig`, $R$ is `NLAlib.Schur.denseEigRotations`, $B$ is
`NLAlib.Schur.denseSchurB` and $\Gamma$ is `NLAlib.Schur.denseSchurΓ`. No printed source:
[BanksGarzaVargasSrivastava2022, Theorem 1.4] computes eigenvalues only.

Note: General form, any Schur solver with a regularized matrix and any eigenvector stage:
`NLAlib.Schur.eigSolverWith_pwrites`; its matrix content is `NLAlib.eigDecompOf_of_schur`.
Result: dense-eigendecomposition -/
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
          (denseSchurΓ n δ φ / 4) μ') μ} ≤ φ := by
  sorry

/-- **The dense eigensolver terminates on every tape**: on a scalar machine with the standard
model at $\boldsymbol{u} \le \boldsymbol{u}_E$, index literals, exact natural literals up to
$n + 1$, exact `toNat` and comparisons, draws that store the tape entry and an exact polar disk
sampler, for $0 < \delta \le 1$, $0 < \varphi \le 1$ and every complex $\mathbf{A}$ of order
$n + 1$, the run of `NLAlib.Schur.denseEig` from a memory holding $\mathbf{A}$, the words of
`NLAlib.Schur.denseEigSchurParams` and the floor succeeds on every tape, writes only
$\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the flag, and stores a matrix at
`a`, $\widehat{\mathbf{U}}$ with $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le 58R\boldsymbol{u}$ and a matrix at `v`. Here $\boldsymbol{u}_E$ is
`NLAlib.Schur.uDenseEig` and $R$ is `NLAlib.Schur.denseEigRotations`. -/
theorem denseEig_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseEig n δ φ) {a p pe uo v f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : EigSolverInput (denseEigSchurParams n δ φ) [denseEigFloor n δ φ] a p pe uo v f A μ)
    (τ : Tape ℝ) :
    Writes .total I τ (denseEig (O := O) (Q := Q) sG).body
      (Env.frame (denseEigDims n δ φ) [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOrth (n := n) a uo (58 * denseEigRotations n δ φ * u) μ' ∧
        ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix v V μ'.store) μ := by
  sorry

/-- **The bits of precision of the dense eigensolver**: there are constants $c_1, c_2$ such that
for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$\log_2(1/\boldsymbol{u}_E) \le c_1L^4(\log_2L + 1)^2 + c_2$ with $\boldsymbol{u}_E$ =
`NLAlib.Schur.uDenseEig` and $L = \log_2(4(n + 1)/(\delta\varphi))$: $\log(1/\delta_C) = O(L)$ by
the closed forms of $B$ and $\Gamma$. -/
theorem logb_inv_uDenseEig_le : ∃ c₁ c₂ : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → Real.logb 2 (uDenseEig n δ φ)⁻¹ ≤
      c₁ * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 4 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 2 + c₂ := by
  sorry

/-- **The operation count of the dense eigensolver** (on every tape): the instrumented static
count of `NLAlib.Schur.denseEig` at the order $n + 1$, $n_r$ regularizer words, $n_q$ core words,
the shift degree $k$, the iteration cap $F$, the leaf cap $T$, $n_e$ stage words and zero offsets
is at most the dense Schur solver's $384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$
(`NLAlib.Schur.denseSchur_work_le`), the stage's $10^4(n + 1)^3$
(`NLAlib.Schur.size_stmtCost_triEigvecStage_le`) and the glue $128$. -/
theorem denseEig_work_le (sG n nr nq k F T ne : ℕ) :
    Count.size (stmtCost (denseEig (O := O) (Q := Q) sG).body.instrument
        [n + 1, nr, nq, k, F, T, ne, 0, 0, 0, 0, 0, 0, 0]) ≤
      384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 +
        10000 * (n + 1) ^ 3 + 128 := by
  sorry

/-- **The operation count of the dense eigensolver is $n^3$ times a polylogarithm**: there is a
constant $C$ such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, the
instrumented static count at `NLAlib.Schur.denseEigDims` and zero offsets is at most
$C(n + 1)^3L^9(\log_2 L + 1)^6$, $L = \log_2(4(n + 1)/(\delta\varphi))$, that of the dense Schur
solver (`NLAlib.Schur.denseSchur_work_le_polylog`) at the core tolerance $\delta_C$ with
$\log(1/\delta_C) = O(L)$. -/
theorem denseEig_work_le_polylog (sG : ℕ) : ∃ C : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ →
    δ ≤ 1 → 0 < φ → φ ≤ 1 →
    (Count.size (stmtCost (denseEig (O := O) (Q := Q) sG).body.instrument
      (denseEigDims n δ φ ++ [0, 0, 0, 0, 0, 0, 0])) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ 3 * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 9 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 6 := by
  sorry

end Theorems

end NLAlib.Schur
