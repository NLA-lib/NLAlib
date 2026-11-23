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

/-- **The core tolerance**: $0 < \delta_C \le 1$, and $2^{10}(n + 1)^2B\,\delta_C$ is at most
$\delta$ and at most $\Gamma$. -/
theorem denseEigCoreDelta_pos_le {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) : 0 < denseEigCoreDelta n δ φ ∧ denseEigCoreDelta n δ φ ≤ 1 ∧
      denseEigCoreDelta n δ φ * (2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ) ≤ δ ∧
      denseEigCoreDelta n δ φ * (2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ) ≤
        denseSchurΓ n δ φ := by
  obtain ⟨-, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hK : 0 < 2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ := by positivity
  have hm0 : 0 < min δ (denseSchurΓ n δ φ) := lt_min hδ hΓ
  have e : denseEigCoreDelta n δ φ * (2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ) =
      min δ (denseSchurΓ n δ φ) := by
    unfold denseEigCoreDelta; field_simp
  refine ⟨by unfold denseEigCoreDelta; positivity, ?_, by rw [e]; exact min_le_left _ _,
    by rw [e]; exact min_le_right _ _⟩
  have hN : (1 : ℝ) ≤ 2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ := by
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    nlinarith
  have h1 : denseEigCoreDelta n δ φ * 1 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hN (by unfold denseEigCoreDelta; positivity :
      0 ≤ denseEigCoreDelta n δ φ)
    linarith [min_le_left δ (denseSchurΓ n δ φ)]
  linarith

/-- **The precision threshold is positive** for $0 < \delta \le 1$ and $0 < \varphi \le 1$: the
headline is not vacuous. -/
theorem uDenseEig_pos {n : ℕ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uDenseEig n δ φ := by
  obtain ⟨hD0, hD1, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  have hR : 0 < (denseEigRotations n δ φ : ℝ) := by
    unfold denseEigRotations denseSchurRotationsAt denseSchurRotationsAtWith; positivity
  exact lt_min (uDenseSchurAt_pos hδ hδ1 hD0 hD1 hφ hφ1) (by positivity)

/-- The monomials of the eigensolver's precision condition: from $N^3Ru \le D/4096$ with
$N, R \ge 1$ and $u \ge 0$, each smaller monomial is at most $D/4096$. -/
private theorem denseEig_monomials_le {N R u D : ℝ} (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hu0 : 0 ≤ u)
    (h : N ^ 3 * R * u ≤ D / 4096) :
    N ^ 3 * u ≤ D / 4096 ∧ N * R * u ≤ D / 4096 ∧ R * u ≤ D / 4096 ∧ N * u ≤ D / 4096 ∧
      N ^ 2 * u ≤ D / 4096 := by
  have hN0 : 0 ≤ N := by linarith
  have hRu : 0 ≤ R * u := mul_nonneg (by linarith) hu0
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hN23 : N ^ 2 ≤ N ^ 3 := by nlinarith [sq_nonneg N]
  have h3 := mul_le_mul_of_nonneg_left hR1 (mul_nonneg (pow_nonneg hN0 3) hu0)
  have h1 := mul_le_mul_of_nonneg_right (hNN.trans hN23) hRu
  have h2 := mul_le_mul_of_nonneg_right hN1 hRu
  have h4 := mul_le_mul_of_nonneg_left hR1 (mul_nonneg hN0 hu0)
  have h5 := mul_le_mul_of_nonneg_right hN23 hu0
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The final inequalities of the eigensolver's constants, in the order $N$, its square root $s$,
the core tolerance $D$, the class $(B, \Gamma)$ and the errors $e_U$, $e_X$, $\eta$. -/
private theorem denseEig_final_le {N s u D B Γ δ eU eX η : ℝ} (hN1 : 1 ≤ N) (hsN : s ≤ N)
    (hu0 : 0 ≤ u) (hD0 : 0 < D) (hD1 : D ≤ 1) (hB : 2 ≤ B) (hΓ : 0 < Γ)
    (hNu : N * u ≤ D / 4096) (hN2u : N ^ 2 * u ≤ D / 4096)
    (heUD : eU ≤ 58 * D / 4096) (heX : eX ≤ D) (hη0 : 0 ≤ η) (hη : η ≤ 3 * D)
    (hDδ : D * (2 ^ 10 * N ^ 2 * B) ≤ δ) (hDΓ : D * (2 ^ 10 * N ^ 2 * B) ≤ Γ) :
    δ / 16 + 3 * (s * u) + eX ≤ δ / 2 ∧ eU ≤ 1 / 8 ∧
      4 * (N + 2) * u + 2 * eU + 2 * N * (8 * (N + 1) * u) ≤ 1 / 8 ∧
      16 * (4 * (D / (64 * N))) * s < 7 * (1 / 2) * Γ ∧
      eX + 6 * eU ≤ 1 / 2 * Γ / (16 * N * B) ∧ 8 * s * B * η ≤ 1 / 2 * Γ ∧
      δ / 16 + 3 * (s * u) + η ≤ δ ∧ δ / 16 + 3 * (s * u) + s * η ≤ δ ∧
      δ / 16 + 3 * (s * u) + 2 * N * B * η ≤ δ := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hNB := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hNN hB0.le) hD0.le
  have hDNB : D * N * B ≤ δ / 1024 := by linarith
  have hDNBΓ : D * N * B ≤ Γ / 1024 := by linarith
  have h2 : (2 : ℝ) ≤ N ^ 2 * B := by nlinarith
  have h2048 := mul_le_mul_of_nonneg_left h2 hD0.le
  have hDδ' : D ≤ δ / 2048 := by linarith
  have hDΓ' : D ≤ Γ / 2048 := by linarith
  have hsu := mul_le_mul_of_nonneg_right hsN hu0
  have huN := mul_le_mul_of_nonneg_right hN1 hu0
  have hND := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ B) (mul_pos hN0 hD0).le
  have hsη : s * η ≤ N * (3 * D) := mul_le_mul hsN hη hη0 hN0.le
  refine ⟨by linarith, by linarith, by nlinarith, ?_, ?_, ?_, by linarith, by linarith, ?_⟩
  · have e : 16 * (4 * (D / (64 * N))) * s = D * s / N := by field_simp; ring
    rw [e, div_lt_iff₀ hN0]
    have h3 : D * s ≤ D * N := mul_le_mul_of_nonneg_left hsN hD0.le
    have h4 := mul_le_mul_of_nonneg_right hDΓ' hN0.le
    have h5 := mul_pos hΓ hN0
    linarith
  · rw [le_div_iff₀ (by positivity)]
    have h1 : (eX + 6 * eU) * (16 * N * B) ≤ 2 * D * (16 * N * B) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · have h3 := mul_le_mul_of_nonneg_left hsη (by positivity : (0 : ℝ) ≤ 8 * B)
    linarith
  · have h3 := mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ 2 * N * B)
    linarith

/-- The pipeline error of the eigensolver is at most $D$: with $s \le N$, $sd = D/16$,
$0 \le \varepsilon \le 29Ru$ and the monomials at most $D/4096$. -/
private theorem denseEig_pipelineError_le {N s u d D ε R : ℝ} (hN1 : 1 ≤ N) (hsN : s ≤ N)
    (hu0 : 0 ≤ u) (hsd : s * d = D / 16) (hε0 : 0 ≤ ε) (hε29 : ε ≤ 29 * R * u)
    (hN3 : N ^ 3 * u ≤ D / 4096) (hNR : N * R * u ≤ D / 4096) (hNu : N * u ≤ D / 4096) :
    2 * 2 * s * (3 * (50 * N ^ 2 * u) / (1 / 2) + d + 8 * ε / (1 / 2)) +
      (8 + 2 * 2 / (1 / 2)) * N * u ≤ D := by
  have hN0 : 0 ≤ N := by linarith
  have e : 2 * 2 * s * (3 * (50 * N ^ 2 * u) / (1 / 2) + d + 8 * ε / (1 / 2)) +
      (8 + 2 * 2 / (1 / 2)) * N * u = 1200 * (s * (N ^ 2 * u)) + 4 * (s * d) + 64 * (s * ε) +
        16 * (N * u) := by ring
  have h1 := mul_le_mul_of_nonneg_right hsN (mul_nonneg (pow_nonneg hN0 2) hu0)
  have h2 : s * ε ≤ N * (29 * R * u) := mul_le_mul hsN hε29 hε0 hN0
  rw [e, hsd]
  linarith

/-- The eigenvector error $\eta$ of the eigensolver is at most $3D$. -/
private theorem denseEig_eta_le {N s u D eX eU : ℝ} (hN1 : 1 ≤ N) (hs1 : 1 ≤ s) (hsN : s ≤ N)
    (hu0 : 0 ≤ u) (hD0 : 0 < D) (hN3 : N ^ 3 * u ≤ D / 4096) (heX : eX ≤ D)
    (heU : eU ≤ 58 * D / 4096) :
    2 * eX + 3 * eU + 4 * s * (16 * (1 + s) * (N + 1) * u) + 8 * N * (8 * (N + 1) * u) ≤
      3 * D := by
  have hN0 : 0 ≤ N := by linarith
  have h1 : s * (1 + s) ≤ N * (2 * N) := mul_le_mul hsN (by linarith) (by linarith) hN0
  have h2 : s * (1 + s) * (N + 1) ≤ N * (2 * N) * (2 * N) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 64 * u)
  have h4 : N * (N + 1) ≤ 2 * N ^ 3 := by nlinarith [mul_nonneg hN0 hN0, sq_nonneg (N - 1)]
  have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 64 * u)
  linarith

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
  subst heR heX heU hcR hcV hcN
  obtain ⟨hD0, hD1, hDδ, hDΓ⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  obtain ⟨-, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  set D := denseEigCoreDelta n δ φ with hDdef
  set B := denseSchurB n δ φ with hBdef
  set Γ := denseSchurΓ n δ φ with hΓdef
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hN1 : 1 ≤ N := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  set s := √N with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hN1
  have hsN : s ≤ N := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hss : s * s = N := Real.mul_self_sqrt (by linarith)
  set R : ℝ := (denseEigRotations n δ φ : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef, hR]; push_cast
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ hN1
    have := (Nat.cast_nonneg Rc : (0 : ℝ) ≤ Rc); linarith
  -- the threshold terms
  have huA : u ≤ uDenseSchurAt n δ D φ := hu.trans (min_le_left _ _)
  have hu' := huA.trans (min_le_left _ _)
  obtain ⟨-, hu2, -, -, -, -, -, hu8⟩ := le_of_le_uDenseSchurAtWith hu'
  obtain ⟨-, h4096⟩ := mul_denseSchurRotationsAtWith_le hD0 hu'
  have hu9 : u ≤ D / (4096 * N ^ 3 * R) := hu.trans (min_le_right _ _)
  have hN3R : N ^ 3 * R * u ≤ D / 4096 := by
    rw [le_div_iff₀ (by positivity)] at hu9 ⊢; linarith
  obtain ⟨hN3, hNR, hRu, hNu, hN2u⟩ := denseEig_monomials_le hN1 hR1 hu0 hN3R
  have hsu : s * u ≤ D / 4096 := by
    have := mul_le_mul_of_nonneg_right hsN hu0; linarith
  obtain ⟨hε0, -, hεU, -⟩ := denseSchur_errors_le (Rc := Rc) hD0 hu0
    (by rw [← hR]; exact h4096) hu2 hu8 hD1
  rw [← hR, ← hRdef] at hεU
  set ε := (1 + 27 * N ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 with hεdef
  set eU := 2 * ε + ε ^ 2 with heUdef
  have hε29 : ε ≤ 29 * R * u := by have := sq_nonneg ε; linarith
  have heUD : eU ≤ 58 * D / 4096 := by linarith
  -- the error against the regularized matrix
  have hsδ : s * denseSchurDelta n D = D / 16 := by
    unfold denseSchurDelta; rw [← hNdef, ← hs]; field_simp
  have heX : schurPipelineEX n (1 / 2) 2 u (50 * N ^ 2 * u) (denseSchurDelta n D) ε ≤ D := by
    unfold schurPipelineEX
    rw [← hNdef, ← hs]
    exact denseEig_pipelineError_le hN1 hsN hu0 hsδ hε0 hε29 hN3 hNR hNu
  set eX := schurPipelineEX n (1 / 2) 2 u (50 * N ^ 2 * u) (denseSchurDelta n D) ε with heXdef
  have heX0 : 0 ≤ eX := by
    unfold schurPipelineEX at heXdef; rw [heXdef]
    have : 0 ≤ denseSchurDelta n D := by unfold denseSchurDelta; positivity
    positivity
  have heR : 2 * s * (denseSchurDelta n δ / 2) + 3 * s * u = δ / 16 + 3 * (s * u) := by
    unfold denseSchurDelta; rw [← hNdef, ← hs]; field_simp
  -- the stage constants
  have e2 : (n : ℝ) + 2 = N + 1 := by rw [hNdef]; ring
  set η := eigEta n eX eU (16 * (1 + s) * ((n : ℝ) + 2) * u) (8 * ((n : ℝ) + 2) * u) with hηdef
  have hη : η ≤ 3 * D := by
    rw [hηdef]; unfold eigEta; rw [← hNdef, ← hs, e2]
    exact denseEig_eta_le hN1 hs1 hsN hu0 hD0 hN3 heX heUD
  have hη0 : 0 ≤ η := by
    rw [hηdef]; unfold eigEta; rw [← hNdef, ← hs]; positivity
  obtain ⟨c1, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    denseEig_final_le hN1 hsN hu0 hD0 hD1 hB hΓ hNu hN2u heUD heX hη0 hη hDδ hDΓ
  rw [heR]
  refine ⟨c1, hεU, c3, ?_, ?_, c6, c7, c8, c9, c10⟩
  · have e3 : (n : ℝ) + 3 = N + 2 := by rw [hNdef]; ring
    unfold eigColTol
    rw [← hNdef, e3, e2]
    exact c4
  · unfold denseEigFloor
    rw [← hDdef, ← hNdef]
    exact c5

/-! ### The program -/

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The dense eigensolver**: `NLAlib.Schur.eigSolverWith` of the dense Schur solver
`NLAlib.Schur.denseSchur` on the Gaussian stream `sG` and the eigenvector stage
`NLAlib.Schur.triEigvecStage`. The interface is
`[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
Algorithm: dense-eigendecomposition -/
def denseEig (sG : ℕ) : Stmt O Q :=
  eigSolverWith (denseSchur (O := O) (Q := Q) sG) (triEigvecStage (O := O) (Q := Q))

end Program

/-- Larger errors, a larger condition bound and a smaller gap are weaker. -/
theorem EigOutput.mono {n : ℕ} {a v f : ℕ × ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {eC eM c eE K g eC' eM' c' eE' K' g' : ℝ} {μ' : Mem ℝ}
    (h : EigOutput a v f A eC eM c eE K g μ') (hC : eC ≤ eC') (hM : eM ≤ eM') (hc : c ≤ c')
    (hE : eE ≤ eE') (hK : K ≤ K') (hg : g' ≤ g) : EigOutput a v f A eC' eM' c' eE' K' g' μ' := by
  obtain ⟨hf, T, V, hT, hV, ⟨hcol, hres, hmat⟩, hU, hκ, hb, hgap⟩ := h
  have hA := specNorm_nonneg A
  refine ⟨hf, T, V, hT, hV, ⟨fun j => (hcol j).trans hc, fun j => (hres j).trans ?_, ?_⟩, hU,
    hκ.trans hK, hb.trans (mul_le_mul_of_nonneg_right hE hA),
    fun i j hij => (mul_le_mul_of_nonneg_right hg hA).trans (hgap i j hij)⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA) (norm_nonneg _)
  · exact hmat.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hA)
      (specNorm_nonneg _))

/-! ### The theorems -/

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

-- The stage contracts at their long parameters make the elaboration heavy.
set_option maxHeartbeats 1000000 in
-- (heavy elaboration, see above)
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
    P.real {ω | ¬ Writes .total I (ξ ω) (denseEig (O := O) (Q := Q) sG)
      (Env.frame (denseEigDims n δ φ) [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOutput a uo f A δ (58 * denseEigRotations n δ φ * u) μ' ∧
        EigOutput a v f A δ δ (1 / 8) δ (2 * √((n : ℝ) + 1) * denseSchurB n δ φ)
          (denseSchurΓ n δ φ / 4) μ') μ} ≤ φ := by
  obtain ⟨hD0, hD1, -, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  obtain ⟨-, -, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set D := denseEigCoreDelta n δ φ with hDdef
  set Rc := shqrSchurRotations n (denseSchurDegree n δ φ)
    (denseSchurShQRParamsAt n δ D φ ++ denseSchurLeafParamsAt n δ D φ).length
    (denseSchurCapAt n δ D φ)
    (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCapAt n δ D φ)) with hRcdef
  have hR : denseEigRotations n δ φ = (n + 1) ^ 2 + Rc := rfl
  obtain ⟨he, heU58, heU, hc, hfloor, hsep, hκ, h1, h2, h3⟩ :=
    denseEig_errors_le (Rc := Rc) hδ hδ1 hφ hφ1 hu0 hu hR rfl rfl rfl rfl rfl rfl
  have hSolve := denseSchurAt_pwrites_regularizedSchur (O := O) (Q := Q) (sG := sG) (A := A)
    (a := a) (p := p) (uo := uo) (f := f) hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hδ hδ1 hD0
    hD1 hφ hφ1 (hu.trans (min_le_left _ _))
  have hρ : 0 < denseEigFloor n δ φ := by unfold denseEigFloor; positivity
  have h64 : 64 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * u ≤ 1 := by
    have hu9 : u ≤ D / (4096 * ((n : ℝ) + 1) ^ 3 * denseEigRotations n δ φ) :=
      hu.trans (min_le_right _ _)
    have hR1 : (1 : ℝ) ≤ denseEigRotations n δ φ := by
      rw [hR]; push_cast
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by
        have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
      have := (Nat.cast_nonneg Rc : (0 : ℝ) ≤ Rc); linarith
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    rw [le_div_iff₀ (by positivity)] at hu9
    have h4 : 4096 * ((n : ℝ) + 1) ^ 3 * u ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hR1 (by positivity :
        (0 : ℝ) ≤ 4096 * ((n : ℝ) + 1) ^ 3 * u)
      nlinarith
    push_cast
    have : ((n : ℝ) + 1 + 1) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 3 := by nlinarith
    nlinarith
  have hEv : EigenvectorStageContract _ _ _ _ _ _ _ (triEigvecStage (O := O) (Q := Q)) I :=
    triEigvecStage_eigenvectorStageContract (O := O) (Q := Q) hS hM hL
      (hNat.mono (by omega)) hC hρ h64
  have e2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have e3 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [e2, e3, e1] at hEv
  have hw := eigSolverWith_pwrites (pe := pe) (v := v) hL hC hI hloc hSolve hEv hΓ
    (by linarith)
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) heU hc hfloor hsep hκ
  have := hξ.isProbabilityMeasure
  refine (measureReal_mono (fun ω (hω : ¬ _) (hs : Writes _ _ _ _ _ _ _ _) =>
    hω (hs.mono le_rfl fun μ' _ hout => ?_))).trans (hw.measureReal_not_writes_le hin hξ)
  obtain ⟨hso, heo⟩ := hout
  refine ⟨hso.mono (by linarith) heU58, heo.mono h1 h2 (by linarith) h3 le_rfl ?_⟩
  linarith

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
    Writes .total I τ (denseEig (O := O) (Q := Q) sG)
      (Env.frame (denseEigDims n δ φ) [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOrth (n := n) a uo (58 * denseEigRotations n δ φ * u) μ' ∧
        ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix v V μ'.store) μ := by
  obtain ⟨hD0, hD1, -, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  set D := denseEigCoreDelta n δ φ with hDdef
  set Rc := shqrSchurRotations n (denseSchurDegree n δ φ)
    (denseSchurShQRParamsAt n δ D φ ++ denseSchurLeafParamsAt n δ D φ).length
    (denseSchurCapAt n δ D φ)
    (smallEigLeafRotations (denseSchurDegree n δ φ) (denseSchurLeafCapAt n δ D φ)) with hRcdef
  have hR : denseEigRotations n δ φ = (n + 1) ^ 2 + Rc := rfl
  obtain ⟨-, heU58, -⟩ :=
    denseEig_errors_le (Rc := Rc) hδ hδ1 hφ hφ1 hu0 hu hR rfl rfl rfl rfl rfl rfl
  obtain ⟨-, hu2, -⟩ := le_of_le_uDenseSchurAtWith
    ((hu.trans (min_le_left _ _)).trans (min_le_left _ _))
  have hd1 : denseSchurDelta n D ≤ 1 / 16 := (denseSchur_params_basic (n := n) hD0 hD1 hφ hφ1).2.1
  have h400 : 400 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hu2; nlinarith
  have hSolve : TerminatingSchurSolver (58 * denseEigRotations n δ φ * u) n
      (denseSchurDimsAt n δ D φ) (denseEigSchurParams n δ φ) (denseSchur (O := O) (Q := Q) sG)
      I := fun {τ} {μ} {a p uo f} A hin =>
    (denseSchurAt_writes_orth hS hM hL hNat hQ hC hSmp hDisk h400 hin τ).mono le_rfl
      fun μ' _ ⟨hT, U, hU, ho⟩ => ⟨hT, U, hU, ho.trans heU58⟩
  exact eigSolverWith_terminates hL hC hSolve (triEigvecStage_completes hS hL hC (n + 1) _)
    hin τ

/-- The core tolerance costs polynomially many bits: there is an exponent $P$ with
$4(n + 1)/(\min(\delta, \delta_C)\varphi) \le Y^P$, $Y = 4(n + 1)/(\delta\varphi)$, the condition
bound and the inverse separation being polynomial in $Y$. -/
private theorem denseEig_tolerance_hiBd : ∃ P : ℕ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → HiBd (4 * ((n : ℝ) + 1) / (δ * φ)) P
      (4 * ((n : ℝ) + 1) / (min δ (denseEigCoreDelta n δ φ) * φ)) := by
  obtain ⟨E, hE⟩ := denseSchur_arg_bounds
  refine ⟨4 * E + 20, fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hY4, hYc, hBY, -, -, -, -, hδY⟩ := hE (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hd0, hd1, -, -, -, hB, hΓ⟩ := denseSchur_params_basic (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hD0, -, hDδ, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  clear hE
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hδφ : δ * φ ≤ 1 := by nlinarith
  set Y := 4 * ((n : ℝ) + 1) / (δ * φ) with hYdef
  have hY1 : 1 ≤ Y := by linarith
  have hNY : HiBd Y 1 ((n : ℝ) + 1) := ⟨by linarith, by
    rw [pow_one, hYdef, le_div_iff₀ (by positivity)]; nlinarith⟩
  have hφY : LoBd Y 1 φ := ⟨hφ, by
    rw [pow_one, hYdef, mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith⟩
  have hm : LoBd Y E (min (denseSchurΓ n δ φ / 2) 8) := by
    have hm0 : 0 < min (denseSchurΓ n δ φ / 2) 8 := lt_min (half_pos hΓ) (by norm_num)
    refine ⟨hm0, ?_⟩
    have hA : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 := by nlinarith
    have hp : denseSchurDelta n δ * (φ / 2) ≤ 1 := by nlinarith
    have hp0 : 0 < denseSchurDelta n δ * (φ / 2) := by positivity
    have e : min (denseSchurΓ n δ φ / 2) 8 * (4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
        (denseSchurDelta n δ * min (denseSchurΓ n δ φ / 2) 8 * (φ / 2))) =
        4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
          (denseSchurDelta n δ * (φ / 2)) := by
      field_simp
    have h1 : 1 ≤ 4 * ((n : ℝ) + 1) * (2 * denseSchurB n δ φ) * 8 ^ 2 /
        (denseSchurDelta n δ * (φ / 2)) := by
      rw [le_div_iff₀ hp0]
      linarith
    calc (1 : ℝ) ≤ _ := h1
      _ = _ := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hYc.2 hm0.le
  have hΓY : LoBd Y E (denseSchurΓ n δ φ) :=
    hm.of_le ((min_le_left _ _).trans (by linarith))
  have hBY' : HiBd Y E (denseSchurB n δ φ) :=
    hBY.of_le (by linarith) (by linarith)
  have hden := ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 2 ^ 10)
    (by norm_num : (2 : ℝ) ^ 10 ≤ 4 ^ 5)).mul (hNY.pow 2)).mul hBY'
  have hDY : LoBd Y (E + (5 + 1 * 2 + E)) (denseEigCoreDelta n δ φ) :=
    (hδY.min hΓY).div hden
  have hK : (1 : ℝ) ≤ 2 ^ 10 * ((n : ℝ) + 1) ^ 2 * denseSchurB n δ φ := by
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ hN1
    nlinarith
  have hDle : denseEigCoreDelta n δ φ ≤ δ := by nlinarith
  rw [min_eq_right hDle]
  have h := ((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4)
    (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul hNY).div (hDY.mul hφY)
  exact h.mono hY1 (by omega)

/-- The polylogarithm at a polynomially larger argument: if $2 \le L$, $2 \le L_c \le PL$ and
$1 \le P$, then $\log_2 L_c + 1 \le (\log_2 P + 1)(\log_2 L + 1)$. -/
private theorem logb_add_one_le_of_le_mul {P L Lc : ℝ} (hP : 1 ≤ P) (hL : 2 ≤ L) (hLc : 2 ≤ Lc)
    (h : Lc ≤ P * L) : Real.logb 2 Lc + 1 ≤ (Real.logb 2 P + 1) * (Real.logb 2 L + 1) := by
  have h1 : Real.logb 2 Lc ≤ Real.logb 2 P + Real.logb 2 L := by
    rw [← Real.logb_mul (by linarith) (by linarith)]
    exact Real.logb_le_logb_of_le one_lt_two (by linarith) h
  have hp := Real.logb_nonneg one_lt_two hP
  have hl := Real.logb_nonneg one_lt_two (by linarith : (1 : ℝ) ≤ L)
  nlinarith [mul_nonneg hp hl]

/-- **The bits of precision of the dense eigensolver**: there are constants $c_1, c_2$ such that
for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$,
$\log_2(1/\boldsymbol{u}_E) \le c_1L^4(\log_2L + 1)^2 + c_2$ with $\boldsymbol{u}_E$ =
`NLAlib.Schur.uDenseEig` and $L = \log_2(4(n + 1)/(\delta\varphi))$: $\log(1/\delta_C) = O(L)$,
$B$ and $1/\Gamma$ being polynomial in $4(n + 1)/(\delta\varphi)$. -/
theorem logb_inv_uDenseEig_le : ∃ c₁ c₂ : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ → δ ≤ 1 → 0 < φ →
    φ ≤ 1 → Real.logb 2 (uDenseEig n δ φ)⁻¹ ≤
      c₁ * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 4 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 2 + c₂ := by
  obtain ⟨c₁, c₂, hb⟩ := logb_inv_uDenseSchurAt_le
  obtain ⟨P, hP⟩ := denseEig_tolerance_hiBd
  obtain ⟨Q, hQ⟩ := denseSchurRotationsAt_hiBd
  obtain ⟨Ka, -, hca⟩ := denseSchurAt_caps_le
  obtain ⟨Kb, -, hcb⟩ := denseSchur_caps_le
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (P : ℝ) + 1 := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp]; linarith [P.cast_nonneg (α := ℝ)]
  have hlp : 0 ≤ Real.logb 2 p := Real.logb_nonneg one_lt_two hp1
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ((1 + (6 + 1 * 3 + Q) : ℕ) : ℝ) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; positivity
  refine ⟨(max c₁ 0 + e) * (p ^ 4 * (Real.logb 2 p + 1) ^ 2), max c₂ 0,
    fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hD0, hD1, -, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  have hbn := hb (n := n) hδ hδ1 hD0 hD1 hφ hφ1
  have hPn := hP (n := n) hδ hδ1 hφ hφ1
  have hR : HiBd _ Q (denseEigRotations n δ φ : ℝ) := hQ (n := n) hδ hδ1 hD0 hD1 hφ hφ1
  obtain ⟨hLc2, -⟩ := hca (n := n) hδ hδ1 hD0 hD1 hφ hφ1
  obtain ⟨hL2, -⟩ := hcb (n := n) hδ hδ1 hφ hφ1
  clear hb hP hQ hca hcb
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hmin : min δ (denseEigCoreDelta n δ φ) ≤ denseEigCoreDelta n δ φ := min_le_right _ _
  have hm0 : 0 < min δ (denseEigCoreDelta n δ φ) := lt_min hδ hD0
  have hmφ : min δ (denseEigCoreDelta n δ φ) * φ ≤ denseEigCoreDelta n δ φ := by nlinarith
  have hmφ1 : min δ (denseEigCoreDelta n δ φ) * φ ≤ 1 := by linarith
  set Yc := 4 * ((n : ℝ) + 1) / (min δ (denseEigCoreDelta n δ φ) * φ) with hYc
  set Lc := Real.logb 2 Yc with hLcdef
  set L := Real.logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  have hY4 : 4 ≤ Yc := by
    rw [hYc, le_div_iff₀ (by positivity)]
    nlinarith
  have hNY : HiBd Yc 1 ((n : ℝ) + 1) := ⟨by linarith, by
    rw [pow_one, hYc, le_div_iff₀ (by positivity)]; nlinarith⟩
  have hDY : LoBd Yc 1 (denseEigCoreDelta n δ φ) := ⟨hD0, by
    rw [pow_one, hYc, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith⟩
  have h2 := (hDY.div (((HiBd.const hY4 (by norm_num : (0 : ℝ) < 4096)
    (by norm_num : (4096 : ℝ) ≤ 4 ^ 6)).mul (hNY.pow 3)).mul hR)).logb_inv_le
  rw [← he] at h2
  have hLc1 : 1 ≤ Lc := by linarith
  have hℓc : 1 ≤ Real.logb 2 Lc + 1 := by
    linarith [Real.logb_nonneg one_lt_two hLc1]
  have hLcle : Lc ≤ p * L := by
    have h := hPn.logb_le
    rw [← hLcdef, ← hLdef] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by rw [hp]; linarith) (by linarith))
  have hℓ := logb_add_one_le_of_le_mul hp1 hL2 hLc2 hLcle
  have hX : Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2 ≤
      p ^ 4 * (Real.logb 2 p + 1) ^ 2 * (L ^ 4 * (Real.logb 2 L + 1) ^ 2) := by
    calc Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2
        ≤ (p * L) ^ 4 * ((Real.logb 2 p + 1) * (Real.logb 2 L + 1)) ^ 2 := by gcongr
      _ = _ := by ring
  have hLX : Lc ≤ Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2 := by
    have h4 : Lc ≤ Lc ^ 4 := le_self_pow₀ hLc1 (by norm_num)
    have h1 : 1 ≤ (Real.logb 2 Lc + 1) ^ 2 := one_le_pow₀ hℓc
    nlinarith [pow_pos (by linarith : 0 < Lc) 4]
  have hX0 : 0 ≤ Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2 := by positivity
  have hM : max c₁ 0 * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) + e * Lc ≤
      (max c₁ 0 + e) * (p ^ 4 * (Real.logb 2 p + 1) ^ 2) * L ^ 4 * (Real.logb 2 L + 1) ^ 2 := by
    have hM0 : 0 ≤ max c₁ 0 + e := by positivity
    calc max c₁ 0 * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) + e * Lc
        ≤ max c₁ 0 * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) +
            e * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) := by gcongr
      _ = (max c₁ 0 + e) * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) := by ring
      _ ≤ (max c₁ 0 + e) * (p ^ 4 * (Real.logb 2 p + 1) ^ 2 *
            (L ^ 4 * (Real.logb 2 L + 1) ^ 2)) := by gcongr
      _ = _ := by ring
  have hc1 : c₁ * Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2 ≤
      max c₁ 0 * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
  have hc2 := le_max_left c₂ 0
  have hc20 := le_max_right c₂ 0
  have heL : 0 ≤ e * Lc := by positivity
  have hc10 : 0 ≤ max c₁ 0 * (Lc ^ 4 * (Real.logb 2 Lc + 1) ^ 2) := by positivity
  unfold uDenseEig
  rcases min_choice (uDenseSchurAt n δ (denseEigCoreDelta n δ φ) φ)
    (denseEigCoreDelta n δ φ / (4096 * ((n : ℝ) + 1) ^ 3 * denseEigRotations n δ φ)) with h | h <;>
    rw [h] <;> linarith

/-- **The operation count of the dense eigensolver** (on every tape): the instrumented static
count of `NLAlib.Schur.denseEig` at the order $n + 1$, $n_r$ regularizer words, $n_q$ core words,
the shift degree $k$, the iteration cap $F$, the leaf cap $T$, $n_e$ stage words and zero offsets
is at most the dense Schur solver's $384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$
(`NLAlib.Schur.denseSchur_work_le`), the stage's $10^4(n + 1)^3$
(`NLAlib.Schur.size_stmtCost_triEigvecStage_le`) and the glue $128$. -/
theorem denseEig_work_le (sG n nr nq k F T ne : ℕ) :
    Count.size (stmtCost (denseEig (O := O) (Q := Q) sG).instrument
        [n + 1, nr, nq, k, F, T, ne, 0, 0, 0, 0, 0, 0, 0]) ≤
      384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 +
        10000 * (n + 1) ^ 3 + 128 := by
  have h := size_stmtCost_eigSolverWith_le (denseSchur (O := O) (Q := Q) sG)
    (triEigvecStage (O := O) (Q := Q)) (n + 1) nr nq k F T ne
  have h1 := denseSchur_work_le (O := O) (Q := Q) sG n nr nq k F T
  have h2 := size_stmtCost_triEigvecStage_le (O := O) (Q := Q) n ne
  unfold denseEig
  omega

/-- `NLAlib.Schur.denseEig_work_le` in the reals, at one stage word. -/
private theorem denseEig_work_le_cast (sG n nr nq k F T : ℕ) :
    (Count.size (stmtCost (denseEig (O := O) (Q := Q) sG).instrument
        [n + 1, nr, nq, k, F, T, 1, 0, 0, 0, 0, 0, 0, 0]) : ℝ) ≤
      384547 * ((n : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ^ 4 * ((nr : ℝ) + nq + 1) * ((F : ℝ) + 1) *
        ((T : ℝ) + 1) ^ 2 + 10000 * ((n : ℝ) + 1) ^ 3 + 128 := by
  exact_mod_cast denseEig_work_le (O := O) (Q := Q) sG n nr nq k F T 1

/-- **The operation count of the dense eigensolver is $n^3$ times a polylogarithm**: there is a
constant $C$ such that for every order $n + 1$, $0 < \delta \le 1$ and $0 < \varphi \le 1$, the
instrumented static count at `NLAlib.Schur.denseEigDims` and zero offsets is at most
$C(n + 1)^3L^9(\log_2 L + 1)^6$, $L = \log_2(4(n + 1)/(\delta\varphi))$, that of the dense Schur
solver (`NLAlib.Schur.denseSchur_work_le_polylog`) at the core tolerance $\delta_C$ with
$\log(1/\delta_C) = O(L)$. -/
theorem denseEig_work_le_polylog (sG : ℕ) : ∃ C : ℝ, ∀ {n : ℕ} {δ φ : ℝ}, 0 < δ →
    δ ≤ 1 → 0 < φ → φ ≤ 1 →
    (Count.size (stmtCost (denseEig (O := O) (Q := Q) sG).instrument
      (denseEigDims n δ φ ++ [0, 0, 0, 0, 0, 0, 0])) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ 3 * Real.logb 2 (4 * (n + 1) / (δ * φ)) ^ 9 *
        (Real.logb 2 (Real.logb 2 (4 * (n + 1) / (δ * φ))) + 1) ^ 6 := by
  obtain ⟨C, hC0, hC⟩ := denseSchurAt_work_factor_le
  obtain ⟨P, hP⟩ := denseEig_tolerance_hiBd
  obtain ⟨Ka, -, hca⟩ := denseSchurAt_caps_le
  obtain ⟨Kb, -, hcb⟩ := denseSchur_caps_le
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (P : ℝ) + 1 := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp]; linarith [P.cast_nonneg (α := ℝ)]
  have hlp : 0 ≤ Real.logb 2 p := Real.logb_nonneg one_lt_two hp1
  refine ⟨(C + 10128) * (p ^ 9 * (Real.logb 2 p + 1) ^ 6), fun {n δ φ} hδ hδ1 hφ hφ1 => ?_⟩
  obtain ⟨hD0, hD1, -, -⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  have hf := hC (n := n) hδ hδ1 hD0 hD1 hφ hφ1
  have hPn := hP (n := n) hδ hδ1 hφ hφ1
  obtain ⟨hLc2, -⟩ := hca (n := n) hδ hδ1 hD0 hD1 hφ hφ1
  obtain ⟨hL2, -⟩ := hcb (n := n) hδ hδ1 hφ hφ1
  clear hC hP hca hcb
  set D := denseEigCoreDelta n δ φ with hDdef
  have hd : denseEigDims n δ φ ++ [0, 0, 0, 0, 0, 0, 0] =
      [n + 1, (denseSchurRegParams n δ φ).length,
      (denseSchurThresholdAt n δ D φ :: (denseSchurShQRParamsAt n δ D φ ++
        denseSchurLeafParamsAt n δ D φ)).length, denseSchurDegree n δ φ, denseSchurCapAt n δ D φ,
      denseSchurLeafCapAt n δ D φ, 1, 0, 0, 0, 0, 0, 0, 0] := rfl
  rw [hd]
  clear hd
  have hwR := denseEig_work_le_cast (O := O) (Q := Q) sG n (denseSchurRegParams n δ φ).length
    (denseSchurThresholdAt n δ D φ :: (denseSchurShQRParamsAt n δ D φ ++
      denseSchurLeafParamsAt n δ D φ)).length (denseSchurDegree n δ φ) (denseSchurCapAt n δ D φ)
    (denseSchurLeafCapAt n δ D φ)
  refine hwR.trans ?_
  set Lc := Real.logb 2 (4 * ((n : ℝ) + 1) / (min δ D * φ)) with hLcdef
  set L := Real.logb 2 (4 * ((n : ℝ) + 1) / (δ * φ)) with hLdef
  have hLc1 : 1 ≤ Lc := by linarith
  have hℓc : 1 ≤ Real.logb 2 Lc + 1 := by
    linarith [Real.logb_nonneg one_lt_two hLc1]
  have hLcle : Lc ≤ p * L := by
    have h := hPn.logb_le
    rw [← hLcdef, ← hLdef] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by rw [hp]; linarith) (by linarith))
  have hℓ := logb_add_one_le_of_le_mul hp1 hL2 hLc2 hLcle
  have hN1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith)
  have hX1 : 1 ≤ Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hLc1) (one_le_pow₀ hℓc)
  have hX : Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6 ≤
      p ^ 9 * (Real.logb 2 p + 1) ^ 6 * (L ^ 9 * (Real.logb 2 L + 1) ^ 6) := by
    calc Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6
        ≤ (p * L) ^ 9 * ((Real.logb 2 p + 1) * (Real.logb 2 L + 1)) ^ 6 := by gcongr
      _ = _ := by ring
  have hN0 : 0 ≤ ((n : ℝ) + 1) ^ 3 := by linarith
  have hS : 10000 * ((n : ℝ) + 1) ^ 3 + 128 ≤
      10128 * (((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6)) := by
    have : ((n : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6) :=
      le_mul_of_one_le_right hN0 hX1
    linarith
  have e1 : C * ((n : ℝ) + 1) ^ 3 * Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6 =
      C * (((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6)) := by ring
  rw [e1] at hf
  calc _ ≤ C * (((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6)) +
        10128 * (((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6)) := by linarith
    _ = (C + 10128) * ((n : ℝ) + 1) ^ 3 * (Lc ^ 9 * (Real.logb 2 Lc + 1) ^ 6) := by ring
    _ ≤ (C + 10128) * ((n : ℝ) + 1) ^ 3 *
        (p ^ 9 * (Real.logb 2 p + 1) ^ 6 * (L ^ 9 * (Real.logb 2 L + 1) ^ 6)) := by gcongr
    _ = _ := by ring

end Theorems

end NLAlib.Schur
