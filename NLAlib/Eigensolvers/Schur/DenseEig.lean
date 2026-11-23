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
  obtain ⟨hD0, hD1⟩ := denseEigCoreDelta_pos_le (n := n) hδ hδ1 hφ hφ1
  have hR : 0 < (denseEigRotations n δ φ : ℝ) := by
    unfold denseEigRotations denseSchurRotationsAt denseSchurRotationsAtWith; positivity
  exact lt_min (uDenseSchurAt_pos hδ hδ1 hD0 hD1 hφ hφ1) (by positivity)

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
  have hN3 : N ^ 3 * u ≤ D / 4096 := by
    have := mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ N ^ 3 * u); nlinarith
  have hNR : N * R * u ≤ D / 4096 := by
    have : N * R * u ≤ N ^ 3 * R * u := by
      have h1 : N ≤ N ^ 3 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ R * u); nlinarith
    linarith
  have hRu : R * u ≤ D / 4096 := by
    have := mul_le_mul_of_nonneg_right hN1 (by positivity : (0 : ℝ) ≤ R * u); nlinarith
  have hNu : N * u ≤ D / 4096 := by
    have := mul_le_mul_of_nonneg_left hR1 (by positivity : (0 : ℝ) ≤ N * u); nlinarith
  have hN2u : N ^ 2 * u ≤ D / 4096 := by
    have : N ^ 2 * u ≤ N ^ 3 * u := by
      have : N ^ 2 ≤ N ^ 3 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hu0
    linarith
  have hsu : s * u ≤ D / 4096 := by
    have := mul_le_mul_of_nonneg_right hsN hu0; linarith
  obtain ⟨hε0, -, hεU, -⟩ := denseSchur_errors_le (Rc := Rc) hD0 hu0
    (by rw [← hR]; exact h4096) hu2 hu8 hD1
  rw [← hR] at hεU
  set ε := (1 + 27 * N ^ 2 * u) * (1 + 24 * u) ^ Rc - 1 with hεdef
  set eU := 2 * ε + ε ^ 2 with heUdef
  have hε29 : ε ≤ 29 * R * u := by nlinarith
  have heU0 : 0 ≤ eU := by positivity
  have heUD : eU ≤ 58 * D / 4096 := by linarith
  -- the error against the regularized matrix
  have hsδ : s * denseSchurDelta n D = D / 16 := by
    unfold denseSchurDelta; rw [← hNdef, ← hs]; field_simp
  have heX : schurPipelineEX n (1 / 2) 2 u (50 * N ^ 2 * u) (denseSchurDelta n D) ε ≤ D := by
    unfold schurPipelineEX
    rw [← hNdef, ← hs]
    have e : 2 * 2 * s * (3 * (50 * N ^ 2 * u) / (1 / 2) + denseSchurDelta n D + 8 * ε / (1 / 2)) +
        (8 + 2 * 2 / (1 / 2)) * N * u = 1200 * (s * (N ^ 2 * u)) +
          4 * (s * denseSchurDelta n D) + 64 * (s * ε) + 16 * (N * u) := by ring
    rw [e, hsδ]
    have h1 : s * (N ^ 2 * u) ≤ N ^ 3 * u := by
      have := mul_le_mul_of_nonneg_right hsN (by positivity : (0 : ℝ) ≤ N ^ 2 * u); nlinarith
    have h2 : s * ε ≤ 29 * (N * R * u) := by
      have := mul_le_mul hsN hε29 hε0 (by linarith); nlinarith
    linarith
  set eX := schurPipelineEX n (1 / 2) 2 u (50 * N ^ 2 * u) (denseSchurDelta n D) ε with heXdef
  have heX0 : 0 ≤ eX := by
    unfold schurPipelineEX at heXdef; rw [heXdef]
    have : 0 ≤ denseSchurDelta n D := by unfold denseSchurDelta; positivity
    positivity
  have heR : 2 * s * (denseSchurDelta n δ / 2) + 3 * s * u = δ / 16 + 3 * (s * u) := by
    unfold denseSchurDelta; rw [← hNdef, ← hs]; field_simp; ring
  -- the stage constants
  have hcR : 4 * s * (16 * (1 + s) * ((n : ℝ) + 2) * u) ≤ 256 * (N ^ 3 * u) := by
    have e2 : (n : ℝ) + 2 = N + 1 := by rw [hNdef]; ring
    rw [e2]
    have h1 : s * (1 + s) ≤ N * (2 * N) := mul_le_mul hsN (by linarith) (by linarith) (by linarith)
    have h2 : s * (1 + s) * (N + 1) ≤ N * (2 * N) * (2 * N) :=
      mul_le_mul h1 (by linarith) (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 64 * u)
    nlinarith
  have hcV : 8 * N * (8 * ((n : ℝ) + 2) * u) ≤ 128 * (N ^ 3 * u) := by
    have e2 : (n : ℝ) + 2 = N + 1 := by rw [hNdef]; ring
    rw [e2]
    have : N * (N + 1) ≤ 2 * N ^ 3 := by nlinarith
    nlinarith
  set η := eigEta n eX eU (16 * (1 + s) * ((n : ℝ) + 2) * u) (8 * ((n : ℝ) + 2) * u) with hηdef
  have hη : η ≤ 3 * D := by
    rw [hηdef]; unfold eigEta; rw [← hNdef, ← hs]
    linarith
  have hη0 : 0 ≤ η := by
    rw [hηdef]; unfold eigEta; rw [← hNdef, ← hs]; positivity
  have hD1024 : D * (1024 * N ^ 2 * B) ≤ δ := by rw [← hNdef] at hDδ; linarith
  have hDΓ' : D * (1024 * N ^ 2 * B) ≤ Γ := by rw [← hNdef] at hDΓ; linarith
  have hDNB : D * N * B ≤ δ / 1024 := by
    have : D * N * B ≤ D * (N ^ 2 * B) := by
      have := mul_le_mul_of_nonneg_left (by nlinarith : N ≤ N ^ 2) (by positivity : (0 : ℝ) ≤ D)
      nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ B)]
    linarith
  have hDNBΓ : D * N * B ≤ Γ / 1024 := by
    have : D * N * B ≤ D * (N ^ 2 * B) := by
      have := mul_le_mul_of_nonneg_left (by nlinarith : N ≤ N ^ 2) (by positivity : (0 : ℝ) ≤ D)
      nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ B)]
    linarith
  have hDδ' : D ≤ δ / 2048 := by
    have : D * 2048 ≤ D * (1024 * N ^ 2 * B) := mul_le_mul_of_nonneg_left (by nlinarith) hD0.le
    linarith
  have hDΓ'' : D ≤ Γ / 2048 := by
    have : D * 2048 ≤ D * (1024 * N ^ 2 * B) := mul_le_mul_of_nonneg_left (by nlinarith) hD0.le
    linarith
  rw [heR]
  refine ⟨by linarith, by rw [hRdef] at hεU; exact hεU, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold eigColTol; rw [← hNdef]
    have e3 : (n : ℝ) + 3 = N + 2 := by rw [hNdef]; ring
    rw [e3]
    nlinarith
  · unfold denseEigFloor; rw [← hDdef, ← hNdef, ← hs]
    have e : 16 * (4 * (D / (64 * N))) * s = D * s / N := by field_simp; ring
    rw [e, div_lt_iff₀ (by linarith)]
    have : D * s ≤ D * N := mul_le_mul_of_nonneg_left hsN hD0.le
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have h1 : (eX + 6 * eU) * (16 * N * B) ≤ 2 * D * (16 * N * B) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  · have : 8 * s * B * η ≤ 8 * N * B * (3 * D) := by
      have := mul_le_mul hsN hη hη0 (by linarith)
      have hB0 : (0 : ℝ) ≤ 8 * B := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hB0]
    nlinarith
  · linarith
  · have : s * η ≤ N * (3 * D) := mul_le_mul hsN hη hη0 (by linarith)
    have : N * D ≤ D * N * B := by nlinarith
    linarith
  · have : 2 * N * B * η ≤ 2 * N * B * (3 * D) :=
      mul_le_mul_of_nonneg_left hη (by positivity)
    nlinarith

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
  have hEv := triEigvecStage_eigenvectorStageContract (O := O) (Q := Q) hS hM hL
    (hNat.mono (by omega)) hC hρ h64
  have e2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have e3 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [e2, e3, e1] at hEv
  have hw := eigSolverWith_pwrites hS hM hL hNat hC hI hloc hSolve hEv hΓ (by linarith)
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) heU hc hfloor hsep hκ
  refine (measureReal_mono fun ω hω hs => hω (hs.mono le_rfl fun μ' _ hout => ?_)).trans
    (hw.measureReal_not_writes_le hin hξ)
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
  exact eigSolverWith_terminates hS hL hC hSolve (triEigvecStage_completes hS hL hC (n + 1) _)
    hin τ

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
  sorry

end Theorems

end NLAlib.Schur
