/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthBackward
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Krylov.Basic.Compression
public import NLAlib.Krylov.Eigenvalues.Ritz
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Spectral consequences of the backward model of a reorthogonalized run

With $e$ = `NLAlib.LanczosReorthRun.backwardRadius`: the Ritz values interlace the eigenvalues of
$\mathbf{H}$ up to $e$; converged Ritz values are not duplicated (a residual-gated count;
interlacing alone gives no count, see the note's counterexample); Ritz-pair residuals; the
Kaniel–Paige–Saad bound for the backward model; Gauss quadrature exactness and its transfer to
$\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$ for Lipschitz $f$. Eigenvalues are indexed
decreasingly from $0$ (`NLAlib.eigenvalue`). Design: `docs/design/Krylov-LanczosReorth.md`
§3.2.

Common hypotheses: $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$ on the orthogonality level $\mu$
(`NLAlib.LanczosReorthRun.orthLevel`), $\mu + \varepsilon + \varepsilon_2 \le 1/100$
(`NLAlib.LanczosReorthRun.recLevel`) and $\tau \le 1$.

## Main results

* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add`,
  `NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal`: interlacing.
* `NLAlib.LanczosReorthRun.card_le_card_eigenvalue_mem`: no duplicated converged Ritz values.
* `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul`,
  `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_β_le`: Ritz residuals.
* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_mem_Icc`: containment.
* `NLAlib.LanczosReorthRun.exists_backward_kaniel_paige_saad`: the Kaniel–Paige–Saad bound.
* `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`,
  `NLAlib.LanczosReorthRun.exists_pure_backward_abs_quadForm_cfc_sub_le`: Gauss quadrature.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- The matrix of a run is Hermitian (it is real symmetric). -/
private theorem isHermitian_matrix : L.H.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact L.transpose_H

/-- A symmetric perturbation of the matrix of a run is Hermitian. -/
private theorem isHermitian_add {E : Matrix (Fin n) (Fin n) ℝ} (hEs : Eᵀ = E) :
    (L.H + E).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
    L.transpose_H, hEs]

/-- Weyl's inequality for the backward model: $|\lambda_i(\mathbf{H} + \mathbf{E}) -
\lambda_i(\mathbf{H})| \le e$ when $\|\mathbf{E}\|_{\mathsf F} \le e$. -/
private theorem abs_eigenvalue_add_sub_le {E : Matrix (Fin n) (Fin n) ℝ} (hEs : Eᵀ = E)
    (hE : frobNorm E ≤ L.backwardRadius) (i : ℕ) :
    |eigenvalue (L.H + E) i - eigenvalue L.H i| ≤ L.backwardRadius := by
  refine ((L.isHermitian_add hEs).abs_eigenvalue_sub_le L.isHermitian_matrix i).trans ?_
  rw [add_sub_cancel_left]
  exact (specNorm_le_frobNorm E).trans hE

/-- The backward identity compresses to the computed tridiagonal: with $\mathbf{U}_k$ the first
$k$ columns of the polar factor of $\mathbf{V}_{k+1}$,
$\mathbf{U}_k^{\mathsf{H}}(\mathbf{H} + \mathbf{E})\mathbf{U}_k = \mathbf{T}_k$. -/
private theorem conjTranspose_mul_mul_eq_tridiagonal (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) {E : Matrix (Fin n) (Fin n) ℝ}
    (hid : (L.H + E) * (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc =
      (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *
          L.toLanczosData.tridiagonal +
        Matrix.vecMulVec (L.β k • fun i => polarFactor (basisOf L.v (k + 1)) i (Fin.last k))
          (Pi.single L.toLanczosData.lastIndex 1)) :
    ((polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc)ᴴ * (L.H + E) *
      (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc =
        L.toLanczosData.tridiagonal := by
  have hPo := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  set P := polarFactor (basisOf L.v (k + 1))
  have hU : HasOrthonormalCols (P.submatrix id Fin.castSucc) :=
    hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hc : (P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k)) = 0 := by
    funext j
    have h := congrFun (congrFun (hPo.conjTranspose_mul_self) (Fin.castSucc j)) (Fin.last k)
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne] at h
    have hj : ((P.submatrix id Fin.castSucc)ᴴ *ᵥ (L.β k • fun i => P i (Fin.last k))) j =
        L.β k * ∑ x, P x (Fin.castSucc j) * P x (Fin.last k) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]
    rw [hj]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial] at h
    rw [h, mul_zero]
    rfl
  rw [Matrix.mul_assoc, hid, Matrix.mul_add, ← Matrix.mul_assoc,
    hU.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_vecMulVec, hc]
  ext a b
  simp [Matrix.vecMulVec]

/-- A Ritz pair of $\mathbf{T}_k$ is an approximate eigenpair of the backward model: if
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$ then
$(\mathbf{H} + \mathbf{E})\mathbf{U}_k\mathbf{y} - \theta\,\mathbf{U}_k\mathbf{y} =
(y_{k-1}\beta_k)\,\mathbf{u}_{k+1}$. -/
private theorem mulVec_sub_smul_eq {E : Matrix (Fin n) (Fin n) ℝ}
    (hid : (L.H + E) * (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc =
      (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *
          L.toLanczosData.tridiagonal +
        Matrix.vecMulVec (L.β k • fun i => polarFactor (basisOf L.v (k + 1)) i (Fin.last k))
          (Pi.single L.toLanczosData.lastIndex 1))
    {y : Fin k → ℝ} {θ : ℝ} (hy : L.toLanczosData.tridiagonal *ᵥ y = θ • y) :
    (L.H + E) *ᵥ ((polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *ᵥ y) -
        θ • ((polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *ᵥ y) =
      (y L.toLanczosData.lastIndex * L.β k) • fun i =>
        polarFactor (basisOf L.v (k + 1)) i (Fin.last k) := by
  rw [Matrix.mulVec_mulVec, hid, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy,
    Matrix.mulVec_smul, add_sub_cancel_left]
  funext a
  simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, mul_left_comm]

/-- **Ritz values interlace from above up to $e$**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, $\theta_i \le \lambda_i(\mathbf{H}) + e$ for $i < k$, with $\theta_i$ the
eigenvalues of $\mathbf{T}_k$ and $e$ = `NLAlib.LanczosReorthRun.backwardRadius`.
[HornJohnson2013, Corollary 4.3.37] for the exact case.
Result: lanczos-reorth-interlacing -/
theorem eigenvalue_tridiagonal_le_add (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ≤ eigenvalue L.H i + L.backwardRadius := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hU : HasOrthonormalCols ((polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc) :=
    (L.hasOrthonormalCols_polarFactor_basisOf hη hsmall).submatrix (Equiv.refl _)
      (Fin.castSucc_injective _)
  have hPoin := (L.isHermitian_add hEs).eigenvalue_conjTranspose_mul_mul_le hU
    (k := i) (by simpa using hi)
  rw [L.conjTranspose_mul_mul_eq_tridiagonal hη hsmall hid] at hPoin
  linarith [le_abs_self (eigenvalue (L.H + E) i - eigenvalue L.H i),
    L.abs_eigenvalue_add_sub_le hEs hE i]

/-- **Ritz values interlace from below up to $e$**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, $\lambda_{i + n - k}(\mathbf{H}) - e \le \theta_i$ for $i < k$ (and $k \le n$ by
`NLAlib.LanczosReorthRun.succ_le_card`), with $e$ = `NLAlib.LanczosReorthRun.backwardRadius`.
[HornJohnson2013, Corollary 4.3.37] for the exact case.
Result: lanczos-reorth-interlacing -/
theorem eigenvalue_sub_le_eigenvalue_tridiagonal (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.H (i + (n - k)) - L.backwardRadius ≤ eigenvalue L.toLanczosData.tridiagonal i := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hkn := L.succ_le_card hη hsmall
  have hU : HasOrthonormalCols ((polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc) :=
    (L.hasOrthonormalCols_polarFactor_basisOf hη hsmall).submatrix (Equiv.refl _)
      (Fin.castSucc_injective _)
  have hPoin := (L.isHermitian_add hEs).eigenvalue_le_eigenvalue_conjTranspose_mul_mul hU
    (k := i) (d := n - k) (by simpa using hi) (by simp; omega)
  rw [L.conjTranspose_mul_mul_eq_tridiagonal hη hsmall hid] at hPoin
  linarith [neg_abs_le (eigenvalue (L.H + E) (i + (n - k)) - eigenvalue L.H (i + (n - k))),
    L.abs_eigenvalue_add_sub_le hEs hE (i + (n - k))]

/-- **Converged Ritz values are not duplicated**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, for $r$ orthonormal eigenvectors $\mathbf{y}_i$ of $\mathbf{T}_k$ with
eigenvalues $\theta_i \in [a, b]$ and residuals
$\beta_k\lvert\mathbf{e}_{k-1}^{\mathsf{T}}\mathbf{y}_i\rvert < (g - 2e)/\sqrt r$, $g > 2e$
($e$ = `NLAlib.LanczosReorthRun.backwardRadius`), the matrix $\mathbf{H}$ has at least $r$
eigenvalues in $(a - g, b + g)$. With $[a, b]$ a window around a simple isolated eigenvalue this
forbids two converged copies; the residual condition cannot be dropped
(`docs/design/Krylov-LanczosReorth.md` §3.2, counterexample $\operatorname{diag}(1,0,-1)$).
The phenomenon: [Paige1971, §9.2], [Parlett1998, Ch. 13]; this statement: no printed source.
Result: lanczos-reorth-ritz-value-count -/
theorem card_le_card_eigenvalue_mem (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {r : ℕ} {Y : Matrix (Fin k) (Fin r) ℝ}
    (hY : HasOrthonormalCols Y) {θ : Fin r → ℝ}
    (hTY : ∀ i, L.toLanczosData.tridiagonal *ᵥ (fun c => Y c i) = θ i • fun c => Y c i)
    {a b g : ℝ} (hθ : ∀ i, θ i ∈ Set.Icc a b) (hg : 2 * L.backwardRadius < g)
    (hres : ∀ i, L.β k * |Y L.toLanczosData.lastIndex i| <
      (g - 2 * L.backwardRadius) / Real.sqrt r) :
    r ≤ ((Finset.range n).filter fun i => eigenvalue L.H i ∈ Set.Ioo (a - g) (b + g)).card := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have he0 : 0 ≤ L.backwardRadius := (frobNorm_nonneg E).trans hE
  have hPo := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  set U := P.submatrix id Fin.castSucc with hUdef
  have hU : HasOrthonormalCols U := hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  have hβ := L.β_nonneg le_rfl
  have hX : HasOrthonormalCols (U * Y) := by
    change (U * Y)ᴴ * (U * Y) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ U Y,
      hU.conjTranspose_mul_self, Matrix.one_mul]
    exact hY
  have hcard := (L.isHermitian_add hEs).card_le_card_eigenvalue_mem_of_hasOrthonormalCols hX
    (d := g - L.backwardRadius) (by linarith) hθ (fun i => by
    change ‖WithLp.toLp 2 ((L.H + E) *ᵥ (U *ᵥ fun c => Y c i) - θ i • (U *ᵥ fun c => Y c i))‖ <
      (g - L.backwardRadius) / Real.sqrt r
    have hle : (g - 2 * L.backwardRadius) / Real.sqrt r ≤ (g - L.backwardRadius) / Real.sqrt r := by
      gcongr; linarith
    rw [L.mulVec_sub_smul_eq hid (hTY i), WithLp.toLp_smul, norm_smul,
      show (fun j => P j (Fin.last k)) = P.col (Fin.last k) from rfl, hPo.norm_toLp_col,
      mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hβ, mul_comm]
    linarith [hres i])
  refine hcard.trans (Finset.card_le_card fun i hi => ?_)
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo] at hi ⊢
  have hW := abs_le.mp (L.abs_eigenvalue_add_sub_le hEs hE i)
  exact ⟨hi.1, by linarith [hi.2.1, hW.1], by linarith [hi.2.2, hW.2]⟩

/-- **Ritz-pair residuals**: under $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, for $n$ nonempty, every unit eigenvector $\mathbf{y}$ of $\mathbf{T}_k$ with
eigenvalue $\theta$ gives an eigenvalue of $\mathbf{H}$ within
$\beta_k\lvert y_{k-1}\rvert + e$, $e$ = `NLAlib.LanczosReorthRun.backwardRadius`.
[Paige1980, (3.14)–(3.15)] for plain Lanczos. -/
theorem exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.toLanczosData.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ i < n, |eigenvalue L.H i - θ| ≤ L.β k * |y L.toLanczosData.lastIndex| +
      L.backwardRadius := by
  obtain ⟨E, hEs, hE, hid⟩ := L.exists_backward hη hsmall hrec hτ
  have hPo := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  set P := polarFactor (basisOf L.v (k + 1)) with hPdef
  set U := P.submatrix id Fin.castSucc with hUdef
  have hU : HasOrthonormalCols U := hPo.submatrix (Equiv.refl _) (Fin.castSucc_injective _)
  obtain ⟨i, hi, hab⟩ :=
    (L.isHermitian_add hEs).exists_abs_eigenvalue_sub_mul_norm_le (U *ᵥ y) θ
  refine ⟨i, by simpa using hi, ?_⟩
  have hr : ‖WithLp.toLp 2 ((L.H + E) *ᵥ (U *ᵥ y) - θ • (U *ᵥ y))‖ ≤
      L.β k * |y L.toLanczosData.lastIndex| := by
    rw [L.mulVec_sub_smul_eq hid hy, WithLp.toLp_smul, norm_smul,
      show (fun j => P j (Fin.last k)) = P.col (Fin.last k) from rfl, hPo.norm_toLp_col,
      mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.β_nonneg le_rfl), mul_comm]
  rw [hU.norm_toLp_mulVec, hy1, mul_one] at hab
  linarith [abs_sub_le (eigenvalue L.H i) (eigenvalue (L.H + E) i) θ,
    abs_sub_comm (eigenvalue (L.H + E) i) (eigenvalue L.H i), L.abs_eigenvalue_add_sub_le hEs hE i]

/-- **A small last coefficient makes the computed space nearly invariant**: under
$\eta_0 \le 1/100$, the fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$,
$\mu + \varepsilon + \varepsilon_2 \le 1/100$ and $\tau \le 1$, for $n$ nonempty, if
$\beta_k \le \rho$, every Ritz value is within $\rho + e$ of an eigenvalue of $\mathbf{H}$,
$e$ = `NLAlib.LanczosReorthRun.backwardRadius` (with $\rho = \tau\nu_{k+1}$-type bounds when the
next step fails the criterion). [Paige1971, §6.1] (the stopping criterion (6.10) and its
eigenvalue bound). -/
theorem exists_abs_eigenvalue_sub_le_of_β_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {ρ : ℝ} (hρ : L.β k ≤ ρ)
    {i : ℕ} (hi : i < k) :
    ∃ l < n, |eigenvalue L.H l - eigenvalue L.toLanczosData.tridiagonal i| ≤
      ρ + L.backwardRadius := by
  have hT : L.toLanczosData.tridiagonal.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      LanczosData.transpose_tridiagonal]
  obtain ⟨y, hy1, hy⟩ := hT.exists_norm_eq_one_and_mulVec_eq (k := i) (by simpa using hi)
  obtain ⟨l, hl, hab⟩ := L.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul hη hsmall hrec hτ hy hy1
  refine ⟨l, hl, hab.trans ?_⟩
  have hyl : |y L.toLanczosData.lastIndex| ≤ 1 := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 y) L.toLanczosData.lastIndex
    rwa [hy1, Real.norm_eq_abs] at this
  linarith [(mul_le_of_le_one_right (L.β_nonneg le_rfl) hyl).trans hρ]

/-- **Containment**: under $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, every Ritz value lies in $[\lambda_{n-1}(\mathbf{H}) - e,
\lambda_0(\mathbf{H}) + e]$, $e$ = `NLAlib.LanczosReorthRun.backwardRadius`. [Paige1980, (3.48)] for
plain Lanczos. -/
theorem eigenvalue_tridiagonal_mem_Icc (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ∈
      Set.Icc (eigenvalue L.H (n - 1) - L.backwardRadius)
        (eigenvalue L.H 0 + L.backwardRadius) := by
  have hkn := L.succ_le_card hη hsmall
  have hup := L.eigenvalue_tridiagonal_le_add hη hsmall hrec hτ hi
  have hlo := L.eigenvalue_sub_le_eigenvalue_tridiagonal hη hsmall hrec hτ hi
  have h0 := L.isHermitian_matrix.eigenvalue_le_eigenvalue (i := 0) (j := i)
    (Nat.zero_le _) (by simp; omega)
  have hn := L.isHermitian_matrix.eigenvalue_le_eigenvalue (i := i + (n - k)) (j := n - 1)
    (by omega) (by simp; omega)
  constructor <;> linarith

/-- **Kaniel–Paige–Saad for the backward model**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, some symmetric $\mathbf{E}$ with $\|\mathbf{E}\|_{\mathsf F} \le e$
(`NLAlib.LanczosReorthRun.backwardRadius`) has $\lvert\lambda_0(\mathbf{H} + \mathbf{E}) -
\lambda_0(\mathbf{H})\rvert \le e$, and the bound
`Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le` holds for
$(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$, $\mathbf{u}_1$ the first column of the polar factor of
$\mathbf{V}_{k+1}$, with $\mathbf{T}_k$ in place of the compression. The tangent is that of
$\mathbf{H} + \mathbf{E}$. [Saad2011, Theorem 6.4] for the exact bound.
Result: lanczos-reorth-kaniel-paige-saad -/
theorem exists_backward_kaniel_paige_saad (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      |eigenvalue (L.H + E) 0 - eigenvalue L.H 0| ≤ L.backwardRadius ∧
      ∀ {a c : ℝ}, a < c → c < eigenvalue (L.H + E) 0 →
        spectrum ℝ (L.H + E) ⊆ Set.Icc a c ∪ {eigenvalue (L.H + E) 0} →
        0 < (spectralMeasure (L.H + E)
          (colSeq (polarFactor (basisOf L.v (k + 1))) 1)).real {eigenvalue (L.H + E) 0} →
        eigenvalue (L.H + E) 0 - eigenvalue L.toLanczosData.tridiagonal 0 ≤
          4 * (eigenvalue (L.H + E) 0 - a) *
            spectralTangentSq (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1)
              (eigenvalue (L.H + E) 0) *
            ((Real.sqrt (eigenvalue (L.H + E) 0 - a) - Real.sqrt (eigenvalue (L.H + E) 0 - c)) /
              (Real.sqrt (eigenvalue (L.H + E) 0 - a) +
                Real.sqrt (eigenvalue (L.H + E) 0 - c))) ^ (2 * (k - 1)) := by
  obtain ⟨E, hEt, hEf, hst, hT, -⟩ := L.exists_lanczosState_backward hη hsmall hrec hτ
  set U := polarFactor (basisOf L.v (k + 1))
  have hM := L.isHermitian_add hEt
  -- the polar factor is orthonormal, so are the first `k` Lanczos vectors
  have hU : HasOrthonormalCols U := L.hasOrthonormalCols_polarFactor_basisOf hη hsmall
  have hQ : HasOrthonormalCols (arnoldiMatrix (L.H + E) (colSeq U 1) k) := by
    rw [← hM.lanczosMatrix_eq_arnoldiMatrix]
    have hQU : lanczosMatrix (L.H + E) (colSeq U 1) k =
        U.submatrix (Equiv.refl _) Fin.castSucc := by
      ext i j
      simp only [lanczosMatrix, Matrix.of_apply, hst j j.isLt, colSeq, Matrix.submatrix_apply,
        Equiv.refl_apply]
      rw [dif_pos (by omega)]
      rfl
    rw [hQU]
    exact hU.submatrix _ (Fin.castSucc_injective _)
  refine ⟨E, hEt, hEf, ?_, fun {a c} hac hc hs hb => ?_⟩
  · exact L.abs_eigenvalue_add_sub_le hEt hEf 0
  · have hK : LinearMap.range (arnoldiMatrix (L.H + E) (colSeq U 1) k).mulVecLin =
        krylovSpace (L.H + E) (colSeq U 1) (k - 1 + 1) := by
      rw [range_arnoldiMatrix, Nat.sub_add_cancel L.k_pos]
    have h := hM.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le hac hc hs hb hQ hK
    rwa [← hM.lanczosTridiagonal_eq, hT] at h

/-- Powers of degree below $2m$ pass to the compression onto an orthonormal basis of
$\mathcal K_m(\mathbf{A}, \mathbf{b})$, for symmetric $\mathbf{A}$. -/
private theorem dotProduct_pow_mulVec_eq_compression {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {b : Fin n → ℝ} {Q : Matrix (Fin n) (Fin m) ℝ} (hQ : HasOrthonormalCols Q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b m) {j : ℕ} (hj : j < 2 * m) :
    b ⬝ᵥ (A ^ j *ᵥ b) = (Qᵀ *ᵥ b) ⬝ᵥ ((Qᵀ * A * Q) ^ j *ᵥ (Qᵀ *ᵥ b)) := by
  have hQQ : Qᵀ * Q = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ
  have hproj : ∀ i < m, Q *ᵥ (Qᵀ *ᵥ (A ^ i *ᵥ b)) = A ^ i *ᵥ b := fun i hi => by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hK ▸ pow_mulVec_mem_krylovSpace A b hi)
    rw [Matrix.mulVecLin_apply] at hy
    rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hpow : ∀ i ≤ m, Qᵀ *ᵥ (A ^ i *ᵥ b) = (Qᵀ * A * Q) ^ i *ᵥ (Qᵀ *ᵥ b) := fun i hi => by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      HasOrthonormalCols.conjTranspose_mulVec_aeval_mulVec_eq hQ hK
        (p := (Polynomial.X : Polynomial ℝ) ^ i)
        ((Polynomial.degree_X_pow_le i).trans (by exact_mod_cast hi))
  have hdot : ∀ {l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ), Mᵀ = M → ∀ a c (x : Fin l → ℝ),
      x ⬝ᵥ (M ^ (a + c) *ᵥ x) = (M ^ a *ᵥ x) ⬝ᵥ (M ^ c *ᵥ x) := fun M hM a c x => by
    rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_pow, hM]
  have hC : (Qᵀ * A * Q)ᵀ = Qᵀ * A * Q := by
    simp only [Matrix.transpose_mul, hA, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨a, c, rfl, ha, hc⟩ : ∃ a c, j = a + c ∧ a < m ∧ c ≤ m :=
    ⟨j - min j m, min j m, by omega, by omega, by omega⟩
  rw [hdot A hA, hdot _ hC, ← hproj a ha, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, hpow a ha.le, hpow c hc]

/-- Polynomials of degree below $2m$ pass to the compression onto an orthonormal basis of
$\mathcal K_m(\mathbf{A}, \mathbf{b})$, for symmetric $\mathbf{A}$. -/
private theorem dotProduct_aeval_mulVec_eq_compression {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {b : Fin n → ℝ} {Q : Matrix (Fin n) (Fin m) ℝ} (hQ : HasOrthonormalCols Q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b m) {p : Polynomial ℝ}
    (hp : p.natDegree < 2 * m) :
    b ⬝ᵥ (Polynomial.aeval A p *ᵥ b) =
      (Qᵀ *ᵥ b) ⬝ᵥ (Polynomial.aeval (Qᵀ * A * Q) p *ᵥ (Qᵀ *ᵥ b)) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec,
    Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
    dotProduct_pow_mulVec_eq_compression hA hQ hK (by have := Finset.mem_range.mp hi; omega)]

/-- **Gauss quadrature on the backward model**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$, if $\mathbf{b} \ne \mathbf{0}$ and $\|\mathbf{b}/\|\mathbf{b}\| - \mathbf{v}_1\| \le
\delta_b$, some symmetric $\mathbf{H}'$ with
$$\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F} \le e + 3\|\mathbf{H}\|_2\,
(\delta_b + 2\sqrt{3(k+1)}\,\mu)$$
($e$ = `NLAlib.LanczosReorthRun.backwardRadius`) has $\|\mathbf{b}\|^2\,[p(\mathbf{T}_k)]_{00} =
\mathbf{b}^{\mathsf{T}}p(\mathbf{H}')\mathbf{b}$ for every polynomial $p$ of degree at most
$2k - 1$ (the entry at `NLAlib.LanczosReorthRun.firstIndex`): the computed tridiagonal is the
Gauss rule of the spectral measure of $(\mathbf{H}', \mathbf{b})$.
[GolubMeurant2010, Theorem 6.6].
Result: lanczos-reorth-gauss-quadrature -/
theorem exists_pure_backward_gauss (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * k - 1 →
        ‖WithLp.toLp 2 b‖ ^ 2 *
            (Polynomial.aeval L.toLanczosData.tridiagonal p) L.firstIndex L.firstIndex =
          b ⬝ᵥ (Polynomial.aeval H' p *ᵥ b) := by
  obtain ⟨H', hH't, hbd, hT⟩ := L.exists_pure_backward hη hsmall hrec hτ hb hδ
  refine ⟨H', hH't, hbd, fun p hp => ?_⟩
  have hA : H'.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hH't]
  obtain ⟨q, hq⟩ : ∃ q, k = q + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos L.k_pos).symm⟩
  subst hq
  -- the grade is at least `k`: `b ≠ 0`, and `β_j > 0` is an entry of the tridiagonal
  have hgr : q + 1 ≤ krylovGrade H' b := by
    rcases q with _ | q
    · by_contra h
      have h0 := krylovGrade_le_iff.mp (by omega : krylovGrade H' b ≤ 0)
      rw [krylovSpace_zero, pow_zero, Matrix.one_mulVec, Submodule.mem_bot] at h0
      exact hb h0
    · have hβ : (lanczosState H' b (q + 1)).beta = L.β (q + 1) := by
        have h := congrFun (congrFun hT ⟨q + 1, by omega⟩) ⟨q, by omega⟩
        simpa [lanczosTridiagonal, LanczosData.tridiagonal, toLanczosData] using h
      have hpos : 0 < L.β (q + 1) := L.β_succ_pos (by omega)
      by_contra h
      exact hpos.ne' (hβ ▸ (hA.lanczosState_beta_eq_zero_iff b q).mpr (by omega))
  set Q := arnoldiMatrix H' b (q + 1)
  have hTQ : L.toLanczosData.tridiagonal = Qᵀ * H' * Q := by
    rw [← hT, hA.lanczosTridiagonal_eq, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hQb : Qᵀ *ᵥ b = ‖WithLp.toLp 2 b‖ • Pi.single 0 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    simpa using conjTranspose_arnoldiMatrix_mulVec_self H' b q
  -- both sides are quadratic forms of the compression `T = Qᵀ H' Q`
  rw [dotProduct_aeval_mulVec_eq_compression hH't (hasOrthonormalCols_arnoldiMatrix_iff.mpr hgr)
    (range_arnoldiMatrix _ _ _) (by omega), ← hTQ, hQb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.col_apply, smul_eq_mul]
  rw [show L.firstIndex = 0 from rfl]
  ring

/-- **Transfer to $\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$**: under $\eta_0 \le 1/100$, the
fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$
and $\tau \le 1$, if $\mathbf{b} \ne \mathbf{0}$ and
$\|\mathbf{b}/\|\mathbf{b}\| - \mathbf{v}_1\| \le \delta_b$, some symmetric $\mathbf{H}'$ with
$\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F} \le e + 3\|\mathbf{H}\|_2(\delta_b + 2\sqrt{3(k+1)}\,\mu)$
($e$ = `NLAlib.LanczosReorthRun.backwardRadius`) has Lanczos tridiagonal $\mathbf{T}_k$ from
$\mathbf{b}$ and, for every $1$-Lipschitz $f$,
$\lvert\mathbf{b}^{\mathsf{T}}f(\mathbf{H}')\mathbf{b} -
\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}\rvert \le
\|\mathbf{b}\|^2\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F}$, so the exact quadrature error theory
for $(\mathbf{H}', \mathbf{b})$ transfers with that additive term. [Kittaneh1985, abstract].
Result: lanczos-reorth-gauss-quadrature -/
theorem exists_pure_backward_abs_quadForm_cfc_sub_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      lanczosTridiagonal H' b k = L.toLanczosData.tridiagonal ∧
      ∀ f : ℝ → ℝ, LipschitzWith 1 f →
        |b ⬝ᵥ (cfc f H' *ᵥ b) - b ⬝ᵥ (cfc f L.H *ᵥ b)| ≤
          ‖WithLp.toLp 2 b‖ ^ 2 * frobNorm (H' - L.H) := by
  obtain ⟨H', hH'T, hfrob, htri⟩ := L.exists_pure_backward hη hsmall hrec hτ hb hδ
  have hH' : H'.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hH'T]
  refine ⟨H', hH'T, hfrob, htri, fun f hf => ?_⟩
  have hH := L.isHermitian_matrix
  have h := norm_star_dotProduct_mulVec_le (cfc f H' - cfc f L.H) b b
  have hc := hH'.frobNorm_cfc_sub_cfc_le hH hf
  have e : b ⬝ᵥ (cfc f H' *ᵥ b) - b ⬝ᵥ (cfc f L.H *ᵥ b) =
      b ⬝ᵥ ((cfc f H' - cfc f L.H) *ᵥ b) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [e, ← Real.norm_eq_abs]
  rw [star_trivial] at h
  calc ‖b ⬝ᵥ ((cfc f H' - cfc f L.H) *ᵥ b)‖
      ≤ ‖WithLp.toLp 2 b‖ * specNorm (cfc f H' - cfc f L.H) * ‖WithLp.toLp 2 b‖ := h
    _ ≤ ‖WithLp.toLp 2 b‖ * frobNorm (cfc f H' - cfc f L.H) * ‖WithLp.toLp 2 b‖ := by
        gcongr; exact specNorm_le_frobNorm _
    _ ≤ ‖WithLp.toLp 2 b‖ * frobNorm (H' - L.H) * ‖WithLp.toLp 2 b‖ := by gcongr
    _ = ‖WithLp.toLp 2 b‖ ^ 2 * frobNorm (H' - L.H) := by ring

end LanczosReorthRun

end NLAlib
