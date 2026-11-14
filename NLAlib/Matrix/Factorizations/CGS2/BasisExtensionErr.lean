/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.CGS2.BasisExtension
public import NLAlib.Matrix.FinitePrecision.ClassicalGramSchmidt

/-!
# Rounded column-wise two-pass classical Gram–Schmidt extends a basis

The rounded guarantee of the column-wise scheme with threshold deflation, on decoded matrices.
Column $c$ of the block is reduced against $\mathbf{V}_c = [\mathbf{Q}, \mathbf{Q}'_{<c}]$, which
has zero columns where earlier columns were dropped. A zero column contributes nothing to a
reduction, so the single-vector guarantee `NLAlib.IsOrthErr` is restated with the Gram defect on
the support in its antecedent, `NLAlib.IsOrthErrOnSupport`; it follows from `NLAlib.IsOrthErr` on
the nonzero columns. From this guarantee for every column, computed norms of relative accuracy
$E$, and a deflation test with threshold $\tau$, the block meets the rounded contract
`NLAlib.IsBasisExtensionErr` with
$\mu = 2\varepsilon_1 + 4\varepsilon_3/\tau + 5E$ and
$\varepsilon = \varepsilon_2 + 2E + 2\tau$. Design: `docs/design/LowRank-BlockLanczos.md` §3.5.

## Main definitions

* `NLAlib.IsOrthErrOnSupport`: the guarantee of one orthogonalization step against a basis with
  zero columns.
* `NLAlib.cgs2ExtendMu`, `NLAlib.cgs2ExtendEps`: the parameters $\mu$ and $\varepsilon$ of the
  column-wise scheme.

## Main results

* `NLAlib.IsOrthErr.isOrthErrOnSupport`, `NLAlib.IsOrthErrOnSupport.of_submatrix`: the guarantee
  with no zero column, and compression to a selection of columns containing the nonzero ones.
* `NLAlib.IsOrthErrOnSupport.norm_transpose_mulVec_le_of_admissible`,
  `NLAlib.IsOrthErrOnSupport.norm_le_two_mul`: an admissible normalized column, and the norm of
  the reduced vector.
* `NLAlib.isOrthErrOnSupport_of_two_passes`: two classical passes against a basis with zero
  columns.
* `NLAlib.cgs2ExtendMu_nonneg`: the parameter $\mu$ is nonnegative.
* `NLAlib.isBasisExtensionErr_of_columns`: the column-wise scheme meets the rounded contract.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The guarantee of one orthogonalization step against a basis with zero columns**: if the
Gram defect on the support $\mathbf{D}$ of $\mathbf{V}$ satisfies $\|\mathbf{D}\|_2 \le \eta_0$,
the coefficients $\mathbf{h}$ and the reduced vector $\mathbf{w}'$ satisfy
$\|\mathbf{w} - \mathbf{V}\mathbf{h} - \mathbf{w}'\| \le \varepsilon_2\|\mathbf{w}\|$ and
$\|\mathbf{V}^{\mathsf{T}}\mathbf{w}'\| \le \varepsilon_1\|\mathbf{w}'\| +
\varepsilon_3\|\mathbf{w}\|$. The coefficients at zero columns of $\mathbf{V}$ are unconstrained.
With no zero column this is `NLAlib.IsOrthErr`. -/
structure IsOrthErrOnSupport {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ ε₁ ε₂ ε₃ : ℝ) (V : Matrix (Fin n) ι ℝ) (w : Fin n → ℝ) (h : ι → ℝ)
    (w' : Fin n → ℝ) : Prop where
  /-- The representation of the input. -/
  residual : specNorm (gramDefect V) ≤ η₀ →
    ‖WithLp.toLp 2 (w - V *ᵥ h - w')‖ ≤ ε₂ * ‖WithLp.toLp 2 w‖
  /-- The local loss of orthogonality. -/
  orth : specNorm (gramDefect V) ≤ η₀ →
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ ≤ ε₁ * ‖WithLp.toLp 2 w'‖ + ε₃ * ‖WithLp.toLp 2 w‖

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {η₀ ε₁ ε₂ ε₃ : ℝ}

/-- For a basis $\mathbf{V}$ with no zero column, the guarantee `NLAlib.IsOrthErr` of one
orthogonalization step with parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ is the guarantee on the support with the
same parameters. -/
theorem IsOrthErr.isOrthErrOnSupport {j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ} {w : Fin n → ℝ}
    {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hne : ∀ i, V.col i ≠ 0) : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w' := by
  have hg : gramDefect V = Vᵀ * V - 1 := by
    rw [gramDefect_eq_conjTranspose_mul_self_sub_one hne,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  exact ⟨fun hV => hO.residual (hg ▸ hV), fun hV => hO.orth (hg ▸ hV)⟩

/-- Compression to a selection of columns. Let $e$ be an injective selection of columns of
$\mathbf{V}$ such that every column outside the selection is zero, and $\mathbf{V}_e$ the
selected columns. If the step $(\mathbf{h}_e, \mathbf{w}')$, with $\mathbf{h}_e$ the selected
entries of $\mathbf{h}$, meets the guarantee on the support for $\mathbf{w}$ and $\mathbf{V}_e$
with parameters $(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$, then
$(\mathbf{h}, \mathbf{w}')$ meets it for $\mathbf{w}$ and $\mathbf{V}$: a zero column contributes
nothing to $\mathbf{V}\mathbf{h}$ and to $\mathbf{V}^{\mathsf{T}}\mathbf{w}'$. -/
theorem IsOrthErrOnSupport.of_submatrix {V : Matrix (Fin n) ι ℝ} {w : Fin n → ℝ} {h : ι → ℝ}
    {w' : Fin n → ℝ} {e : κ → ι} (he : Function.Injective e)
    (hz : ∀ i, i ∉ Set.range e → V.col i = 0)
    (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ (V.submatrix id e) w (h ∘ e) w') :
    IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w' := by
  -- Antecedent: `gramDefect_submatrix V he` and `specNorm_submatrix_le` give
  -- `specNorm (gramDefect (V.submatrix id e)) ≤ specNorm (gramDefect V)`.
  -- `V *ᵥ h = V.submatrix id e *ᵥ (h ∘ e)`: split the sum over `ι` into the range of `e`
  -- (`Finset.sum_map` with the embedding of `e`) and its complement, where `hz` gives zero terms.
  -- `‖toLp (Vᵀ *ᵥ w')‖ = ‖toLp ((V.submatrix id e)ᵀ *ᵥ w')‖`: the same split of the sum of
  -- squares (`EuclideanSpace.norm_sq_eq`), the entries outside the range being zero.
  sorry

/-- One admissible normalized column against a basis with zero columns. Let
$(\mathbf{h}, \mathbf{w}')$ meet the guarantee on the support with parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ for the input $\mathbf{w}$ and the basis
$\mathbf{V}$, whose Gram defect on the support $\mathbf{D}$ satisfies
$\|\mathbf{D}\|_2 \le \eta_0 \le 1/100$, with $\varepsilon_1, \varepsilon_3 \ge 0$. Let $\nu$ and
$\beta$ be computed norms, $\lvert\nu - \|\mathbf{w}\|\rvert \le E\|\mathbf{w}\|$ and
$\lvert\beta - \|\mathbf{w}'\|\rvert \le E\|\mathbf{w}'\|$ with $0 \le E \le 1/100$, let
$\beta\mathbf{v} = \mathbf{w}' + \boldsymbol{\delta}$ with
$\|\boldsymbol{\delta}\| \le E\|\mathbf{w}'\|$, and let the column be admissible,
$\tau\nu < \beta$ with $\tau > 0$. Then
$\|\mathbf{V}^{\mathsf{T}}\mathbf{v}\| \le 2(\varepsilon_1 + \varepsilon_3/\tau + E)$. -/
theorem IsOrthErrOnSupport.norm_transpose_mulVec_le_of_admissible {E τ ν β : ℝ}
    {V : Matrix (Fin n) ι ℝ} {w : Fin n → ℝ} {h : ι → ℝ} {w' v δ : Fin n → ℝ}
    (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w') (hV : specNorm (gramDefect V) ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hε₁ : 0 ≤ ε₁) (hε₃ : 0 ≤ ε₃) (he0 : 0 ≤ E) (he1 : E ≤ 1 / 100)
    (hτ : 0 < τ) (hν : |ν - ‖WithLp.toLp 2 w‖| ≤ E * ‖WithLp.toLp 2 w‖)
    (hβ : |β - ‖WithLp.toLp 2 w'‖| ≤ E * ‖WithLp.toLp 2 w'‖)
    (hv : β • v = w' + δ) (hδ : ‖WithLp.toLp 2 δ‖ ≤ E * ‖WithLp.toLp 2 w'‖)
    (hadm : τ * ν < β) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ v)‖ ≤ 2 * (ε₁ + ε₃ / τ + E) := by
  -- Let `e` enumerate the nonzero columns of `V` (`Fintype.equivFin` of the subtype) and
  -- `Ve := V.submatrix id e`. `specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect` gives
  -- the antecedent of `IsOrthErr` for `Ve`; the two clauses of `hO` are those of
  -- `IsOrthErr η₀ ε₁ ε₂ ε₃ Ve w (h ∘ e) w'` (the sums of `IsOrthErrOnSupport.of_submatrix`), so
  -- `IsOrthErr.norm_transpose_mulVec_le_of_admissible` bounds `‖toLp (Veᵀ *ᵥ v)‖`, which is
  -- `‖toLp (Vᵀ *ᵥ v)‖`.
  sorry

/-- The reduced vector is not longer than twice the input. Let $(\mathbf{h}, \mathbf{w}')$
meet the guarantee on the support with parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ for the input $\mathbf{w}$ and the basis
$\mathbf{V}$, whose Gram defect on the support $\mathbf{D}$ satisfies
$\|\mathbf{D}\|_2 \le \eta_0 \le 1/100$, with
$0 \le \varepsilon_1, \varepsilon_2, \varepsilon_3 \le 1/10$. Then
$\|\mathbf{w}'\| \le 2\|\mathbf{w}\|$. -/
theorem IsOrthErrOnSupport.norm_le_two_mul {V : Matrix (Fin n) ι ℝ} {w : Fin n → ℝ} {h : ι → ℝ}
    {w' : Fin n → ℝ} (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (gramDefect V) ≤ η₀) (hη : η₀ ≤ 1 / 100) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 10)
    (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1 / 10) (hε₃ : 0 ≤ ε₃) (hε₃' : ε₃ ≤ 1 / 10) :
    ‖WithLp.toLp 2 w'‖ ≤ 2 * ‖WithLp.toLp 2 w‖ := by
  -- Compress to the nonzero columns as in `norm_transpose_mulVec_le_of_admissible`, so that
  -- `IsOrthErr.norm_coef_le` bounds the coefficients: with `a = ‖w‖`, `x = ‖w'‖`,
  -- `‖h ∘ e‖ ≤ (√(1 + η₀) * a + (ε₁ * x + ε₃ * a) + √(1 + η₀) * ε₂ * a) / (1 - η₀)`.
  -- Write `w' = w - Ve *ᵥ (h ∘ e) - r` with `‖r‖ ≤ ε₂ * a` and take the inner product with `w'`:
  -- `x ^ 2 ≤ x * a + ‖Veᵀ *ᵥ w'‖ * ‖h ∘ e‖ + x * ε₂ * a`. The numbers give
  -- `x ^ 2 ≤ (1 / 50) * x ^ 2 + (5 / 4) * x * a + (1 / 8) * a ^ 2`, hence `x ≤ 2 * a`
  -- (`nlinarith`).
  sorry

/-- **Twice is enough against a basis with zero columns**: let two classical passes against
$\mathbf{V}$ satisfy, whenever the Gram defect on the support $\mathbf{D}$ of $\mathbf{V}$ has
$\|\mathbf{D}\|_2 \le \eta_0$, the coefficient, residual and projection-error bounds
$\|\mathbf{h}_1 - \mathbf{V}^{\mathsf{T}}\mathbf{w}\| \le c_1\|\mathbf{w}\|$,
$\|\mathbf{w} - \mathbf{V}\mathbf{h}_1 - \mathbf{w}_1\| \le c_1\|\mathbf{w}\|$,
$\|\mathbf{w}_1 - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\| \le
c_1\|\mathbf{w}\|$, and the same from $\mathbf{w}_1$ to $\mathbf{h}_2$, $\mathbf{w}_2$, and let
the coefficients be summed with relative error $u$,
$\lvert h_i - (h_{1,i} + h_{2,i})\rvert \le u\lvert h_{1,i} + h_{2,i}\rvert$. Then for
$\eta_0 \le 1/100$, $c_1 \le 1/100$, $u \ge 0$, $4u \le c_1$ the step
$(\mathbf{h}, \mathbf{w}_2)$ meets the guarantee on the support with
$\varepsilon_1 = 2c_1$, $\varepsilon_2 = 3c_1$, $\varepsilon_3 = 2(\eta_0 + c_1)^2$.
[GiraudLangouRozloznikVandenEshof2005, Theorem 2] for a basis with no zero column. -/
theorem isOrthErrOnSupport_of_two_passes {V : Matrix (Fin n) ι ℝ} {w w₁ w₂ : Fin n → ℝ}
    {h₁ h₂ h : ι → ℝ} {c₁ u : ℝ} (hη : η₀ ≤ 1 / 100) (hc₁ : c₁ ≤ 1 / 100) (hu : 0 ≤ u)
    (hu₁ : 4 * u ≤ c₁)
    (hp₁ : specNorm (gramDefect V) ≤ η₀ →
      ‖WithLp.toLp 2 (h₁ - Vᵀ *ᵥ w)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w - V *ᵥ h₁ - w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖)
    (hp₂ : specNorm (gramDefect V) ≤ η₀ →
      ‖WithLp.toLp 2 (h₂ - Vᵀ *ᵥ w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₁ - V *ᵥ h₂ - w₂)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁)))‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖)
    (hsum : ∀ i, |h i - (h₁ i + h₂ i)| ≤ u * |h₁ i + h₂ i|) :
    IsOrthErrOnSupport η₀ (2 * c₁) (3 * c₁) (2 * (η₀ + c₁) ^ 2) V w h w₂ := by
  -- Let `e : Fin j → ι` enumerate the nonzero columns of `V` and `Ve := V.submatrix id e`. The
  -- three bounds of each pass restrict to `Ve`: `V *ᵥ x = Ve *ᵥ (x ∘ e)`,
  -- `V *ᵥ (Vᵀ *ᵥ w) = Ve *ᵥ (Veᵀ *ᵥ w)`, and `‖toLp ((h₁ - Vᵀ *ᵥ w) ∘ e)‖ ≤ ‖toLp (h₁ - Vᵀ *ᵥ w)‖`.
  -- With the antecedent from `specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect`,
  -- `isOrthErr_of_two_passes` gives `IsOrthErr` for `Ve`, `IsOrthErr.isOrthErrOnSupport` the
  -- guarantee on its support, and `IsOrthErrOnSupport.of_submatrix` the claim for `V`.
  sorry

/-- **The orthogonality parameter of the column-wise scheme**, as a function of the parameters
$\varepsilon_1$, $\varepsilon_3$ of the single-vector guarantee, the relative accuracy $E$ of the
computed norms and of the scaling, and the deflation threshold $\tau$:
$\mu = 2\varepsilon_1 + 4\varepsilon_3/\tau + 5E$. For two classical passes with pass
coefficient $c_1$, $\varepsilon_1 = 2c_1$ and $\varepsilon_3 = 2(\eta_0 + c_1)^2$, so
$\mu = 4c_1 + 8(\eta_0 + c_1)^2/\tau + 5E$. -/
noncomputable def cgs2ExtendMu (ε₁ ε₃ E τ : ℝ) : ℝ := 2 * ε₁ + 4 * ε₃ / τ + 5 * E

/-- **The residual parameter of the column-wise scheme**, as a function of the parameter
$\varepsilon_2$ of the single-vector guarantee, the relative accuracy $E$ of the computed norms
and of the scaling, and the deflation threshold $\tau$:
$\varepsilon = \varepsilon_2 + 2E + 2\tau$. For two classical passes with pass coefficient $c_1$,
$\varepsilon_2 = 3c_1$. -/
noncomputable def cgs2ExtendEps (ε₂ E τ : ℝ) : ℝ := ε₂ + 2 * E + 2 * τ

/-- The orthogonality parameter $\mu = 2\varepsilon_1 + 4\varepsilon_3/\tau + 5E$ of the
column-wise scheme is nonnegative for $\varepsilon_1, \varepsilon_3, E \ge 0$ and $\tau > 0$. -/
theorem cgs2ExtendMu_nonneg {E τ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₃ : 0 ≤ ε₃) (hE : 0 ≤ E) (hτ : 0 < τ) :
    0 ≤ cgs2ExtendMu ε₁ ε₃ E τ := by
  unfold cgs2ExtendMu
  have h3 : 0 ≤ 4 * ε₃ / τ := div_nonneg (by linarith) hτ.le
  linarith

/-- **The column-wise scheme with threshold deflation meets the rounded contract.** Let
$\mathbf{Q}$ be the basis, $\mathbf{W}$ the block, $\mathbf{W}'$ the reduced block, $\mathbf{Q}'$
the new block and $\mathbf{H}$, $\mathbf{R}$ the coefficients, $\mathbf{R}$ upper triangular.
For every column $c$ assume: the step from $\mathbf{w}_c$ to $\mathbf{w}'_c$ with the
coefficients $(\mathbf{H}_c, \mathbf{R}_{<c,c})$ meets the single-vector guarantee on the support
with parameters $(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ for the basis
$[\mathbf{Q}, \mathbf{Q}'_{<c}]$; a zero $\mathbf{w}_c$ gives a zero $\mathbf{w}'_c$; the computed
norms satisfy $\lvert\nu_c - \|\mathbf{w}_c\|\rvert \le E\|\mathbf{w}_c\|$ and
$\lvert\beta_c - \|\mathbf{w}'_c\|\rvert \le E\|\mathbf{w}'_c\|$; and either the column is
dropped, $\beta_c \le \tfrac32\tau\nu_c$, $\mathbf{q}'_c = \mathbf{0}$, $r_{cc} = 0$, or it is
kept, $\tfrac12\tau\nu_c < \beta_c$, $r_{cc} = \beta_c$,
$\|\beta_c\mathbf{q}'_c - \mathbf{w}'_c\| \le E\|\mathbf{w}'_c\|$. The two thresholds allow for the
rounding of the test. If $\eta_0 \le 1/100$,
$0 \le \varepsilon_1, \varepsilon_2, \varepsilon_3 \le 1/10$, $0 \le E \le 1/100$ and $\tau > 0$,
then $(\mathbf{Q}', \mathbf{H}, \mathbf{R})$ is a rounded extension of $\mathbf{Q}$ by
$\mathbf{W}$ with parameters $\eta_0$,
$\mu = 2\varepsilon_1 + 4\varepsilon_3/\tau + 5E$ and
$\varepsilon = \varepsilon_2 + 2E + 2\tau$. No printed source;
`docs/design/LowRank-BlockLanczos.md` §3.5. -/
theorem isBasisExtensionErr_of_columns {k b : ℕ} {E τ : ℝ} {Q : Matrix (Fin n) (Fin k) ℝ}
    {W W' Q' : Matrix (Fin n) (Fin b) ℝ} {H : Matrix (Fin k) (Fin b) ℝ}
    {R : Matrix (Fin b) (Fin b) ℝ} {ν β : Fin b → ℝ}
    (hη : η₀ ≤ 1 / 100) (hε₁ : 0 ≤ ε₁) (hε₁' : ε₁ ≤ 1 / 10) (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1 / 10)
    (hε₃ : 0 ≤ ε₃) (hε₃' : ε₃ ≤ 1 / 10) (hE : 0 ≤ E) (hE' : E ≤ 1 / 100) (hτ : 0 < τ)
    (hR : R.BlockTriangular id)
    (hO : ∀ c, IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ (Matrix.fromCols Q (colsBefore Q' c)) (W.col c)
      (Sum.elim (H.col c) ((strictUpper R).col c)) (W'.col c))
    (hzero : ∀ c, W.col c = 0 → W'.col c = 0)
    (hν : ∀ c, |ν c - ‖WithLp.toLp 2 (W.col c)‖| ≤ E * ‖WithLp.toLp 2 (W.col c)‖)
    (hβ : ∀ c, |β c - ‖WithLp.toLp 2 (W'.col c)‖| ≤ E * ‖WithLp.toLp 2 (W'.col c)‖)
    (hstep : ∀ c, (β c ≤ 3 / 2 * τ * ν c ∧ Q'.col c = 0 ∧ R c c = 0) ∨
      (τ / 2 * ν c < β c ∧ R c c = β c ∧
        ‖WithLp.toLp 2 (β c • Q'.col c - W'.col c)‖ ≤ E * ‖WithLp.toLp 2 (W'.col c)‖)) :
    IsBasisExtensionErr η₀ (cgs2ExtendMu ε₁ ε₃ E τ) (cgs2ExtendEps ε₂ E τ) Q W Q' H R := by
  -- `upper` is `hR`. `zero_col`: `hν`, `hzero`, `hβ` give `ν c = 0` and `β c = 0`, which excludes
  -- the kept branch of `hstep c`. Assume the window, with `μ := cgs2ExtendMu ε₁ ε₃ E τ ≥ 0`.
  -- (1) By strong induction on `c`, `specNorm (gramDefect (fromCols Q (colsBefore Q' c))) ≤ η₀`:
  -- `frobNorm_gramDefect_fromCols_sq` and the column clause for `c' < c` bound the squared
  -- Frobenius norm by that of `gramDefect Q` plus `3 * c * μ ^ 2`, within the window;
  -- `specNorm_gramDefect_le_frobNorm` concludes.
  -- (2) `column`, kept branch: `IsOrthErrOnSupport.norm_transpose_mulVec_le_of_admissible` at
  -- the threshold `τ / 2` with `δ := β c • Q'.col c - W'.col c` bounds `‖Vᵀ q'_c‖` by
  -- `2 * (ε₁ + 2 * ε₃ / τ + E) ≤ μ`, and `‖Vᵀ q'_c‖ ^ 2` is the left side of the clause;
  -- `(1 - E) / (1 + E) ≤ ‖q'_c‖ ≤ (1 + E) / (1 - E)` gives `|‖q'_c‖ ^ 2 - 1| ≤ 5 * E ≤ μ`.
  -- (3) `residual`: by `frobNorm_sq_eq_sum_col` it suffices that column `c` of the residual,
  -- `w_c - V *ᵥ h_c - R c c • q'_c` (`mul_strictUpper_col`, `hR`), has norm at most `ε * ‖w_c‖`.
  -- Kept: it is `(w_c - V h_c - w'_c) - δ`, at most `(ε₂ + 2 * E) * ‖w_c‖` by
  -- `IsOrthErrOnSupport.norm_le_two_mul`. Dropped: it is `(w_c - V h_c - w'_c) + w'_c` with
  -- `‖w'_c‖ ≤ β c / (1 - E) ≤ 3 / 2 * τ * (1 + E) / (1 - E) * ‖w_c‖ ≤ 2 * τ * ‖w_c‖`.
  sorry

end NLAlib
