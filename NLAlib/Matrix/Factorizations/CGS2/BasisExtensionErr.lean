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

omit [DecidableEq ι] [DecidableEq κ] in
/-- A zero column contributes nothing to `V *ᵥ h`: the product is that of the selected columns
with the selected entries. -/
private theorem submatrix_mulVec_comp_eq {V : Matrix (Fin n) ι ℝ} {e : κ → ι}
    (he : Function.Injective e) (hz : ∀ i, i ∉ Set.range e → V.col i = 0) (h : ι → ℝ) :
    V.submatrix id e *ᵥ (h ∘ e) = V *ᵥ h := by
  funext r
  simp only [Matrix.mulVec, dotProduct]
  refine Fintype.sum_of_injective e he (fun k => V.submatrix id e r k * (h ∘ e) k)
    (fun i => V r i * h i) (fun i hi => ?_) fun k => rfl
  rw [show V r i = 0 from congrFun (hz i hi) r, zero_mul]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A zero column contributes nothing to `‖Vᵀ *ᵥ x‖`: the norm is that of the selected columns. -/
private theorem norm_toLp_submatrix_transpose_mulVec {V : Matrix (Fin n) ι ℝ} {e : κ → ι}
    (he : Function.Injective e) (hz : ∀ i, i ∉ Set.range e → V.col i = 0) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((V.submatrix id e)ᵀ *ᵥ x)‖ = ‖WithLp.toLp 2 (Vᵀ *ᵥ x)‖ := by
  have h : ∑ k, ‖((V.submatrix id e)ᵀ *ᵥ x) k‖ ^ 2 = ∑ i, ‖(Vᵀ *ᵥ x) i‖ ^ 2 := by
    refine Fintype.sum_of_injective e he _ _ (fun i hi => ?_) fun k => rfl
    have h0 : (Vᵀ *ᵥ x) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_eq_zero fun r _ => by
        rw [show V r i = 0 from congrFun (hz i hi) r, zero_mul]
    rw [h0, norm_zero, zero_pow two_ne_zero]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt h

omit [Fintype ι] [DecidableEq ι] in
/-- The nonzero columns of a matrix can be enumerated: there is an injective selection of
nonzero columns outside of which every column is zero. -/
private theorem exists_injective_col_ne_zero [Finite ι] (V : Matrix (Fin n) ι ℝ) :
    ∃ (j : ℕ) (e : Fin j → ι), Function.Injective e ∧ (∀ k, V.col (e k) ≠ 0) ∧
      ∀ i, i ∉ Set.range e → V.col i = 0 := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨_, fun k => ((Fintype.equivFin {i // V.col i ≠ 0}).symm k : ι),
    Subtype.val_injective.comp (Fintype.equivFin _).symm.injective,
    fun k => ((Fintype.equivFin {i // V.col i ≠ 0}).symm k).2, fun i hi => ?_⟩
  by_contra h
  exact hi ⟨Fintype.equivFin {i // V.col i ≠ 0} ⟨i, h⟩, by simp⟩

/-- The guarantee on the support, with its antecedent, gives `IsOrthErr` with its antecedent for
a selection of nonzero columns containing all of them. -/
private theorem IsOrthErrOnSupport.isOrthErr_submatrix {j : ℕ} {V : Matrix (Fin n) ι ℝ}
    {w : Fin n → ℝ} {h : ι → ℝ} {w' : Fin n → ℝ} {e : Fin j → ι}
    (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w') (hV : specNorm (gramDefect V) ≤ η₀)
    (he : Function.Injective e) (hne : ∀ k, V.col (e k) ≠ 0)
    (hz : ∀ i, i ∉ Set.range e → V.col i = 0) :
    IsOrthErr η₀ ε₁ ε₂ ε₃ (V.submatrix id e) w (h ∘ e) w' ∧
      specNorm ((V.submatrix id e)ᵀ * V.submatrix id e - 1) ≤ η₀ := by
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩,
    (specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect V he hne).trans hV⟩
  · rw [submatrix_mulVec_comp_eq he hz]
    exact hO.residual hV
  · rw [norm_toLp_submatrix_transpose_mulVec he hz]
    exact hO.orth hV

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
  have hVe : specNorm (gramDefect V) ≤ η₀ → specNorm (gramDefect (V.submatrix id e)) ≤ η₀ :=
    fun hV => by
      rw [gramDefect_submatrix V he]
      exact (specNorm_submatrix_le _ he he).trans hV
  refine ⟨fun hV => ?_, fun hV => ?_⟩
  · rw [← submatrix_mulVec_comp_eq he hz]
    exact hO.residual (hVe hV)
  · rw [← norm_toLp_submatrix_transpose_mulVec he hz]
    exact hO.orth (hVe hV)

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
  obtain ⟨j, e, hinj, hne, hz⟩ := exists_injective_col_ne_zero V
  obtain ⟨hOe, hVe⟩ := hO.isOrthErr_submatrix hV hinj hne hz
  rw [← norm_toLp_submatrix_transpose_mulVec hinj hz]
  exact hOe.norm_transpose_mulVec_le_of_admissible hVe hη hε₁ hε₃ he0 he1 hτ hν hβ hv hδ hadm

/-- The arithmetic of `IsOrthErrOnSupport.norm_le_two_mul`: with $a = \|\mathbf{w}\|$,
$x = \|\mathbf{w}'\|$, $g = \|\mathbf{V}^{\mathsf{T}}\mathbf{w}'\|$,
$T = \|\mathbf{V}^{\mathsf{T}}\mathbf{w}\|$, $H = \|\mathbf{h}\|$, $R$ the norm of the residual
and $s = \sqrt{1 + \eta_0}$, the bounds of the guarantee give $x \le 2a$. -/
private theorem norm_le_two_mul_arith {s a x g T H R : ℝ} (hη : η₀ ≤ 1 / 100)
    (hε₁' : ε₁ ≤ 1 / 10) (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1 / 10)
    (hε₃' : ε₃ ≤ 1 / 10) (hs1 : s ≤ 201 / 200) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hH0 : 0 ≤ H) (hg : g ≤ ε₁ * x + ε₃ * a) (hT : T ≤ s * a)
    (hH : H ≤ (T + g + s * ε₂ * a) / (1 - η₀)) (hR : R ≤ ε₂ * a)
    (hx2 : x ^ 2 ≤ x * a + g * H + x * R) : x ≤ 2 * a := by
  have hpos : 0 < 1 - η₀ := by linarith
  have hH' : H * (1 - η₀) ≤ T + g + s * ε₂ * a := (le_div_iff₀ hpos).1 hH
  have hsε : s * ε₂ ≤ 201 / 2000 := by nlinarith
  have h1 : s * ε₂ * a ≤ 201 / 2000 * a := mul_le_mul_of_nonneg_right hsε ha
  have h2 : s * a ≤ 201 / 200 * a := mul_le_mul_of_nonneg_right hs1 ha
  have h3 : ε₁ * x ≤ 1 / 10 * x := mul_le_mul_of_nonneg_right hε₁' hx
  have h4 : ε₃ * a ≤ 1 / 10 * a := mul_le_mul_of_nonneg_right hε₃' ha
  have h5 : ε₂ * a ≤ 1 / 10 * a := mul_le_mul_of_nonneg_right hε₂' ha
  have h6 : H * η₀ ≤ H * (1 / 100) := mul_le_mul_of_nonneg_left hη hH0
  have hg' : g ≤ x / 10 + a / 10 := by linarith
  have hHb : H ≤ 5 / 4 * a + 11 / 100 * x := by linarith
  have hgH : g * H ≤ (x / 10 + a / 10) * (5 / 4 * a + 11 / 100 * x) :=
    mul_le_mul hg' hHb hH0 (by linarith)
  have hxR : x * R ≤ x * (1 / 10 * a) := mul_le_mul_of_nonneg_left (by linarith) hx
  by_contra hcon
  rw [not_le] at hcon
  have hxpos : 0 < x := by linarith
  nlinarith [mul_pos hxpos (sub_pos.2 hcon), mul_nonneg ha (sub_pos.2 hcon).le, sq_nonneg a]

/-- The reduced vector is not longer than twice the input. Let $(\mathbf{h}, \mathbf{w}')$
meet the guarantee on the support with parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ for the input $\mathbf{w}$ and the basis
$\mathbf{V}$, whose Gram defect on the support $\mathbf{D}$ satisfies
$\|\mathbf{D}\|_2 \le \eta_0 \le 1/100$, with
$\varepsilon_1, \varepsilon_3 \le 1/10$ and $0 \le \varepsilon_2 \le 1/10$. Then
$\|\mathbf{w}'\| \le 2\|\mathbf{w}\|$. -/
theorem IsOrthErrOnSupport.norm_le_two_mul {V : Matrix (Fin n) ι ℝ} {w : Fin n → ℝ} {h : ι → ℝ}
    {w' : Fin n → ℝ} (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (gramDefect V) ≤ η₀) (hη : η₀ ≤ 1 / 100) (hε₁' : ε₁ ≤ 1 / 10)
    (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1 / 10) (hε₃' : ε₃ ≤ 1 / 10) :
    ‖WithLp.toLp 2 w'‖ ≤ 2 * ‖WithLp.toLp 2 w‖ := by
  obtain ⟨j, e, hinj, hne, hz⟩ := exists_injective_col_ne_zero V
  obtain ⟨hOe, hVe⟩ := hO.isOrthErr_submatrix hV hinj hne hz
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hs1 : Real.sqrt (1 + η₀) ≤ 201 / 200 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hVw : ‖WithLp.toLp 2 ((V.submatrix id e)ᵀ *ᵥ w)‖ ≤
      Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖ :=
    (norm_toLp_mulVec_le _ w).trans (mul_le_mul_of_nonneg_right (by
      rw [specNorm_transpose]
      exact specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hVe) (norm_nonneg _))
  have hid : w' ⬝ᵥ w' = w' ⬝ᵥ w - ((V.submatrix id e)ᵀ *ᵥ w') ⬝ᵥ (h ∘ e) -
      w' ⬝ᵥ (w - V.submatrix id e *ᵥ (h ∘ e) - w') := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    simp only [dotProduct_sub]
    ring
  have h1 := abs_le.1 (EuclideanSpace.abs_dotProduct_le_norm w' w)
  have h2 := abs_le.1 (EuclideanSpace.abs_dotProduct_le_norm ((V.submatrix id e)ᵀ *ᵥ w') (h ∘ e))
  have h3 := abs_le.1 (EuclideanSpace.abs_dotProduct_le_norm w'
    (w - V.submatrix id e *ᵥ (h ∘ e) - w'))
  have hx2 : ‖WithLp.toLp 2 w'‖ ^ 2 ≤ ‖WithLp.toLp 2 w'‖ * ‖WithLp.toLp 2 w‖ +
      ‖WithLp.toLp 2 ((V.submatrix id e)ᵀ *ᵥ w')‖ * ‖WithLp.toLp 2 (h ∘ e)‖ +
      ‖WithLp.toLp 2 w'‖ * ‖WithLp.toLp 2 (w - V.submatrix id e *ᵥ (h ∘ e) - w')‖ := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hid]
    linarith [h1.2, h2.1, h3.1]
  exact norm_le_two_mul_arith hη hε₁' hε₂ hε₂' hε₃' hs1
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hOe.orth hVe) hVw
    (hOe.norm_coef_le hVe (by linarith)) (hOe.residual hVe) hx2

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
  suffices H : specNorm (gramDefect V) ≤ η₀ →
      ‖WithLp.toLp 2 (w - V *ᵥ h - w₂)‖ ≤ 3 * c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (Vᵀ *ᵥ w₂)‖ ≤
        2 * c₁ * ‖WithLp.toLp 2 w₂‖ + 2 * (η₀ + c₁) ^ 2 * ‖WithLp.toLp 2 w‖ from
    ⟨fun hV => (H hV).1, fun hV => (H hV).2⟩
  intro hV
  obtain ⟨j, e, hinj, hne, hz⟩ := exists_injective_col_ne_zero V
  have hVe := (specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect V hinj hne).trans hV
  obtain ⟨e₁, r₁, f₁⟩ := hp₁ hV
  obtain ⟨e₂, r₂, f₂⟩ := hp₂ hV
  have hmv : ∀ x : ι → ℝ, V.submatrix id e *ᵥ (x ∘ e) = V *ᵥ x :=
    submatrix_mulVec_comp_eq hinj hz
  have hVV : ∀ y : Fin n → ℝ,
      V.submatrix id e *ᵥ ((V.submatrix id e)ᵀ *ᵥ y) = V *ᵥ (Vᵀ *ᵥ y) := fun y => hmv (Vᵀ *ᵥ y)
  have hcomp : ∀ (x : ι → ℝ) (y : Fin n → ℝ),
      ‖WithLp.toLp 2 (x ∘ e - (V.submatrix id e)ᵀ *ᵥ y)‖ ≤ ‖WithLp.toLp 2 (x - Vᵀ *ᵥ y)‖ :=
    fun x y => EuclideanSpace.norm_toLp_comp_le_of_injective hinj (x - Vᵀ *ᵥ y)
  have hOe := isOrthErr_of_two_passes (V := V.submatrix id e) (w := w) (w₁ := w₁) (w₂ := w₂)
    (h₁ := h₁ ∘ e) (h₂ := h₂ ∘ e) (h := h ∘ e) hη hc₁ hu hu₁
    (fun _ => ⟨(hcomp h₁ w).trans e₁, by rw [hmv]; exact r₁, by rw [hVV]; exact f₁⟩)
    (fun _ => ⟨(hcomp h₂ w₁).trans e₂, by rw [hmv]; exact r₂, by rw [hVV]; exact f₂⟩)
    fun k => hsum (e k)
  refine ⟨?_, ?_⟩
  · rw [← hmv]
    exact hOe.residual hVe
  · rw [← norm_toLp_submatrix_transpose_mulVec hinj hz]
    exact hOe.orth hVe

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

/-- A vector $\mathbf{q}$ with $\beta\mathbf{q}$ within $Ep$ of a vector of norm $p > 0$, and
$\beta$ within $Ep$ of $p$, has $\lvert\|\mathbf{q}\|^2 - 1\rvert \le 5E$ for $0 \le E \le 1/100$;
here $x = \|\mathbf{q}\|$. -/
private theorem abs_sq_sub_one_le_of_scaled {E β p x : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 100)
    (hp : 0 < p) (hx0 : 0 ≤ x) (hβl : (1 - E) * p ≤ β) (hβu : β ≤ (1 + E) * p)
    (hxl : (1 - E) * p ≤ β * x) (hxu : β * x ≤ (1 + E) * p) : |x ^ 2 - 1| ≤ 5 * E := by
  have hu : (1 - E) * x ≤ 1 + E := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_pos hp (sub_pos.2 h), mul_le_mul_of_nonneg_right hβl hx0]
  have hl : 1 - E ≤ (1 + E) * x := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_pos hp (sub_pos.2 h), mul_le_mul_of_nonneg_right hβu hx0]
  have h1 : ((1 - E) * x) ^ 2 ≤ (1 + E) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hx0) hu 2
  have h2 : (1 - E) ^ 2 ≤ ((1 + E) * x) ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
  rw [mul_pow] at h1 h2
  have hp1 : (1 + E) ^ 2 ≤ (1 - E) ^ 2 * (1 + 5 * E) := by
    nlinarith [mul_nonneg hE0 (by linarith : (0 : ℝ) ≤ 1 - 10 * E),
      mul_nonneg hE0 (sq_nonneg E)]
  have hp2 : (1 + E) ^ 2 * (1 - 5 * E) ≤ (1 - E) ^ 2 := by
    nlinarith [mul_nonneg hE0 (sq_nonneg E), sq_nonneg E]
  have hpos1 : 0 < (1 - E) ^ 2 := pow_pos (by linarith) 2
  have hpos2 : 0 < (1 + E) ^ 2 := pow_pos (by linarith) 2
  refine abs_le.2 ⟨?_, ?_⟩
  · by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul_of_pos_left (by linarith : x ^ 2 < 1 - 5 * E) hpos2]
  · by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul_of_pos_left (by linarith : 1 + 5 * E < x ^ 2) hpos1]

/-- One kept column of the column-wise scheme: with the antecedent of the single-vector
guarantee, the kept normalized column $\mathbf{q}$ has
$\lvert\|\mathbf{q}\|^2 - 1\rvert \le \mu$ and $\|\mathbf{V}^{\mathsf{T}}\mathbf{q}\| \le \mu$,
$\mu = 2\varepsilon_1 + 4\varepsilon_3/\tau + 5E$. -/
private theorem IsOrthErrOnSupport.column_of_kept {E τ ν β : ℝ} {V : Matrix (Fin n) ι ℝ}
    {w : Fin n → ℝ} {h : ι → ℝ} {w' q : Fin n → ℝ}
    (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w') (hV : specNorm (gramDefect V) ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hε₁ : 0 ≤ ε₁) (hε₃ : 0 ≤ ε₃) (hE : 0 ≤ E) (hE' : E ≤ 1 / 100)
    (hτ : 0 < τ) (hν : |ν - ‖WithLp.toLp 2 w‖| ≤ E * ‖WithLp.toLp 2 w‖)
    (hβ : |β - ‖WithLp.toLp 2 w'‖| ≤ E * ‖WithLp.toLp 2 w'‖) (hk : τ / 2 * ν < β)
    (hδ : ‖WithLp.toLp 2 (β • q - w')‖ ≤ E * ‖WithLp.toLp 2 w'‖) :
    |‖WithLp.toLp 2 q‖ ^ 2 - 1| ≤ cgs2ExtendMu ε₁ ε₃ E τ ∧
      ‖WithLp.toLp 2 (Vᵀ *ᵥ q)‖ ≤ cgs2ExtendMu ε₁ ε₃ E τ := by
  have hT : 0 ≤ ε₃ / τ := div_nonneg hε₃ hτ.le
  have hμ : cgs2ExtendMu ε₁ ε₃ E τ = 2 * ε₁ + 4 * (ε₃ / τ) + 5 * E := by
    unfold cgs2ExtendMu
    ring
  have hν' := abs_le.1 hν
  have hβ' := abs_le.1 hβ
  have ha0 := norm_nonneg (WithLp.toLp 2 w)
  have hνE : E * ‖WithLp.toLp 2 w‖ ≤ ‖WithLp.toLp 2 w‖ :=
    mul_le_of_le_one_left ha0 (by linarith)
  have hβpos : 0 < β := lt_of_le_of_lt (mul_nonneg (by linarith) (by linarith)) hk
  have hppos : 0 < ‖WithLp.toLp 2 w'‖ := by
    by_contra h
    have h0 : ‖WithLp.toLp 2 w'‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [h0, mul_zero] at hβ'
    linarith [hβ'.1, hβ'.2]
  have hδ0 : |‖WithLp.toLp 2 (β • q)‖ - ‖WithLp.toLp 2 w'‖| ≤ E * ‖WithLp.toLp 2 w'‖ :=
    (abs_norm_sub_norm_le (WithLp.toLp 2 (β • q)) (WithLp.toLp 2 w')).trans
      (by rwa [← WithLp.toLp_sub])
  have hδ' := abs_le.1 hδ0
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hβpos.le] at hδ'
  refine ⟨?_, ?_⟩
  · have h5 := abs_sq_sub_one_le_of_scaled (β := β) hE hE' hppos
      (norm_nonneg (WithLp.toLp 2 q))
      (by linarith [hβ'.1]) (by linarith [hβ'.2]) (by linarith [hδ'.1]) (by linarith [hδ'.2])
    rw [hμ]
    linarith
  · have h6 := hO.norm_transpose_mulVec_le_of_admissible (v := q) (δ := β • q - w') hV hη hε₁
      hε₃ hE hE' (half_pos hτ) hν hβ (add_sub_cancel _ _).symm hδ hk
    have h7 : ε₃ / (τ / 2) = 2 * (ε₃ / τ) := by
      rw [div_div_eq_mul_div]
      ring
    rw [h7] at h6
    rw [hμ]
    linarith

/-- The residual of one column of the column-wise scheme: with the antecedent of the
single-vector guarantee, a dropped column (`q = 0`, `r = 0`) or a kept one (`r = β`) leaves
`‖w - V *ᵥ h - r • q‖ ≤ (ε₂ + 2 * E + 2 * τ) * ‖w‖`. -/
private theorem IsOrthErrOnSupport.norm_residual_col_le {E τ ν β r : ℝ}
    {V : Matrix (Fin n) ι ℝ} {w : Fin n → ℝ} {h : ι → ℝ} {w' q : Fin n → ℝ}
    (hO : IsOrthErrOnSupport η₀ ε₁ ε₂ ε₃ V w h w') (hV : specNorm (gramDefect V) ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hε₁' : ε₁ ≤ 1 / 10) (hε₂ : 0 ≤ ε₂) (hε₂' : ε₂ ≤ 1 / 10)
    (hε₃' : ε₃ ≤ 1 / 10) (hE : 0 ≤ E) (hE' : E ≤ 1 / 100) (hτ : 0 < τ)
    (hν : |ν - ‖WithLp.toLp 2 w‖| ≤ E * ‖WithLp.toLp 2 w‖)
    (hβ : |β - ‖WithLp.toLp 2 w'‖| ≤ E * ‖WithLp.toLp 2 w'‖)
    (hstep : (β ≤ 3 / 2 * τ * ν ∧ q = 0 ∧ r = 0) ∨
      (τ / 2 * ν < β ∧ r = β ∧ ‖WithLp.toLp 2 (β • q - w')‖ ≤ E * ‖WithLp.toLp 2 w'‖)) :
    ‖WithLp.toLp 2 (w - V *ᵥ h - r • q)‖ ≤ cgs2ExtendEps ε₂ E τ * ‖WithLp.toLp 2 w‖ := by
  unfold cgs2ExtendEps
  have hres := hO.residual hV
  have h2 := hO.norm_le_two_mul hV hη hε₁' hε₂ hε₂' hε₃'
  have ha0 := norm_nonneg (WithLp.toLp 2 w)
  have hp0 := norm_nonneg (WithLp.toLp 2 w')
  have ht0 : 0 ≤ τ * ‖WithLp.toLp 2 w‖ := mul_nonneg hτ.le ha0
  rcases hstep with ⟨hd, hq, hr⟩ | ⟨-, hr, hδ⟩
  · have hid : w - V *ᵥ h - r • q = (w - V *ᵥ h - w') + w' := by
      rw [hq, smul_zero]
      abel
    have hν' := abs_le.1 hν
    have hβ' := abs_le.1 hβ
    have h3 : τ * ν ≤ τ * ((1 + E) * ‖WithLp.toLp 2 w‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hν'.2]) hτ.le
    have h4 : E * (τ * ‖WithLp.toLp 2 w‖) ≤ 1 / 100 * (τ * ‖WithLp.toLp 2 w‖) :=
      mul_le_mul_of_nonneg_right hE' ht0
    have h5 : E * ‖WithLp.toLp 2 w'‖ ≤ 1 / 100 * ‖WithLp.toLp 2 w'‖ :=
      mul_le_mul_of_nonneg_right hE' hp0
    have h6 : ‖WithLp.toLp 2 w'‖ ≤ 2 * (τ * ‖WithLp.toLp 2 w‖) := by linarith [hβ'.1]
    rw [hid, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    nlinarith [mul_nonneg hE ha0]
  · have hid : w - V *ᵥ h - r • q = (w - V *ᵥ h - w') - (β • q - w') := by
      rw [hr]
      abel
    have h3 : E * ‖WithLp.toLp 2 w'‖ ≤ E * (2 * ‖WithLp.toLp 2 w‖) :=
      mul_le_mul_of_nonneg_left h2 hE
    rw [hid, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans ?_
    linarith

/-- The squared norm of `Vᵀ *ᵥ v` for `V = fromCols Q (colsBefore Q' c)`: the part against `Q`
and the inner products with the columns of `Q'` before `c`. -/
private theorem norm_toLp_fromCols_colsBefore_transpose_mulVec_sq {k b : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) (Q' : Matrix (Fin n) (Fin b) ℝ) (c : Fin b)
    (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((Matrix.fromCols Q (colsBefore Q' c))ᵀ *ᵥ v)‖ ^ 2 =
      ‖WithLp.toLp 2 (Qᵀ *ᵥ v)‖ ^ 2 + ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ v) ^ 2 := by
  have hterm : ∀ c', ((colsBefore Q' c)ᵀ *ᵥ v) c' ^ 2 =
      if c' < c then (Q'.col c' ⬝ᵥ v) ^ 2 else 0 := by
    intro c'
    have hrow : ((colsBefore Q' c)ᵀ *ᵥ v) c' = (colsBefore Q' c).col c' ⬝ᵥ v := rfl
    by_cases h : c' < c
    · rw [if_pos h, hrow, col_colsBefore_of_lt Q' h]
    · rw [if_neg h, hrow, col_colsBefore_of_not_lt Q' h, zero_dotProduct, zero_pow two_ne_zero]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec, EuclideanSpace.norm_toLp_sumElim_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq ((colsBefore Q' c)ᵀ *ᵥ v),
    Finset.sum_congr rfl fun c' _ => hterm c', ← Finset.sum_filter]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

/-- Within the window, the basis before column `c` meets the antecedent of the single-vector
guarantee when the earlier columns meet the column clause of the rounded contract. -/
private theorem specNorm_gramDefect_fromCols_colsBefore_le {k b : ℕ} {μ : ℝ}
    {Q : Matrix (Fin n) (Fin k) ℝ} {Q' : Matrix (Fin n) (Fin b) ℝ}
    (hw : ExtensionWindow η₀ μ b Q) (c : Fin b)
    (hcol : ∀ c' < c, Q'.col c' = 0 ∨ (|‖WithLp.toLp 2 (Q'.col c')‖ ^ 2 - 1| ≤ μ ∧
      ‖WithLp.toLp 2 (Qᵀ *ᵥ Q'.col c')‖ ^ 2 +
        ∑ c'' ∈ Finset.Iio c', (Q'.col c'' ⬝ᵥ Q'.col c') ^ 2 ≤ μ ^ 2)) :
    specNorm (gramDefect (Matrix.fromCols Q (colsBefore Q' c))) ≤ η₀ := by
  have hE : IsBasisExtensionErr η₀ μ 0 Q (colsBefore Q' c) (colsBefore Q' c) 0 1 := by
    refine ⟨Matrix.blockTriangular_one, fun _ h => h, fun _ => ?_, fun _ c' => ?_⟩
    · rw [Matrix.mul_zero, sub_zero, Matrix.mul_one, sub_self, frobNorm_zero, zero_mul]
    · by_cases hc : c' < c
      · rw [col_colsBefore_of_lt Q' hc]
        rcases hcol c' hc with h0 | ⟨h1, h2⟩
        · exact Or.inl h0
        · refine Or.inr ⟨h1, ?_⟩
          have hs : ∑ c'' ∈ Finset.Iio c', ((colsBefore Q' c).col c'' ⬝ᵥ Q'.col c') ^ 2 =
              ∑ c'' ∈ Finset.Iio c', (Q'.col c'' ⬝ᵥ Q'.col c') ^ 2 :=
            Finset.sum_congr rfl fun c'' h'' => by
              rw [col_colsBefore_of_lt Q' ((Finset.mem_Iio.1 h'').trans hc)]
          rw [hs]
          exact h2
      · exact Or.inl (col_colsBefore_of_not_lt Q' hc)
  have h2 := Real.sqrt_le_sqrt (hE.frobNorm_gramDefect_fromCols_sq_le hw)
  rw [Real.sqrt_sq (frobNorm_nonneg _)] at h2
  exact (specNorm_gramDefect_le_frobNorm _).trans (h2.trans
    (show Real.sqrt (frobNorm (gramDefect Q) ^ 2 + 3 * b * μ ^ 2) ≤ η₀ from hw))

/-- A matrix whose columns are bounded by `ε` times those of another has Frobenius norm at most
`ε` times the other's. -/
private theorem frobNorm_le_mul_of_col_le {b : ℕ} {ε : ℝ} {A B : Matrix (Fin n) (Fin b) ℝ}
    (hε : 0 ≤ ε)
    (h : ∀ c, ‖WithLp.toLp 2 (A.col c)‖ ≤ ε * ‖WithLp.toLp 2 (B.col c)‖) :
    frobNorm A ≤ ε * frobNorm B := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (mul_nonneg hε (frobNorm_nonneg _))).1 ?_
  rw [mul_pow, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h c) 2

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
`docs/design/LowRank-BlockLanczos.md` §3.5.
Result: cgs2-basis-extension-error -/
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
  have hεn : 0 ≤ cgs2ExtendEps ε₂ E τ := by
    unfold cgs2ExtendEps
    linarith
  have hcolP : ExtensionWindow η₀ (cgs2ExtendMu ε₁ ε₃ E τ) b Q → ∀ c, Q'.col c = 0 ∨
      (|‖WithLp.toLp 2 (Q'.col c)‖ ^ 2 - 1| ≤ cgs2ExtendMu ε₁ ε₃ E τ ∧
        ‖WithLp.toLp 2 (Qᵀ *ᵥ Q'.col c)‖ ^ 2 +
          ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 ≤ cgs2ExtendMu ε₁ ε₃ E τ ^ 2) := by
    intro hw
    have key : ∀ (N : ℕ) (c : Fin b), (c : ℕ) = N → (Q'.col c = 0 ∨
        (|‖WithLp.toLp 2 (Q'.col c)‖ ^ 2 - 1| ≤ cgs2ExtendMu ε₁ ε₃ E τ ∧
          ‖WithLp.toLp 2 (Qᵀ *ᵥ Q'.col c)‖ ^ 2 +
            ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 ≤
              cgs2ExtendMu ε₁ ε₃ E τ ^ 2)) := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro c hc
        have hVc := specNorm_gramDefect_fromCols_colsBefore_le hw c fun c' h =>
          ih c' (by rw [← hc]; exact Fin.lt_def.1 h) c' rfl
        rcases hstep c with ⟨-, h0, -⟩ | ⟨hk, -, hδ⟩
        · exact Or.inl h0
        · obtain ⟨h1, h2⟩ :=
            (hO c).column_of_kept hVc hη hε₁ hε₃ hE hE' hτ (hν c) (hβ c) hk hδ
          refine Or.inr ⟨h1, ?_⟩
          rw [← norm_toLp_fromCols_colsBefore_transpose_mulVec_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    exact fun c => key c c rfl
  refine ⟨hR, fun c hc => ?_, fun hw => ?_, hcolP⟩
  · have hν0 : ν c = 0 := by
      have h := hν c
      rw [hc, WithLp.toLp_zero, norm_zero, mul_zero, sub_zero] at h
      exact abs_nonpos_iff.1 h
    have hβ0 : β c = 0 := by
      have h := hβ c
      rw [hzero c hc, WithLp.toLp_zero, norm_zero, mul_zero, sub_zero] at h
      exact abs_nonpos_iff.1 h
    rcases hstep c with ⟨-, h0, -⟩ | ⟨hk, -, -⟩
    · exact h0
    · rw [hν0, hβ0, mul_zero] at hk
      exact absurd hk (lt_irrefl _)
  · refine frobNorm_le_mul_of_col_le hεn fun c => ?_
    have hVc := specNorm_gramDefect_fromCols_colsBefore_le hw c fun c' _ => hcolP hw c'
    have hcol : (W - Q * H - Q' * R).col c = W.col c - Matrix.fromCols Q (colsBefore Q' c) *ᵥ
        Sum.elim (H.col c) ((strictUpper R).col c) - R c c • Q'.col c := by
      have h1 : (W - Q * H - Q' * R).col c = W.col c - Q *ᵥ H.col c - (Q' * R).col c := rfl
      rw [h1, mul_col_eq_of_blockTriangular Q' hR, Matrix.fromCols_mulVec_sumElim]
      abel
    rw [hcol]
    exact (hO c).norm_residual_col_le hVc hη hε₁' hε₂ hε₂' hε₃' hE hE' hτ (hν c) (hβ c)
      (hstep c)

end NLAlib
