/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Compare

/-!
# The decoded guarantee of an orthogonalization step

One step of an orthogonalization scheme reduces a vector $\mathbf{w}$ against the $j$ columns of
a computed, nearly orthonormal basis $\mathbf{V}$, writing coefficients $\mathbf{h}$ and the
reduced vector $\mathbf{w}'$. `NLAlib.IsOrthErr` is the guarantee a scheme provides on decoded
values: given $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$,
$$\|\mathbf{w} - \mathbf{V}\mathbf{h} - \mathbf{w}'\| \le \varepsilon_2\|\mathbf{w}\|, \qquad
\|\mathbf{V}^{\mathsf{T}}\mathbf{w}'\| \le
\varepsilon_1\|\mathbf{w}'\| + \varepsilon_3\|\mathbf{w}\|.$$
The term $\varepsilon_3$ is first order in $\eta_0$ for one classical Gram–Schmidt pass and second
order for two ("twice is enough"). Design: `docs/design/Krylov-LanczosReorth.md` §1.1.

## Main definitions

* `NLAlib.IsOrthErr`: the decoded guarantee of one orthogonalization step.

## Main results

* `NLAlib.IsOrthErr.mono`: monotonicity in the four parameters.
* `NLAlib.IsOrthErr.norm_coef_le`: the coefficients are small for a nearly orthogonal input.
* `NLAlib.IsOrthErr.norm_transpose_mulVec_smul_le`: orthogonality of the normalized output.
* `NLAlib.IsOrthErr.norm_transpose_mulVec_le_of_admissible`: an admissible normalized column is
  nearly orthogonal to the basis, with an absolute bound.
* `NLAlib.specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le`,
  `NLAlib.frobNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le`: norms of a nearly
  orthonormal basis.
* `NLAlib.frobNorm_transpose_mul_self_sub_one_sq`,
  `NLAlib.frobNorm_transpose_mul_self_sub_one_le_of_columns`: the loss of orthogonality column by
  column.
* `NLAlib.injective_mulVec_of_specNorm_transpose_mul_self_sub_one_lt_one`,
  `NLAlib.le_of_specNorm_transpose_mul_self_sub_one_lt_one`: a nearly orthonormal basis has
  independent columns.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The decoded guarantee of one orthogonalization step** against a nearly orthonormal basis:
if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$, the coefficients
$\mathbf{h}$ and the reduced vector $\mathbf{w}'$ represent $\mathbf{w}$ up to
$\varepsilon_2\|\mathbf{w}\|$, and $\mathbf{w}'$ is orthogonal to the basis up to
$\varepsilon_1\|\mathbf{w}'\| + \varepsilon_3\|\mathbf{w}\|$. No admissibility condition on
$\mathbf{w}$; [GiraudLangouRozloznikVandenEshof2005, Theorems 1–2] for classical Gram–Schmidt with
one and two passes in this sense. -/
structure IsOrthErr {n j : ℕ} (η₀ ε₁ ε₂ ε₃ : ℝ) (V : Matrix (Fin n) (Fin j) ℝ)
    (w : Fin n → ℝ) (h : Fin j → ℝ) (w' : Fin n → ℝ) : Prop where
  /-- The representation of the input. -/
  residual : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (w - V *ᵥ h - w')‖ ≤ ε₂ * ‖WithLp.toLp 2 w‖
  /-- The local loss of orthogonality. -/
  orth : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ ≤ ε₁ * ‖WithLp.toLp 2 w'‖ + ε₃ * ‖WithLp.toLp 2 w‖

variable {n j : ℕ}

/-- A nearly orthonormal basis has spectral norm close to one: if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta$ then
$\|\mathbf{V}\|_2 \le \sqrt{1 + \eta}$. -/
theorem specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le
    {V : Matrix (Fin n) (Fin j) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) : specNorm V ≤ Real.sqrt (1 + η) := by
  have h1 : specNorm (Vᵀ * V) ≤ 1 + η := by
    calc specNorm (Vᵀ * V) = specNorm ((Vᵀ * V - 1) + 1) := by rw [sub_add_cancel]
      _ ≤ specNorm (Vᵀ * V - 1) + specNorm 1 := specNorm_add_le _ _
      _ ≤ η + 1 := add_le_add hV specNorm_one_le
      _ = 1 + η := add_comm _ _
  have h2 : specNorm V ^ 2 = specNorm (Vᵀ * V) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, specNorm_conjTranspose_mul_self]
  exact (Real.le_sqrt (specNorm_nonneg V) ((specNorm_nonneg _).trans h1)).2
    (by rw [← h2] at h1; exact h1)

/-- The Frobenius norm of a nearly orthonormal basis: if the $j$ columns of $\mathbf{V}$
satisfy $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta$ then
$\|\mathbf{V}\|_{\mathsf{F}} \le \sqrt{j(1 + \eta)}$. -/
theorem frobNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le
    {V : Matrix (Fin n) (Fin j) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) : frobNorm V ≤ Real.sqrt (j * (1 + η)) := by
  have hdiag : ∀ i, (Vᵀ * V) i i ≤ 1 + η := fun i => by
    have h := norm_apply_le_specNorm (Vᵀ * V - 1) i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Real.norm_eq_abs] at h
    linarith [le_abs_self ((Vᵀ * V) i i - 1)]
  have htr : (Vᵀ * V).trace ≤ j * (1 + η) := by
    rw [Matrix.trace]
    calc ∑ i, (Vᵀ * V) i i ≤ ∑ _i : Fin j, (1 + η) := Finset.sum_le_sum fun i _ => hdiag i
      _ = j * (1 + η) := by simp; ring
  have h2 : frobNorm V ^ 2 ≤ j * (1 + η) := by
    rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real]
    exact htr
  exact (Real.le_sqrt (frobNorm_nonneg V) (le_trans (sq_nonneg _) h2)).2 h2

/-- `NLAlib.IsOrthErr` is monotone: it survives a smaller precondition $\eta_0' \le \eta_0$ and
larger parameters $\varepsilon_i \le \varepsilon_i'$. -/
theorem IsOrthErr.mono {η₀ ε₁ ε₂ ε₃ η₀' ε₁' ε₂' ε₃' : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hη : η₀' ≤ η₀) (h₁ : ε₁ ≤ ε₁') (h₂ : ε₂ ≤ ε₂') (h₃ : ε₃ ≤ ε₃') :
    IsOrthErr η₀' ε₁' ε₂' ε₃' V w h w' := by
  refine ⟨fun hV => ?_, fun hV => ?_⟩
  · exact (hO.residual (hV.trans hη)).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
  · exact (hO.orth (hV.trans hη)).trans (by gcongr)

/-- The coefficients of an orthogonalization step are small when the input is nearly orthogonal
to the basis: if $(\mathbf{h}, \mathbf{w}')$ meets `NLAlib.IsOrthErr` for $\mathbf{w}$ and
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0 < 1$, then
$$\|\mathbf{h}\| \le \frac{\|\mathbf{V}^{\mathsf{T}}\mathbf{w}\| + \|\mathbf{V}^{\mathsf{T}}
\mathbf{w}'\| + \sqrt{1 + \eta_0}\,\varepsilon_2\|\mathbf{w}\|}{1 - \eta_0}.$$
No printed source; `docs/design/Krylov-LanczosReorth.md` §1.1. -/
theorem IsOrthErr.norm_coef_le {η₀ ε₁ ε₂ ε₃ : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hη : η₀ < 1) :
    ‖WithLp.toLp 2 h‖ ≤ (‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ + ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ +
      Real.sqrt (1 + η₀) * ε₂ * ‖WithLp.toLp 2 w‖) / (1 - η₀) := by
  have hpos : 0 < 1 - η₀ := by linarith
  have hsq := specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hid : h = Vᵀ *ᵥ w - Vᵀ *ᵥ w' - Vᵀ *ᵥ (w - V *ᵥ h - w') - (Vᵀ * V - 1) *ᵥ h := by
    simp only [Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hn : ‖WithLp.toLp 2 h‖ ≤ ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ + ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ +
      ‖WithLp.toLp 2 (Vᵀ *ᵥ (w - V *ᵥ h - w'))‖ + ‖WithLp.toLp 2 ((Vᵀ * V - 1) *ᵥ h)‖ := by
    calc ‖WithLp.toLp 2 h‖
        = ‖WithLp.toLp 2 (Vᵀ *ᵥ w - Vᵀ *ᵥ w' - Vᵀ *ᵥ (w - V *ᵥ h - w') - (Vᵀ * V - 1) *ᵥ h)‖ := by
          rw [← hid]
      _ ≤ _ := by
          simp only [WithLp.toLp_sub]
          linarith [norm_sub_le (WithLp.toLp 2 (Vᵀ *ᵥ w) - WithLp.toLp 2 (Vᵀ *ᵥ w') -
              WithLp.toLp 2 (Vᵀ *ᵥ (w - V *ᵥ h - w'))) (WithLp.toLp 2 ((Vᵀ * V - 1) *ᵥ h)),
            norm_sub_le (WithLp.toLp 2 (Vᵀ *ᵥ w) - WithLp.toLp 2 (Vᵀ *ᵥ w'))
              (WithLp.toLp 2 (Vᵀ *ᵥ (w - V *ᵥ h - w'))),
            norm_sub_le (WithLp.toLp 2 (Vᵀ *ᵥ w)) (WithLp.toLp 2 (Vᵀ *ᵥ w'))]
  have hG : ‖WithLp.toLp 2 ((Vᵀ * V - 1) *ᵥ h)‖ ≤ η₀ * ‖WithLp.toLp 2 h‖ :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
  have hF : ‖WithLp.toLp 2 (Vᵀ *ᵥ (w - V *ᵥ h - w'))‖ ≤
      Real.sqrt (1 + η₀) * (ε₂ * ‖WithLp.toLp 2 w‖) :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul (by rw [specNorm_transpose]; exact hsq)
      (hO.residual hV) (norm_nonneg _) (Real.sqrt_nonneg _))
  rw [le_div_iff₀ hpos]
  nlinarith [hn, hG, hF]

/-- The orthogonality of the normalized output: if $(\mathbf{h}, \mathbf{w}')$ meets
`NLAlib.IsOrthErr` for $\mathbf{w}$, $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2
\le \eta_0$ and $\mathbf{w}' \ne \mathbf{0}$, then
$\|\mathbf{V}^{\mathsf{T}}(\mathbf{w}'/\|\mathbf{w}'\|)\| \le \varepsilon_1 + \varepsilon_3
\|\mathbf{w}\|/\|\mathbf{w}'\|$. The ratio $\|\mathbf{w}\|/\|\mathbf{w}'\|$ is what
admissibility controls. -/
theorem IsOrthErr.norm_transpose_mulVec_smul_le {η₀ ε₁ ε₂ ε₃ : ℝ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w : Fin n → ℝ} {h : Fin j → ℝ} {w' : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hw' : w' ≠ 0) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ (‖WithLp.toLp 2 w'‖⁻¹ • w'))‖ ≤
      ε₁ + ε₃ * ‖WithLp.toLp 2 w‖ / ‖WithLp.toLp 2 w'‖ := by
  have hne : WithLp.toLp 2 w' ≠ 0 := by
    intro h
    apply hw'
    simpa using congrArg WithLp.ofLp h
  have hpos : 0 < ‖WithLp.toLp 2 w'‖ := norm_pos_iff.2 hne
  have hsmul : WithLp.toLp 2 (Vᵀ *ᵥ (‖WithLp.toLp 2 w'‖⁻¹ • w')) =
      ‖WithLp.toLp 2 w'‖⁻¹ • WithLp.toLp 2 (Vᵀ *ᵥ w') := by
    rw [Matrix.mulVec_smul]
    simp
  rw [hsmul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  calc ‖WithLp.toLp 2 w'‖⁻¹ * ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖
      ≤ ‖WithLp.toLp 2 w'‖⁻¹ * (ε₁ * ‖WithLp.toLp 2 w'‖ + ε₃ * ‖WithLp.toLp 2 w‖) :=
        mul_le_mul_of_nonneg_left (hO.orth hV) (inv_nonneg.2 hpos.le)
    _ = ε₁ + ε₃ * ‖WithLp.toLp 2 w‖ / ‖WithLp.toLp 2 w'‖ := by
        field_simp

/-- The loss of orthogonality when a column is appended: for
$\mathbf{V} = [\mathbf{V}', \mathbf{x}]$,
$$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}^2 =
\|\mathbf{V}'^{\mathsf{T}}\mathbf{V}' - \mathbf{I}\|_{\mathsf F}^2 +
2\|\mathbf{V}'^{\mathsf{T}}\mathbf{x}\|^2 + (\|\mathbf{x}\|^2 - 1)^2.$$ -/
theorem frobNorm_transpose_mul_self_sub_one_sq {m : ℕ} (V : Matrix (Fin n) (Fin (m + 1)) ℝ) :
    frobNorm (Vᵀ * V - 1) ^ 2 =
      frobNorm ((V.submatrix id Fin.castSucc)ᵀ * V.submatrix id Fin.castSucc - 1) ^ 2 +
      2 * ‖WithLp.toLp 2 ((V.submatrix id Fin.castSucc)ᵀ *ᵥ fun i => V i (Fin.last m))‖ ^ 2 +
      (‖WithLp.toLp 2 (fun i => V i (Fin.last m))‖ ^ 2 - 1) ^ 2 := by
  have hne : ∀ i : Fin m, Fin.castSucc i ≠ Fin.last m := fun i => (Fin.castSucc_lt_last i).ne
  have hc : ∀ i : Fin m, ∑ j, V j (Fin.last m) * V j i.castSucc =
      ∑ j, V j i.castSucc * V j (Fin.last m) :=
    fun i => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Matrix.sub_apply,
    Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Real.norm_eq_abs, sq_abs, Matrix.mulVec, dotProduct, id, Fin.castSucc_inj, hne,
    (hne _).symm, ↓reduceIte, sub_zero, hc, Finset.sum_add_distrib,
    Finset.mul_sum, ← sq]
  simp only [two_mul, Finset.sum_add_distrib]
  ring

/-- Column-wise orthogonality accumulates as $\sqrt{3m}$: if, for $c < m$, the vector
$\mathbf{v}_{c+1}$ of a sequence satisfies $\|\mathbf{V}_c^{\mathsf{T}}\mathbf{v}_{c+1}\| \le
\mu$ and $\lvert\|\mathbf{v}_{c+1}\|^2 - 1\rvert \le \mu$, where $\mathbf{V}_c =
[\mathbf{v}_1, \dots, \mathbf{v}_c]$, and $\mu \ge 0$, then
$\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$.
`docs/design/Krylov-LanczosReorth.md` §1.2. -/
theorem frobNorm_transpose_mul_self_sub_one_le_of_columns (v : ℕ → Fin n → ℝ) (m : ℕ) {μ : ℝ}
    (hμ : 0 ≤ μ) (hg : ∀ c < m, ‖WithLp.toLp 2
      ((Matrix.of fun i (d : Fin c) => v ((d : ℕ) + 1) i)ᵀ *ᵥ v (c + 1))‖ ≤ μ)
    (hd : ∀ c < m, |‖WithLp.toLp 2 (v (c + 1))‖ ^ 2 - 1| ≤ μ) :
    frobNorm ((Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i)ᵀ *
      (Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i) - 1) ≤ Real.sqrt (3 * m) * μ := by
  have key : ∀ k, k ≤ m → frobNorm ((Matrix.of fun i (d : Fin k) => v ((d : ℕ) + 1) i)ᵀ *
      (Matrix.of fun i (d : Fin k) => v ((d : ℕ) + 1) i) - 1) ^ 2 ≤ 3 * k * μ ^ 2 := by
    intro k
    induction k with
    | zero => intro _; rw [frobNorm_sq_eq_sum]; simp
    | succ k ih =>
      intro hk
      have hsub : (Matrix.of fun i (d : Fin (k + 1)) => v ((d : ℕ) + 1) i).submatrix id
          Fin.castSucc = Matrix.of fun i (d : Fin k) => v ((d : ℕ) + 1) i := by
        ext i d; simp
      have hcol := frobNorm_transpose_mul_self_sub_one_sq
        (Matrix.of fun i (d : Fin (k + 1)) => v ((d : ℕ) + 1) i)
      simp only [hsub, Matrix.of_apply, Fin.val_last] at hcol
      have hA := pow_le_pow_left₀ (norm_nonneg _) (hg k (by omega)) 2
      have hB := pow_le_pow_left₀ (abs_nonneg _) (hd k (by omega)) 2
      rw [sq_abs] at hB
      rw [hcol]
      push_cast
      linarith [ih (by omega)]
  have hfin := key m le_rfl
  have hb2 : (Real.sqrt (3 * m) * μ) ^ 2 = 3 * m * μ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hb0 : 0 ≤ Real.sqrt (3 * m) * μ := by positivity
  nlinarith [frobNorm_nonneg ((Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i)ᵀ *
    (Matrix.of fun i (d : Fin m) => v ((d : ℕ) + 1) i) - 1)]

/-- A nearly orthonormal basis has independent columns: if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 < 1$ then $\mathbf{x} \mapsto
\mathbf{V}\mathbf{x}$ is injective. -/
theorem injective_mulVec_of_specNorm_transpose_mul_self_sub_one_lt_one
    {V : Matrix (Fin n) (Fin j) ℝ} (hV : specNorm (Vᵀ * V - 1) < 1) :
    Function.Injective V.mulVec := by
  have key : ∀ z, V *ᵥ z = 0 → z = 0 := by
    intro z hz
    have hG : (Vᵀ * V - 1) *ᵥ z = -z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
        zero_sub]
    have hle : ‖WithLp.toLp 2 z‖ ≤ specNorm (Vᵀ * V - 1) * ‖WithLp.toLp 2 z‖ := by
      have := norm_toLp_mulVec_le (Vᵀ * V - 1) z
      rwa [hG, WithLp.toLp_neg, norm_neg] at this
    have hz0 : ‖WithLp.toLp 2 z‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (WithLp.toLp 2 z), specNorm_nonneg (Vᵀ * V - 1)])
        (norm_nonneg _)
    have : WithLp.toLp 2 z = 0 := norm_eq_zero.1 hz0
    simpa using congrArg WithLp.ofLp this
  intro x y hxy
  have h0 : x - y = 0 := key _ (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 h0

/-- A nearly orthonormal basis has at most as many columns as rows: if the $n \times j$ matrix
$\mathbf{V}$ satisfies $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 < 1$ then
$j \le n$. -/
theorem le_of_specNorm_transpose_mul_self_sub_one_lt_one {V : Matrix (Fin n) (Fin j) ℝ}
    (hV : specNorm (Vᵀ * V - 1) < 1) : j ≤ n := by
  have hinj : Function.Injective (Matrix.mulVecLin V) :=
    injective_mulVec_of_specNorm_transpose_mul_self_sub_one_lt_one hV
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-! ### One admissible column -/

/-- One admissible normalized column is nearly orthogonal to the basis, with an absolute bound.
Let $(\mathbf{h}, \mathbf{w}')$ meet `NLAlib.IsOrthErr` with parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$ for the input $\mathbf{w}$ and the basis
$\mathbf{V}$, with $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$
and $\varepsilon_1, \varepsilon_3 \ge 0$. Let $\nu$ and $\beta$ be computed norms,
$\lvert\nu - \|\mathbf{w}\|\rvert \le E\|\mathbf{w}\|$ and
$\lvert\beta - \|\mathbf{w}'\|\rvert \le E\|\mathbf{w}'\|$ with $0 \le E \le 1/100$, let
$\mathbf{v}$ be the computed normalized vector, $\beta\mathbf{v} = \mathbf{w}' +
\boldsymbol\delta$ with $\|\boldsymbol\delta\| \le E\|\mathbf{w}'\|$, and let the step be
admissible for a threshold $\tau > 0$: $\tau\nu < \beta$. Then
$$\|\mathbf{V}^{\mathsf{T}}\mathbf{v}\| \le 2(\varepsilon_1 + \varepsilon_3/\tau + E).$$ -/
theorem IsOrthErr.norm_transpose_mulVec_le_of_admissible {n k : ℕ}
    {η₀ ε₁ ε₂ ε₃ E τ ν β : ℝ} {V : Matrix (Fin n) (Fin k) ℝ} {w : Fin n → ℝ} {h : Fin k → ℝ}
    {w' v δ : Fin n → ℝ} (hO : IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w')
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hη : η₀ ≤ 1 / 100) (hε₁ : 0 ≤ ε₁) (hε₃ : 0 ≤ ε₃)
    (he0 : 0 ≤ E) (he1 : E ≤ 1 / 100) (hτ : 0 < τ)
    (hν : |ν - ‖WithLp.toLp 2 w‖| ≤ E * ‖WithLp.toLp 2 w‖)
    (hβ : |β - ‖WithLp.toLp 2 w'‖| ≤ E * ‖WithLp.toLp 2 w'‖)
    (hv : β • v = w' + δ) (hδ : ‖WithLp.toLp 2 δ‖ ≤ E * ‖WithLp.toLp 2 w'‖)
    (hadm : τ * ν < β) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ v)‖ ≤ 2 * (ε₁ + ε₃ / τ + E) := by
  have hord := hO.orth hV
  have hs : Real.sqrt (1 + η₀) ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hsq : specNorm Vᵀ ≤ Real.sqrt (1 + η₀) := by
    rw [specNorm_transpose]
    exact specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hδ' := (norm_toLp_mulVec_le Vᵀ δ).trans
    (mul_le_mul hsq hδ (norm_nonneg _) (Real.sqrt_nonneg _))
  have hvec : β • (Vᵀ *ᵥ v) = Vᵀ *ᵥ w' + Vᵀ *ᵥ δ := by
    rw [← Matrix.mulVec_add, ← hv, Matrix.mulVec_smul]
  have hν' := abs_le.mp hν
  have hβ' := abs_le.mp hβ
  have hq0 := norm_nonneg (WithLp.toLp 2 w)
  have hp0 := norm_nonneg (WithLp.toLp 2 w')
  set a := ‖WithLp.toLp 2 (Vᵀ *ᵥ v)‖ with ha
  set p := ‖WithLp.toLp 2 w'‖ with hp
  set q := ‖WithLp.toLp 2 w‖ with hq
  set s := Real.sqrt (1 + η₀) with hsdef
  set T := ε₃ / τ with hT
  have hτν : τ * ((1 - E) * q) ≤ τ * ν := mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have hτq : 0 ≤ τ * ((1 - E) * q) := mul_nonneg hτ.le (mul_nonneg (by linarith) hq0)
  have hβpos : 0 < β := by linarith
  have hnorm : β * a = ‖WithLp.toLp 2 (β • (Vᵀ *ᵥ v))‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hβpos.le]
  have hb : β * a ≤ ε₁ * p + ε₃ * q + s * (E * p) := by
    rw [hnorm, hvec, WithLp.toLp_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hF2 : τ * ((1 - E) * q) ≤ (1 + E) * p := by linarith
  have hT0 : 0 ≤ T := div_nonneg hε₃ hτ.le
  have hq2 : ε₃ * q * (1 - E) ≤ T * (1 + E) * p := by
    have h := mul_le_mul_of_nonneg_left hF2 hT0
    calc ε₃ * q * (1 - E) = T * (τ * ((1 - E) * q)) := by
          rw [hT]; field_simp
      _ ≤ T * ((1 + E) * p) := h
      _ = T * (1 + E) * p := by ring
  have hβlow : (1 - E) * p ≤ β := by linarith [hβ'.1]
  have h1 : a * β * (1 - E) ≤ ((1 - E) * (ε₁ + s * E) + T * (1 + E)) * p := by
    nlinarith [mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ 1 - E)]
  have hpoly : (1 - E) * (ε₁ + s * E) + T * (1 + E) ≤ 2 * (ε₁ + T + E) * (1 - E) ^ 2 := by
    have c1 : 0 ≤ ε₁ * (1 - E) * (1 - 2 * E) :=
      mul_nonneg (mul_nonneg hε₁ (by linarith)) (by linarith)
    have c2 : 0 ≤ T * (1 - 5 * E + 2 * E ^ 2) := mul_nonneg hT0 (by nlinarith)
    have c3 : 0 ≤ E * (1 - E) * (2 * (1 - E) - s) :=
      mul_nonneg (mul_nonneg he0 (by linarith)) (by linarith)
    nlinarith [c1, c2, c3]
  have h2 : ((1 - E) * (ε₁ + s * E) + T * (1 + E)) * p ≤ 2 * (ε₁ + T + E) * (1 - E) * β := by
    have hK : 0 ≤ 2 * (ε₁ + T + E) * (1 - E) := by
      have : 0 ≤ ε₁ + T + E := by linarith
      have : 0 ≤ 1 - E := by linarith
      positivity
    linarith [mul_le_mul_of_nonneg_right hpoly hp0, mul_le_mul_of_nonneg_left hβlow hK]
  have hpos : 0 < β * (1 - E) := mul_pos hβpos (by linarith)
  by_contra! hcon
  linarith [mul_lt_mul_of_pos_right hcon hpos]

end NLAlib
