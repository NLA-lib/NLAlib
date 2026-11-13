/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Chebyshev.EvenFilter
public import NLAlib.Polynomial.Chebyshev.Residual

/-!
# Ritz values

Bounds on the largest Ritz value $\theta_0 = \lambda_0(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$
of a Krylov space $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (that is, $q$ multiplications by
$\mathbf{A}$), $\mathbf{Q}$ any orthonormal basis of it, below the largest eigenvalue
$\lambda_0 = \lambda_0(\mathbf{A})$. The lower bound $\theta_0 \le \lambda_0$ is Poincaré
separation (`Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le`). The start enters only
through the squared tangent of its angle with the top eigenspace $E_{\lambda_0}$, read off the
spectral measure, $\tan^2\angle(\mathbf{b}, E_{\lambda_0}) =
\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ (`NLAlib.spectralTangentSq`); a repeated top
eigenvalue needs no extra work.

Three bounds: the gapped Kaniel–Paige–Saad bound, from the filter theorem
`Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le` with a reflected Chebyshev residual;
the gap-free bound $\varepsilon\lambda_0 + 4e^{-4q\sqrt{\varepsilon}}\lambda_0\tan^2$ for positive
semidefinite $\mathbf{A}$; and Kuczyński and Woźniakowski's gap-free squared-logarithmic bound,
from the even Chebyshev filter. The last two are incomparable: the first is better for a fixed
accuracy with a good start, the second needs no $\varepsilon$ and degrades only logarithmically
with a poor start, which is the random-start regime.

## Main results

* `Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le`: Kaniel–Paige–Saad.
* `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add`: the gap-free
  bound.
* `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`: the
  Kuczyński–Woźniakowski bound.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-! ### Private steps -/

/-- A polynomial that does not vanish at an atom does not annihilate $\mathbf{b}$. -/
private theorem aeval_mulVec_ne_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℝ[X]}
    {c : ℝ} (hpc : p.eval c ≠ 0) {b : n → 𝕜} (hb : 0 < (spectralMeasure A b).real {c}) :
    aeval A p *ᵥ b ≠ 0 := by
  intro h0
  have hn := hA.norm_toLp_cfc_mulVec_sq (fun x => p.eval x) b
  rw [hA.cfc_eq_aeval_of_forall_eval_eq (f := fun x => p.eval x) fun _ _ => rfl, h0,
    WithLp.toLp_zero, norm_zero, ← integral_spectralMeasure] at hn
  have h := mul_spectralMeasure_real_le_integral_sq A b (fun x => p.eval x) c
  have hpos : 0 < p.eval c ^ 2 * (spectralMeasure A b).real {c} := by positivity
  rw [← hn] at h
  linarith

/-- **The largest Ritz value dominates the Rayleigh quotients of the Krylov space**: for a frame
$\mathbf{Q}$ of $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ and $\deg p \le q$ with
$p(\mathbf{A})\mathbf{b} \ne \mathbf{0}$, $\rho_{\mathbf{A}}(p(\mathbf{A})\mathbf{b}) \le
\lambda_0(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$. -/
private theorem rayleighQuotient_aeval_mulVec_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {b : n → 𝕜} {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) {p : ℝ[X]}
    (hp : p.degree ≤ q) (hne : aeval A p *ᵥ b ≠ 0) :
    rayleighQuotient A (aeval A p *ᵥ b) ≤ eigenvalue (Qᴴ * A * Q) 0 := by
  have hp' : p.degree < ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast q.lt_succ_self)
  obtain ⟨y, hy⟩ : aeval A p *ᵥ b ∈ LinearMap.range Q.mulVecLin :=
    hK ▸ aeval_mulVec_mem_krylovSpace A b hp'
  rw [Matrix.mulVecLin_apply] at hy
  have hy0 : WithLp.toLp 2 y ≠ 0 := by
    intro h
    have : y = 0 := by simpa using congrArg WithLp.ofLp h
    rw [this, Matrix.mulVec_zero] at hy
    exact hne hy.symm
  have hpos : 0 < ‖WithLp.toLp 2 y‖ ^ 2 := pow_pos (norm_pos_iff.2 hy0) 2
  rw [← hy, rayleighQuotient, ← quadForm_conjTranspose_mul_mul, hQ.norm_toLp_mulVec,
    div_le_iff₀ hpos]
  exact (Matrix.isHermitian_conjTranspose_mul_mul Q hA).re_quadForm_le_eigenvalue_zero_mul y

/-- **The split filter bound**: for Hermitian $\mathbf{A}$, a filter with $g(c) = 1$, a threshold
$t$ with $c - x \le D$ and $\lvert g(x)\rvert \le \delta$ at the eigenvalues $x \le t$ and
$c - x \le \eta$ at those above $t$,
$c - \rho_{\mathbf{A}}(g(\mathbf{A})\mathbf{b}) \le D\delta^2\tan^2\angle(\mathbf{b}, E_c) +
\eta$. -/
private theorem sub_rayleighQuotient_cfc_mulVec_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {c t D δ η : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η) {g : ℝ → ℝ} (hgc : g c = 1)
    (hlow : ∀ x ∈ spectrum ℝ A, x ≤ t → c - x ≤ D ∧ |g x| ≤ δ)
    (hhigh : ∀ x ∈ spectrum ℝ A, t < x → c - x ≤ η) (b : n → 𝕜)
    (hb : 0 < (spectralMeasure A b).real {c}) :
    c - rayleighQuotient A (cfc g A *ᵥ b) ≤ D * δ ^ 2 * spectralTangentSq A b c + η := by
  set μ := spectralMeasure A b with hμ
  have hi : ∀ f : ℝ → ℝ, Integrable f μ := integrable_spectralMeasure A b
  have hae : ∀ᵐ x ∂μ, x ∈ spectrum ℝ A := ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero A b)
  have hden : μ.real {c} ≤ ∫ x, g x ^ 2 ∂μ := by
    simpa [hgc] using mul_spectralMeasure_real_le_integral_sq A b g c
  have hG : 0 < ∫ x, g x ^ 2 ∂μ := hb.trans_le hden
  have hDd : 0 ≤ D * δ ^ 2 := mul_nonneg hD (sq_nonneg _)
  have hnum : ∫ x, (c - x) * g x ^ 2 ∂μ ≤ D * δ ^ 2 * μ.real {c}ᶜ + η * ∫ x, g x ^ 2 ∂μ := by
    rw [mul_comm (D * δ ^ 2), ← smul_eq_mul,
      ← integral_indicator_const _ (measurableSet_singleton c).compl, ← integral_const_mul,
      ← integral_add (hi _) (hi _)]
    refine integral_mono_ae (hi _) (hi _) ?_
    filter_upwards [hae] with x hx
    have hg2 : 0 ≤ η * g x ^ 2 := mul_nonneg hη (sq_nonneg _)
    by_cases hxc : x = c
    · simpa [hxc] using hg2
    rw [Set.indicator_of_mem (Set.mem_compl_singleton_iff.2 hxc)]
    rcases le_or_gt x t with hxt | hxt
    · obtain ⟨h1, h2⟩ := hlow x hx hxt
      have hsq : g x ^ 2 ≤ δ ^ 2 := by
        rw [← sq_abs (g x)]
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      have : (c - x) * g x ^ 2 ≤ D * δ ^ 2 := by
        rcases le_or_gt 0 (c - x) with h0 | h0
        · exact mul_le_mul h1 hsq (sq_nonneg _) hD
        · exact (mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)).trans hDd
      linarith
    · have : (c - x) * g x ^ 2 ≤ η * g x ^ 2 :=
        mul_le_mul_of_nonneg_right (hhigh x hx hxt) (sq_nonneg _)
      linarith
  have hsub : c - rayleighQuotient A (cfc g A *ᵥ b) =
      (∫ x, (c - x) * g x ^ 2 ∂μ) / ∫ x, g x ^ 2 ∂μ := by
    have hI : ∫ x, (c - x) * g x ^ 2 ∂μ = c * ∫ x, g x ^ 2 ∂μ - ∫ x, x * g x ^ 2 ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (hi _) (hi _), integral_const_mul]
    rw [hA.rayleighQuotient_cfc_mulVec_eq_integral_div, ← hμ, hI]
    field_simp
  have htan : μ.real {c}ᶜ ≤ spectralTangentSq A b c * ∫ x, g x ^ 2 ∂μ := by
    rw [spectralTangentSq, ← hμ, div_mul_eq_mul_div, le_div_iff₀ hb]
    exact mul_le_mul_of_nonneg_left hden measureReal_nonneg
  rw [hsub, div_le_iff₀ hG]
  nlinarith [mul_le_mul_of_nonneg_left htan hDd]

/-- The spectral measure rescaled to $[0, 1]$ by $x \mapsto x/\lambda_0$: its integrals are those
of $\mu_{\mathbf{A},\mathbf{b}}$ composed with the scaling. -/
private theorem integral_map_mul_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) (s : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂(spectralMeasure A b).map (fun y => s * y) =
      ∫ y, f (s * y) ∂spectralMeasure A b :=
  integral_map (continuous_const.mul continuous_id).aemeasurable hf.aestronglyMeasurable

/-! ### Ritz-value bounds -/

/-- **Kaniel–Paige–Saad**: for Hermitian $\mathbf{A}$ whose eigenvalues other than
$\lambda_0 = \lambda_0(\mathbf{A})$ lie in $[a, c]$, $a < c < \lambda_0$, a vector $\mathbf{b}$
with a component in the top eigenspace $E_{\lambda_0}$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le 4(\lambda_0 - a)\tan^2\angle(\mathbf{b}, E_{\lambda_0})
\Bigl(\frac{\sqrt{\lambda_0 - a} - \sqrt{\lambda_0 - c}}{\sqrt{\lambda_0 - a} +
\sqrt{\lambda_0 - c}}\Bigr)^{2q}\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure.
The proof gives the sharp factor $1/T_q\bigl(1 + 2(\lambda_0 - c)/(c - a)\bigr)^2$ in place of
$4(\cdot)^{2q}$; they differ by $(1 + \rho^{2q})^2 \le 4$ (rule B6).
[Saad2011, Theorem 6.4, Eq. (6.42)] (case $i = 1$); there with
$a = \lambda_{n}$, $c = \lambda_2$, an eigenvector of a simple eigenvalue and the Chebyshev form.
Result: kaniel-paige-saad -/
theorem _root_.Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0}) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * (eigenvalue A 0 - a) * spectralTangentSq A b (eigenvalue A 0) *
        ((√(eigenvalue A 0 - a) - √(eigenvalue A 0 - c)) /
          (√(eigenvalue A 0 - a) + √(eigenvalue A 0 - c))) ^ (2 * q) := by
  set lam := eigenvalue A 0
  have hl : 0 < lam - c := by linarith
  have hla : lam - c < lam - a := by linarith
  set R := chebyshevResidual (lam - c) (lam - a) q
  set P := R.comp (C lam - X)
  have hPeval : ∀ x, P.eval x = R.eval (lam - x) := fun x => by
    simp only [P, eval_comp, eval_sub, eval_C, eval_X]
  have hPdeg : P.degree ≤ q := by
    refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    have h1 : (C lam - X : ℝ[X]).natDegree ≤ 1 := by
      rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp
    have h2 : R.natDegree ≤ q := natDegree_le_iff_degree_le.mpr (degree_chebyshevResidual_le _ _ q)
    nlinarith
  have hP1 : P.eval lam = 1 := by
    rw [hPeval, sub_self]
    exact eval_chebyshevResidual_zero q hl hla
  have hR := isUniformApproxOn_chebyshevResidual_two_mul_pow q hl hla
  have hfilt := hA.abs_sub_rayleighQuotient_cfc_mulVec_le (s := Set.Icc a c) (c := lam)
    (D := lam - a) (δ := 2 * ((√(lam - a) - √(lam - c)) / (√(lam - a) + √(lam - c))) ^ q)
    (g := fun x => P.eval x) hs
    (fun x hx => by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
      linarith [hx.1])
    (by rw [hP1]; exact one_ne_zero)
    (fun x hx => by
      have h := hR.apply (show lam - x ∈ Set.Icc (lam - c) (lam - a) from
        ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      rw [Real.dist_eq, sub_zero] at h
      rw [hP1, abs_one, mul_one, hPeval]
      exact h) b hb
  rw [hA.cfc_eq_aeval_of_forall_eval_eq (f := fun x => P.eval x) fun _ _ => rfl] at hfilt
  have hθ := rayleighQuotient_aeval_mulVec_le hA hQ hK hPdeg
    (aeval_mulVec_ne_zero hA (by rw [hP1]; exact one_ne_zero) hb)
  calc lam - eigenvalue (Qᴴ * A * Q) 0 ≤ lam - rayleighQuotient A (aeval A P *ᵥ b) := by linarith
    _ ≤ |lam - rayleighQuotient A (aeval A P *ᵥ b)| := le_abs_self _
    _ ≤ _ := hfilt
    _ = _ := by ring

/-- **The gap-free Ritz-value bound**: for positive semidefinite $\mathbf{A}$,
$0 < \varepsilon < 1$, a vector $\mathbf{b}$ with a component in the top eigenspace
$E_{\lambda_0}$ of $\lambda_0 = \lambda_0(\mathbf{A})$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le \varepsilon\lambda_0 +
4e^{-4q\sqrt{\varepsilon}}\lambda_0\tan^2\angle(\mathbf{b}, E_{\lambda_0})\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure.
Sharp form: $1/T_q((1 + \varepsilon)/(1 - \varepsilon))^2$ in place of $4e^{-4q\sqrt\varepsilon}$
(`exp_mul_sqrt_div_two_le_eval_T_real`); the factor lost is
$e^{4q(\operatorname{artanh}\sqrt\varepsilon - \sqrt\varepsilon)}(1 + \rho^{2q})^2$ with
$\rho = (1 - \sqrt\varepsilon)/(1 + \sqrt\varepsilon)$, which is unbounded in $q$ at fixed
$\varepsilon$ (its exponent is about $4q\varepsilon^{3/2}/3$ for small $\varepsilon$). Incomparable
with `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`: this bound is
better for a fixed target accuracy with a good start, that one needs no $\varepsilon$ and degrades
only logarithmically with a poor start. [MuscoMusco2015, Theorem 1, §2.3] treats randomized block
iteration; the
deterministic single-start estimate and its explicit constants are composed here from
Chebyshev filtering.
Result: ritz-value-gap-free -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      ε * eigenvalue A 0 +
        4 * Real.exp (-4 * q * √ε) * eigenvalue A 0 * spectralTangentSq A b (eigenvalue A 0) := by
  set lam := eigenvalue A 0
  have hspec := hA.spectrum_subset_Icc_eigenvalue_zero
  have hlam0 : 0 ≤ lam := (hspec (mem_spectrum_of_spectralMeasure_real_pos hb)).1
  rcases hlam0.eq_or_lt with hl | hlpos
  · have hT := (hA.conjTranspose_mul_mul_same Q).eigenvalue_nonneg 0
    rw [← hl]
    linarith
  have hεl : 0 < ε * lam := mul_pos hε₀ hlpos
  have hεl' : ε * lam < lam := by nlinarith
  set R := chebyshevResidual (ε * lam) lam q
  set P := R.comp (C lam - X)
  have hPeval : ∀ x, P.eval x = R.eval (lam - x) := fun x => by
    simp only [P, eval_comp, eval_sub, eval_C, eval_X]
  have hPdeg : P.degree ≤ q := by
    refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    have h1 : (C lam - X : ℝ[X]).natDegree ≤ 1 := by
      rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp
    have h2 : R.natDegree ≤ q := natDegree_le_iff_degree_le.mpr (degree_chebyshevResidual_le _ _ q)
    nlinarith
  have hP1 : P.eval lam = 1 := by
    rw [hPeval, sub_self]
    exact eval_chebyshevResidual_zero q hεl hεl'
  have hR := isUniformApproxOn_chebyshevResidual q hεl hεl'
  set δ := ((Chebyshev.T ℝ (q : ℤ)).eval ((lam + ε * lam) / (lam - ε * lam)))⁻¹ with hδdef
  -- $\delta \le 2e^{-2q\sqrt\varepsilon}$
  have hδ : δ ≤ 2 * Real.exp (-(2 * q * √ε)) := by
    have hT := Chebyshev.exp_mul_sqrt_div_two_le_eval_T_real q hε₀.le hε₁
    have harg : (lam + ε * lam) / (lam - ε * lam) = (1 + ε) / (1 - ε) := by
      rw [show lam + ε * lam = (1 + ε) * lam by ring, show lam - ε * lam = (1 - ε) * lam by ring,
        mul_div_mul_right _ _ hlpos.ne']
    rw [hδdef, harg]
    calc _ ≤ (Real.exp (2 * q * √ε) / 2)⁻¹ := inv_anti₀ (by positivity) hT
      _ = 2 * Real.exp (-(2 * q * √ε)) := by rw [Real.exp_neg, inv_div, div_eq_mul_inv]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (by
    have h := hR.apply (show lam ∈ Set.Icc (ε * lam) lam from ⟨hεl'.le, le_rfl⟩)
    rwa [Real.dist_eq, sub_zero] at h)
  have hsplit := sub_rayleighQuotient_cfc_mulVec_le hA.isHermitian (c := lam)
    (t := (1 - ε) * lam) (D := lam) (δ := δ) (η := ε * lam) hlam0 hεl.le
    (g := fun x => P.eval x) hP1
    (fun x hx hxt => by
      have hx0 := (hspec hx).1
      refine ⟨by linarith, ?_⟩
      have h := hR.apply (show lam - x ∈ Set.Icc (ε * lam) lam from
        ⟨by linarith, by linarith⟩)
      rw [Real.dist_eq, sub_zero] at h
      rw [hPeval]
      exact h)
    (fun x _ hxt => by linarith) b hb
  rw [hA.isHermitian.cfc_eq_aeval_of_forall_eval_eq (f := fun x => P.eval x)
    fun _ _ => rfl] at hsplit
  have hθ := rayleighQuotient_aeval_mulVec_le hA.isHermitian hQ hK hPdeg
    (aeval_mulVec_ne_zero hA.isHermitian (by rw [hP1]; exact one_ne_zero) hb)
  have hδ2 : δ ^ 2 ≤ 4 * Real.exp (-4 * q * √ε) := by
    calc δ ^ 2 ≤ (2 * Real.exp (-(2 * q * √ε))) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
      _ = 4 * Real.exp (-4 * q * √ε) := by
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
        ring_nf
  have htan := spectralTangentSq_nonneg A b lam
  nlinarith [mul_le_mul_of_nonneg_left hδ2 (mul_nonneg hlam0 htan)]

/-- **Kuczyński–Woźniakowski, deterministic Lanczos step**: for positive semidefinite
$\mathbf{A}$, a vector $\mathbf{b}$ with a component in the top eigenspace $E_{\lambda_0}$ of
$\lambda_0 = \lambda_0(\mathbf{A})$, $q \ge 1$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le \frac{4\lambda_0}{q^2}\Bigl(1 +
\frac{\log(1 + \tan^2\angle(\mathbf{b}, E_{\lambda_0}))}{\log 2}\Bigr)^2\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure: a squared logarithmic
dependence on the start and no gap. Incomparable with
`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add`: this bound needs no
$\varepsilon$ and degrades only logarithmically with a poor start, that one is better for a fixed
target accuracy with a good start. [MartinssonTropp2020, Theorem 6.2] presents a randomized Krylov
estimate following
[KuczynskiWozniakowski1992, abstract]. Here the specified-start estimate is deterministic and its
constants are composed from the even Chebyshev filter.
Result: ritz-value-gap-free -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ} (hq : 1 ≤ q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * eigenvalue A 0 *
        (1 + Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / Real.log 2) ^ 2 / q ^ 2 := by
  set lam := eigenvalue A 0
  set μ := spectralMeasure A b with hμ
  have hspec := hA.spectrum_subset_Icc_eigenvalue_zero
  have hlam0 : 0 ≤ lam := (hspec (mem_spectrum_of_spectralMeasure_real_pos hb)).1
  rcases hlam0.eq_or_lt with hl | hlpos
  · have hT := (hA.conjTranspose_mul_mul_same Q).eigenvalue_nonneg 0
    rw [← hl, mul_zero, zero_mul, zero_div]
    linarith
  -- rescale to $[0, 1]$
  have hfm : Measurable fun y : ℝ => lam⁻¹ * y := (continuous_const.mul continuous_id).measurable
  set ν := μ.map fun y => lam⁻¹ * y
  have hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1 := by
    refine (ae_map_iff hfm.aemeasurable measurableSet_Icc).2 ?_
    filter_upwards [ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero A b)] with y hy
    obtain ⟨h0, h1⟩ := hspec hy
    exact ⟨mul_nonneg (inv_nonneg.2 hlam0) h0, by rw [inv_mul_le_one₀ hlpos]; exact h1⟩
  have hpre : (fun y : ℝ => lam⁻¹ * y) ⁻¹' {1} = {lam} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      field_simp at h
      linarith
    · rintro rfl
      exact inv_mul_cancel₀ hlpos.ne'
  have hν1 : ν.real {1} = μ.real {lam} := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hfm (measurableSet_singleton 1), hpre]
  have hνu : ν.real Set.univ = μ.real Set.univ := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hfm MeasurableSet.univ,
      Set.preimage_univ]
  obtain ⟨p, hpdeg, hp1, hbound⟩ :=
    exists_natDegree_le_one_sub_integral_mul_div_le hsupp (hν1 ▸ hb) hq
  -- the filter $P(x) = p(x/\lambda_0)$
  set P := p.comp (C lam⁻¹ * X)
  have hPeval : ∀ y, P.eval y = p.eval (lam⁻¹ * y) := fun y => by
    simp only [P, eval_comp, eval_mul, eval_C, eval_X]
  have hPdeg : P.degree ≤ q := by
    refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    have h1 : (C lam⁻¹ * X : ℝ[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    nlinarith
  have hP1 : P.eval lam = 1 := by rw [hPeval, inv_mul_cancel₀ hlpos.ne', hp1]
  have hint1 : ∫ x, x * p.eval x ^ 2 ∂ν = lam⁻¹ * ∫ y, y * P.eval y ^ 2 ∂μ := by
    rw [integral_map_mul_spectralMeasure A b _ _ (by fun_prop), ← integral_const_mul]
    simp only [hPeval, mul_assoc]
    rfl
  have hint2 : ∫ x, p.eval x ^ 2 ∂ν = ∫ y, P.eval y ^ 2 ∂μ := by
    rw [integral_map_mul_spectralMeasure A b _ _ (by fun_prop)]
    simp only [hPeval]
    rfl
  have hG : 0 < ∫ y, P.eval y ^ 2 ∂μ := by
    have h := mul_spectralMeasure_real_le_integral_sq A b (fun y => P.eval y) lam
    rw [hP1, one_pow, one_mul] at h
    exact hb.trans_le h
  have hρ := hA.isHermitian.rayleighQuotient_cfc_mulVec_eq_integral_div (fun y => P.eval y) b
  rw [hA.isHermitian.cfc_eq_aeval_of_forall_eval_eq (f := fun x => P.eval x)
    fun _ _ => rfl, ← hμ] at hρ
  have hθ := rayleighQuotient_aeval_mulVec_le hA.isHermitian hQ hK hPdeg
    (aeval_mulVec_ne_zero hA.isHermitian (by rw [hP1]; exact one_ne_zero) hb)
  have hratio : ν.real Set.univ / ν.real {1} = 1 + spectralTangentSq A b lam := by
    rw [hνu, hν1, hA.isHermitian.one_add_spectralTangentSq hb, ← hμ,
      hA.isHermitian.spectralMeasure_real_univ]
  rw [hint1, hint2, hratio] at hbound
  -- $\lambda_0 - \rho = \lambda_0(1 - \text{the rescaled ratio})$
  have heq : lam - rayleighQuotient A (aeval A P *ᵥ b) =
      lam * (1 - lam⁻¹ * (∫ y, y * P.eval y ^ 2 ∂μ) / ∫ y, P.eval y ^ 2 ∂μ) := by
    rw [hρ]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hbound hlam0
  calc lam - eigenvalue (Qᴴ * A * Q) 0 ≤ lam - rayleighQuotient A (aeval A P *ᵥ b) := by linarith
    _ = _ := heq
    _ ≤ _ := hmul
    _ = _ := by ring

end NLAlib
