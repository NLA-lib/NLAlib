/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Matrix.Spectral.SpectralMeasure

/-!
# The power method and inverse iteration

The power method after $q$ multiplications estimates an eigenvalue $c$ of a Hermitian
$\mathbf{A}$ by the Rayleigh quotient $\rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})$; inverse
iteration with shift $\sigma$ by
$\rho_{\mathbf{A}}((\mathbf{A} - \sigma\mathbf{I})^{-q}\mathbf{b})$.
There is no definition of an iterate: both are powers applied to the start. The start enters
only through the squared tangent of its angle with the eigenspace $E_c$, read off the spectral
measure, $\tan^2\angle(\mathbf{b}, E_c) =
\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$
(`NLAlib.spectralTangentSq`).

The gapped bounds are instances of the filter theorem
`Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le`, with the filters $x^q$ and
$(x - \sigma)^{-q}$. For positive semidefinite $\mathbf{A}$, Kuczyński and Woźniakowski's
gap-free step bounds $\lambda_0 - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})$ by
$\lambda_0\log(1 + \tan^2)/(2q + 1)$, the input of the random-start power method.

## Main results

* `Matrix.IsHermitian.abs_sub_rayleighQuotient_pow_mulVec_le`: the gapped power method.
* `Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`: the gap-free step.
* `Matrix.IsHermitian.abs_sub_rayleighQuotient_inv_pow_mulVec_le`: inverse iteration.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The power method, gapped**: for Hermitian $\mathbf{A}$ with spectrum in
$[-r, r] \cup \{c\}$, $r < \lvert c\rvert$, and $\mathbf{b}$ with a component in the eigenspace
$E_c$ of $c$, after $q$ multiplications
$$\bigl\lvert c - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})\bigr\rvert \le
(\lvert c\rvert + r)\Bigl(\frac{r}{\lvert c\rvert}\Bigr)^{2q}\tan^2\angle(\mathbf{b}, E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$ of the
spectral measure. [TrefethenBau1997, Theorem 27.1, p. 205]; Trefethen–Bau give an asymptotic rate
for a simple dominant eigenvalue
and an eigenvector, here an explicit bound with any multiplicity.
Result: power-iteration -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c r : ℝ} (hrc : r < |c|) (hs : spectrum ℝ A ⊆ Set.Icc (-r) r ∪ {c})
    (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A (A ^ q *ᵥ b)| ≤
      (|c| + r) * (r / |c|) ^ (2 * q) * spectralTangentSq A b c := by
  by_cases hc : c = 0
  · -- then $r < 0$, the spectrum is $\{0\}$ and $\mathbf{A} = \mathbf{0}$
    subst hc
    have hA' : IsSelfAdjoint A := hA
    have hr : r < 0 := by simpa using hrc
    have hs0 : spectrum ℝ A ⊆ {0} := fun x hx =>
      (hs hx).resolve_left fun h => by linarith [h.1, h.2]
    have hA0 : A = 0 := by
      rw [← cfc_id' ℝ A hA', cfc_congr (g := fun _ => (0 : ℝ)) (fun x hx => hs0 hx),
        cfc_const_zero]
    have htan : spectralTangentSq A b 0 = 0 := by
      rw [spectralTangentSq, measureReal_def, measure_mono_null (Set.compl_subset_compl.2 hs0)
        (spectralMeasure_compl_spectrum_eq_zero A b), ENNReal.toReal_zero, zero_div]
    rw [htan, mul_zero, rayleighQuotient, hA0, quadForm_zero_left, map_zero, zero_div, sub_zero,
      abs_zero]
  have hc0 : 0 < |c| := abs_pos.2 hc
  have h := hA.abs_sub_rayleighQuotient_cfc_mulVec_le (s := Set.Icc (-r) r) (D := |c| + r)
    (δ := (r / |c|) ^ q) (g := fun x => x ^ q) hs
    (fun x hx => by linarith [abs_sub x c, abs_le.2 ⟨hx.1, hx.2⟩]) (pow_ne_zero q hc)
    (fun x hx => by
      rw [abs_pow, abs_pow, div_pow, div_mul_cancel₀ _ (pow_ne_zero q hc0.ne')]
      exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.2 ⟨hx.1, hx.2⟩) q) b hb
  rw [cfc_pow_id A q (show IsSelfAdjoint A from hA)] at h
  refine h.trans_eq ?_
  rw [← pow_mul, mul_comm q 2]

/-- The Rayleigh quotient of $\mathbf{A}^q\mathbf{b}$ as a ratio of moments of the spectral
measure: $\rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b}) = \int x^{2q+1}\,d\mu / \int x^{2q}\,d\mu$. -/
private theorem rayleighQuotient_pow_mulVec_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) :
    rayleighQuotient A (A ^ q *ᵥ b) =
      (∫ x, x ^ (2 * q + 1) ∂spectralMeasure A b) / ∫ x, x ^ (2 * q) ∂spectralMeasure A b := by
  have hq := (hA.pow q).eq
  have hnorm : ‖WithLp.toLp 2 (A ^ q *ᵥ b)‖ ^ 2 = RCLike.re (quadForm (A ^ (2 * q)) b) := by
    have h : A ^ q * A ^ q = (A ^ q)ᴴ * A ^ q := by rw [hq]
    rw [two_mul, pow_add, h, quadForm_conjTranspose_mul_self, RCLike.ofReal_re]
  rw [rayleighQuotient, hnorm, hA.integral_pow_spectralMeasure, hA.integral_pow_spectralMeasure,
    ← quadForm_conjTranspose_mul_mul, hq, ← pow_succ, ← pow_add,
    show q + 1 + q = 2 * q + 1 by ring]

/-- The moments $a_j = \int x^j\,d\mu_{\mathbf{A},\mathbf{b}}$ of a positive semidefinite
$\mathbf{A}$, if positive, have nondecreasing ratios $a_{j+1}/a_j$ (Cauchy–Schwarz). -/
private theorem integral_pow_succ_div_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (b : n → 𝕜)
    (hpos : ∀ j : ℕ, 0 < ∫ x, x ^ j ∂spectralMeasure A b) (j : ℕ) :
    (∫ x, x ^ (j + 1) ∂spectralMeasure A b) / ∫ x, x ^ j ∂spectralMeasure A b ≤
      (∫ x, x ^ (j + 2) ∂spectralMeasure A b) / ∫ x, x ^ (j + 1) ∂spectralMeasure A b := by
  set μ := spectralMeasure A b
  have hi : ∀ f : ℝ → ℝ, Integrable f μ := integrable_spectralMeasure A b
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    filter_upwards [ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero A b)] with x hx
    exact hA.spectrum_subset_Ici hx
  set t := (∫ x, x ^ (j + 1) ∂μ) / ∫ x, x ^ j ∂μ
  have h0 : 0 ≤ ∫ x, x ^ j * (x - t) ^ 2 ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hae] with x hx; positivity)
  have hfun : (fun x : ℝ => x ^ j * (x - t) ^ 2) =
      fun x => x ^ (j + 2) - 2 * t * x ^ (j + 1) + t ^ 2 * x ^ j := by
    ext x
    ring
  rw [hfun, integral_add (hi _) (hi _), integral_sub (hi _) (hi _), integral_const_mul,
    integral_const_mul] at h0
  have hta : t * ∫ x, x ^ j ∂μ = ∫ x, x ^ (j + 1) ∂μ := div_mul_cancel₀ _ (hpos j).ne'
  have ht2 : t ^ 2 * ∫ x, x ^ j ∂μ = t * ∫ x, x ^ (j + 1) ∂μ := by rw [sq, mul_assoc, hta]
  rw [le_div_iff₀ (hpos (j + 1))]
  linarith

/-- With nondecreasing moment ratios, $a_j \le a_0\,(a_{k+1}/a_k)^j$ for $j \le k + 1$. -/
private theorem integral_pow_le_mul_pow {A : Matrix n n 𝕜} (hA : A.PosSemidef) (b : n → 𝕜)
    (hpos : ∀ j : ℕ, 0 < ∫ x, x ^ j ∂spectralMeasure A b) (k : ℕ) :
    ∀ j ≤ k + 1, ∫ x, x ^ j ∂spectralMeasure A b ≤ (∫ x, x ^ 0 ∂spectralMeasure A b) *
      ((∫ x, x ^ (k + 1) ∂spectralMeasure A b) / ∫ x, x ^ k ∂spectralMeasure A b) ^ j := by
  set a : ℕ → ℝ := fun j => ∫ x, x ^ j ∂spectralMeasure A b
  have hmono : Monotone fun j => a (j + 1) / a j :=
    monotone_nat_of_le_succ (integral_pow_succ_div_le hA b hpos)
  have hρ : 0 ≤ a (k + 1) / a k := (div_pos (hpos _) (hpos _)).le
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h2 : a (j + 1) ≤ a (k + 1) / a k * a j := by
      have h := hmono (show j ≤ k by omega)
      rwa [div_le_iff₀ (hpos j)] at h
    calc a (j + 1) ≤ a (k + 1) / a k * a j := h2
      _ ≤ a (k + 1) / a k * (a 0 * (a (k + 1) / a k) ^ j) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) hρ
      _ = a 0 * (a (k + 1) / a k) ^ (j + 1) := by ring

/-- **Gap-free deterministic power step**: for positive semidefinite
$\mathbf{A}$ and $\mathbf{b}$ with a component in the top eigenspace $E_{\lambda_0}$ of
$\lambda_0 = \lambda_0(\mathbf{A})$, after $q$ multiplications
$$\lambda_0 - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b}) \le
\frac{\lambda_0\log(1 + \tan^2\angle(\mathbf{b}, E_{\lambda_0}))}{2q + 1}\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure; no gap, every $q$ including
$0$. [MartinssonTropp2020, Theorem 6.1] presents a randomized power estimate following
[KuczynskiWozniakowski1992, abstract]. Here the bound is deterministic for the specified start;
the logarithmic overlap and the explicit constant are derived from its spectral measure. -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0})
    (q : ℕ) :
    eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ b) ≤
      eigenvalue A 0 * Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / (2 * q + 1) := by
  set μ := spectralMeasure A b with hμ
  set lam := eigenvalue A 0
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    filter_upwards [ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero A b)] with x hx
    exact hA.spectrum_subset_Ici hx
  have hlam : lam ∈ spectrum ℝ A := mem_spectrum_of_spectralMeasure_real_pos hb
  have hlam0 : 0 ≤ lam := hA.spectrum_subset_Ici hlam
  rcases hlam0.eq_or_lt with hl | hlpos
  · rw [← hl, zero_mul, zero_div, zero_sub, neg_nonpos]
    exact div_nonneg (hA.re_quadForm_nonneg _) (sq_nonneg _)
  -- the moments $a_j \ge \lambda_0^j\mu(\{\lambda_0\})$ are positive
  have hlow : ∀ j : ℕ, lam ^ j * μ.real {lam} ≤ ∫ x, x ^ j ∂μ := fun j =>
    mul_spectralMeasure_real_le_integral A b (f := fun x => x ^ j)
      (hae.mono fun x hx => pow_nonneg hx j) lam
  have hpos : ∀ j : ℕ, 0 < ∫ x, x ^ j ∂μ := fun j =>
    (mul_pos (pow_pos hlpos j) hb).trans_le (hlow j)
  set k := 2 * q
  set ρ := (∫ x, x ^ (k + 1) ∂μ) / ∫ x, x ^ k ∂μ
  have hρ : 0 < ρ := div_pos (hpos _) (hpos _)
  have ha0 : ∫ x, x ^ 0 ∂μ = ‖WithLp.toLp 2 b‖ ^ 2 := by
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one]
    exact hA.isHermitian.spectralMeasure_real_univ b
  have hB : 0 < ‖WithLp.toLp 2 b‖ ^ 2 := ha0 ▸ hpos 0
  -- $(\rho/\lambda_0)^{k+1} \ge \mu(\{\lambda_0\})/\|\mathbf{b}\|^2$
  have hpow : μ.real {lam} / ‖WithLp.toLp 2 b‖ ^ 2 ≤ (ρ / lam) ^ (k + 1) := by
    have h := (hlow (k + 1)).trans (integral_pow_le_mul_pow hA b hpos k (k + 1) le_rfl)
    rw [ha0] at h
    rw [div_pow, div_le_div_iff₀ hB (pow_pos hlpos _)]
    linarith
  have hlog : -Real.log (ρ / lam) ≤
      Real.log (1 + spectralTangentSq A b lam) / ((k + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (div_pos hb hB) hpow
    rw [Real.log_pow, Real.log_div hb.ne' hB.ne'] at h
    rw [hA.isHermitian.one_add_spectralTangentSq hb, Real.log_div hB.ne' hb.ne',
      le_div_iff₀ (by positivity)]
    linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hρ hlpos)
  rw [rayleighQuotient_pow_mulVec_eq hA.isHermitian, ← hμ]
  calc lam - ρ = lam * (1 - ρ / lam) := by field_simp
    _ ≤ lam * -Real.log (ρ / lam) := mul_le_mul_of_nonneg_left (by linarith) hlam0
    _ ≤ lam * (Real.log (1 + spectralTangentSq A b lam) / ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hlam0
    _ = lam * Real.log (1 + spectralTangentSq A b lam) / (2 * q + 1) := by
        simp only [k]
        push_cast
        ring

/-- **Inverse iteration**: for Hermitian $\mathbf{A}$ with spectrum in $s \cup \{c\}$, a shift
$\sigma \ne c$ with $d \le \lvert x - \sigma\rvert$ for $x \in s$, $d > 0$,
$\lvert x - c\rvert \le D$ for $x \in s$, and $\mathbf{b}$ with a component in the eigenspace
$E_c$ of $c$, after $q$ steps
$$\bigl\lvert c - \rho_{\mathbf{A}}((\mathbf{A} - \sigma\mathbf{I})^{-q}\mathbf{b})\bigr\rvert
\le D\Bigl(\frac{\lvert c - \sigma\rvert}{d}\Bigr)^{2q}\tan^2\angle(\mathbf{b}, E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$ of the
spectral measure. [TrefethenBau1997, Theorem 27.2, pp. 206–207]; there an asymptotic rate for a
simple
eigenvalue and an eigenvector, here an explicit bound with any multiplicity. -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_inv_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} {c σ d D : ℝ} (hs : spectrum ℝ A ⊆ s ∪ {c})
    (hσc : σ ≠ c) (hd : 0 < d) (hds : ∀ x ∈ s, d ≤ |x - σ|)
    (hD : ∀ x ∈ s, |x - c| ≤ D) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A ((A - σ • (1 : Matrix n n 𝕜))⁻¹ ^ q *ᵥ b)| ≤
      D * (|c - σ| / d) ^ (2 * q) * spectralTangentSq A b c := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    A.finite_real_spectrum.continuousOn f
  have hA' : IsSelfAdjoint A := hA
  have hcσ : c - σ ≠ 0 := sub_ne_zero.2 hσc.symm
  have hσ : ∀ x ∈ spectrum ℝ A, x - σ ≠ 0 := fun x hx => by
    rcases hs hx with hxs | hxc
    · intro h0
      have := hds x hxs
      rw [h0, abs_zero] at this
      linarith
    · rw [Set.mem_singleton_iff.1 hxc]
      exact hcσ
  have hB : cfc (fun x => x - σ) A = A - σ • (1 : Matrix n n 𝕜) := by
    rw [cfc_sub (fun x => x) (fun _ => σ) A (hcont _) (hcont _), cfc_id' ℝ A hA',
      cfc_const σ A hA', Algebra.algebraMap_eq_smul_one]
  have hinv : cfc (fun x => (x - σ)⁻¹) A = (A - σ • (1 : Matrix n n 𝕜))⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← hB, ← cfc_mul _ _ A (hcont _) (hcont _), cfc_congr (g := fun _ => (1 : ℝ))
      fun x hx => inv_mul_cancel₀ (hσ x hx), cfc_const_one ℝ A hA']
  have hg : cfc (fun x => (x - σ)⁻¹ ^ q) A = (A - σ • (1 : Matrix n n 𝕜))⁻¹ ^ q := by
    rw [cfc_pow (fun x => (x - σ)⁻¹) q A (hcont _) hA', hinv]
  have h := hA.abs_sub_rayleighQuotient_cfc_mulVec_le (s := s) (D := D)
    (δ := (|c - σ| / d) ^ q) (g := fun x => (x - σ)⁻¹ ^ q) hs hD
    (pow_ne_zero q (inv_ne_zero hcσ))
    (fun x hx => by
      have hcσ' : 0 < |c - σ| := abs_pos.2 hcσ
      rw [abs_pow, abs_pow, abs_inv, abs_inv, div_pow, inv_pow, inv_pow,
        show |c - σ| ^ q / d ^ q * (|c - σ| ^ q)⁻¹ = (d ^ q)⁻¹ by field_simp]
      exact inv_anti₀ (pow_pos hd q) (pow_le_pow_left₀ hd.le (hds x hx) q)) b hb
  rw [hg] at h
  refine h.trans_eq ?_
  rw [← pow_mul, mul_comm q 2]

end NLAlib
