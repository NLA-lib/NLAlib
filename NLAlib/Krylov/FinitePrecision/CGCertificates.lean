/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGModel

/-!
# Input-based backward-error certificates for finite-precision conjugate gradients

Scalar feasibility conditions on the iteration count, precision and spectral endpoints
control every successful run. Geometric error accumulation is retained, and a positive
spectral margin is explicit. The single prefix induction gives the direction and coefficient
bounds needed by the a posteriori backward model.

## Main definitions

* `NLAlib.CGBackwardCertificate`: scalar bounds and their input-based closure inequalities.

## Main results

* `NLAlib.CGRun.norm_p_sq_le_sum_inv`: direction growth from line-search defects.
* `NLAlib.CGRun.norm_p_sq_le_of_certificate`: the direction bound supplied by a certificate.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificate`: the certified model distance.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- Input-based scalar data certifying a CG backward model within Frobenius distance $d$.
For application to $k\ge1$ successful steps with $0\le\varepsilon\le1/100$ and input spectrum
in $[a,a']$, choose $P,K,B,d$. Their intended bounds are
$\|\mathbf{p}_j\|\le P\rho_j$,
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2\le K\rho_j^2$ and
$\beta_{j+1},\delta_j/\gamma_j\le B$, where $\rho_j=\|\mathbf{r}_j\|$.
The record requires scalar inequalities only, with no measured trajectory bounds.

Put $m=k-1$ and use the accumulated line-search factor with its current
value <!-- value cgLineSearchFactor m \varepsilon -->
$$t=(41/10)\varepsilon\sum_{i=0}^{m-1}(1+(31/10)\varepsilon)^i(1+P+K),\qquad
\Lambda=(1+3t+4\varepsilon+2\varepsilon^2)(1+4\varepsilon)^2.$$
For the backward budget, put $f=8\varepsilon[a'(1+P)^2+B]$ and
use <!-- value cgAdjacentInnerFactor k \varepsilon -->
$$p=13\varepsilon\sum_{i=0}^{k-1}(1+(31/10)\varepsilon)^i
\bigl[a'(1+P)^2+B(1+P)\bigr].$$
Besides $P\ge0$ and $0\le d<a$, require $c=a-\varepsilon(2+\varepsilon)a'>0$ and
$$a'(1+\varepsilon)^2\le Kc,\qquad
\Lambda^m\frac{a'+d}{a-d}\le P^2,\qquad (1+4\varepsilon)(a'+d)\le B.$$
The final closure inequality is <!-- value normalizedBackwardBound k f p -->
$$22k^2f+17k\sqrt{k}p\le d.$$
Finite sums include zero precision and $m=0$. The strict inequalities retain positive
curvature and inverse spectral margins; feasibility at every horizon is not asserted.
The raw structure constructor accepts the chosen scalars and these proofs. No printed source. -/
structure CGBackwardCertificate (k : ℕ) (ε a a' : ℝ) where
  /-- Bound on direction norm divided by residual norm. -/
  P : ℝ
  /-- Bound on the scaled curvature quantity. -/
  K : ℝ
  /-- Bound on the Lanczos and direction-update coefficients. -/
  B : ℝ
  /-- Frobenius distance allowed for the backward model. -/
  d : ℝ
  /-- The direction bound is nonnegative. -/
  P_nonneg : 0 ≤ P
  /-- The model distance is nonnegative. -/
  d_nonneg : 0 ≤ d
  /-- The backward model retains a positive spectral margin. -/
  d_lt : d < a
  /-- Rounding does not exhaust the lower curvature bound. -/
  curvature_margin : 0 < a - ε * (2 + ε) * a'
  /-- The curvature bound absorbs the local errors. -/
  curvature_le : a' * (1 + ε) ^ 2 ≤ K * (a - ε * (2 + ε) * a')
  /-- The direction bound absorbs accumulated line-search errors and residual ratios. -/
  direction_le :
    let t := cgLineSearchFactor (k - 1) ε * (1 + P + K)
    ((1 + 3 * t + 4 * ε + 2 * ε ^ 2) * (1 + 4 * ε) ^ 2) ^ (k - 1) *
      ((a' + d) / (a - d)) ≤ P ^ 2
  /-- The coefficient bound absorbs the enlarged upper spectral endpoint. -/
  coefficient_le : (1 + 4 * ε) * (a' + d) ≤ B
  /-- The a posteriori error budget fits within the chosen model distance. -/
  backward_le : normalizedBackwardBound k (8 * ε * (a' * (1 + P) ^ 2 + B))
    (cgAdjacentInnerFactor k ε * (a' * (1 + P) ^ 2 + B * (1 + P))) ≤ d

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The direction coefficient against the exact residual ratio, one-sided:
$0 \le \delta_i \le (1 + 4\varepsilon)\rho_{i+1}^2/\rho_i^2$. -/
private theorem δ_bounds_ratio {n m : ℕ} (D : CGRun n m) {i : ℕ} (hi : i < m) :
    0 ≤ D.δ i ∧ D.δ i ≤ (1 + 4 * D.ε) * (D.ρ (i + 1) ^ 2 / D.ρ i ^ 2) := by
  have h := abs_le.mp (D.abs_δ_sub_le hi)
  have hq : 0 ≤ D.ρ (i + 1) ^ 2 / D.ρ i ^ 2 := by positivity
  have hε : 4 * D.ε ≤ 1 := by
    linarith [D.ε_le]
  constructor <;> nlinarith

/-- **One step of the direction recursion**: with $\lvert\mathbf{p}_i^{\mathsf{T}}
\mathbf{r}_{i+1}\rvert \le t\rho_i^2$, $t \ge0$,
$\|\mathbf{p}_{i+1}\|^2 \le (1 + 3t + 4\varepsilon + 2\varepsilon^2)(\rho_{i+1}^2 +
\delta_i^2\|\mathbf{p}_i\|^2)$. -/
private theorem norm_p_succ_sq_le {n m : ℕ} (D : CGRun n m) {i : ℕ} (hi : i < m) {t : ℝ}
    (ht0 : 0 ≤ t) (hτ : |D.p i ⬝ᵥ D.r (i + 1)| ≤ t * D.ρ i ^ 2) :
    ‖WithLp.toLp 2 (D.p (i + 1))‖ ^ 2 ≤ (1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2) *
      (D.ρ (i + 1) ^ 2 + D.δ i ^ 2 * ‖WithLp.toLp 2 (D.p i)‖ ^ 2) := by
  obtain ⟨hδ0, hδ⟩ := δ_bounds_ratio D hi
  have hε := D.ε_nonneg
  have hε1 := D.ε_le
  set R := D.ρ (i + 1) with hR
  set Q := ‖WithLp.toLp 2 (D.p i)‖ with hQ
  set δ := D.δ i with hδdef
  set τ := D.p i ⬝ᵥ D.r (i + 1) with hτdef
  have hR0 : 0 ≤ R := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  set u := R ^ 2 + δ ^ 2 * Q ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  set w := D.r (i + 1) + δ • D.p i with hw
  have hW2 : ‖WithLp.toLp 2 w‖ ^ 2 = R ^ 2 + 2 * δ * τ + δ ^ 2 * Q ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hR, ρ,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hQ,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hw, hτdef]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (D.r (i + 1)) (D.p i)]
    ring
  -- `δ|τ| ≤ (1 + 4ε) t R²`
  have hδτ : δ * |τ| ≤ (1 + 4 * D.ε) * t * R ^ 2 := by
    rcases (norm_nonneg (WithLp.toLp 2 (D.r i))).lt_or_eq with hρ | hρ
    · change 0 < D.ρ i at hρ
      have hρ2 : 0 < D.ρ i ^ 2 := by positivity
      calc δ * |τ| ≤ ((1 + 4 * D.ε) * (R ^ 2 / D.ρ i ^ 2)) * (t * D.ρ i ^ 2) :=
            mul_le_mul hδ hτ (abs_nonneg _) (by positivity)
        _ = (1 + 4 * D.ε) * t * R ^ 2 := by field_simp
    · change 0 = D.ρ i at hρ
      rw [← hρ] at hτ
      have : |τ| = 0 := le_antisymm (by simpa using hτ) (abs_nonneg _)
      rw [this, mul_zero]; positivity
  have hW2le : ‖WithLp.toLp 2 w‖ ^ 2 ≤ (1 + 2 * (1 + 4 * D.ε) * t) * u := by
    rw [hW2]
    have hτu := mul_le_mul_of_nonneg_left (le_abs_self τ) hδ0
    have huR : R ^ 2 ≤ u := le_add_of_nonneg_right (by positivity)
    have h5 := mul_le_mul_of_nonneg_left huR
      (by positivity : 0 ≤ 2 * (1 + 4 * D.ε) * t)
    nlinarith
  set W := ‖WithLp.toLp 2 w‖ with hWdef
  have hW0 : 0 ≤ W := norm_nonneg _
  set E := ‖WithLp.toLp 2 (D.ep i)‖ with hEdef
  have hE : E ≤ D.ε * (R + δ * Q) := by
    have := D.norm_ep_le i hi
    rwa [abs_of_nonneg hδ0] at this
  have hE0 : 0 ≤ E := norm_nonneg _
  have hZ2 : (R + δ * Q) ^ 2 ≤ 2 * u := by nlinarith [sq_nonneg (R - δ * Q)]
  have hZ0 : 0 ≤ R + δ * Q := by positivity
  have hp : ‖WithLp.toLp 2 (D.p (i + 1))‖ ≤ W + E := by
    rw [D.p_succ i hi, WithLp.toLp_add]
    exact norm_add_le _ _
  have hp2 : ‖WithLp.toLp 2 (D.p (i + 1))‖ ^ 2 ≤ (W + E) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hp 2
  refine hp2.trans ?_
  have h2WE : 2 * W * E ≤ D.ε * (W ^ 2 + (R + δ * Q) ^ 2) := by
    have : W * E ≤ W * (D.ε * (R + δ * Q)) := mul_le_mul_of_nonneg_left hE hW0
    nlinarith [sq_nonneg (W - (R + δ * Q)), mul_nonneg hε (sq_nonneg (W - (R + δ * Q)))]
  have hE2 : E ^ 2 ≤ D.ε ^ 2 * (R + δ * Q) ^ 2 := by
    have := pow_le_pow_left₀ hE0 hE 2
    rwa [mul_pow] at this
  have h3 : D.ε * (W ^ 2 + (R + δ * Q) ^ 2) ≤
      D.ε * ((3 + 2 * (1 + 4 * D.ε) * t) * u) := by
    apply mul_le_mul_of_nonneg_left _ hε
    nlinarith
  have h4 : D.ε ^ 2 * (R + δ * Q) ^ 2 ≤ D.ε ^ 2 * (2 * u) :=
    mul_le_mul_of_nonneg_left hZ2 (sq_nonneg _)
  have hcoef : (1 + D.ε) * (1 + 2 * (1 + 4 * D.ε) * t) + 2 * D.ε + 2 * D.ε ^ 2 ≤
      1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2 := by
    have he2 := mul_le_mul_of_nonneg_left hε1 hε
    have hq : 2 + 10 * D.ε + 8 * D.ε ^ 2 ≤ 3 := by nlinarith only [he2, hε1]
    have := mul_le_mul_of_nonneg_right hq ht0
    nlinarith only [this, hε]
  have h5 := mul_le_mul_of_nonneg_right hcoef hu0
  nlinarith only [hW2le, h2WE, hE2, h3, h4, h5]


/-- **The unrolled direction recursion**: with $\lvert\mathbf{p}_i^{\mathsf{T}}
\mathbf{r}_{i+1}\rvert \le t\rho_i^2$ for $i < j$,
$\|\mathbf{p}_j\|^2 \le \Lambda^j\rho_j^4\sum_{i \le j}\rho_i^{-2}$,
$\Lambda = (1 + 3t + 4\varepsilon + 2\varepsilon^2)(1 + 4\varepsilon)^2$. -/
theorem norm_p_sq_le_sum_inv {n m : ℕ} (D : CGRun n m) {t : ℝ} (ht0 : 0 ≤ t)
    {j : ℕ} (hj : j < m)
    (hτ : ∀ i < j, |D.p i ⬝ᵥ D.r (i + 1)| ≤ t * D.ρ i ^ 2) :
    ‖WithLp.toLp 2 (D.p j)‖ ^ 2 ≤ ((1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2) * (1 + 4 * D.ε) ^ 2) ^ j *
      D.ρ j ^ 4 * ∑ i ∈ Finset.range (j + 1), (D.ρ i ^ 2)⁻¹ := by
  have hε := D.ε_nonneg
  set c₁ := 1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2 with hc₁
  set Λ := c₁ * (1 + 4 * D.ε) ^ 2 with hΛ
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁]; nlinarith
  have hΛc : c₁ ≤ Λ := by
    rw [hΛ]; nlinarith [sq_nonneg (1 + 4 * D.ε)]
  have hΛ1 : 1 ≤ Λ := hc₁1.trans hΛc
  induction j with
  | zero =>
    have hρ := D.ρ_pos hj
    simp only [pow_zero, one_mul, zero_add, Finset.range_one, Finset.sum_singleton]
    have : ‖WithLp.toLp 2 (D.p 0)‖ = D.ρ 0 := by simp [ρ, D.p_zero, D.r_zero]
    rw [this]
    field_simp
    exact le_rfl
  | succ j ih =>
    have hjm : j < m := Nat.lt_of_succ_lt hj
    have ih' := ih hjm (fun i hi => hτ i (hi.trans (Nat.lt_succ_self j)))
    have hstep := norm_p_succ_sq_le D hjm ht0 (hτ j (Nat.lt_succ_self j))
    obtain ⟨hδ0, hδ⟩ := δ_bounds_ratio D hjm
    have hρ := D.ρ_pos hjm
    have hR := D.ρ_pos hj
    set R := D.ρ (j + 1)
    set Sj := ∑ i ∈ Finset.range (j + 1), (D.ρ i ^ 2)⁻¹ with hSj
    have hS0 : 0 ≤ Sj := Finset.sum_nonneg fun i _ => by positivity
    have hδ2 : D.δ j ^ 2 ≤ (1 + 4 * D.ε) ^ 2 * (R ^ 2 / D.ρ j ^ 2) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hδ0 hδ 2
    have hQ : D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2 ≤
        (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj := by
      calc D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2
          ≤ ((1 + 4 * D.ε) ^ 2 * (R ^ 2 / D.ρ j ^ 2) ^ 2) * (Λ ^ j * D.ρ j ^ 4 * Sj) :=
            mul_le_mul hδ2 ih' (sq_nonneg _) (by positivity)
        _ = (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj := by
            field_simp
    rw [Finset.sum_range_succ, ← hSj]
    refine hstep.trans ?_
    have hR2 : R ^ 2 = R ^ 4 * (R ^ 2)⁻¹ := by field_simp
    have hΛj : c₁ ≤ Λ ^ (j + 1) := hΛc.trans (le_self_pow₀ hΛ1 (Nat.succ_ne_zero j))
    have hR4 : 0 ≤ R ^ 4 * (R ^ 2)⁻¹ := by positivity
    calc c₁ * (R ^ 2 + D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2)
        ≤ c₁ * (R ^ 4 * (R ^ 2)⁻¹ + (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj) := by
          rw [← hR2]; gcongr
      _ = c₁ * (R ^ 4 * (R ^ 2)⁻¹) + Λ ^ (j + 1) * R ^ 4 * Sj := by
          rw [hΛ, pow_succ]; ring
      _ ≤ Λ ^ (j + 1) * (R ^ 4 * (R ^ 2)⁻¹) + Λ ^ (j + 1) * R ^ 4 * Sj := by
          gcongr
      _ = Λ ^ (j + 1) * R ^ 4 * (Sj + (R ^ 2)⁻¹) := by ring

/-- Spectral consequences of an input certificate for a nonempty run. -/
private theorem certificate_spectral_facts {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a') :
    0 < a ∧ a ≤ a' ∧ specNorm C.A ≤ a' := by
  have ha := lt_of_le_of_lt S.d_nonneg S.d_lt
  have hn := C.n_pos
  have hA := C.isHermitian
  have h0 := hA.spectrum_subset_iff.mp hs 0 (by simpa using hn)
  have haa' := h0.1.trans h0.2
  refine ⟨ha, haa', ?_⟩
  have hc : n - 1 + 1 = Fintype.card (Fin n) := by simp; omega
  rw [hA.specNorm_eq_max hc]
  have h1 := hA.spectrum_subset_iff.mp hs (n - 1) (by omega)
  rw [abs_of_pos (ha.trans_le h0.1), abs_of_pos (ha.trans_le h1.1)]
  exact max_le h0.2 h1.2

/-- The remaining scalar bounds in an input certificate are nonnegative. -/
private theorem certificate_nonneg {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a') :
    0 ≤ S.K ∧ 0 ≤ S.B := by
  obtain ⟨ha, haa', -⟩ := C.certificate_spectral_facts hs S
  have ha' := ha.trans_le haa'
  have hε := C.ε_nonneg
  have hleft : 0 < a' * (1 + C.ε) ^ 2 := by positivity
  have hK : 0 < S.K := pos_of_mul_pos_left (hleft.trans_le S.curvature_le)
    S.curvature_margin.le
  have hB : 0 < (1 + 4 * C.ε) * (a' + S.d) := by have := S.d_nonneg; positivity
  exact ⟨hK.le, (hB.trans_le S.coefficient_le).le⟩

/-- The computed step times the computed curvature is bounded by the perturbed residual norm. -/
private theorem γ_mul_μ_le {j : ℕ} (hj : j < k) :
    C.γ j * C.μ j ≤ (1 + C.ε) ^ 2 * C.ρ j ^ 2 := by
  rw [C.γ_mul_μ hj, C.ν_eq' hj.le]
  have hθ := (abs_le.mp (C.abs_θ_le j hj.le)).2
  obtain ⟨hl, hu⟩ := abs_le.mp (C.abs_eγ_le j hj)
  have hε := C.ε_nonneg
  have hε1 := C.ε_le
  have h := mul_le_mul (show 1 + C.θ j ≤ 1 + C.ε by linarith)
    (show 1 + C.eγ j ≤ 1 + C.ε by linarith) (by linarith : 0 ≤ 1 + C.eγ j)
    (by positivity : 0 ≤ 1 + C.ε)
  have := mul_le_mul_of_nonneg_left h (sq_nonneg (C.ρ j))
  nlinarith only [this]

/-- A positive curvature margin gives the certificate's scaled step bound, without an
accumulated-error premise. The spectrum lies in $[a,a']$ and the scalar certificate is feasible.
No printed source. -/
theorem specNorm_mul_γ_mul_norm_p_sq_le_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k) :
    specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ S.K * C.ρ j ^ 2 := by
  obtain ⟨ha, haa', hspec⟩ := C.certificate_spectral_facts hs S
  have ha' := ha.le.trans haa'
  have hε := C.ε_nonneg
  have hγ := (C.γ_pos hj).le
  set Q := ‖WithLp.toLp 2 (C.p j)‖
  have hQ : 0 ≤ Q := norm_nonneg _
  have hlow : a * Q ^ 2 ≤ C.p j ⬝ᵥ (C.A *ᵥ C.p j) := by
    have horder : a • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ C.A :=
      (C.isHermitian.smul_one_le_iff_spectrum_subset_Ici a).2 fun x hx => (hs hx).1
    have h := re_quadForm_le_re_quadForm_of_le horder (C.p j)
    rw [re_quadForm_real_smul_one] at h
    simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using h
  have hes : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * Q ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have he := C.norm_es_le j hj
    calc Q * ‖WithLp.toLp 2 (C.es j)‖ ≤ Q * (C.ε * specNorm C.A * Q) :=
          mul_le_mul_of_nonneg_left he hQ
      _ ≤ Q * (C.ε * a' * Q) := by gcongr
      _ = _ := by ring
  have hsn : ‖WithLp.toLp 2 (C.s j)‖ ≤ (1 + C.ε) * a' * Q :=
    (C.norm_s_le hj).trans (by gcongr)
  have heμ : |C.eμ j| ≤ C.ε * (1 + C.ε) * a' * Q ^ 2 := by
    refine (C.abs_eμ_le j hj).trans ?_
    calc C.ε * Q * ‖WithLp.toLp 2 (C.s j)‖ ≤ C.ε * Q * ((1 + C.ε) * a' * Q) := by gcongr
      _ = _ := by ring
  have hμ : (a - C.ε * (2 + C.ε) * a') * Q ^ 2 ≤ C.μ j := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
    nlinarith only [hlow, hes, heμ, neg_abs_le (C.p j ⬝ᵥ C.es j), neg_abs_le (C.eμ j)]
  have hstep := (mul_le_mul_of_nonneg_left hμ hγ).trans (C.γ_mul_μ_le hj)
  have h1 := mul_le_mul_of_nonneg_left hstep ha'
  have h2 := mul_le_mul_of_nonneg_right S.curvature_le (sq_nonneg (C.ρ j))
  have h3 := mul_le_mul_of_nonneg_right hspec (mul_nonneg hγ (sq_nonneg Q))
  have h4 := mul_le_mul_of_nonneg_left h3 S.curvature_margin.le
  apply (mul_le_mul_iff_right₀ S.curvature_margin).mp
  nlinarith only [h1, h2, h4]

/-- Squared direction bounds give the norm bounds consumed by the local-error estimates. -/
private theorem norm_p_le_of_sq_le {P : ℝ} (hP0 : 0 ≤ P) {j : ℕ}
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ P ^ 2 * C.ρ j ^ 2) :
    ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hP0 (C.ρ_nonneg j)) two_ne_zero).mp
  simpa only [mul_pow] using hP

/-- The posterior model of a prefix fits the certificate's global error budget. -/
private theorem prefix_frobNorm_le {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ k)
    (hP : ∀ i < m, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2)
    (hB : ∀ i, i + 1 < m → C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i) :
    frobNorm ((C.take m hm hmk).backwardH - (C.take m hm hmk).dilatedH) ≤ S.d := by
  obtain ⟨ha, haa', hspec⟩ := C.certificate_spectral_facts hs S
  obtain ⟨hK0, hB0⟩ := C.certificate_nonneg hs S
  have hε := C.ε_nonneg
  have ha' := ha.le.trans haa'
  have hP0 := S.P_nonneg
  have hN := specNorm_nonneg C.A
  have hP' : ∀ i < m, ‖WithLp.toLp 2 ((C.take m hm hmk).p i)‖ ≤
      S.P * (C.take m hm hmk).ρ i := fun i hi => C.norm_p_le_of_sq_le hP0 (hP i hi)
  have h := (C.take m hm hmk).frobNorm_backwardH_sub_dilatedH_le_geom_sum_of_certificates
    hP' hB hB0
  refine h.trans (le_trans ?_ S.backward_le)
  change normalizedBackwardBound m (8 * C.ε * (specNorm C.A * (1 + S.P) ^ 2 + S.B))
    (cgAdjacentInnerFactor m C.ε * (specNorm C.A * (1 + S.P) ^ 2 + S.B * (1 + S.P))) ≤ _
  have hf : 8 * C.ε * (specNorm C.A * (1 + S.P) ^ 2 + S.B) ≤
      8 * C.ε * (a' * (1 + S.P) ^ 2 + S.B) := by gcongr
  have hp : cgAdjacentInnerFactor m C.ε *
      (specNorm C.A * (1 + S.P) ^ 2 + S.B * (1 + S.P)) ≤
      cgAdjacentInnerFactor k C.ε * (a' * (1 + S.P) ^ 2 + S.B * (1 + S.P)) :=
    mul_le_mul (cgAdjacentInnerFactor_mono hε hmk) (by gcongr) (by positivity)
      (cgAdjacentInnerFactor_nonneg _ hε)
  have hmR : (m : ℝ) ≤ k := by exact_mod_cast hmk
  rw [normalizedBackwardBound, normalizedBackwardBound]
  have hp0 := cgAdjacentInnerFactor_nonneg m hε
  gcongr

/-- The spectrum of a certified prefix retains the chosen positive margin. -/
private theorem prefix_spectrum_subset {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ k)
    (hP : ∀ i < m, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2)
    (hB : ∀ i, i + 1 < m → C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i) :
    spectrum ℝ (C.take m hm hmk).backwardH ⊆ Set.Icc (a - S.d) (a' + S.d) :=
  (C.take m hm hmk).toNormalizedLanczosData.spectrum_backwardH_subset_Icc hs
    (C.prefix_frobNorm_le hs S hm hmk hP hB)

/-- Earlier step certificates control the residual-ratio sum at the next step. -/
private theorem certificate_residual_ratios {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k)
    (hP : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2)
    (hB : ∀ i, i + 1 < j → C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i) :
    ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 ≤ (a' + S.d) / (a - S.d) := by
  obtain ⟨ha, haa', -⟩ := C.certificate_spectral_facts hs S
  have hd := S.d_nonneg
  rcases Nat.eq_zero_or_pos j with h0 | hj0
  · subst j
    have hρ := C.ρ_pos C.k_pos
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [div_self (by positivity)]
    exact (one_le_div (sub_pos.mpr S.d_lt)).2 (by linarith)
  · exact (C.take j hj0 hj.le).sum_ρ_sq_div_ρ_sq_le (sub_pos.mpr S.d_lt)
      (C.prefix_spectrum_subset hs S hj0 hj.le hP hB) le_rfl

/-- Earlier direction bounds give a uniform geometric line-search bound before the next step. -/
private theorem certificate_lineSearch {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k)
    (hP : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2) :
    ∀ i < j, |C.p i ⬝ᵥ C.r (i + 1)| ≤
      (cgLineSearchFactor (k - 1) C.ε * (1 + S.P + S.K)) * C.ρ i ^ 2 := by
  intro i hi
  have hj0 : 0 < j := by omega
  obtain ⟨hK0, -⟩ := C.certificate_nonneg hs S
  have hP0 := S.P_nonneg
  have hP' : ∀ l < j, ‖WithLp.toLp 2 ((C.take j hj0 hj.le).p l)‖ ≤
      S.P * (C.take j hj0 hj.le).ρ l := fun l hl => C.norm_p_le_of_sq_le hP0 (hP l hl)
  have hK' : ∀ l < j, specNorm (C.take j hj0 hj.le).A * (C.take j hj0 hj.le).γ l *
      ‖WithLp.toLp 2 ((C.take j hj0 hj.le).p l)‖ ^ 2 ≤
      S.K * (C.take j hj0 hj.le).ρ l ^ 2 := fun l hl =>
    C.specNorm_mul_γ_mul_norm_p_sq_le_of_certificate hs S (hl.trans hj)
  have h := (C.take j hj0 hj.le).abs_p_dotProduct_r_succ_le_geom_sum hP' hK' hi
  refine h.trans ?_
  change cgLineSearchFactor (i + 1) C.ε * (1 + S.P + S.K) * C.ρ i ^ 2 ≤ _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (cgLineSearchFactor_mono C.ε_nonneg (by omega))
      (by positivity)) (sq_nonneg _)

/-- The geometric direction recursion and prefix residual ratios close the next direction bound. -/
private theorem certificate_direction {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k)
    (hP : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2)
    (hB : ∀ i, i + 1 < j → C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ S.P ^ 2 * C.ρ j ^ 2 := by
  obtain ⟨hK0, -⟩ := C.certificate_nonneg hs S
  have hε := C.ε_nonneg
  have hP0 := S.P_nonneg
  set t := cgLineSearchFactor (k - 1) C.ε * (1 + S.P + S.K)
  have ht0 : 0 ≤ t := mul_nonneg (cgLineSearchFactor_nonneg _ hε) (by positivity)
  set Λ := (1 + 3 * t + 4 * C.ε + 2 * C.ε ^ 2) * (1 + 4 * C.ε) ^ 2
  have hΛ1 : 1 ≤ Λ := by dsimp only [Λ]; nlinarith [sq_nonneg C.ε]
  have hΛj : Λ ^ j ≤ Λ ^ (k - 1) := pow_le_pow_right₀ hΛ1 (by omega)
  have hu := C.norm_p_sq_le_sum_inv ht0 hj (C.certificate_lineSearch hs S hj hP)
  have hS := C.certificate_residual_ratios hs S hj hP hB
  have hsum : C.ρ j ^ 4 * ∑ i ∈ Finset.range (j + 1), (C.ρ i ^ 2)⁻¹ =
      C.ρ j ^ 2 * ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [mul_assoc, hsum] at hu
  have hbound : Λ ^ (k - 1) * ((a' + S.d) / (a - S.d)) ≤ S.P ^ 2 := S.direction_le
  have hratio0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 := by positivity
  have h1 := mul_le_mul hΛj hS hratio0 (pow_nonneg (by linarith : 0 ≤ Λ) _)
  have h2 := mul_le_mul_of_nonneg_right (h1.trans hbound) (sq_nonneg (C.ρ j))
  dsimp only [Λ] at h2
  nlinarith only [hu, h2]

/-- A prefix model through the current step closes its coefficient bounds. -/
private theorem certificate_coefficients {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k)
    (hP : ∀ i < j + 1, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2)
    (hB : ∀ i < j, C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i) :
    C.lanczosβ (j + 1) ≤ S.B ∧ C.δ j ≤ S.B * C.γ j := by
  obtain ⟨ha, haa', -⟩ := C.certificate_spectral_facts hs S
  have hε := C.ε_nonneg
  have hd := S.d_nonneg
  have hu : 0 < a' + S.d := by linarith
  set D := C.take (j + 1) (Nat.succ_pos j) hj
  have hspec := C.prefix_spectrum_subset hs S (Nat.succ_pos j) hj hP
    (fun i hi => hB i (by omega))
  have hPD : D.backwardH.PosDef :=
    D.isHermitian_backwardH.posDef_of_spectrum_subset_Icc (sub_pos.mpr S.d_lt) hspec
  have hγ := D.cgAlpha_backwardH_of_posDef hPD (Nat.lt_succ_self j)
  have hr0 := D.norm_cgState_backwardH_r_of_posDef hPD (Nat.le_succ j)
  have hr1 := D.norm_cgState_backwardH_r_of_posDef hPD (le_refl (j + 1))
  have hρ := C.ρ_pos hj
  have hγpos := C.γ_pos hj
  have hrne : (cgState D.backwardH D.dilatedRhs 0 j).r ≠ 0 := by
    intro h0
    rw [h0, WithLp.toLp_zero, norm_zero] at hr0
    change 0 = C.ρ j at hr0
    linarith
  have hγl := hPD.one_div_le_cgAlpha hspec D.dilatedRhs 0 j hrne
  have hr := hPD.norm_cgState_r_succ_sq_div_le (sub_pos.mpr S.d_lt) hspec D.dilatedRhs j
  rw [hγ] at hγl hr
  rw [hr0, hr1] at hr
  change 1 / (a' + S.d) ≤ C.γ j at hγl
  change C.ρ (j + 1) ^ 2 ≤ (a' + S.d) * C.γ j * C.ρ j ^ 2 at hr
  have hlγ : 1 ≤ (a' + S.d) * C.γ j := by
    rw [div_le_iff₀ hu] at hγl
    nlinarith only [hγl]
  have huB : a' + S.d ≤ S.B :=
    (le_mul_of_one_le_left hu.le (by linarith : 1 ≤ 1 + 4 * C.ε)).trans S.coefficient_le
  obtain ⟨-, hδ⟩ := δ_bounds_ratio C hj
  constructor
  · have hρ1 : C.ρ (j + 1) ≤ (a' + S.d) * C.γ j * C.ρ j := by
      apply (pow_le_pow_iff_left₀ (C.ρ_nonneg _) (by positivity) two_ne_zero).mp
      calc C.ρ (j + 1) ^ 2 ≤ (a' + S.d) * C.γ j * C.ρ j ^ 2 := hr
        _ ≤ (a' + S.d) * C.γ j * C.ρ j ^ 2 * ((a' + S.d) * C.γ j) :=
          le_mul_of_one_le_right (by positivity) hlγ
        _ = _ := by ring
    simp only [lanczosβ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    rw [div_le_iff₀ (by positivity : 0 < C.γ j * C.ρ j)]
    have hBγρ := mul_le_mul_of_nonneg_right huB (mul_nonneg hγpos.le hρ.le)
    exact hρ1.trans (by nlinarith only [hBγρ])
  · calc C.δ j ≤ (1 + 4 * C.ε) * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := hδ
      _ ≤ (1 + 4 * C.ε) * ((a' + S.d) * C.γ j) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_iff₀ (by positivity)).2 hr
      _ ≤ S.B * C.γ j := by
        have := mul_le_mul_of_nonneg_right S.coefficient_le hγpos.le
        nlinarith only [this]

/-- The single prefix induction behind the input-based certificate bounds. -/
private theorem certificate_induction {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j ≤ k) :
    ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2 ∧
      C.lanczosβ (i + 1) ≤ S.B ∧ C.δ i ≤ S.B * C.γ i := by
  induction j with
  | zero => intro i hi; omega
  | succ j ih =>
    have hjk : j < k := hj
    have IH := ih hjk.le
    have hP := C.certificate_direction hs S hjk (fun i hi => (IH i hi).1)
      (fun i hi => (IH i (by omega)).2)
    have hP' : ∀ i < j + 1, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ S.P ^ 2 * C.ρ i ^ 2 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact (IH i hi).1
      · exact hP
    have hB := C.certificate_coefficients hs S hjk hP' (fun i hi => (IH i hi).2)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact IH i hi
    · exact ⟨hP, hB⟩

/-- A feasible input certificate and spectrum in $[a,a']$ bound every taken direction by
$\|\mathbf{p}_j\|^2\le P^2\rho_j^2$, $j<k$. No printed source. -/
theorem norm_p_sq_le_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ S.P ^ 2 * C.ρ j ^ 2 :=
  (C.certificate_induction hs S le_rfl j hj).1

/-- A feasible input certificate and spectrum in $[a,a']$ bound every Lanczos coefficient by
$\beta_{j+1}\le B$, $j<k$, including a zero terminal coefficient. No printed source. -/
theorem lanczosβ_succ_le_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k) : C.lanczosβ (j + 1) ≤ S.B :=
  (C.certificate_induction hs S le_rfl j hj).2.1

/-- A feasible input certificate and spectrum in $[a,a']$ give
$\delta_j\le B\gamma_j$, $j<k$. No printed source. -/
theorem δ_le_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j < k) : C.δ j ≤ S.B * C.γ j :=
  (C.certificate_induction hs S le_rfl j hj).2.2

/-- **Input-certified CG backward error**: a feasible input certificate and spectrum in $[a,a']$
bound the backward model's Frobenius
error by the chosen distance $d$, without a fixed iteration-precision threshold. The positive
margin $a-d$ is part of the scalar certificate. No printed source.
Result: cg-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a') :
    frobNorm (C.backwardH - C.dilatedH) ≤ S.d := by
  have h := C.prefix_frobNorm_le hs S C.k_pos le_rfl
    (fun i hi => C.norm_p_sq_le_of_certificate hs S hi)
    (fun i hi => ⟨C.lanczosβ_succ_le_of_certificate hs S (by omega),
      C.δ_le_of_certificate hs S (by omega)⟩)
  exact h

/-- The spectrum of a run's backward model lies in $[a-d,a'+d]$ when its input matrix has
spectrum in $[a,a']$ and the scalar backward certificate is feasible. No printed source. -/
theorem spectrum_backwardH_subset_Icc_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a') :
    spectrum ℝ C.backwardH ⊆ Set.Icc (a - S.d) (a' + S.d) :=
  C.toNormalizedLanczosData.spectrum_backwardH_subset_Icc hs
    (C.frobNorm_backwardH_sub_dilatedH_le_of_certificate hs S)

end CGRun

end NLAlib
