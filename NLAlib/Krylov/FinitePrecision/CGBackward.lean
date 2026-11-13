/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGCertificates

/-!
# An a priori backward model for finite-precision conjugate gradients

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under the smallness hypothesis
$$\text{(H)}\qquad k^2\sqrt{k}\,\varepsilon\,\kappa^2 \le 10^{-5},$$
the run certificates are bounded a priori ($\|\mathbf{p}_j\|^2 \le 3.3\kappa\|\mathbf{r}_j\|^2$,
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\|\mathbf{r}_j\|^2$, $\beta_{j+1},
\delta_j/\gamma_j \le 1.6a'$). The backward model of the run
satisfies <!-- value cgBackwardFactor k -->
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
6000k^2\sqrt{k}\,\varepsilon\,\kappa\,a' \le a/2 .$$
Exact CG on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots, \mathbf{0}))$ computes the
computed step lengths $\gamma_j$ exactly and residuals of exactly the computed norms
$\|\mathbf{r}_j\|$; its $\tilde{\mathbf{H}}$-norm error decreases by exactly
$\gamma_j\|\mathbf{r}_j\|^2$ per step, the estimator of [StrakosTichy2002, (4.9)]; and its
squared error at step $k$ is $\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j
\|\mathbf{r}_j\|^2$ up to $2\|\mathbf{b}\|^2c/a^2$, $c$ the model distance.

The fixed bounds are a scalar specialization of `NLAlib.CGBackwardCertificate` with
$P=\sqrt{3.3\kappa}$, $K=1.05\kappa$, $B=1.6a'$ and $d=a/2$. The single prefix induction
lives in `NLAlib/Krylov/FinitePrecision/CGCertificates.lean`: earlier certificates construct
positive definite prefix models, which reproduce the computed coefficients and residual norms
and bound the next direction. This file checks the scalar feasibility conditions under (H)
and derives its numerical results from that general engine.

Validity range: for $\varepsilon > 0$, (H) bounds
$k \le (10^{-5}/(\varepsilon\kappa^2))^{2/5}$, improving the earlier exponent $1/3$.
The a posteriori model of `NLAlib/Krylov/FinitePrecision/CGRunModel.lean` has no such limit.

Literature. [Greenbaum1989] states the backward model for perturbed recurrences, with a
perturbation of order $\varepsilon^{1/4}$, and does not bound the perturbation terms of CG in
terms of $\varepsilon$ [MeurantStrakos2006, §5.2]; [GreenbaumLiuChen2021] derive the terms and
check them numerically. The Chebyshev rate of the computed residuals is qualitatively
[Greenbaum1989].

Constants are unoptimised.

## Main definitions

* `NLAlib.cgBackwardFactor`: the fixed-smallness backward factor.

## Main results

* `NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`,
  `NLAlib.CGRun.lanczosβ_succ_le`, `NLAlib.CGRun.δ_le`, `NLAlib.CGRun.ρ_le`: a priori
  certificates.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`: the a priori backward model.
* `NLAlib.CGRun.cgAlpha_backwardH`, `NLAlib.CGRun.norm_cgState_backwardH_r`: exact CG on the
  model reproduces the run.
* `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`,
  `NLAlib.CGRun.abs_quadForm_backwardH_sub_cgIterate_sub_le`: the model's errors in terms of the
  computed coefficients.
* `NLAlib.CGRun.ρ_le_chebyshev_of_spectrum_backwardH`,
  `NLAlib.CGRun.ρ_le_chebyshev_of_frobNorm_le`: residual bounds retaining the certified model
  interval, with no horizon hypothesis; the run requires only local $\varepsilon\le1/100$.
* `NLAlib.CGRun.ρ_le_chebyshev_of_certificate`: residual decay from input-only scalar conditions.
* `NLAlib.CGRun.ρ_le_chebyshev`: the a priori corollary with ratio $2\kappa + 1$.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The factor in the a priori CG backward bound, with
value <!-- value cgBackwardFactor k --> $6000k^2\sqrt{k}$.
No printed source. It replaces the earlier bound $40000k^3$ using the stacked dilation
estimate; the run's local orthogonality defect still grows with the iteration count. -/
noncomputable irreducible_def cgBackwardFactor (k : ℕ) : ℝ :=
  6000 * (k : ℝ) ^ 2 * Real.sqrt k

/-- The CG backward factor is nonnegative. -/
theorem cgBackwardFactor_nonneg (k : ℕ) : 0 ≤ cgBackwardFactor k := by
  rw [cgBackwardFactor_def]
  positivity

/-- The CG backward factor has the comparison
bound <!-- value cgBackwardFactor k --> $6000k^2\sqrt{k}$. -/
theorem cgBackwardFactor_le (k : ℕ) :
    cgBackwardFactor k ≤ 6000 * (k : ℝ) ^ 2 * Real.sqrt k := by
  rw [cgBackwardFactor_def]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The Rayleigh bounds of a symmetric matrix with spectrum in $[l, l']$. -/
private theorem quadForm_bounds {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.IsHermitian) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') (x : m → ℝ) :
    l * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (H *ᵥ x) ∧ x ⬝ᵥ (H *ᵥ x) ≤ l' * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos (Fintype.card m) with h0 | hpos
  · have : IsEmpty m := Fintype.card_eq_zero_iff.mp h0
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card m := ⟨Fintype.card m - 1, by omega⟩
    have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc x
    have h2 := hH.re_quadForm_le_eigenvalue_zero_mul x
    simp only [quadForm_def, star_trivial, RCLike.re_to_real] at h1 h2
    have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
    have e2 := (hH.spectrum_subset_iff.mp hs 0 hpos).2
    have hx := sq_nonneg ‖WithLp.toLp 2 x‖
    exact ⟨(mul_le_mul_of_nonneg_right e1 hx).trans h1,
      h2.trans (mul_le_mul_of_nonneg_right e2 hx)⟩

/-- A nonempty spectrum in $[l, l']$ forces $l \le l'$. -/
private theorem le_of_spectrum {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {H : Matrix m m ℝ} (hH : H.IsHermitian) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') :
    l ≤ l' :=
  let h := hH.spectrum_subset_iff.mp hs 0 Fintype.card_pos
  h.1.trans h.2

/-! ### Helpers for the a priori induction -/

/-- The elementary consequences of the spectral hypothesis and of (H) for a run of $m$ steps:
$a \le a'$, $\kappa \ge 1$, $\|\mathbf{A}\|_2 \le a'$, and the smallness of $m^i\varepsilon\kappa$,
$i \le 2$. -/
private theorem small_facts {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon m D.ε (a' / a)) :
    a ≤ a' ∧ 1 ≤ a' / a ∧ specNorm D.A ≤ a' ∧ D.ε ≤ 1 / 10 ^ 5 ∧
      D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (m : ℝ) * D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (m : ℝ) ^ 2 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (m : ℝ) ^ 2 * Real.sqrt m * D.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  have hn := D.n_pos
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hherm := D.isHermitian
  have haa' : a ≤ a' := le_of_spectrum hherm hs
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast D.k_pos
  have hε := D.ε_nonneg
  have hspec : specNorm D.A ≤ a' := by
    have hc : n - 1 + 1 = Fintype.card (Fin n) := by simp; omega
    rw [hherm.specNorm_eq_max hc]
    have e0 := hherm.spectrum_subset_iff.mp hs 0 (by simp; omega)
    have e1 := hherm.spectrum_subset_iff.mp hs (n - 1) (by simp; omega)
    rw [abs_of_pos (ha.trans_le e0.1), abs_of_pos (ha.trans_le e1.1)]
    exact max_le e0.2 e1.2
  have hκ2 : a' / a ≤ (a' / a) ^ 2 := by nlinarith
  have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hm3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * Real.sqrt m := by
    have hs : 1 ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr hm
    nlinarith
  have h3 : (m : ℝ) ^ 2 * Real.sqrt m * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by
      have := mul_le_mul_of_nonneg_left hκ2
        (by positivity : 0 ≤ (m : ℝ) ^ 2 * Real.sqrt m * D.ε)
      linarith) hsmall
  have h2 : (m : ℝ) ^ 2 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm3 (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h3
  have h1 : (m : ℝ) * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm2 (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h2
  have h0 : D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h1
  have he : D.ε ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_left hκ hε; nlinarith) h0
  exact ⟨haa', hκ, hspec, he, h0, h1, h2, h3⟩

/-- The scalar comparison used both to construct the certificate and to report its
sharper final backward bound. -/
private theorem normalizedBackwardBound_le_cgBackwardFactor {m : ℕ} {ε κ N a' : ℝ}
    (hmpos : 0 < m) (hε : 0 ≤ ε) (hκ : 1 ≤ κ) (hN0 : 0 ≤ N) (hN : N ≤ a') :
    normalizedBackwardBound m (8 * ε * (N * (1 + Real.sqrt (33 / 10 * κ)) ^ 2 + 8 / 5 * a'))
      (16 * (m : ℝ) * ε * (N * (1 + Real.sqrt (33 / 10 * κ)) ^ 2 +
        8 / 5 * a' * (1 + Real.sqrt (33 / 10 * κ) + 21 / 20 * κ))) ≤
      cgBackwardFactor m * ε * κ * a' := by
  have ha' : 0 ≤ a' := hN0.trans hN
  set P := Real.sqrt (33 / 10 * κ) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * κ := Real.sq_sqrt (by positivity)
  have h1P : (1 + P) ^ 2 ≤ 86 / 10 * κ := by nlinarith [sq_nonneg (1 - P)]
  have hPK : 1 + P + 21 / 20 * κ ≤ 42 / 10 * κ := by nlinarith [sq_nonneg (1 - P)]
  have hsP : N * (1 + P) ^ 2 ≤ a' * (86 / 10 * κ) :=
    mul_le_mul hN h1P (by positivity) ha'
  have hBκ : 8 / 5 * a' ≤ 8 / 5 * (κ * a') := by nlinarith
  have hf : 8 * ε * (N * (1 + P) ^ 2 + 8 / 5 * a') ≤
      8 * ε * (102 / 10 * (κ * a')) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have hp : 16 * (m : ℝ) * ε * (N * (1 + P) ^ 2 + 8 / 5 * a' *
      (1 + P + 21 / 20 * κ)) ≤ 16 * (m : ℝ) * ε * (1532 / 100 * (κ * a')) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 8 / 5 * a' * (1 + P + 21 / 20 * κ) ≤ 8 / 5 * a' * (42 / 10 * κ) :=
      mul_le_mul_of_nonneg_left hPK (by positivity)
    nlinarith
  rw [normalizedBackwardBound, cgBackwardFactor_def]
  have h := add_le_add (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 22 * (m : ℝ) ^ 2))
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 17 * (m : ℝ) * Real.sqrt m))
  refine h.trans ?_
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hsqrt : 1 ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr hm
  have hE : 0 ≤ (m : ℝ) ^ 2 * (ε * (κ * a')) := by positivity
  have hscale := mul_le_mul_of_nonneg_right hsqrt hE
  nlinarith only [hscale, hE]

/-- **The model from the a priori certificates**: with $\Pi^2 = 3.3\kappa$, $K = 1.05\kappa$,
$B = 1.6a'$ the a posteriori engine gives <!-- value cgBackwardFactor m -->
$6000m^2\sqrt{m}\varepsilon\kappa a'$. -/
private theorem frobNorm_le_of_apriori {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon m D.ε (a' / a))
    (hP : ∀ i < m, ‖WithLp.toLp 2 (D.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * D.ρ i ^ 2)
    (hK : ∀ i < m, specNorm D.A * D.γ i * ‖WithLp.toLp 2 (D.p i)‖ ^ 2 ≤
      21 / 20 * (a' / a) * D.ρ i ^ 2)
    (hB : ∀ i, i + 1 < m → D.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ D.δ i ≤ 8 / 5 * a' * D.γ i) :
    frobNorm (D.backwardH - D.dilatedH) ≤ cgBackwardFactor m * D.ε * (a' / a) * a' := by
  obtain ⟨haa', hκ, hspec, _, _, hmεκ, -⟩ := small_facts D ha hs hsmall
  have hε := D.ε_nonneg
  have hwindow : (m : ℝ) * D.ε ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ (m : ℝ) * D.ε)
    nlinarith
  set κ := a' / a with hκdef
  have ha' : 0 < a' := ha.trans_le haa'
  set P := Real.sqrt (33 / 10 * κ) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * κ := Real.sq_sqrt (by positivity)
  have hP' : ∀ i < m, ‖WithLp.toLp 2 (D.p i)‖ ≤ P * D.ρ i := fun i hi => by
    have hρ : 0 ≤ D.ρ i := norm_nonneg _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hP2]
    exact hP i hi
  have h := D.frobNorm_backwardH_sub_dilatedH_le_of_certificates hwindow hP' hK hB (by linarith)
  refine h.trans ?_
  exact normalizedBackwardBound_le_cgBackwardFactor D.k_pos hε hκ
    (specNorm_nonneg D.A) hspec

/-- **Weyl localisation from the a priori model bound**: under (H) the model is within $0.06a$ of
$\mathbf{I} \otimes \mathbf{A}$, so its spectrum is in $[a/2, a' + a/2]$. -/
private theorem spectrum_subset_of_frobNorm_le {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon m D.ε (a' / a))
    (hc : frobNorm (D.backwardH - D.dilatedH) ≤ cgBackwardFactor m * D.ε * (a' / a) * a') :
    spectrum ℝ D.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) := by
  have hc' : cgBackwardFactor m * D.ε * (a' / a) * a' ≤ a / 2 := by
    have heq : 6000 * (m : ℝ) ^ 2 * Real.sqrt m * D.ε * (a' / a) * a' =
        6000 * ((m : ℝ) ^ 2 * Real.sqrt m * D.ε * (a' / a) ^ 2) * a := by
      field_simp
    have hε := D.ε_nonneg
    have ha' : 0 ≤ a' := ha.le.trans (small_facts D ha hs hsmall).1
    calc cgBackwardFactor m * D.ε * (a' / a) * a'
        ≤ 6000 * (m : ℝ) ^ 2 * Real.sqrt m * D.ε * (a' / a) * a' := by
          gcongr; exact cgBackwardFactor_le m
      _ = _ := heq
      _ ≤ a / 2 := by
        unfold CGPrecisionHorizon at hsmall
        nlinarith
  have h := NormalizedLanczosData.spectrum_backwardH_subset_Icc (D := D.toNormalizedLanczosData)
    (a := a) (a' := a') hs (hc.trans hc')
  exact h.trans (Set.Icc_subset_Icc (by linarith) le_rfl)

/-- A power of a number close to $1$: $(1 + x)^j \le 11/10$ for $0 \le x \le 1$ and
$jx \le 1/11$. -/
private theorem one_add_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {j : ℕ}
    (hjx : (j : ℝ) * x ≤ 1 / 11) : (1 + x) ^ j ≤ 11 / 10 := by
  have h1 : 1 + (j : ℝ) * (-x) ≤ (1 + -x) ^ j := one_add_mul_le_pow (by linarith) j
  have h2 : (10 : ℝ) / 11 ≤ (1 - x) ^ j := by
    rw [sub_eq_add_neg]; linarith
  have h3 : (1 + x) ^ j * (1 - x) ^ j ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h4 : 0 ≤ (1 + x) ^ j := by positivity
  nlinarith

/-- $\Lambda^j \le 1.1$ for the growth factor of the unrolled direction recursion. -/
private theorem growth_pow_le {ε t : ℝ} {j : ℕ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 5)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10) (hjt : (j : ℝ) * t ≤ 21 / 10 ^ 5)
    (hjε : (j : ℝ) * ε ≤ 1 / 10 ^ 5) :
    ((1 + 3 * t + 4 * ε + 2 * ε ^ 2) * (1 + 4 * ε) ^ 2) ^ j ≤ 11 / 10 := by
  set x := (1 + 3 * t + 4 * ε + 2 * ε ^ 2) * (1 + 4 * ε) ^ 2 - 1 with hxdef
  have hexp : x = 3 * t + 12 * ε + 50 * ε ^ 2 + 24 * (t * ε) + 80 * ε ^ 3 + 48 * (t * ε ^ 2) +
      32 * ε ^ 4 := by rw [hxdef]; ring
  have h1 : ε ^ 2 ≤ ε / 10 ^ 5 := by nlinarith
  have h2 : t * ε ≤ ε / 10 := by nlinarith
  have h3 : ε ^ 3 ≤ ε / 10 ^ 5 := by nlinarith [sq_nonneg ε]
  have h4 : t * ε ^ 2 ≤ ε / 10 ^ 5 := by nlinarith [mul_nonneg ht0 hε]
  have h5 : ε ^ 4 ≤ ε / 10 ^ 5 := by nlinarith [pow_nonneg hε 3]
  have hx0 : 0 ≤ x := by rw [hexp]; positivity
  have hx : x ≤ 3 * t + 15 * ε := by rw [hexp]; linarith
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjx : (j : ℝ) * x ≤ 1 / 11 := by
    have := mul_le_mul_of_nonneg_left hx hj0
    nlinarith
  have := one_add_pow_le hx0 (by linarith) hjx
  rwa [hxdef, add_sub_cancel] at this

/-- The fixed accuracy margins imply the division-free curvature certificate. -/
private theorem curvature_certificate_of_small {ε κ a a' : ℝ} (ha : 0 < a)
    (hε : 0 ≤ ε) (he : ε ≤ 1 / 10 ^ 5) (hκ : 1 ≤ κ) (hεκ : ε * κ ≤ 1 / 10 ^ 5)
    (hκa : κ * a = a') :
    0 < a - ε * (2 + ε) * a' ∧
      a' * (1 + ε) ^ 2 ≤ (21 / 20 * κ) * (a - ε * (2 + ε) * a') := by
  have ha' : 0 < a' := by rw [← hκa]; exact mul_pos (by linarith only [hκ]) ha
  set z := ε * (2 + ε) * κ with hz
  have hzle : z ≤ 3 / 10 ^ 5 := by
    have hprod := mul_le_mul_of_nonneg_right (show 2 + ε ≤ 3 by linarith only [he])
      (show 0 ≤ ε * κ by positivity)
    dsimp [z]
    nlinarith only [hprod, hεκ]
  have hmargin : a - ε * (2 + ε) * a' = (1 - z) * a := by
    rw [← hκa, hz]
    ring
  have hcurv : 0 < a - ε * (2 + ε) * a' := by
    rw [hmargin]
    exact mul_pos (by linarith only [hzle]) ha
  have he2 : ε ^ 2 ≤ ε / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left he hε
    nlinarith only [this]
  have hq : (1 + ε) ^ 2 ≤ 21 / 20 * (1 - z) := by
    nlinarith only [he, he2, hzle]
  have hcurvle : a' * (1 + ε) ^ 2 ≤
      (21 / 20 * κ) * (a - ε * (2 + ε) * a') := by
    calc a' * (1 + ε) ^ 2 ≤ a' * (21 / 20 * (1 - z)) :=
          mul_le_mul_of_nonneg_left hq ha'.le
      _ = _ := by rw [hmargin, ← hκa]; ring
  exact ⟨hcurv, hcurvle⟩

/-- The geometric posterior expression is bounded by the existing numerical factor
under the fixed short-horizon assumptions. -/
private theorem normalizedBackwardBound_geom_le_cgBackwardFactor {m : ℕ} {ε κ a' : ℝ}
    (hmpos : 0 < m) (hε : 0 ≤ ε) (hκ : 1 ≤ κ) (ha' : 0 ≤ a')
    (hwindow : (m : ℝ) * ε ≤ 1 / 100) :
    normalizedBackwardBound m (8 * ε * (a' * (1 + Real.sqrt (33 / 10 * κ)) ^ 2 + 8 / 5 * a'))
      (cgAdjacentInnerFactor m ε * (a' * (1 + Real.sqrt (33 / 10 * κ)) ^ 2 +
        8 / 5 * a' * (1 + Real.sqrt (33 / 10 * κ)))) ≤
      cgBackwardFactor m * ε * κ * a' := by
  set P := Real.sqrt (33 / 10 * κ)
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hp : cgAdjacentInnerFactor m ε *
      (a' * (1 + P) ^ 2 + 8 / 5 * a' * (1 + P)) ≤
      16 * (m : ℝ) * ε * (a' * (1 + P) ^ 2 +
        8 / 5 * a' * (1 + P + 21 / 20 * κ)) := by
    apply mul_le_mul (cgAdjacentInnerFactor_le_mul hε hwindow) ?_ (by positivity) (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (by linarith only [hκ]) (by positivity))
  have hmodel : normalizedBackwardBound m (8 * ε * (a' * (1 + P) ^ 2 + 8 / 5 * a'))
      (cgAdjacentInnerFactor m ε * (a' * (1 + P) ^ 2 + 8 / 5 * a' * (1 + P))) ≤
      cgBackwardFactor m * ε * κ * a' := by
    refine le_trans ?_ (normalizedBackwardBound_le_cgBackwardFactor hmpos hε hκ ha' le_rfl)
    unfold normalizedBackwardBound
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
  exact hmodel

/-- The fixed smallness condition supplies an input-only scalar certificate. The general
certificate theorem, rather than a second induction, supplies all run inequalities. -/
private noncomputable def smallnessCertificate {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    CGBackwardCertificate k C.ε a a' := by
  have hF := small_facts C ha hs hsmall
  have haa' := hF.1
  have hκ := hF.2.1
  have he := hF.2.2.2.1
  have hεκ := hF.2.2.2.2.1
  have hk1 := hF.2.2.2.2.2.1
  have hk2 := hF.2.2.2.2.2.2.1
  have hε := C.ε_nonneg
  have ha' : 0 < a' := ha.trans_le haa'
  set κ := a' / a with hκdef
  set P := Real.sqrt (33 / 10 * κ) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * κ := Real.sq_sqrt (by positivity)
  have hκa : κ * a = a' := div_mul_cancel₀ _ ha.ne'
  have hPK : 1 + P + 21 / 20 * κ ≤ 42 / 10 * κ := by
    nlinarith only [sq_nonneg (1 - P), hP2, hκ]
  have hkε : (k : ℝ) * C.ε ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ (k : ℝ) * C.ε)
    nlinarith only [this, hk1]
  have hwindow : (k : ℝ) * C.ε ≤ 1 / 100 := by linarith only [hkε]
  have hcurvature := curvature_certificate_of_small ha hε he hκ hεκ hκa
  set t := cgLineSearchFactor (k - 1) C.ε * (1 + P + 21 / 20 * κ) with ht
  have ht0 : 0 ≤ t := mul_nonneg (cgLineSearchFactor_nonneg _ hε) (by positivity)
  have hline : cgLineSearchFactor (k - 1) C.ε ≤ 5 * k * C.ε :=
    (cgLineSearchFactor_mono hε (Nat.sub_le k 1)).trans
      (cgLineSearchFactor_le_mul hε hwindow)
  have htle : t ≤ 21 * ((k : ℝ) * C.ε * κ) := by
    have h := mul_le_mul hline hPK (by positivity) (by positivity)
    dsimp [t]
    nlinarith only [h]
  have ht1 : t ≤ 1 / 10 := by nlinarith only [htle, hk1]
  have hkm : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hjt : ((k - 1 : ℕ) : ℝ) * t ≤ 21 / 10 ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_right hkm ht0
    have h2 := mul_le_mul_of_nonneg_left htle (Nat.cast_nonneg k)
    nlinarith only [h1, h2, hk2]
  have hjε : ((k - 1 : ℕ) : ℝ) * C.ε ≤ 1 / 10 ^ 5 :=
    (mul_le_mul_of_nonneg_right hkm hε).trans hkε
  have hΛ := growth_pow_le hε he ht0 ht1 hjt hjε
  have heff : (a' + a / 2) / (a - a / 2) = 2 * κ + 1 := by
    rw [hκdef]
    field_simp
    ring
  have hdir : ((1 + 3 * t + 4 * C.ε + 2 * C.ε ^ 2) * (1 + 4 * C.ε) ^ 2) ^ (k - 1) *
      ((a' + a / 2) / (a - a / 2)) ≤ P ^ 2 := by
    rw [heff, hP2]
    calc _ ≤ 11 / 10 * (2 * κ + 1) :=
          mul_le_mul_of_nonneg_right hΛ (by positivity)
      _ ≤ _ := by linarith only [hκ]
  have hB : (1 + 4 * C.ε) * (a' + a / 2) ≤ 8 / 5 * a' := by
    calc _ ≤ (1 + 4 * C.ε) * (3 / 2 * a') := by gcongr; linarith only [haa']
      _ = ((1 + 4 * C.ε) * (3 / 2)) * a' := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [he]) ha'.le
  have hmodel := normalizedBackwardBound_geom_le_cgBackwardFactor C.k_pos hε hκ ha'.le hwindow
  have hdist : cgBackwardFactor k * C.ε * κ * a' ≤ a / 2 := by
    calc cgBackwardFactor k * C.ε * κ * a'
        ≤ 6000 * (k : ℝ) ^ 2 * Real.sqrt k * C.ε * κ * a' := by
          gcongr
          exact cgBackwardFactor_le k
      _ = 6000 * ((k : ℝ) ^ 2 * Real.sqrt k * C.ε * κ ^ 2) * a := by
          rw [← hκa]
          ring
      _ ≤ a / 2 := by
          have h := mul_le_mul_of_nonneg_right hsmall ha.le
          nlinarith only [h, ha]
  exact {
    P := P
    K := 21 / 20 * κ
    B := 8 / 5 * a'
    d := a / 2
    P_nonneg := hP0
    d_nonneg := by positivity
    d_lt := by linarith only [ha]
    curvature_margin := hcurvature.1
    curvature_le := hcurvature.2
    direction_le := hdir
    coefficient_le := hB
    backward_le := hmodel.trans hdist }

/-- The fixed numerical certificates are a specialization of the general scalar certificate
engine. The prefix induction is proved only in
`NLAlib/Krylov/FinitePrecision/CGCertificates.lean`. -/
private theorem aprioriCertificates {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j ≤ k) :
    ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2 ∧
      C.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ C.δ i ≤ 8 / 5 * a' * C.γ i := by
  let S := C.smallnessCertificate ha hs hsmall
  intro i hi
  have hik : i < k := hi.trans_le hj
  have hP := C.norm_p_sq_le_of_certificate hs S hik
  have hK := C.specNorm_mul_γ_mul_norm_p_sq_le_of_certificate hs S hik
  have hB := C.lanczosβ_succ_le_of_certificate hs S hik
  have hδ := C.δ_le_of_certificate hs S hik
  change ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤
    (Real.sqrt (33 / 10 * (a' / a))) ^ 2 * C.ρ i ^ 2 at hP
  rw [Real.sq_sqrt (by have := (small_facts C ha hs hsmall).2.1; positivity)] at hP
  exact ⟨hP, hK, hB, hδ⟩

/-- **Directions against residuals, a priori**: under (H), $\|\mathbf{p}_j\|^2 \le
3.3\kappa\|\mathbf{r}_j\|^2$ for $j < k$, $\kappa = a'/a$. [StrakosTichy2002, (9.13)] has
$\|\mathbf{p}_j\|/\|\mathbf{r}_j\| \le 1 + j\kappa^{1/2}$ from an imported monotonicity. -/
theorem norm_p_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ j ^ 2 := by
  exact (C.aprioriCertificates ha hs hsmall le_rfl j hj).1

/-- **The curvature certificate, a priori**: under (H),
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\rho_j^2$, $j < k$. -/
theorem specNorm_mul_γ_mul_norm_p_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ j ^ 2 := by
  exact (C.aprioriCertificates ha hs hsmall le_rfl j hj).2.1

/-- **The off-diagonal coefficients, a priori**: under (H), $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j) \le 1.6a'$, $j < k$. -/
theorem lanczosβ_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    C.lanczosβ (j + 1) ≤ 8 / 5 * a' := by
  exact (C.aprioriCertificates ha hs hsmall le_rfl j hj).2.2.1

/-- **The coefficient ratio, a priori**: under (H), $\delta_j \le 1.6a'\gamma_j$, $j < k$. -/
theorem δ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    C.δ j ≤ 8 / 5 * a' * C.γ j := by
  exact (C.aprioriCertificates ha hs hsmall le_rfl j hj).2.2.2

/-! ### The backward model -/

/-- **The a priori backward model of finite-precision CG**: for spectrum in $[a, a']$, $a > 0$,
$\kappa = a'/a$, and (H) $k^2\sqrt{k}\varepsilon\kappa^2 \le 10^{-5}$, the
bound is <!-- value cgBackwardFactor k -->
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
6000k^2\sqrt{k}\,\varepsilon\,\kappa\,a' .$$
No printed source. the module docstring compares it with the literature.
For $\varepsilon > 0$ the validity range is
$k \le (10^{-5}/(\varepsilon\kappa^2))^{2/5}$; the model distance is at most $0.06a$.
Result: cg-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    frobNorm (C.backwardH - C.dilatedH) ≤ cgBackwardFactor k * C.ε * (a' / a) * a' := by
  have h := C.aprioriCertificates ha hs hsmall le_rfl
  exact frobNorm_le_of_apriori C ha hs hsmall (fun i hi => (h i hi).1) (fun i hi => (h i hi).2.1)
    (fun i hi => (h i (by omega)).2.2)

/-- **The model is positive definite with condition number at most $2\kappa + 1$**: under (H)
its spectrum lies in $[a/2, a' + a/2]$. -/
theorem spectrum_backwardH_subset_Icc {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    spectrum ℝ C.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) := by
  exact spectrum_subset_of_frobNorm_le C ha hs hsmall
    (C.frobNorm_backwardH_sub_dilatedH_le ha hs hsmall)

/-- **Exact CG on the model computes the computed step lengths**: under (H), for $j < k$,
the step length of `NLAlib.cgState` on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots))$
from $\mathbf{0}$ is $\gamma_j$. -/
theorem cgAlpha_backwardH {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j < k) :
    cgAlpha C.backwardH (cgState C.backwardH C.dilatedRhs 0 j) = C.γ j := by
  exact C.cgAlpha_backwardH_of_posDef (C.isHermitian_backwardH.posDef_of_spectrum_subset_Icc
    (by positivity : 0 < a / 2) (C.spectrum_backwardH_subset_Icc ha hs hsmall)) hj

/-- **Exact CG on the model has the computed residual norms**: under (H), for $j \le k$,
$\|\tilde{\mathbf{r}}_j\| = \|\mathbf{r}_j\|$. -/
theorem norm_cgState_backwardH_r {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).r‖ = C.ρ j := by
  exact C.norm_cgState_backwardH_r_of_posDef (C.isHermitian_backwardH.posDef_of_spectrum_subset_Icc
    (by positivity : 0 < a / 2) (C.spectrum_backwardH_subset_Icc ha hs hsmall)) hj

/-- **Residual ratios of the run, a priori**: under (H), $\|\mathbf{r}_j\| \le
\sqrt{3\kappa}\,\|\mathbf{r}_i\|$ for $i \le j \le k$ (the computed residual norms are those of
exact CG on a matrix of condition number at most $2\kappa + 1$). This is [StrakosTichy2002,
(7.20)] with the imported monotonicity replaced by the model. -/
theorem ρ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ k) :
    C.ρ j ≤ Real.sqrt (3 * (a' / a)) * C.ρ i := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hPD := C.isHermitian_backwardH.posDef_of_spectrum_subset_Icc
    (by positivity : 0 < a / 2) hspec
  have h := hPD.norm_cgState_r_le (by positivity : 0 < a / 2) hspec C.dilatedRhs hij
  rw [C.norm_cgState_backwardH_r ha hs hsmall hj,
    C.norm_cgState_backwardH_r ha hs hsmall (hij.trans hj)] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (norm_nonneg _))
  have hκ : 1 ≤ a' / a := (small_facts C ha hs hsmall).2.1
  have he : (a' + a / 2) / (a / 2) = 2 * (a' / a) + 1 := by field_simp
  rw [he]
  linarith

/-! ### Helpers for the error relations -/

/-- The bilinear form of a symmetric matrix is symmetric. -/
private theorem dotProduct_mulVec_comm {m : Type*} [Fintype m] {H : Matrix m m ℝ}
    (hT : Hᵀ = H) (u v : m → ℝ) : u ⬝ᵥ (H *ᵥ v) = v ⬝ᵥ (H *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

/-- The dilated matrix acts blockwise. -/
private theorem dilatedH_mulVec_apply (v : Fin n × Fin (k + 1) → ℝ) (i : Fin n)
    (r : Fin (k + 1)) : (C.dilatedH *ᵥ v) (i, r) = (C.A *ᵥ fun j => v (j, r)) i := by
  simp only [dilatedH, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The residual against the energy**: for positive definite $\mathbf{H}$ with spectrum in
$[l, l']$, $\|\mathbf{H}\mathbf{e}\|^2 \le l'\,\mathbf{e}^{\mathsf{T}}\mathbf{H}\mathbf{e}$
(Cauchy–Schwarz for the form of $\mathbf{H}$). -/
private theorem norm_mulVec_sq_le {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.PosDef) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') (e : m → ℝ) :
    ‖WithLp.toLp 2 (H *ᵥ e)‖ ^ 2 ≤ l' * (e ⬝ᵥ (H *ᵥ e)) := by
  have hu : H ≤ l' • (1 : Matrix m m ℝ) :=
    (hH.isHermitian.le_smul_one_iff_spectrum_subset_Iic l').mpr fun x hx => (hs hx).2
  simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using
    hH.posSemidef.norm_toLp_mulVec_sq_le hu e

/-- The norm of a solution of a positive definite system: $\|\mathbf{x}\| \le
\|\mathbf{b}\|/l$ for $\mathbf{H}\mathbf{x} = \mathbf{b}$, spectrum in $[l, l']$, $l > 0$. -/
private theorem norm_le_of_mulVec_eq {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.IsHermitian) {l l' : ℝ} (hl : 0 < l) (hs : spectrum ℝ H ⊆ Set.Icc l l')
    {x b : m → ℝ} (hx : H *ᵥ x = b) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 b‖ / l := by
  have h1 := (quadForm_bounds hH hs x).1
  rw [hx] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm x b)
  rw [le_div_iff₀ hl]
  rcases (norm_nonneg (WithLp.toLp 2 x)).lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; simp

/-- The energy of the solution: $\mathbf{x}^{\mathsf{T}}\mathbf{H}\mathbf{x} \le
\|\mathbf{b}\|^2/l$. -/
private theorem dotProduct_mulVec_le_of_mulVec_eq {m : Type*} [Fintype m] [DecidableEq m]
    {H : Matrix m m ℝ} (hH : H.IsHermitian) {l l' : ℝ} (hl : 0 < l)
    (hs : spectrum ℝ H ⊆ Set.Icc l l') {x b : m → ℝ} (hx : H *ᵥ x = b) :
    x ⬝ᵥ (H *ᵥ x) ≤ ‖WithLp.toLp 2 b‖ ^ 2 / l := by
  have h := norm_le_of_mulVec_eq hH hl hs hx
  rw [hx]
  refine (le_abs_self _).trans ((EuclideanSpace.abs_dotProduct_le_norm x b).trans ?_)
  calc ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 b‖ ≤ ‖WithLp.toLp 2 b‖ / l * ‖WithLp.toLp 2 b‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖WithLp.toLp 2 b‖ ^ 2 / l := by ring

/-- **The computed residual bound from a model interval**: for a $k$-step CG run whose backward
model has spectrum in $[l,l']$, $l>0$, put $\kappa_c=l'/l$. For $j\le k$,
$$\|\mathbf{r}_j\| \le 2\sqrt{\kappa_c}\Bigl(\frac{\sqrt{\kappa_c} - 1}{\sqrt{\kappa_c} + 1}\Bigr)^j
\|\mathbf{b}\| .$$
No horizon condition is imposed; the run requires local $\varepsilon\le1/100$.
This is an upper envelope, not monotonicity of the residual norms. No printed source in this
form; compare the qualitative backward-model discussion in [MeurantStrakos2006, §5.2].
Result: cg-computed-residual-bound -/
theorem ρ_le_chebyshev_of_spectrum_backwardH {l l' : ℝ} (hl : 0 < l)
    (hH : spectrum ℝ C.backwardH ⊆ Set.Icc l l') {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt (l' / l) *
      ((Real.sqrt (l' / l) - 1) / (Real.sqrt (l' / l) + 1)) ^ j *
        ‖WithLp.toLp 2 C.b‖ := by
  have hherm := C.isHermitian_backwardH
  have hPD := hherm.posDef_of_spectrum_subset_Icc hl hH
  have := C.nonempty_index
  have hll' := le_of_spectrum hherm hH
  have hκ : 1 ≤ l' / l := (le_div_iff₀ hl).mpr (by simpa only [one_mul] using hll')
  set xs := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hxs : C.backwardH *ᵥ xs = C.dilatedRhs := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hPD.isUnit), Matrix.one_mulVec]
  have hcheb := hherm.re_quadForm_sub_cgIterate_le_four_mul_pow hl hH hxs 0 j
  rw [sub_zero] at hcheb
  simp only [quadForm_def, star_trivial, RCLike.re_to_real] at hcheb
  set q := (Real.sqrt (l' / l) - 1) / (Real.sqrt (l' / l) + 1) with hq
  have hsq1 : 1 ≤ Real.sqrt (l' / l) := Real.one_le_sqrt.mpr hκ
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hr : (cgState C.backwardH C.dilatedRhs 0 j).r =
      C.backwardH *ᵥ (xs - cgIterate C.backwardH C.dilatedRhs 0 j) := by
    rw [cgState_r_eq, hPD.cgState_x_eq, Matrix.mulVec_sub, hxs]
  have h1 := norm_mulVec_sq_le hPD hH (xs - cgIterate C.backwardH C.dilatedRhs 0 j)
  conv_lhs at h1 => rw [← hr, C.norm_cgState_backwardH_r_of_posDef hPD hj]
  have h2 := dotProduct_mulVec_le_of_mulVec_eq hherm hl hH hxs
  rw [C.norm_dilatedRhs] at h2
  have hl' : 0 ≤ l' := hl.le.trans hll'
  have h3 : C.ρ j ^ 2 ≤ (2 * Real.sqrt (l' / l) * q ^ j * ‖WithLp.toLp 2 C.b‖) ^ 2 := by
    have hq2 : 0 ≤ q ^ (2 * j) := by positivity
    have hsqrt2 : Real.sqrt (l' / l) ^ 2 = l' / l := Real.sq_sqrt (by linarith)
    calc C.ρ j ^ 2 ≤ l' * (4 * q ^ (2 * j) * (xs ⬝ᵥ (C.backwardH *ᵥ xs))) :=
          h1.trans (mul_le_mul_of_nonneg_left hcheb hl')
      _ ≤ l' * (4 * q ^ (2 * j) * (‖WithLp.toLp 2 C.b‖ ^ 2 / l)) := by
          gcongr
      _ = (2 * Real.sqrt (l' / l) * q ^ j * ‖WithLp.toLp 2 C.b‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, hsqrt2, ← pow_mul]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **Computed residual bound from model distance**: a $k$-step CG run with original spectrum in
$[a,a']$ and certified Frobenius model error
$d<a$ has the Chebyshev residual envelope with ratio $\kappa_c=(a'+d)/(a-d)$:
$$\|\mathbf{r}_j\|\le2\sqrt{\kappa_c}
\Bigl(\frac{\sqrt{\kappa_c}-1}{\sqrt{\kappa_c}+1}\Bigr)^j\|\mathbf b\|\quad(j\le k)\,.$$
The run's local $\varepsilon\le1/100$ remains; no horizon condition is needed.
The certificate may come from the a posteriori recurrence bounds.
No printed source.
This bounds the residual envelope for $j\le k$; it does not assert stepwise monotonicity.
Result: cg-computed-residual-bound -/
theorem ρ_le_chebyshev_of_frobNorm_le {a a' d : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hd : d < a)
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ d) {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt ((a' + d) / (a - d)) *
      ((Real.sqrt ((a' + d) / (a - d)) - 1) /
        (Real.sqrt ((a' + d) / (a - d)) + 1)) ^ j * ‖WithLp.toLp 2 C.b‖ :=
  C.ρ_le_chebyshev_of_spectrum_backwardH (sub_pos.mpr hd)
    (C.toNormalizedLanczosData.spectrum_backwardH_subset_Icc hs hgap) hj

/-- **Input-certified computed residual bound**: computed residual decay from an input-only scalar
certificate, with effective condition
number $\kappa_c=(a'+d)/(a-d)$ and input spectrum in $[a,a']$. For $j\le k$,
$$\|\mathbf r_j\|\le2\sqrt{\kappa_c}
\Bigl(\frac{\sqrt{\kappa_c}-1}{\sqrt{\kappa_c}+1}\Bigr)^j\|\mathbf b\|\,.$$
The certificate's strict spectral margin supplies positive definiteness;
no additional iteration-horizon condition is imposed.
No printed source.
This bounds the residual envelope for $j\le k$; it does not assert stepwise monotonicity.
Result: cg-computed-residual-bound -/
theorem ρ_le_chebyshev_of_certificate {a a' : ℝ}
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (S : CGBackwardCertificate k C.ε a a')
    {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt ((a' + S.d) / (a - S.d)) *
      ((Real.sqrt ((a' + S.d) / (a - S.d)) - 1) /
        (Real.sqrt ((a' + S.d) / (a - S.d)) + 1)) ^ j * ‖WithLp.toLp 2 C.b‖ :=
  C.ρ_le_chebyshev_of_frobNorm_le hs S.d_lt
    (C.frobNorm_backwardH_sub_dilatedH_le_of_certificate hs S) hj

/-- **Finite-horizon Chebyshev bound for the computed residual**: for a $k$-step CG run,
$\operatorname{spec}(\mathbf A)\subseteq[a,a']$, $a>0$, $\kappa=a'/a$ and
$k^{5/2}\varepsilon\kappa^2\le10^{-5}$, put $\kappa_c=2\kappa+1$. For $j\le k$,
$$\|\mathbf{r}_j\|\le2\sqrt{\kappa_c}
\Bigl(\frac{\sqrt{\kappa_c}-1}{\sqrt{\kappa_c}+1}\Bigr)^j\|\mathbf b\|\,.$$
No printed source in this form; compare [MeurantStrakos2006, §5.2].
This bounds the residual envelope for $j\le k$; it does not assert stepwise monotonicity.
Result: cg-computed-residual-bound -/
theorem ρ_le_chebyshev {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt (2 * (a' / a) + 1) *
      ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ j *
        ‖WithLp.toLp 2 C.b‖ := by
  have h := C.ρ_le_chebyshev_of_spectrum_backwardH (by positivity : 0 < a / 2)
    (C.spectrum_backwardH_subset_Icc ha hs hsmall) hj
  have he : (a' + a / 2) / (a / 2) = 2 * (a' / a) + 1 := by field_simp
  rwa [he] at h

/-! ### Errors of exact CG on the model, in the computed quantities -/

/-- **The model's error decrements are the computed estimator**: under (H), for
$\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star = (\mathbf{b}, \mathbf{0}, \dots)$ and $j + d \le k$,
$$\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}^2 -
\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_{j+d}\|_{\tilde{\mathbf{H}}}^2 =
\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2,$$
exactly, with the computed $\gamma_i$ and the norms of the computed residuals: the estimator
$\nu_{j,d}$ of [StrakosTichy2002, (4.9), (10.7)] is exact for the model. -/
theorem quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {j d : ℕ}
    (hjd : j + d ≤ k) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 j) -
        quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 (j + d)) =
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hPD := C.isHermitian_backwardH.posDef_of_spectrum_subset_Icc
    (by positivity : 0 < a / 2) hspec
  have hstep : ∀ i < k, quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 i) -
      quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 (i + 1)) =
        C.γ i * C.ρ i ^ 2 := fun i hi => by
    have h := hPD.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ hxs i
    rw [C.cgAlpha_backwardH ha hs hsmall hi, C.norm_cgState_backwardH_r ha hs hsmall hi.le] at h
    simpa only [RCLike.re_to_real] using h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ← ih (by omega),
      ← hstep (j + d) (by omega)]
    ring

/-- **The model's error is a Gauss quadrature error of the computed tridiagonal matrix**:
under (H), $\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 =
\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2$, and
the sum is $\|\mathbf{b}\|^2(\mathbf{T}_k^{-1})_{00}$ for $\mathbf{T}_k$ = `cgTridiagonal C.γ C.ρ k`
(`NLAlib.sq_mul_inv_cgTridiagonal_zero_zero`): the identity
$\|\mathbf{x} - \mathbf{x}_k\|_{\mathbf{A}}^2 = \|\mathbf{r}_0\|^2[(\mathbf{T}_n^{-1})_{11} -
(\mathbf{T}_k^{-1})_{11}]$ of [MeurantStrakos2006, (3.17)] holds for the model with the
computed $\mathbf{T}_k$ and
$\tilde{\mathbf{v}}^{\mathsf{T}}\tilde{\mathbf{H}}^{-1}\tilde{\mathbf{v}}$
in place of $(\mathbf{T}_n^{-1})_{11}$. -/
theorem quadForm_backwardH_sub_cgIterate_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) =
      quadForm C.backwardH xs - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2 := by
  have h := C.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate ha hs hsmall
    hxs (j := 0) (d := k) (by omega)
  rw [cgIterate_zero, sub_zero, zero_add, ← Finset.range_eq_Ico] at h
  linarith

/-- **The model's initial error is the true one up to the model distance**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star =
(\mathbf{b}, \mathbf{0}, \dots)$, with <!-- value cgBackwardFactor k -->
$c = 6000k^2\sqrt{k}\varepsilon\kappa a'$,
$$\bigl\lvert\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 -
\|\mathbf{x}_\star\|_{\mathbf{A}}^2\bigr\rvert \le 2\|\mathbf{b}\|^2c/a^2 .$$
The start of the model is exactly $\mathbf{b}/\|\mathbf{b}\|$ in the first block
($\mathbf{r}_0 = \mathbf{b}$ is not rounded), so the comparison is with the true problem. -/
theorem abs_quadForm_backwardH_sub_quadForm_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH xs - quadForm C.A x| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hherm := C.isHermitian_backwardH
  have hT : C.backwardHᵀ = C.backwardH := by
    have := hherm.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hc := C.frobNorm_backwardH_sub_dilatedH_le ha hs hsmall
  set c := cgBackwardFactor k * C.ε * (a' / a) * a'
  -- the dilated true solution
  set xh : Fin n × Fin (k + 1) → ℝ := fun p => if (p.2 : ℕ) = 0 then x p.1 else 0 with hxhdef
  have hHxh : C.dilatedH *ᵥ xh = C.dilatedRhs := by
    funext p
    obtain ⟨i, r⟩ := p
    rw [C.dilatedH_mulVec_apply]
    by_cases h0 : (r : ℕ) = 0
    · have h0' : r = 0 := Fin.ext h0
      have : (fun j => xh (j, r)) = x := funext fun j => by simp [hxhdef, h0']
      rw [this, hx]
      simp [dilatedRhs, h0]
    · have h0' : r ≠ 0 := fun h => h0 (by simp [h])
      have : (fun j => xh (j, r)) = 0 := funext fun j => by simp [hxhdef, h0']
      rw [this, Matrix.mulVec_zero]
      simp [dilatedRhs, h0]
  have hxhb : xh ⬝ᵥ C.dilatedRhs = x ⬝ᵥ C.b := by
    simp only [dotProduct, Fintype.sum_prod_type, hxhdef, dilatedRhs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp
    · intro r _ hr
      have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
      simp [this]
    · simp
  have hnxh : ‖WithLp.toLp 2 xh‖ = ‖WithLp.toLp 2 x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp [hxhdef]
    · intro r _ hr
      simp [hxhdef, hr]
    · simp
  -- the difference is `-xsᵀΔx̂`
  have hdiff : quadForm C.backwardH xs - quadForm C.A x =
      -(xs ⬝ᵥ ((C.backwardH - C.dilatedH) *ᵥ xh)) := by
    simp only [quadForm_def, star_trivial]
    rw [hxs, hx, ← hxhb, Matrix.sub_mulVec, dotProduct_sub, hHxh,
      dotProduct_mulVec_comm hT xs xh, hxs, dotProduct_comm]
    ring
  rw [hdiff, abs_neg]
  have hnxs := norm_le_of_mulVec_eq hherm (by positivity : 0 < a / 2) hspec hxs
  rw [C.norm_dilatedRhs] at hnxs
  have hnx := norm_le_of_mulVec_eq C.isHermitian ha hs hx
  have hΔ : ‖WithLp.toLp 2 ((C.backwardH - C.dilatedH) *ᵥ xh)‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [hnxh]
    exact mul_le_mul_of_nonneg_right ((specNorm_le_frobNorm _).trans hc) (norm_nonneg _)
  have hc0 : 0 ≤ c := (frobNorm_nonneg _).trans hc
  refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
  calc ‖WithLp.toLp 2 xs‖ * ‖WithLp.toLp 2 ((C.backwardH - C.dilatedH) *ᵥ xh)‖
      ≤ (‖WithLp.toLp 2 C.b‖ / (a / 2)) * (c * (‖WithLp.toLp 2 C.b‖ / a)) :=
        mul_le_mul hnxs (hΔ.trans (mul_le_mul_of_nonneg_left hnx hc0)) (norm_nonneg _)
          (by positivity)
    _ = 2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * c / a ^ 2 := by field_simp

/-- **The model's error at step $k$ in the computed quantities**: under (H), the
bound is <!-- value cgBackwardFactor k -->
$$\Bigl\lvert\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 -
\Bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2\Bigr)\Bigr\rvert
\le 2\|\mathbf{b}\|^2c/a^2,\qquad c = 6000k^2\sqrt{k}\varepsilon\kappa a' .$$
The computed run's own error $\|\mathbf{x}_\star - \mathbf{x}_k\|_{\mathbf{A}}$ is not covered
here. -/
theorem abs_quadForm_backwardH_sub_cgIterate_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) -
        (quadForm C.A x - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2)| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 := by
  have h1 := C.quadForm_backwardH_sub_cgIterate_eq ha hs hsmall hxs
  have h2 := C.abs_quadForm_backwardH_sub_quadForm_le ha hs hsmall hxs hx
  rw [h1]
  convert h2 using 2
  ring

/-- **The computed estimator is bounded a priori**: under (H),
$\sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2 \le 2\|\mathbf{b}\|^2/a$. -/
theorem sum_γ_mul_ρ_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2 ≤ 2 * ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by
  have hspec := C.spectrum_backwardH_subset_Icc ha hs hsmall
  have hherm := C.isHermitian_backwardH
  have hPD := hherm.posDef_of_spectrum_subset_Icc (by positivity : 0 < a / 2) hspec
  set xs := C.backwardH⁻¹ *ᵥ C.dilatedRhs
  have hxs : C.backwardH *ᵥ xs = C.dilatedRhs := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hPD.isUnit), Matrix.one_mulVec]
  have h1 := C.quadForm_backwardH_sub_cgIterate_eq ha hs hsmall hxs
  have h0 : 0 ≤ quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) := by
    rw [quadForm_def]
    simpa using hPD.posSemidef.dotProduct_mulVec_nonneg
      (xs - cgIterate C.backwardH C.dilatedRhs 0 k)
  have h2 := dotProduct_mulVec_le_of_mulVec_eq hherm (by positivity : 0 < a / 2) hspec hxs
  rw [C.norm_dilatedRhs] at h2
  have h3 : quadForm C.backwardH xs ≤ 2 * ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by
    rw [quadForm_def, star_trivial]
    calc _ ≤ _ := h2
      _ = _ := by field_simp
  linarith

end CGRun

end NLAlib
