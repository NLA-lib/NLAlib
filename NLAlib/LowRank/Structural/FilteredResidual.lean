/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.RitzValues
public import NLAlib.LowRank.Structural.SingularValueDeficit

/-!
# Filtered sketches with their filtered residual

For a real function $g$, $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ and a filtered test
matrix $g(\mathbf{H})\mathbf{\Omega}$, lower bounds on the squared singular values of
$\mathsf{rsvd}(\mathbf{A}, g(\mathbf{H})\mathbf{\Omega})$ (`NLAlib.rsvd`) in which the tail
enters through the residual of the filtered matrix $\mathbf{A}g(\mathbf{H})$, not through a
uniform bound of $g$ on the tail as in `NLAlib.LowRank.Structural.RitzValues`; and the energy of
that residual on the tail against a Schatten norm of the tail. A filter weighted by $x^r$, as in
[BakshiNarayanan2023], makes this energy a Schatten-$p$ quantity for $p \le 4r + 2$, so the bounds
for $p > 2$ built from it carry no factor of the dimension.

## Main results

* `NLAlib.HasOrthonormalCols.singularValues_sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq`:
  gap form.
* `NLAlib.HasOrthonormalCols.sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq_of_le_singularValues`:
  cut form.
* `NLAlib.frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow`: the filtered tail energy against
  a Schatten norm of the tail.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype s] [DecidableEq n] [DecidableEq s]

/-- **Singular values of a filtered sketch with the filtered residual, gap form**: let $g$ be a
real function, $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, $\mathbf{Z}$ a frame
(orthonormal columns) with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$i < t$ and $c > 0$ with $\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c$ for $j \le i$. Then, with
$\mathbf{B} = \mathbf{A}g(\mathbf{H})$,
$$\sigma_i(\mathbf{A})^2 - c^{-2}\,
\|(\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A}, g(\mathbf{H})\mathbf{\Omega})\bigr)^2\,.$$
No bound of $g$ on the tail is assumed: the tail enters through the residual of $\mathbf{B}$.
[MuscoMusco2015, Lemma 9]; property 1 there, for the Chebyshev filter with a uniform bound on the
tail and a Gaussian block, with probability $99/100$, here deterministic, for any filter, with
the filtered residual. -/
theorem HasOrthonormalCols.singularValues_sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {i : ℕ} (hi : i < t) {c : ℝ} (hc : 0 < c)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|) :
    singularValues A i ^ 2 - c⁻¹ ^ 2 *
        specNorm ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := by
  classical
  rcases (singularValues_nonneg A i).eq_or_lt with hσ | hσ
  · rw [← hσ]
    nlinarith [sq_nonneg (c⁻¹ * specNorm
      ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))),
      sq_nonneg (singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i)]
  have hiN : i + 1 ≤ Fintype.card n :=
    ((singularValues_pos_iff A).mp hσ).trans_le A.rank_le_card_width
  obtain ⟨W, -, hW, -, -, -, hHW, -, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hiN
  have hAWW : A * W * Wᴴ = truncatedSVD A (i + 1) := by simpa using htr (i + 1) le_rfl
  have hAZ' := truncatedSVD_mul_mul_conjTranspose_of_le hAZ (show i + 1 ≤ t by omega)
  have hZW := mul_conjTranspose_mul_eq_of_truncatedSVD_mul hσ hW hHW hAWW hAZ'
  have hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin :=
    range_le_iff_exists_mul.mpr ⟨Zᴴ * W, by rw [← Matrix.mul_assoc, hZW]⟩
  have hcap := hW.matrixNorm_one_sub_rangeProjector_mul_mul_le (lpGauge ⊤) g hHW hZ hΩ hWZ hc
    fun j => hhead j (Nat.lt_succ_iff.mp j.isLt)
  rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, hAWW, Matrix.mul_assoc A] at hcap
  have hcap2 := pow_le_pow_left₀ (specNorm_nonneg _) hcap 2
  have hP := (isStarProjection_rangeProjector
    (A * (cfc g (Aᴴ * A) * Ω))).singularValues_sq_sub_specNorm_sq_le A i
  rw [rsvd]
  nlinarith [hcap2, hP]


/-- The Rayleigh quotient loses only the filtered mass strictly below the cut. -/
private theorem cut_mass_le {a b : Type*} [Fintype a] [Fintype b]
    (g : ℝ → ℝ) {d u : a → ℝ} {e v : b → ℝ} {σ c τ ρ : ℝ}
    (hc : 0 < c) (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hd : ∀ j, σ ^ 2 ≤ d j) (hdg : ∀ j, c ≤ |g (d j)|) (he : ∀ j, 0 ≤ e j)
    (hR : ∑ j, e j * (Set.indicator (Set.Iio (τ ^ 2)) g (e j)) ^ 2 * v j ≤
      ρ ^ 2 * ∑ j, u j) :
    σ ^ 2 * c ^ 2 * ∑ j, u j ≤
        ∑ j, g (d j) * d j * g (d j) * u j + ∑ j, g (e j) * e j * g (e j) * v j ∧
      (τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2) *
        (∑ j, g (d j) * d j * g (d j) * u j + ∑ j, g (e j) * e j * g (e j) * v j) ≤
        ∑ j, (d j * g (d j)) ^ 2 * u j + ∑ j, (e j * g (e j)) ^ 2 * v j := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  have hτ2 : τ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hτ hτσ 2
  have hD : σ ^ 2 * c ^ 2 * ∑ j, u j ≤ ∑ j, g (d j) * d j * g (d j) * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hg2 : c ^ 2 ≤ g (d j) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hc.le (hdg j) 2
    have hm := mul_le_mul (hd j) hg2 (sq_nonneg c) ((sq_nonneg σ).trans (hd j))
    nlinarith [mul_le_mul_of_nonneg_right hm (hu j)]
  have hE : 0 ≤ ∑ j, g (e j) * e j * g (e j) * v j :=
    Finset.sum_nonneg fun j _ => by
      nlinarith [mul_nonneg (he j) (mul_nonneg (sq_nonneg (g (e j))) (hv j))]
  have hhead : τ ^ 2 * ∑ j, g (d j) * d j * g (d j) * u j ≤
      ∑ j, (d j * g (d j)) ^ 2 * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hnon := mul_nonneg ((sq_nonneg σ).trans (hd j)) (mul_nonneg (sq_nonneg (g (d j))) (hu j))
    nlinarith [mul_nonneg (sub_nonneg.mpr (hτ2.trans (hd j))) hnon]
  have htail : τ ^ 2 * ∑ j, g (e j) * e j * g (e j) * v j ≤
      ∑ j, (e j * g (e j)) ^ 2 * v j + τ ^ 2 *
        ∑ j, e j * (Set.indicator (Set.Iio (τ ^ 2)) g (e j)) ^ 2 * v j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : e j < τ ^ 2
    · rw [Set.indicator_of_mem (s := Set.Iio (τ ^ 2)) hj]
      nlinarith [mul_nonneg (sq_nonneg (e j * g (e j))) (hv j)]
    · rw [Set.indicator_of_notMem (s := Set.Iio (τ ^ 2)) hj]
      have hnon := mul_nonneg (he j) (mul_nonneg (sq_nonneg (g (e j))) (hv j))
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_gt hj)) hnon]
  have hsum : 0 ≤ ∑ j, u j := Finset.sum_nonneg fun j _ => hu j
  have hfirst := hD.trans (le_add_of_nonneg_right hE)
  have hc2 : c⁻¹ ^ 2 * c ^ 2 = 1 := by field_simp [hc.ne']
  have hscaled := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ c⁻¹ ^ 2 * ρ ^ 2 by positivity)
  have hcancel : c⁻¹ ^ 2 * ρ ^ 2 * (σ ^ 2 * c ^ 2 * ∑ j, u j) =
      σ ^ 2 * ρ ^ 2 * ∑ j, u j := by
    calc _ = (c⁻¹ ^ 2 * c ^ 2) * (σ ^ 2 * ρ ^ 2 * ∑ j, u j) := by ring
      _ = _ := by rw [hc2, one_mul]
  rw [hcancel] at hscaled
  have hτmass := mul_le_mul_of_nonneg_right hτ2 (mul_nonneg (sq_nonneg ρ) hsum)
  have hR' := mul_le_mul_of_nonneg_left hR (sq_nonneg τ)
  constructor
  · exact hfirst
  · nlinarith

/-- The vector form of the filtered cut estimate, in complementary spectral frames. -/
private theorem cut_vector_le {a : Type*} [Fintype a] [DecidableEq a]
    {A : Matrix m n 𝕜} (g : ℝ → ℝ) {i : ℕ} {T : Matrix n (Fin (i + 1)) 𝕜}
    {V : Matrix n a 𝕜} (hT : HasOrthonormalCols T) (hTV : Tᴴ * V = 0)
    (h1 : T * Tᴴ + V * Vᴴ = 1)
    (hHT : Aᴴ * A * T = T * Matrix.diagonal
      fun j : Fin (i + 1) => ((singularValues A j ^ 2 : ℝ) : 𝕜)) {e : a → ℝ}
    (hHV : Aᴴ * A * V = V * Matrix.diagonal fun j => (e j : 𝕜))
    (he : ∀ j, 0 ≤ e j) {X : Matrix n (Fin (i + 1)) 𝕜} (hTX : Tᴴ * X = 1)
    {c τ ρ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (hR : specNorm (A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * (X - T)) ≤ ρ)
    (t : Fin (i + 1) → 𝕜) :
    singularValues A i ^ 2 * c ^ 2 * ‖WithLp.toLp 2 t‖ ^ 2 ≤
        ‖WithLp.toLp 2 ((A * cfc g (Aᴴ * A) * X) *ᵥ t)‖ ^ 2 ∧
      (τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2) * ‖WithLp.toLp 2 ((A * cfc g (Aᴴ * A) * X) *ᵥ t)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (Aᴴ *ᵥ ((A * cfc g (Aᴴ * A) * X) *ᵥ t))‖ ^ 2 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hsa : IsSelfAdjoint (Aᴴ * A) := hH
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (Aᴴ * A)) :=
    fun f => (Aᴴ * A).finite_real_spectrum.continuousOn f
  have hq := hH.re_quadForm_cfc_eq_sum_add_sum h1 hHT hHV
  have hnorm (f : ℝ → ℝ) (z : n → 𝕜) :
      ‖WithLp.toLp 2 (A *ᵥ (cfc f (Aᴴ * A) *ᵥ z))‖ ^ 2 =
        ∑ j : Fin (i + 1), f (singularValues A j ^ 2) * singularValues A j ^ 2 *
          f (singularValues A j ^ 2) * ‖(Tᴴ *ᵥ z) j‖ ^ 2 +
        ∑ j, f (e j) * e j * f (e j) * ‖(Vᴴ *ᵥ z) j‖ ^ 2 := by
    have hF : (cfc f (Aᴴ * A)).IsHermitian := cfc_predicate f (Aᴴ * A)
    have hcf : cfc (fun x => f x * x * f x) (Aᴴ * A) =
        (cfc f (Aᴴ * A))ᴴ * (Aᴴ * A) * cfc f (Aᴴ * A) := by
      rw [cfc_mul (fun x => f x * x) f _ (hcont _) (hcont _),
        cfc_mul f (fun x => x) _ (hcont _) (hcont _), cfc_id' ℝ (Aᴴ * A) hsa, hF.eq]
    have h := hq (fun x => f x * x * f x) z
    rw [hcf, quadForm_conjTranspose_mul_mul, quadForm_conjTranspose_mul_self,
      RCLike.ofReal_re] at h
    exact h
  have hVT : Vᴴ * T = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Vᴴ * T), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTV, Matrix.conjTranspose_zero]
  have hxT : Tᴴ *ᵥ (X *ᵥ t) = t := by rw [Matrix.mulVec_mulVec, hTX, Matrix.one_mulVec]
  have hx'T : Tᴴ *ᵥ ((X - T) *ᵥ t) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, hTX, hT.conjTranspose_mul_self,
      sub_self, Matrix.zero_mulVec]
  have hxV : Vᴴ *ᵥ ((X - T) *ᵥ t) = Vᴴ *ᵥ (X *ᵥ t) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, hVT, sub_zero, Matrix.mulVec_mulVec]
  have hY := hnorm g (X *ᵥ t)
  have hK := hq (fun x => (x * g x) ^ 2) (X *ᵥ t)
  have hcg : cfc (fun x => x * g x) (Aᴴ * A) = Aᴴ * A * cfc g (Aᴴ * A) := by
    rw [cfc_mul (fun x => x) g _ (hcont _) (hcont _), cfc_id' ℝ (Aᴴ * A) hsa]
  rw [← hH.norm_toLp_cfc_mulVec_sq, hcg] at hK
  have hE := hnorm (Set.indicator (Set.Iio (τ ^ 2)) g) ((X - T) *ᵥ t)
  rw [hx'T, hxV] at hE
  simp only [Pi.zero_apply, norm_zero, zero_pow two_ne_zero, mul_zero,
    Finset.sum_const_zero, zero_add] at hE
  have hEb := (norm_toLp_mulVec_le
    (A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * (X - T)) t).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hMass : ∑ j, e j * (Set.indicator (Set.Iio (τ ^ 2)) g (e j)) ^ 2 *
      ‖(Vᴴ *ᵥ (X *ᵥ t)) j‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖t j‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hEb 2
    have hE' : ‖WithLp.toLp 2 (A *ᵥ
        (cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) *ᵥ ((X - T) *ᵥ t)))‖ ^ 2 =
        ∑ j, e j * (Set.indicator (Set.Iio (τ ^ 2)) g (e j)) ^ 2 *
          ‖(Vᴴ *ᵥ (X *ᵥ t)) j‖ ^ 2 := by
      rw [hE]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [← Matrix.mulVec_mulVec] at h
    rw [hE'] at h
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq] using h
  have h := cut_mass_le g (d := fun j : Fin (i + 1) => singularValues A j ^ 2)
    (u := fun j => ‖t j‖ ^ 2) (v := fun j => ‖(Vᴴ *ᵥ (X *ᵥ t)) j‖ ^ 2)
    hc hτ hτi (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _) (fun j => pow_le_pow_left₀ (singularValues_nonneg A _)
      (singularValues_antitone A (Nat.lt_succ_iff.mp j.isLt)) 2)
    (fun j => hhead j (Nat.lt_succ_iff.mp j.isLt)) he hMass
  rw [hxT] at hY hK
  rw [← hY, ← hK] at h
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, EuclideanSpace.norm_sq_eq] using h

/-- **Singular values of a filtered sketch with the filtered residual, cut form**: let $g$ be a
real function, $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, $\mathbf{Z}$ a frame
(orthonormal columns) whose range contains the row space of $\llbracket\mathbf{A}\rrbracket_{i+1}$,
that is $\llbracket\mathbf{A}\rrbracket_{i+1}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_{i+1}$, with
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
let $c > 0$ and let $0 \le \tau \le \sigma_i(\mathbf{A})$ be a cut, with
$\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c$ for $j \le i$. Let $g_\tau$ be $g$ on
$(-\infty, \tau^2)$ and $0$ elsewhere, and $\mathbf{B}_\tau = \mathbf{A}g_\tau(\mathbf{H})$. Then
$$\tau^2 - c^{-2}\,
\|(\mathbf{B}_\tau - \mathbf{B}_\tau\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A}, g(\mathbf{H})\mathbf{\Omega})\bigr)^2\,.$$
Only the part of the filter below the cut enters the residual; everything above the cut counts
as head, and the bound is for $\tau^2$, not $\sigma_i^2$. [MuscoMusco2015, Lemma 9]; property 2
there, with the cut at $\sigma_{k+1}$ times a fixed factor, a uniform bound on the tail and
probability $99/100$, here deterministic with the cut as a parameter and the filtered residual. -/
theorem
    HasOrthonormalCols.sq_sub_inv_sq_mul_le_singularValues_rsvd_cfc_sq_of_le_singularValues
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) {c τ : ℝ} (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|) :
    τ ^ 2 - c⁻¹ ^ 2 * specNorm ((A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) -
        A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * Z * Zᴴ) * Ω *
          pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := by
  classical
  set ρ := specNorm ((A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) -
    A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
  rcases le_or_gt (τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2) 0 with hneg | hpos
  · exact hneg.trans (sq_nonneg _)
  have hσ : 0 < singularValues A i := by
    rcases (singularValues_nonneg A i).eq_or_lt with h0 | h0
    · have hτ0 : τ = 0 := le_antisymm (h0 ▸ hτi) hτ
      rw [hτ0] at hpos
      nlinarith [sq_nonneg (c⁻¹ * ρ)]
    · exact h0
  have hiN : i + 1 ≤ Fintype.card n :=
    ((singularValues_pos_iff A).mp hσ).trans_le A.rank_le_card_width
  obtain ⟨T, V, hT, -, hTV, h1, hHT, hHV, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hiN
  have hZT := mul_conjTranspose_mul_eq_of_truncatedSVD_mul hσ hT hHT
    (by simpa using htr (i + 1) le_rfl) hAZ
  -- the sketched head vectors
  set K := A * cfc g (Aᴴ * A) * (Ω * pinv (Zᴴ * Ω) * Zᴴ * T)
  set M := Ω * pinv (Zᴴ * Ω) * Zᴴ * T
  have hZΩ := hZ.mul_pinv_self_of_rank_eq hΩ
  have hTZ : Tᴴ * (Z * Zᴴ) = Tᴴ := by
    have h := congrArg Matrix.conjTranspose hZT
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      at h
  have hZX : Z * Zᴴ * M = T := by
    calc Z * Zᴴ * M = Z * (Zᴴ * Ω * pinv (Zᴴ * Ω)) * Zᴴ * T := by
          simp only [M, Matrix.mul_assoc]
      _ = T := by rw [hZΩ, Matrix.mul_one, hZT]
  have hTX : Tᴴ * M = 1 := by
    rw [← hTZ, Matrix.mul_assoc, hZX, hT.conjTranspose_mul_self]
  have hR : specNorm
      (A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * (M - T)) ≤ ρ := by
    have heq : A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * (M - T) =
        ((A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) -
          A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * Z * Zᴴ) *
          Ω * pinv (Zᴴ * Ω)) * (Zᴴ * T) := by
      conv_lhs => rw [← hZX]
      simp only [M, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    rw [heq]
    exact (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _)
      ((hZ.specNorm_conjTranspose_mul_le T).trans hT.specNorm_le_one))
  have hv := fun t => cut_vector_le g hT hTV h1 hHT hHV (fun _ => sq_nonneg _)
    hTX hc hτ hτi hhead hR t
  have hinj : Function.Injective K.mulVec := by
    intro t₁ t₂ h12
    have h := (hv (t₁ - t₂)).1
    rw [Matrix.mulVec_sub, h12, sub_self, WithLp.toLp_zero, norm_zero,
      zero_pow two_ne_zero] at h
    have hn : ‖WithLp.toLp 2 (t₁ - t₂)‖ ^ 2 = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right h (by positivity)) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, WithLp.toLp_eq_zero] at hn
    exact sub_eq_zero.mp hn
  have hrank : K.rank = i + 1 := by rw [mulVec_injective_iff_rank_eq.mp hinj, Fintype.card_fin]
  -- min–max for the conjugate transpose of the output, on the range of `K`
  have hPK : rangeProjector (A * (cfc g (Aᴴ * A) * Ω)) * K = K := by
    rw [rangeProjector_mul_eq_self_iff, range_le_iff_exists_mul]
    exact ⟨pinv (Zᴴ * Ω) * Zᴴ * T, by simp only [K, Matrix.mul_assoc]⟩
  have key : Real.sqrt (τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2) ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω))ᴴ i := by
    refine le_singularValues_of_forall_mem _ (LinearMap.range K.mulVecLin) hrank.ge
      fun y hy => ?_
    obtain ⟨t, rfl⟩ := hy
    rw [Matrix.mulVecLin_apply, rsvd, Matrix.conjTranspose_mul,
      (isStarProjection_rangeProjector _).conjTranspose_eq,
      ← Matrix.mulVec_mulVec (M := Aᴴ) (N := rangeProjector (A * (cfc g (Aᴴ * A) * Ω))),
      Matrix.mulVec_mulVec (M := rangeProjector (A * (cfc g (Aᴴ * A) * Ω))) (N := K), hPK]
    refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
    rw [mul_pow, Real.sq_sqrt hpos.le]
    exact (hv t).2
  rw [← singularValues_conjTranspose]
  calc τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2 = Real.sqrt (τ ^ 2 - c⁻¹ ^ 2 * ρ ^ 2) ^ 2 :=
        (Real.sq_sqrt hpos.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2


omit [DecidableEq s] in
/-- **The filtered tail energy against a Schatten norm of the tail**: let $g$ be a real function,
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, $\mathbf{Z}$ a matrix with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$,
$0 < p < \infty$ and $b$ real. If
$\sigma_i(\mathbf{A})^2\,g(\sigma_i(\mathbf{A})^2)^2 \le b\,\sigma_i(\mathbf{A})^p$ for every
$i \ge t$, then, with $\mathbf{B} = \mathbf{A}g(\mathbf{H})$,
$$\|\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2 \le
b\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{S_p}^p\,.$$
The left side is $\sum_{i \ge t}\sigma_i(\mathbf{A})^2 g(\sigma_i(\mathbf{A})^2)^2$. For the
weighted filters of `Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_mul_pow` with
$p \le 4r + 2$ the hypothesis holds with $b$ a multiple of $\sigma_t^{4r+2-p}$.
[BakshiNarayanan2023, proof of Lemma 7.6]; there for rank one and the eigenvalues after the
first, in expectation over a Gaussian start vector, here deterministic, for any filter and any
$t$. -/
theorem frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow {A : Matrix m n 𝕜} (g : ℝ → ℝ)
    {Z : Matrix n s 𝕜} {t : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A t) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) {b : ℝ}
    (hw : ∀ i, t ≤ i → singularValues A i ^ 2 * g (singularValues A i ^ 2) ^ 2 ≤
      b * singularValues A i ^ p.toReal) :
    frobNorm (A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) ^ 2 ≤
      b * schattenNorm p (A - truncatedSVD A t) ^ p.toReal := by
  classical
  let t' := min t (Fintype.card n)
  have ht' : truncatedSVD A t' = truncatedSVD A t := by
    rcases le_total t (Fintype.card n) with h | h
    · rw [show t' = t from min_eq_left h]
    · rw [show t' = Fintype.card n from min_eq_right h,
        truncatedSVD_of_rank_le A A.rank_le_card_width,
        truncatedSVD_of_rank_le A (A.rank_le_card_width.trans h)]
  obtain ⟨T, V, -, hV, hTV, h1, -, hHV, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A
      (min_le_right t (Fintype.card n))
  have hATT : A * T * Tᴴ = truncatedSVD A t := by
    have h := htr t' le_rfl
    rw [Fin.castLE_rfl, Matrix.submatrix_id_id, ht'] at h
    exact h
  have hB := sub_mul_cfc_mul_eq_of_mul_mul_conjTranspose_eq g (hAZ.trans hATT.symm)
  set D := Matrix.diagonal fun j : Fin (Fintype.card n - t') =>
    ((g (singularValues A (t' + j) ^ 2) : ℝ) : 𝕜)
  have hcV : cfc g (Aᴴ * A) * V = V * D :=
    (Matrix.isHermitian_conjTranspose_mul_self A).cfc_mul_eq_mul_diagonal_of_mul_eq hHV g
  have hres : A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * T * Tᴴ =
      (A * V * D) * Vᴴ := by
    calc _ = A * cfc g (Aᴴ * A) * (1 - T * Tᴴ) := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = (A * V * D) * Vᴴ := by
          rw [show 1 - T * Tᴴ = V * Vᴴ by rw [← h1]; abel,
            ← Matrix.mul_assoc, Matrix.mul_assoc A, hcV]
          simp only [Matrix.mul_assoc]
  have hVG : (A * V)ᴴ * (A * V) = Matrix.diagonal
      fun j : Fin (Fintype.card n - t') => ((singularValues A (t' + j) ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A, hHV,
      ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  have hG : (A * V * D)ᴴ * (A * V * D) =
      Matrix.diagonal fun j : Fin (Fintype.card n - t') =>
        ((singularValues A (t' + j) ^ 2 * g (singularValues A (t' + j) ^ 2) ^ 2 : ℝ) : 𝕜) := by
    calc _ = Dᴴ * ((A * V)ᴴ * (A * V)) * D := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hVG]
        simp only [D, Matrix.diagonal_conjTranspose, Pi.star_apply,
          RCLike.star_def, RCLike.conj_ofReal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        push_cast
        ring
  have hnorm : frobNorm (A * V * D) ^ 2 =
      ∑ j : Fin (Fintype.card n - t'),
        singularValues A (t' + j) ^ 2 * g (singularValues A (t' + j) ^ 2) ^ 2 := by
    rw [frobNorm_sq_eq_re_trace, hG, Matrix.trace_diagonal, map_sum]
    simp only [RCLike.ofReal_re]
  have hsum : schattenNorm p (A - truncatedSVD A t) ^ p.toReal =
      ∑ j : Fin (Fintype.card n - t'), singularValues A (t' + j) ^ p.toReal := by
    have h := schattenNorm_sub_truncatedSVD_rpow_eq_add_sum hp0 hp A
      (min_le_right t (Fintype.card n))
    rw [truncatedSVD_of_rank_le A A.rank_le_card_width, sub_self,
      schattenNorm_zero, Real.zero_rpow (ENNReal.toReal_pos hp0 hp).ne', zero_add,
      Finset.sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range, ht'] at h
    exact h
  rw [hB, hres, hV.frobNorm_mul_conjTranspose_right, hnorm, hsum, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hw _ (by
    have := j.isLt
    dsimp [t'] at *
    omega)


end NLAlib
