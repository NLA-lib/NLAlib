/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystrom
public import NLAlib.RandomMatrix.Gaussian.InverseMoments.SpectralTail
public import NLAlib.Regression.SketchAndSolveMoments

/-!
# Conditional Gaussian generalized Nyström with explicit window constants

The reciprocal singular-value window gives the conditional error majorant used for the
relative-error bound with width 200k and co-range width fourteen times the range width.
Design: docs/design/research/Nystrom-Constants.md.

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_fourteen_mul_le`:
  the conditional expected error with explicit moment coefficients.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib
private theorem rank_ratio_le {P L r : ℝ} (hL : 200 ≤ L)
    (hP : 14 * L ≤ P) (hrL : r ≤ L) :
    P * (r / (P - r - 1)) ≤ 1.078 * L := by
  have hd : 0 < P - r - 1 := by linarith
  rw [← mul_div_assoc, div_le_iff₀ hd]
  have hPL : P * r ≤ P * L := mul_le_mul_of_nonneg_left hrL (by linarith)
  have hcoef : P ≤ 1.078 * (P - r - 1) := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ L)
  nlinarith
private theorem weighted_first_moment_coefficient_le {P r β : ℝ}
    (hP : 2800 ≤ P) (hr : 14 * r ≤ P) (hβ : P * β ^ 2 ≤ 2.3) :
    β + 1 / √(P - r - 1) ≤ 2.56 / √P := by
  have hd : 0 < P - r - 1 := by linarith
  have hP0 : 0 < P := by linarith
  have hp := Real.sqrt_pos.mpr hP0
  have hd' := Real.sqrt_pos.mpr hd
  have hp2 := Real.sq_sqrt hP0.le
  have hd2 := Real.sq_sqrt hd.le
  have hb : √P * β ≤ 1.517 := by
    have hs : (√P * β) ^ 2 ≤ 2.3 := by simpa only [mul_pow, hp2] using hβ
    nlinarith
  have hg : √P / √(P - r - 1) ≤ 1.038 := by
    rw [div_le_iff₀ hd']
    nlinarith [sq_nonneg (√P - 1.038 * √(P - r - 1))]
  rw [le_div_iff₀ hp]
  have he : (β + 1 / √(P - r - 1)) * √P = √P * β + √P / √(P - r - 1) := by ring
  rw [he]
  linarith
end NLAlib

namespace NLAlib
private theorem integrated_window_term_le {θ q I e b k γ P : ℝ}
    (hθ : 0 ≤ θ) (hq : 0 ≤ q) (he : 0 ≤ e) (hk : 0 ≤ k) (hγ : 0 ≤ γ)
    (hI : I ≤ 2.56 * e * √b / √P)
    (hw : θ * q * √b ≤ (5 / 3 : ℝ) * √2 * k * γ) :
    (320 / 21 : ℝ) * θ * q * I ≤ 92 * k / √P * e * γ := by
  have hC : (320 / 21 : ℝ) * (5 / 3) * √2 * 2.56 ≤ 92 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg 2
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hI
    (by positivity : 0 ≤ (320 / 21 : ℝ) * θ * q)
  have h2 := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ (320 / 21 : ℝ) * 2.56 * e / √P)
  have h3 := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ k / √P * e * γ)
  ring_nf at h1 h2 h3 ⊢
  linarith
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
variable {m n l p a b : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
  [Fintype a] [Fintype b]
private theorem integrable_compressed_core_norm (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    {F : Matrix a m ℝ} {T : Matrix n b ℝ} (hF : specNorm F ≤ 1) (hT : specNorm T ≤ 1)
    (hη : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p)) :
    Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (F * (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) * T))
      (gaussianMatrix m p) := by
  have hNm := (measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A).comp
    ((measurable_const (a := x)).prodMk (measurable_id (α := Matrix m p ℝ)))
  refine (hη.add (integrable_const 1)).mono'
    (continuous_specNorm.measurable.comp
      ((measurable_const.matrix_mul hNm).matrix_mul measurable_const)).aestronglyMeasurable
    (ae_of_all _ fun ψ => ?_)
  let N := obliqueProjector (A * x) ψᴴ * (A - rsvd A x)
  have h1 : specNorm (F * N * T) ≤ specNorm N := by
    refine (specNorm_mul_le _ _).trans ?_
    calc specNorm (F * N) * specNorm T ≤ specNorm (F * N) :=
      mul_le_of_le_one_right (specNorm_nonneg _) hT
      _ ≤ specNorm F * specNorm N := specNorm_mul_le _ _
      _ ≤ specNorm N := mul_le_of_le_one_left (specNorm_nonneg _) hF
  rw [Real.norm_of_nonneg (specNorm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (specNorm N - 1)]
end NLAlib

namespace NLAlib
private theorem compressed_moment_majorant {I β e f s t v P r b : ℝ}
    (hβ : 0 ≤ β) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hv : 0 ≤ v) (hfs : f ≤ 1) (hff : s ≤ √b) (hts : t ≤ e) (htf : v ≤ e * √b)
    (hI : I ≤ β * f * v + s * t / √(P - r - 1))
    (hcoef : β + 1 / √(P - r - 1) ≤ 2.56 / √P) :
    I ≤ 2.56 * e * √b / √P := by
  have h1 : β * f * v ≤ β * (e * √b) := by
    have hh : f * v ≤ v := mul_le_of_le_one_left hv hfs
    nlinarith [mul_le_mul_of_nonneg_left (hh.trans htf) hβ]
  have h2 : s * t / √(P - r - 1) ≤ √b * e / √(P - r - 1) := by
    gcongr
  have h3 := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ e * √b)
  ring_nf at hI h1 h2 h3 ⊢
  linarith
end NLAlib

namespace NLAlib
private theorem supplied_moment_majorant {P L F e h β : ℝ}
    (hP : 0 < P) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hβ : P * β ^ 2 ≤ 2.3) (hH : P * h ≤ 1.078 * L) :
    (e * √h + F * β) ^ 2 + (e * β) ^ 2 ≤
      (7.3 * F ^ 2 + (1.574 * L + 2.3) * e ^ 2) / P := by
  have hpH : 0 ≤ P * h := mul_nonneg hP.le hh
  have hbH := mul_le_mul hβ hH hpH (by norm_num : (0 : ℝ) ≤ 2.3)
  have hcross : 2 * P * β * √h * e * F ≤ 5 * F ^ 2 + 0.496 * L * e ^ 2 := by
    have hs := sq_nonneg (P * β * √h * e - 5 * F)
    ring_nf at hs
    rw [Real.sq_sqrt hh] at hs
    have hm := mul_le_mul_of_nonneg_right hbH (sq_nonneg e)
    nlinarith only [hs, hm, mul_nonneg hL (sq_nonneg e)]
  rw [le_div_iff₀ hP]
  simp only [add_sq, mul_pow, Real.sq_sqrt hh]
  have h1 := mul_le_mul_of_nonneg_right hβ (sq_nonneg F)
  have h2 := mul_le_mul_of_nonneg_right hβ (sq_nonneg e)
  have h3 := mul_le_mul_of_nonneg_right hH (sq_nonneg e)
  nlinarith only [hcross, h1, h2, h3]
end NLAlib

namespace NLAlib
private theorem nested_projector_norms {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m]
    {P Q : Matrix m m 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hQP : Q * P = P) {b : ℕ} (hQb : Q.rank ≤ b) :
    specNorm (Q - P) ≤ 1 ∧ frobNorm (Q - P) ^ 2 ≤ b := by
  classical
  have hR : IsStarProjection (Q - P) := hP.sub_of_mul_eq_right hQ hQP
  refine ⟨hR.specNorm_le_one, ?_⟩
  rw [hR.frobNorm_sq_eq_rank]
  have heq : Q - P = Q * (1 - P) := by rw [Matrix.mul_sub, Matrix.mul_one, hQP]
  have hr : (Q - P).rank ≤ Q.rank := by
    rw [heq]
    exact Matrix.rank_mul_le_left _ _
  exact_mod_cast hr.trans hQb
private theorem window_count_scalar {θ γ : ℝ} {k b : ℕ} (hθ : 0 ≤ θ)
    (hγ : 0 ≤ γ) (hkb : k ≤ b)
    (hcount : ((b - k : ℕ) : ℝ) * θ ^ 2 ≤ (5 / 3 : ℝ) ^ 2 * γ ^ 2) :
    θ * ((min k (b - k) : ℕ) : ℝ) * √(b : ℝ) ≤
      (5 / 3 : ℝ) * √2 * k * γ := by
  set q := b - k
  have hb : (b : ℝ) = k + q := by
    have : b = k + q := by dsimp only [q]; omega
    exact_mod_cast this
  have hkey : ((min k q : ℕ) : ℝ) ^ 2 * (b : ℝ) ≤ 2 * (k : ℝ) ^ 2 * q := by
    rw [hb]
    rcases le_total k q with h | h
    · rw [min_eq_left h]
      have h' : (k : ℝ) ≤ q := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left h' (sq_nonneg (k : ℝ))]
    · rw [min_eq_right h]
      have h' : (q : ℝ) ≤ k := by exact_mod_cast h
      have hkq : 0 ≤ (k : ℝ) * q := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h' hkq,
        mul_le_mul_of_nonneg_left h' (sq_nonneg (q : ℝ))]
  have hs : (θ * ((min k q : ℕ) : ℝ) * √(b : ℝ)) ^ 2 ≤
      ((5 / 3 : ℝ) * √2 * k * γ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hkey (sq_nonneg θ)
    have h2 := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 2 * (k : ℝ) ^ 2)
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg b),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp only [q] at h1
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hs
end NLAlib

namespace NLAlib
variable {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
private theorem integral_truncation_window_le (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    {k a b : ℕ} (hk : 1 ≤ k) (hp : Fintype.card l ≤ Fintype.card p)
    (hak : a ≤ k) (hkb : k ≤ b)
    (ha : ∀ i < a, (5 / 3 : ℝ) * singularValues (rsvd A x) (k - 1) ≤
      singularValues (rsvd A x) i)
    (ha₂ : singularValues (rsvd A x) a ≤ (5 / 3 : ℝ) * singularValues (rsvd A x) (k - 1))
    (hb : singularValues (rsvd A x) b ≤ singularValues (rsvd A x) (k - 1) / (5 / 3 : ℝ))
    (U V : ℝ)
    (hη : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p))
    (hηU : ∫ ψ, specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤ U)
    (hμ : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm ((rangeProjector (truncatedSVD (rsvd A x) b) -
        rangeProjector (truncatedSVD (rsvd A x) a)) *
        (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) *
        (rangeProjector (truncatedSVD (rsvd A x) b)ᴴ -
          rangeProjector (truncatedSVD (rsvd A x) a)ᴴ))) (gaussianMatrix m p))
    (hμV : ∫ ψ, specNorm ((rangeProjector (truncatedSVD (rsvd A x) b) -
        rangeProjector (truncatedSVD (rsvd A x) a)) *
        (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) *
        (rangeProjector (truncatedSVD (rsvd A x) b)ᴴ -
          rangeProjector (truncatedSVD (rsvd A x) a)ᴴ)) ∂(gaussianMatrix m p) ≤ V) :
    ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
      ∂(gaussianMatrix m p) ≤ frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
        69 * k * U + (320 / 21 : ℝ) * singularValues (rsvd A x) (k - 1) *
          ((min k (b - k) : ℕ) : ℝ) * V := by
  classical
  let N := fun ψ : Matrix m p ℝ => obliqueProjector (A * x) ψᴴ * (A - rsvd A x)
  let W := rangeProjector (truncatedSVD (rsvd A x) b) -
    rangeProjector (truncatedSVD (rsvd A x) a)
  let W' := rangeProjector (truncatedSVD (rsvd A x) b)ᴴ -
    rangeProjector (truncatedSVD (rsvd A x) a)ᴴ
  let C := (320 / 21 : ℝ) * singularValues (rsvd A x) (k - 1) *
    ((min k (b - k) : ℕ) : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (singularValues_nonneg _ _))
      (Nat.cast_nonneg _)
  have hpt : ∀ᵐ ψ ∂(gaussianMatrix m p),
      frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2 ≤
        frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
          69 * k * specNorm (N ψ) ^ 2 + C * specNorm (W * N ψ * W') := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x)
      HasLaw.id ((Matrix.rank_le_card_width _).trans hp)] with ψ hψ
    refine (frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window_of_singularValues_le
      hψ hk hak hkb ha ha₂ hb).trans ?_
    dsimp only [C, N, W, W', id_eq]
    gcongr
    · exact reciprocalWindowNoiseConstant_le
    · exact reciprocalWindowCrossConstant_le
  have h1 : Integrable (fun ψ => frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
      69 * k * specNorm (N ψ) ^ 2) (gaussianMatrix m p) :=
    (integrable_const _).add (hη.const_mul _)
  have hg : Integrable (fun ψ => frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
      69 * k * specNorm (N ψ) ^ 2 + C * specNorm (W * N ψ * W')) (gaussianMatrix m p) :=
    h1.add (hμ.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hg hpt).trans ?_
  rw [integral_add h1 (hμ.const_mul _), integral_add (integrable_const _) (hη.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, probReal_univ, one_smul]
  have h1 := mul_le_mul_of_nonneg_left hηU (by positivity : (0 : ℝ) ≤ 69 * k)
  have h2 := mul_le_mul_of_nonneg_left hμV hC
  dsimp [N, W, W', C] at *
  linarith
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
variable {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
private theorem conditional_window_moment_bound
    (A : Matrix m n ℝ) (x : Matrix n l ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hp : Fintype.card l ≤ Fintype.card p)
    (hη : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p))
    (hηU : ∫ ψ, specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤
      (7.3 * frobNorm (A - rsvd A x) ^ 2 +
        (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) / Fintype.card p)
    (hcomp : ∀ (F : Matrix m m ℝ) (T : Matrix n n ℝ) (b : ℕ),
      specNorm F ≤ 1 → specNorm T ≤ 1 → frobNorm F ^ 2 ≤ b → frobNorm T ^ 2 ≤ b →
      ∫ ψ, specNorm (F * (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) * T)
        ∂(gaussianMatrix m p) ≤
        2.56 * specNorm (A - rsvd A x) * √(b : ℝ) / √(Fintype.card p : ℝ)) :
    ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
      ∂(gaussianMatrix m p) ≤ frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
        69 * k / Fintype.card p *
          (7.3 * frobNorm (A - rsvd A x) ^ 2 +
            (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) +
        92 * k / √(Fintype.card p : ℝ) * specNorm (A - rsvd A x) *
          frobNorm (rsvd A x - truncatedSVD (rsvd A x) k) := by
  classical
  obtain ⟨a, b, hak, hkb, ha, ha₂, hb, hcount⟩ :=
    exists_singularValues_window_of_one_lt (rsvd A x) hk (by norm_num : (1 : ℝ) < 5 / 3)
  let W := rangeProjector (truncatedSVD (rsvd A x) b) -
    rangeProjector (truncatedSVD (rsvd A x) a)
  let W' := rangeProjector (truncatedSVD (rsvd A x) b)ᴴ -
    rangeProjector (truncatedSVD (rsvd A x) a)ᴴ
  have hW := nested_projector_norms (isStarProjection_rangeProjector _)
    (isStarProjection_rangeProjector _)
    (rangeProjector_mul_rangeProjector_of_range_le
      (range_truncatedSVD_mono (rsvd A x) (hak.trans hkb)))
    (b := b) (by rw [rank_rangeProjector]; exact rank_truncatedSVD_le _ _)
  have hW' := nested_projector_norms (isStarProjection_rangeProjector _)
    (isStarProjection_rangeProjector _)
    (rangeProjector_mul_rangeProjector_of_range_le
      (range_conjTranspose_truncatedSVD_le (rsvd A x) (hak.trans hkb)))
    (b := b) (by
      rw [rank_rangeProjector, Matrix.rank_conjTranspose]
      exact rank_truncatedSVD_le _ _)
  have hμ := integrable_compressed_core_norm A x hW.1 hW'.1 hη
  have hI := hcomp W W' b hW.1 hW'.1 hW.2 hW'.2
  have hbound := integral_truncation_window_le A x hk hp hak hkb ha ha₂ hb _ _
    hη hηU hμ le_rfl
  have hwin := integrated_window_term_le (singularValues_nonneg (rsvd A x) (k - 1))
    (Nat.cast_nonneg _) (specNorm_nonneg _) (Nat.cast_nonneg (α := ℝ) k) (frobNorm_nonneg _) hI
    (window_count_scalar (singularValues_nonneg (rsvd A x) (k - 1))
      (frobNorm_nonneg _) hkb hcount)
  dsimp [W, W'] at *
  ring_nf at hbound hwin ⊢
  linarith
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
variable {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
-- The called supplied-moment declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
private theorem core_spectral_second_moment_le
    (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    (hL : 200 ≤ Fintype.card l) (hLP : 14 * Fintype.card l ≤ Fintype.card p) :
    Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p) ∧
    (∫ ψ, specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p)) ≤
      (7.3 * frobNorm (A - rsvd A x) ^ 2 +
        (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) / Fintype.card p := by
  classical
  have hr := Matrix.rank_le_card_width (A * x)
  have hP : 2800 ≤ Fintype.card p := by omega
  have hrP : 14 * (A * x).rank ≤ Fintype.card p := by omega
  let β := √(2.3 / (Fintype.card p : ℝ))
  have hP0 : (0 : ℝ) < Fintype.card p := by exact_mod_cast (by omega : 0 < Fintype.card p)
  have hβ : (Fintype.card p : ℝ) * β ^ 2 ≤ 2.3 := by
    dsimp [β]
    rw [Real.sq_sqrt (by positivity)]
    have he : (Fintype.card p : ℝ) * (2.3 / Fintype.card p) = 2.3 := by field_simp
    exact he.le
  have hcanonical : (∫ G : Matrix (Fin (A * x).rank) p ℝ, specNorm (pinv G) ^ 2
      ∂(gaussianMatrix (Fin (A * x).rank) p)) ≤ β ^ 2 := by
    rw [show β ^ 2 = 2.3 / Fintype.card p by dsimp [β]; rw [Real.sq_sqrt (by positivity)]]
    exact integral_specNorm_pinv_sq_le_div_of_hasLaw_gaussianMatrix_of_fourteen_mul_le
      HasLaw.id hP (by simpa using hrP)
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix
    (HasLaw.id : HasLaw (fun ψ : Matrix m p ℝ => ψ)
      (gaussianMatrix m p) (gaussianMatrix m p))
  have hη :=
    integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
    hS (A * x) (by omega) A
  have hI :=
    integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix_of_integral_le
    hS (A * x) (by omega) A (β := β) (Real.sqrt_nonneg _) hcanonical
  rw [← sub_rsvd] at hη hI
  refine ⟨hη, hI.trans ?_⟩
  have hd : (0 : ℝ) ≤ (Fintype.card p : ℝ) - (A * x).rank - 1 := by
    have hh : ((A * x).rank : ℝ) + 1 ≤ Fintype.card p := by
      exact_mod_cast (by omega : (A * x).rank + 1 ≤ Fintype.card p)
    linarith
  apply supplied_moment_majorant hP0 (Nat.cast_nonneg _)
    (div_nonneg (Nat.cast_nonneg _) hd) hβ
  apply rank_ratio_le
  · exact_mod_cast hL
  · exact_mod_cast hLP
  · exact_mod_cast hr
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
variable {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
-- The called supplied-moment declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
private theorem compressed_core_first_moment_le
    (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    (hL : 200 ≤ Fintype.card l) (hLP : 14 * Fintype.card l ≤ Fintype.card p)
    (F : Matrix m m ℝ) (T : Matrix n n ℝ) (b : ℕ)
    (hF : specNorm F ≤ 1) (hT : specNorm T ≤ 1)
    (hF2 : frobNorm F ^ 2 ≤ b) (hT2 : frobNorm T ^ 2 ≤ b) :
    ∫ ψ, specNorm (F * (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) * T)
      ∂(gaussianMatrix m p) ≤
      2.56 * specNorm (A - rsvd A x) * √(b : ℝ) / √(Fintype.card p : ℝ) := by
  classical
  have hr := Matrix.rank_le_card_width (A * x)
  have hP : 2800 ≤ Fintype.card p := by omega
  have hrP : 14 * (A * x).rank ≤ Fintype.card p := by omega
  let β := √(2.3 / (Fintype.card p : ℝ))
  have hP0 : (0 : ℝ) < Fintype.card p := by exact_mod_cast (by omega : 0 < Fintype.card p)
  have hβ : (Fintype.card p : ℝ) * β ^ 2 ≤ 2.3 := by
    dsimp [β]
    rw [Real.sq_sqrt (by positivity)]
    have he : (Fintype.card p : ℝ) * (2.3 / Fintype.card p) = 2.3 := by field_simp
    exact he.le
  have hcanonical : (∫ G : Matrix (Fin (A * x).rank) p ℝ, specNorm (pinv G) ^ 2
      ∂(gaussianMatrix (Fin (A * x).rank) p)) ≤ β ^ 2 := by
    rw [show β ^ 2 = 2.3 / Fintype.card p by dsimp [β]; rw [Real.sq_sqrt (by positivity)]]
    exact integral_specNorm_pinv_sq_le_div_of_hasLaw_gaussianMatrix_of_fourteen_mul_le
      HasLaw.id hP (by simpa using hrP)
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix
    (HasLaw.id : HasLaw (fun ψ : Matrix m p ℝ => ψ)
      (gaussianMatrix m p) (gaussianMatrix m p))
  have hI :=
    integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix_of_integral_le
    hS (A * x) (by omega) (A * T) F (β := β) (Real.sqrt_nonneg _) hcanonical
  have heq : (1 - rangeProjector (A * x)) * (A * T) = (A - rsvd A x) * T := by
    rw [sub_rsvd, Matrix.mul_assoc]
  rw [heq] at hI
  simp only [Matrix.mul_assoc]
  have hFf : frobNorm F ≤ √(b : ℝ) :=
    (sq_le_sq₀ (frobNorm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by simpa only [Real.sq_sqrt (Nat.cast_nonneg b)] using hF2)
  have hTf : frobNorm T ≤ √(b : ℝ) :=
    (sq_le_sq₀ (frobNorm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by simpa only [Real.sq_sqrt (Nat.cast_nonneg b)] using hT2)
  have hET : specNorm ((A - rsvd A x) * T) ≤ specNorm (A - rsvd A x) :=
    (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _) hT)
  have hETf : frobNorm ((A - rsvd A x) * T) ≤ specNorm (A - rsvd A x) * √(b : ℝ) :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
      (mul_le_mul_of_nonneg_left hTf (specNorm_nonneg _))
  have hcoef := weighted_first_moment_coefficient_le
    (show (2800 : ℝ) ≤ Fintype.card p by exact_mod_cast hP)
    (show 14 * ((A * x).rank : ℝ) ≤ Fintype.card p by exact_mod_cast hrP) hβ
  exact compressed_moment_majorant (Real.sqrt_nonneg _) (specNorm_nonneg _)
    (specNorm_nonneg _) (frobNorm_nonneg _) hF hFf hET hETf hI hcoef
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
variable {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
/-- Conditional Gaussian generalized Nyström: fix an arbitrary range sketch x, assume
$k\ge1$, $\ell\ge200$ and $p\ge14\ell$, and write
$R=\mathsf{rsvd}(A,x)$, $F=\|A-R\|_{\mathsf F}$, $e=\|A-R\|_2$ and
$T=\|R-R_k\|_{\mathsf F}$. Integrating only the standard Gaussian co-range sketch gives
$$\mathbb E_\Psi\|A-\operatorname{trunc}_k(\operatorname{GN}(A,x,\Psi))\|_{\mathsf F}^2
\le\|A-R_k\|_{\mathsf F}^2+
(69k/p)\bigl(7.3F^2+(1.574\ell+2.3)e^2\bigr)+(92k/\sqrt p)eT.$$
No printed source. -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_fourteen_mul_le
    (A : Matrix m n ℝ) (x : Matrix n l ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hL : 200 ≤ Fintype.card l) (hLP : 14 * Fintype.card l ≤ Fintype.card p) :
    ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
      ∂(gaussianMatrix m p) ≤ frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
        69 * k / Fintype.card p *
          (7.3 * frobNorm (A - rsvd A x) ^ 2 +
            (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) +
        92 * k / √(Fintype.card p : ℝ) * specNorm (A - rsvd A x) *
          frobNorm (rsvd A x - truncatedSVD (rsvd A x) k) := by
  obtain ⟨hη, hU⟩ := core_spectral_second_moment_le A x hL hLP
  exact conditional_window_moment_bound A x hk (by omega) hη hU
    (fun F T b hF hT hF2 hT2 =>
      compressed_core_first_moment_le A x hL hLP F T b hF hT hF2 hT2)
end NLAlib
