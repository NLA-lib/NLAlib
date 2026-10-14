/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# Inverse moments of Gaussian matrices

For a wide standard Gaussian matrix `G : r × k` (`r < k`), the moments of `(G Gᴴ)⁻¹` and of the
pseudoinverse `G† = Gᴴ (G Gᴴ)⁻¹` that the randomized range finder consumes (Halko, Martinsson and
Tropp 2011, Propositions 10.2 and 10.3): `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1`,
`E ‖G†‖_F² = r / (k - r - 1)` and the fourth moment of `‖G†‖_F`. The spectral moments of `G†`
(Proposition 10.4) are in `NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral`.

The route: by the Schur complement of one row, a diagonal entry of `(G Gᴴ)⁻¹` is the reciprocal
of the squared distance from that row to the span of the others, which, conditionally on the
others, is `χ²_{k-r+1}`; by rotation invariance every probe `u ⬝ (G Gᴴ)⁻¹ u` with `‖u‖ = 1` has the
same law. The off-diagonal means follow from the probes at `(eᵢ ± eⱼ)/√2`. The fourth moment needs
one more input, the off-diagonal second moment, from the independence of the regression
coefficients of one row on the others and its residual.

`(G Gᴴ)⁻¹` is Lean's `0` on the null set where `G` does not have full row rank, and `pinv` is
total; the integrals are unaffected.

## Main results

* `NLAlib.integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix`: the
  moments of the probes, `E (u ⬝ (G Gᴴ)⁻¹ u)^q = E (1/χ²_{k-r+1})^q`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {r k : Type*} [Fintype r]
  [Fintype k] {X : Ω → Matrix r k ℝ}

section Entries

variable [DecidableEq r]

/-- The rows of `G` other than row `i`, as the columns of a `k × (r - 1)` matrix. -/
private def otherRows (G : Matrix r k ℝ) (i : r) : Matrix k {j // j ≠ i} ℝ :=
  (G.submatrix Subtype.val id)ᴴ

omit [Fintype r] [Fintype k] [DecidableEq r] in
private theorem otherRows_apply (G : Matrix r k ℝ) (i : r) (l : k) (j : {j // j ≠ i}) :
    otherRows G i l j = G j l := by
  simp only [otherRows, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, star_trivial]

/-- **The Schur complement of one row.** If the rows of `G` other than row `i` are linearly
independent, the `i`-th column of `(G Gᴴ)⁻¹` is `s⁻¹ x`, with `s` the squared distance from row `i`
to the span of the others and `x = eᵢ - c` for the regression coefficients `c`. -/
private theorem inv_mul_conjTranspose_mulVec_single [DecidableEq k] (G : Matrix r k ℝ) (i : r)
    (hH : Function.Injective (otherRows G i).mulVec) :
    (G * Gᴴ)⁻¹ *ᵥ Pi.single i 1 =
      (‖WithLp.toLp 2 ((1 - rangeProjector (otherRows G i)) *ᵥ G i)‖ ^ 2)⁻¹ •
        fun j => if h : j = i then 1 else -(pinv (otherRows G i) *ᵥ G i) ⟨j, h⟩ := by
  set B := otherRows G i with hB
  set g := G i with hg
  set P := rangeProjector B with hP
  set c := pinv B *ᵥ g with hc
  set w := (1 - P) *ᵥ g with hw
  set x : r → ℝ := fun j => if h : j = i then 1 else -c ⟨j, h⟩ with hx
  set s := ‖WithLp.toLp 2 w‖ ^ 2 with hs
  have hBc : B *ᵥ c = P *ᵥ g := by
    rw [hc, Matrix.mulVec_mulVec, mul_pinv]
  have hGx : Gᴴ *ᵥ x = w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_trivial]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hw, Matrix.sub_mulVec, Matrix.one_mulVec, ← hBc]
    simp only [hx, dif_pos rfl, mul_one, Pi.sub_apply, Matrix.mulVec, dotProduct, hB,
      otherRows_apply]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_neg j.2]
    ring
  have hBw : Bᴴ *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_mulVec, conjTranspose_mul_one_sub_rangeProjector, Matrix.zero_mulVec]
  have hgw : g ⬝ᵥ w = s := by
    have h1 : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [(isStarProjection_one_sub_rangeProjector B).conjTranspose_eq,
        (isStarProjection_one_sub_rangeProjector B).mul_self]
    rw [hs, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    calc g ⬝ᵥ w = g ⬝ᵥ (((1 - P)ᴴ * (1 - P)) *ᵥ g) := by rw [h1]
      _ = w ⬝ᵥ w := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.vecMul_transpose]
  have hGw : G *ᵥ w = Pi.single i s := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, ← hgw]
      rfl
    · rw [Pi.single_eq_of_ne hj]
      have := congrFun hBw ⟨j, hj⟩
      simpa only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_trivial, hB,
        otherRows_apply, Pi.zero_apply] using this
  have hWx : (G * Gᴴ) *ᵥ x = Pi.single i s := by rw [← Matrix.mulVec_mulVec, hGx, hGw]
  have hunit : IsUnit (G * Gᴴ) ↔ Function.Injective Gᴴ.mulVec := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      isUnit_conjTranspose_mul_self_iff (A := Gᴴ)
  have hxi : x i = 1 := by simp only [hx, dif_pos rfl]
  by_cases hs0 : s = 0
  · have hw0 : w = 0 := by
      have h := hs0
      rw [hs, sq_eq_zero_iff, norm_eq_zero] at h
      exact (WithLp.toLp_injective 2) (h.trans (WithLp.toLp_zero 2).symm)
    have hnot : ¬IsUnit (G * Gᴴ) := by
      rw [hunit]
      intro hinj
      have h0 : x = 0 := hinj (by rw [hGx, hw0, Matrix.mulVec_zero])
      have := congrFun h0 i
      rw [hxi, Pi.zero_apply] at this
      exact one_ne_zero this
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (mt (Matrix.isUnit_iff_isUnit_det _).2 hnot),
      Matrix.zero_mulVec, hs0, inv_zero, zero_smul]
  · have hinj : Function.Injective Gᴴ.mulVec := by
      refine (injective_iff_map_eq_zero Gᴴ.mulVecLin).2 fun y hy => ?_
      rw [Matrix.mulVecLin_apply] at hy
      have hyi : y i = 0 := by
        have h := congrArg (w ⬝ᵥ ·) hy
        simp only [dotProduct_zero] at h
        rw [Matrix.dotProduct_mulVec, Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.vecMul_transpose, hGw, single_dotProduct] at h
        exact (mul_eq_zero.1 h).resolve_left hs0
      have hBy : B *ᵥ (fun j : {j // j ≠ i} => y j) = 0 := by
        rw [← hy]
        funext l
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_trivial, hB,
          otherRows_apply]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hyi, mul_zero, zero_add]
      have hy' : (fun j : {j // j ≠ i} => y j) = 0 := hH (by rw [hBy, Matrix.mulVec_zero])
      funext j
      by_cases hj : j = i
      · rw [hj, hyi, Pi.zero_apply]
      · exact congrFun hy' ⟨j, hj⟩
    have hU := (Matrix.isUnit_iff_isUnit_det _).1 (hunit.2 hinj)
    have h := congrArg ((G * Gᴴ)⁻¹ *ᵥ ·) hWx
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec] at h
    have hsingle : (Pi.single i s : r → ℝ) = s • Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]
      · simp only [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_zero]
    rw [h, hsingle, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]

private theorem inv_mul_conjTranspose_apply_self [DecidableEq k] (G : Matrix r k ℝ) (i : r)
    (hH : Function.Injective (otherRows G i).mulVec) :
    (G * Gᴴ)⁻¹ i i = (‖WithLp.toLp 2 ((1 - rangeProjector (otherRows G i)) *ᵥ G i)‖ ^ 2)⁻¹ := by
  have h := congrFun (inv_mul_conjTranspose_mulVec_single G i hH) i
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, dif_pos rfl, smul_eq_mul,
    mul_one] at h

private theorem inv_mul_conjTranspose_apply_of_ne [DecidableEq k] (G : Matrix r k ℝ) {i j : r}
    (hji : j ≠ i) (hH : Function.Injective (otherRows G i).mulVec) :
    (G * Gᴴ)⁻¹ j i = -(pinv (otherRows G i) *ᵥ G i) ⟨j, hji⟩ *
      (‖WithLp.toLp 2 ((1 - rangeProjector (otherRows G i)) *ᵥ G i)‖ ^ 2)⁻¹ := by
  have h := congrFun (inv_mul_conjTranspose_mulVec_single G i hH) j
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, dif_neg hji, smul_eq_mul,
    mul_comm] at h

/-- Off the null set where the other rows are dependent, the column space of the other rows has
a complement of dimension `k - r + 1` with an orthonormal basis `V`, and `‖(1 - P) g‖ = ‖Vᴴ g‖`. -/
private theorem exists_norm_one_sub_rangeProjector_mulVec_eq [DecidableEq k] {t : Type*} [Fintype t]
    (B : Matrix k t ℝ) (hB : Function.Injective B.mulVec) {d : ℕ}
    (hd : Fintype.card t + d = Fintype.card k) :
    ∃ V : Matrix k (Fin d) ℝ, HasOrthonormalCols V ∧ ∀ g : k → ℝ,
      ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ g)‖ = ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ := by
  have hrank := rank_one_sub_rangeProjector_add_rank B
  rw [mulVec_injective_iff_rank_eq.1 hB] at hrank
  obtain ⟨V, hV, hVV⟩ :=
    (isStarProjection_one_sub_rangeProjector B).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := Fin d) (by rw [Fintype.card_fin]; omega)
  refine ⟨V, hV, fun g => ?_⟩
  rw [← hVV, ← Matrix.mulVec_mulVec, hV.norm_toLp_mulVec]

private theorem card_subtype_ne_add {i : r} (hrk : Fintype.card r ≤ Fintype.card k) :
    Fintype.card {j // j ≠ i} + (Fintype.card k - Fintype.card r + 1) = Fintype.card k := by
  have h1 : Fintype.card {j // j ≠ i} = Fintype.card r - 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have h2 : 0 < Fintype.card r := Fintype.card_pos_iff.2 ⟨i⟩
  omega

/-- Row `i` and the other rows of a Gaussian matrix are independent Gaussians. -/
private theorem hasLaw_row_otherRows (hX : HasLaw X (gaussianMatrix r k) μ) (i : r) :
    HasLaw (fun ω => (X ω i, (X ω).submatrix (Subtype.val : {j // j ≠ i} → r) id))
      ((gaussianVector k).prod (gaussianMatrix {j // j ≠ i} k)) μ := by
  have := hX.isProbabilityMeasure
  have hHlaw : HasLaw (fun ω => (X ω).submatrix (Subtype.val : {j // j ≠ i} → r) id)
      (gaussianMatrix {j // j ≠ i} k) μ :=
    hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Subtype.val_injective Function.injective_id
  refine (indepFun_iff_hasLaw_prodMk_prod (hX.eval i) hHlaw).1 ?_
  have h := (hX.iIndepFun_eval).indepFun_finset₀ {i} (Finset.univ.filter (· ≠ i))
    (by simp) fun j => (hX.eval j).aemeasurable
  have h₁ : Measurable fun f : ({i} : Finset r) → k → ℝ => f ⟨i, Finset.mem_singleton_self i⟩ :=
    measurable_pi_apply _
  have h₂ : Measurable fun (f : (Finset.univ.filter (· ≠ i) : Finset r) → k → ℝ)
      (j : {j // j ≠ i}) => f ⟨j.1, by simpa using j.2⟩ :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  exact h.comp h₁ h₂

omit [DecidableEq r] in
/-- A Gaussian matrix with at most as many rows as columns has independent rows a.s. -/
private theorem ae_injective_conjTranspose_mulVec {t : Type*} [Fintype t] {ν : Measure Ω}
    {Y : Ω → Matrix t k ℝ} (hY : HasLaw Y (gaussianMatrix t k) ν)
    (htk : Fintype.card t ≤ Fintype.card k) :
    ∀ᵐ ω ∂ν, Function.Injective (Y ω)ᴴ.mulVec := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with ω hω
  rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, hω, min_eq_left htk]

omit [DecidableEq r] in
private theorem measurable_one_sub_rangeProjector_mulVec [DecidableEq k] {t : Type*} [Fintype t] :
    Measurable fun p : (k → ℝ) × Matrix t k ℝ => (1 - rangeProjector p.2ᴴ) *ᵥ p.1 :=
  (measurable_const.matrix_sub (measurable_rangeProjector.comp
    ((continuous_id.matrix_conjTranspose).measurable.comp measurable_snd))).matrix_mulVec
    measurable_fst

/-- **The law of a diagonal entry of `(G Gᴴ)⁻¹`**, as an identity of lower integrals: it is that
of `1 / χ²_{k-r+1}`. -/
private theorem lintegral_comp_inv_mul_conjTranspose_apply_self
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r ≤ Fintype.card k) (i : r)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, φ ((X ω * (X ω)ᴴ)⁻¹ i i) ∂μ =
      ∫⁻ z, φ ((‖WithLp.toLp 2 z‖ ^ 2)⁻¹)
        ∂(gaussianVector (Fin (Fintype.card k - Fintype.card r + 1))) := by
  classical
  have := hX.isProbabilityMeasure
  set d := Fintype.card k - Fintype.card r + 1 with hd
  set t := {j // j ≠ i}
  have hcard : Fintype.card t + d = Fintype.card k := card_subtype_ne_add hrk
  set ψ : (k → ℝ) × Matrix t k ℝ → ℝ≥0∞ := fun p =>
    φ ((‖WithLp.toLp 2 ((1 - rangeProjector p.2ᴴ) *ᵥ p.1)‖ ^ 2)⁻¹) with hψ
  have hψm : Measurable ψ := hφ.comp ((((continuous_norm.comp
    (PiLp.continuous_toLp 2 _)).measurable.comp
      measurable_one_sub_rangeProjector_mulVec).pow_const 2).inv)
  have hHlaw : HasLaw (fun ω => (X ω).submatrix (Subtype.val : t → r) id) (gaussianMatrix t k) μ :=
    hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Subtype.val_injective Function.injective_id
  calc ∫⁻ ω, φ ((X ω * (X ω)ᴴ)⁻¹ i i) ∂μ =
        ∫⁻ ω, ψ (X ω i, (X ω).submatrix (Subtype.val : t → r) id) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_injective_conjTranspose_mulVec hHlaw
          (by have := card_subtype_ne_add (k := k) (i := i) hrk; omega)] with ω hω
        rw [inv_mul_conjTranspose_apply_self (X ω) i hω]
        rfl
    _ = ∫⁻ p, ψ p ∂((gaussianVector k).prod (gaussianMatrix t k)) :=
        (hasLaw_row_otherRows hX i).lintegral_comp hψm.aemeasurable
    _ = ∫⁻ H, ∫⁻ g, ψ (g, H) ∂(gaussianVector k) ∂(gaussianMatrix t k) :=
        lintegral_prod_symm _ hψm.aemeasurable
    _ = ∫⁻ _H, ∫⁻ z, φ ((‖WithLp.toLp 2 z‖ ^ 2)⁻¹) ∂(gaussianVector (Fin d))
          ∂(gaussianMatrix t k) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_injective_conjTranspose_mulVec
          (HasLaw.id (μ := gaussianMatrix t k))
          (by have := card_subtype_ne_add (k := k) (i := i) hrk; omega)] with H hinj
        obtain ⟨V, hV, hVg⟩ := exists_norm_one_sub_rangeProjector_mulVec_eq Hᴴ hinj hcard
        have hVlaw : HasLaw (fun g : k → ℝ => Vᴴ *ᵥ g) (gaussianVector (Fin d))
            (gaussianVector k) :=
          hasLaw_mulVec_of_hasLaw_gaussianVector HasLaw.id
            (by rwa [Matrix.conjTranspose_conjTranspose])
        simp only [hψ, hVg]
        exact hVlaw.lintegral_comp (f := fun z => φ ((‖WithLp.toLp 2 z‖ ^ 2)⁻¹))
          (by fun_prop)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

private theorem measurable_inv_mul_conjTranspose :
    Measurable fun G : Matrix r k ℝ => (G * Gᴴ)⁻¹ :=
  (measurable_id.matrix_mul (continuous_id.matrix_conjTranspose).measurable).matrix_inv

/-- The law of `1 / χ²_d`. -/
private noncomputable abbrev invChiSq (d : ℕ) : Measure ℝ :=
  (gaussianVector (Fin d)).map fun z => (‖WithLp.toLp 2 z‖ ^ 2)⁻¹

private theorem hasLaw_of_lintegral_eq {Y : Ω → ℝ} (hY : AEMeasurable Y μ) {d : ℕ}
    (h : ∀ φ : ℝ → ℝ≥0∞, Measurable φ →
      ∫⁻ ω, φ (Y ω) ∂μ = ∫⁻ z, φ ((‖WithLp.toLp 2 z‖ ^ 2)⁻¹) ∂(gaussianVector (Fin d))) :
    HasLaw Y (invChiSq d) μ := by
  refine ⟨hY, Measure.ext_of_lintegral _ fun φ hφ => ?_⟩
  rw [lintegral_map' hφ.aemeasurable hY, h φ hφ, lintegral_map hφ (by fun_prop)]

/-- **The diagonal entries of `(G Gᴴ)⁻¹` are `1 / χ²_{k-r+1}`.** -/
private theorem hasLaw_inv_mul_conjTranspose_apply_self (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) (i : r) :
    HasLaw (fun ω => (X ω * (X ω)ᴴ)⁻¹ i i)
      (invChiSq (Fintype.card k - Fintype.card r + 1)) μ :=
  hasLaw_of_lintegral_eq (((Matrix.measurable_apply i i).comp
    measurable_inv_mul_conjTranspose).comp_aemeasurable hX.aemeasurable)
    fun _ hφ => lintegral_comp_inv_mul_conjTranspose_apply_self hX hrk i hφ

/-- A unit vector `u` is row `i` of an orthogonal matrix. -/
private theorem exists_hasOrthonormalCols_conjTranspose_row_eq {u : r → ℝ}
    (hu : ‖WithLp.toLp 2 u‖ = 1) (i : r) :
    ∃ Q : Matrix r r ℝ, HasOrthonormalCols Qᴴ ∧ Q i = u := by
  set U : Matrix r {a // a = i} ℝ := Matrix.of fun a _ => u a
  have hU : HasOrthonormalCols U := by
    rw [hasOrthonormalCols_iff]
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    rw [Matrix.one_apply_eq, Matrix.mul_apply]
    simp only [U, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    have h := EuclideanSpace.norm_toLp_sq_eq_dotProduct_self u
    rw [hu, one_pow] at h
    exact h.symm
  obtain ⟨U', hU'⟩ := hU.exists_fromCols (p := {a // ¬a = i}) (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have := Fintype.card_pos_iff.2 ⟨i⟩
    omega)
  set N := (Matrix.fromCols U U').submatrix (Equiv.refl r) (Equiv.sumCompl (· = i)).symm
  have hN : HasOrthonormalCols N := hU'.submatrix (Equiv.refl r) (Equiv.injective _)
  refine ⟨Nᴴ, by rwa [Matrix.conjTranspose_conjTranspose], funext fun a => ?_⟩
  simp only [N, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Equiv.refl_apply,
    star_trivial]
  rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x => x = i) rfl, Matrix.fromCols_apply_inl]
  rfl

private theorem inv_mul_mul_conjTranspose_apply {Q : Matrix r r ℝ} (hQ : HasOrthonormalCols Qᴴ)
    (G : Matrix r k ℝ) (i : r) :
    (Q * G * (Q * G)ᴴ)⁻¹ i i = Q i ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ Q i) := by
  have hQ' : HasOrthonormalCols Q := by
    have h := hQ.mul_conjTranspose_self
    rwa [Matrix.conjTranspose_conjTranspose, ← hasOrthonormalCols_iff] at h
  rw [Matrix.conjTranspose_mul, show Q * G * (Gᴴ * Qᴴ) = Q * (G * Gᴴ) * Qᴴ by
      simp only [Matrix.mul_assoc], Matrix.mul_inv_rev, Matrix.mul_inv_rev, hQ'.inv_eq,
    ← Matrix.conjTranspose_nonsing_inv, hQ'.inv_eq, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, dotProduct,
    Matrix.mulVec, Finset.mul_sum]

/-- **Probes of `(G Gᴴ)⁻¹` are `1 / χ²_{k-r+1}`**: for a unit vector `u`, `u ⬝ (G Gᴴ)⁻¹ u` has the
law of the diagonal entries. -/
private theorem hasLaw_dotProduct_inv_mul_conjTranspose_mulVec
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r ≤ Fintype.card k)
    {u : r → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    HasLaw (fun ω => u ⬝ᵥ ((X ω * (X ω)ᴴ)⁻¹ *ᵥ u))
      (invChiSq (Fintype.card k - Fintype.card r + 1)) μ := by
  obtain ⟨i⟩ : Nonempty r := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Subsingleton.elim (WithLp.toLp 2 u) 0, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨Q, hQ, hQi⟩ := exists_hasOrthonormalCols_conjTranspose_row_eq hu i
  have h := hasLaw_inv_mul_conjTranspose_apply_self
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix hX hQ) hrk i
  simp only [inv_mul_mul_conjTranspose_apply hQ, hQi] at h
  exact h

private theorem inv_rpow_norm_sq {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    ((‖WithLp.toLp 2 z‖ ^ 2)⁻¹) ^ s = (‖WithLp.toLp 2 z‖ ^ 2) ^ (-s) := by
  rw [Real.inv_rpow (sq_nonneg _), Real.rpow_neg (sq_nonneg _)]

private theorem integrable_rpow_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ}
    (hY : HasLaw Y (invChiSq d) μ) {s : ℝ} (hs : s < d / 2) :
    Integrable (fun ω => Y ω ^ s) μ := by
  have hf : Measurable fun x : ℝ => x ^ s := by fun_prop
  refine (hY.integrable_comp_iff hf.aestronglyMeasurable).2 ?_
  refine (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2 ?_
  have h := integrable_norm_sq_rpow_of_hasLaw_gaussianVector
    (HasLaw.id (μ := gaussianVector (Fin d))) (s := -s) (by simp only [Fintype.card_fin]; linarith)
  simpa only [Function.comp_def, inv_rpow_norm_sq, id_eq] using h

private theorem integral_rpow_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ}
    (hY : HasLaw Y (invChiSq d) μ) {s : ℝ} (hs : s < d / 2) :
    ∫ ω, Y ω ^ s ∂μ = 2 ^ (-s) * Real.Gamma ((d : ℝ) / 2 - s) / Real.Gamma ((d : ℝ) / 2) := by
  have hf : Measurable fun x : ℝ => x ^ s := by fun_prop
  have h := hY.integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_map (by fun_prop) hf.aestronglyMeasurable]
  simp only [inv_rpow_norm_sq]
  have h2 := integral_norm_sq_rpow_of_hasLaw_gaussianVector
    (HasLaw.id (μ := gaussianVector (Fin d))) (s := -s) (by simp only [Fintype.card_fin]; linarith)
  simp only [id_eq, Fintype.card_fin] at h2
  rw [h2, sub_eq_add_neg]

private theorem integrable_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ}
    (hY : HasLaw Y (invChiSq d) μ) (hd : 3 ≤ d) : Integrable Y μ := by
  have h := integrable_rpow_of_hasLaw_invChiSq hY (s := 1)
    (by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
  simpa only [Real.rpow_one] using h

private theorem integral_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ}
    (hY : HasLaw Y (invChiSq d) μ) (hd : 3 ≤ d) : ∫ ω, Y ω ∂μ = 1 / ((d : ℝ) - 2) := by
  have h := hY.integral_comp (f := id) measurable_id.aestronglyMeasurable
  simp only [Function.id_comp] at h
  rw [h, integral_map (by fun_prop) measurable_id.aestronglyMeasurable]
  have h2 := integral_norm_sq_inv_of_hasLaw_gaussianVector
    (HasLaw.id (μ := gaussianVector (Fin d))) (by rwa [Fintype.card_fin])
  simpa only [id_eq, Fintype.card_fin] using h2

private theorem integral_sq_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ}
    (hY : HasLaw Y (invChiSq d) μ) (hd : 5 ≤ d) :
    ∫ ω, Y ω ^ 2 ∂μ = 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integral_rpow_of_hasLaw_invChiSq hY (s := 2) (by linarith)
  simp only [← Real.rpow_natCast, Nat.cast_ofNat] at h ⊢
  rw [h, show (d : ℝ) / 2 = ((d : ℝ) / 2 - 2 + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
    Real.Gamma_add_one (by linarith), show (d : ℝ) / 2 - 2 + 1 + 1 - 2 = (d : ℝ) / 2 - 2 by ring]
  have hG : 0 < Real.Gamma ((d : ℝ) / 2 - 2) := Real.Gamma_pos_of_pos (by linarith)
  have h1 : (d : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (d : ℝ) - 4 ≠ 0 := by linarith
  rw [Real.rpow_neg (by norm_num), show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
  generalize Real.Gamma ((d : ℝ) / 2 - 2) = g at hG ⊢
  rw [div_eq_div_iff (mul_ne_zero (by linarith) (mul_ne_zero (by linarith) hG.ne'))
    (mul_ne_zero h1 h2)]
  ring

private theorem dotProduct_inv_mul_conjTranspose_mulVec_nonneg (G : Matrix r k ℝ) (u : r → ℝ) :
    0 ≤ u ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ u) := by
  simpa only [star_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose G).inv.dotProduct_mulVec_nonneg u

private theorem isHermitian_inv_mul_conjTranspose (G : Matrix r k ℝ) :
    ((G * Gᴴ)⁻¹).IsHermitian :=
  (Matrix.isHermitian_mul_conjTranspose_self G).inv

private theorem inv_mul_conjTranspose_apply_comm (G : Matrix r k ℝ) (i j : r) :
    (G * Gᴴ)⁻¹ i j = (G * Gᴴ)⁻¹ j i := by
  have h := (isHermitian_inv_mul_conjTranspose G).apply i j
  rwa [star_trivial, eq_comm] at h

/-- The quadratic form of `M` at `a eᵢ + b eⱼ`. -/
private theorem dotProduct_mulVec_single_add_single (M : Matrix r r ℝ) (i j : r) (a b : ℝ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ (M *ᵥ (Pi.single i a + Pi.single j b)) =
      a * a * M i i + a * b * (M i j + M j i) + b * b * M j j := by
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single,
    single_dotProduct, Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul]
  ring

private theorem norm_toLp_single_add_single {i j : r} (hij : i ≠ j) (a b : ℝ) :
    ‖WithLp.toLp 2 (Pi.single i a + Pi.single j b : r → ℝ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  simp only [dotProduct_add, dotProduct_single, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
  ring

/-- The probes at `(eᵢ ± eⱼ)/√2`. -/
private theorem hasLaw_add_div_two_add_mul_inv_apply (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) {i j : r} (hij : i ≠ j) {ε : ℝ} (hε : ε ^ 2 = 1) :
    HasLaw (fun ω => ((X ω * (X ω)ᴴ)⁻¹ i i + (X ω * (X ω)ᴴ)⁻¹ j j) / 2 +
        ε * (X ω * (X ω)ᴴ)⁻¹ i j) (invChiSq (Fintype.card k - Fintype.card r + 1)) μ := by
  set c : ℝ := (√2)⁻¹ with hc
  have hcc : c * c = 1 / 2 := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  have hu : ‖WithLp.toLp 2 (Pi.single i c + Pi.single j (ε * c) : r → ℝ)‖ = 1 := by
    have h := norm_toLp_single_add_single hij c (ε * c)
    have h2 : c ^ 2 + c ^ 2 = 1 ^ 2 := by rw [sq c, hcc]; norm_num
    rw [mul_pow, hε, one_mul, h2] at h
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h
  have h := hasLaw_dotProduct_inv_mul_conjTranspose_mulVec hX hrk hu
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [dotProduct_mulVec_single_add_single, inv_mul_conjTranspose_apply_comm (X ω) j i]
  linear_combination (-((X ω * (X ω)ᴴ)⁻¹ i i + 2 * ε * (X ω * (X ω)ᴴ)⁻¹ i j +
    ε ^ 2 * (X ω * (X ω)ᴴ)⁻¹ j j)) * hcc - ((X ω * (X ω)ᴴ)⁻¹ j j / 2) * hε

private theorem integrable_inv_mul_conjTranspose_apply (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) (i j : r) :
    Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i j) μ := by
  have hd : 3 ≤ Fintype.card k - Fintype.card r + 1 := by omega
  have hdiag (l : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ l l) μ :=
    integrable_of_hasLaw_invChiSq (hasLaw_inv_mul_conjTranspose_apply_self hX (by omega) l) hd
  by_cases hij : i = j
  · subst hij
    exact hdiag i
  have hQ := integrable_of_hasLaw_invChiSq
    (hasLaw_add_div_two_add_mul_inv_apply hX (by omega) hij (ε := 1) (by norm_num)) hd
  refine (hQ.sub ((hdiag i).add (hdiag j) |>.div_const 2)).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

private theorem integral_inv_mul_conjTranspose_apply (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) (i j : r) :
    ∫ ω, (X ω * (X ω)ᴴ)⁻¹ i j ∂μ =
      ((Fintype.card k : ℝ) - Fintype.card r - 1)⁻¹ * (1 : Matrix r r ℝ) i j := by
  have hd : 3 ≤ Fintype.card k - Fintype.card r + 1 := by omega
  have hcast : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 2 =
      (Fintype.card k : ℝ) - Fintype.card r - 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hdiag (l : r) : ∫ ω, (X ω * (X ω)ᴴ)⁻¹ l l ∂μ =
      ((Fintype.card k : ℝ) - Fintype.card r - 1)⁻¹ := by
    rw [integral_of_hasLaw_invChiSq (hasLaw_inv_mul_conjTranspose_apply_self hX (by omega) l) hd,
      hcast, one_div]
  by_cases hij : i = j
  · subst hij
    rw [hdiag, Matrix.one_apply_eq, mul_one]
  have hlaw := hasLaw_add_div_two_add_mul_inv_apply hX (by omega) hij (ε := 1) (by norm_num)
  have hQ := integral_of_hasLaw_invChiSq hlaw hd
  have hint (l : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ l l) μ :=
    integrable_inv_mul_conjTranspose_apply hX hrk l l
  have hsum : Integrable (fun ω => ((X ω * (X ω)ᴴ)⁻¹ i i + (X ω * (X ω)ᴴ)⁻¹ j j) / 2) μ :=
    ((hint i).add (hint j)).div_const 2
  have hfun : (fun ω => (X ω * (X ω)ᴴ)⁻¹ i j) = fun ω =>
      (((X ω * (X ω)ᴴ)⁻¹ i i + (X ω * (X ω)ᴴ)⁻¹ j j) / 2 + 1 * (X ω * (X ω)ᴴ)⁻¹ i j) -
        ((X ω * (X ω)ᴴ)⁻¹ i i + (X ω * (X ω)ᴴ)⁻¹ j j) / 2 := by
    funext ω
    ring
  rw [hfun, integral_sub (integrable_of_hasLaw_invChiSq hlaw hd) hsum, hQ, integral_div,
    integral_add (hint i) (hint j), hdiag, hdiag, hcast, Matrix.one_apply_ne hij, mul_zero]
  ring

/-! ### The off-diagonal second moment -/

omit [DecidableEq r] in
/-- An orthonormal frame adapted to the column space of `B` and its complement. -/
private theorem exists_frame_rangeProjector [DecidableEq k] {t : Type*} [Fintype t] [DecidableEq t]
    (B : Matrix k t ℝ) (hB : Function.Injective B.mulVec) {d : ℕ}
    (hd : Fintype.card t + d = Fintype.card k) :
    ∃ V₁ : Matrix k t ℝ, ∃ V₂ : Matrix k (Fin d) ℝ, HasOrthonormalCols (Matrix.fromCols V₁ V₂) ∧
      V₁ * V₁ᴴ = rangeProjector B ∧ V₂ * V₂ᴴ = 1 - rangeProjector B := by
  have hrankB := mulVec_injective_iff_rank_eq.1 hB
  have hrank := rank_one_sub_rangeProjector_add_rank B
  rw [hrankB] at hrank
  obtain ⟨V₁, hV₁, h₁⟩ :=
    (isStarProjection_rangeProjector B).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := t) (by rw [rank_rangeProjector, hrankB])
  obtain ⟨V₂, hV₂, h₂⟩ :=
    (isStarProjection_one_sub_rangeProjector B).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := Fin d) (by rw [Fintype.card_fin]; omega)
  refine ⟨V₁, V₂, hasOrthonormalCols_fromCols_iff.2 ⟨hV₁, hV₂, ?_⟩, h₁, h₂⟩
  have e₁ : V₁ᴴ = V₁ᴴ * rangeProjector B := by
    rw [← h₁, ← Matrix.mul_assoc, hV₁.conjTranspose_mul_self, Matrix.one_mul]
  have e₂ : V₂ = (1 - rangeProjector B) * V₂ := by
    rw [← h₂, Matrix.mul_assoc, hV₂.conjTranspose_mul_self, Matrix.mul_one]
  rw [e₁, e₂, Matrix.mul_assoc, ← Matrix.mul_assoc (rangeProjector B), Matrix.mul_sub,
    Matrix.mul_one, rangeProjector_mul_rangeProjector, sub_self, Matrix.zero_mul, Matrix.mul_zero]

omit [DecidableEq r] in
/-- For an orthonormal frame `[V₁ V₂]`, `V₁ᴴ g` and `V₂ᴴ g` are independent standard Gaussian
vectors, so `E (b ⬝ V₁ᴴ g)² (‖V₂ᴴ g‖²)⁻² = ‖b‖² E (1/χ²_d)²`. -/
private theorem lintegral_sq_dotProduct_mul_inv_sq {t : Type*} [Fintype t] [DecidableEq t]
    {d : ℕ} {V₁ : Matrix k t ℝ} {V₂ : Matrix k (Fin d) ℝ}
    (hV : HasOrthonormalCols (Matrix.fromCols V₁ V₂)) (b : t → ℝ) :
    ∫⁻ g, ENNReal.ofReal ((b ⬝ᵥ (V₁ᴴ *ᵥ g)) ^ 2 * ((‖WithLp.toLp 2 (V₂ᴴ *ᵥ g)‖ ^ 2)⁻¹) ^ 2)
        ∂(gaussianVector k) =
      ENNReal.ofReal (‖WithLp.toLp 2 b‖ ^ 2) *
        ∫⁻ η, ENNReal.ofReal (((‖WithLp.toLp 2 η‖ ^ 2)⁻¹) ^ 2) ∂(gaussianVector (Fin d)) := by
  classical
  have hL : HasOrthonormalCols (Matrix.fromCols V₁ V₂)ᴴᴴ := by
    rwa [Matrix.conjTranspose_conjTranspose]
  have hlaw := hasLaw_mulVec_of_hasLaw_gaussianVector (HasLaw.id (μ := gaussianVector k)) hL
  have hpair := (measurePreserving_sumPiEquivProdPi
    (fun _ : t ⊕ Fin d => gaussianReal 0 1)).fun_comp_hasLaw hlaw
  have hfun (g : k → ℝ) : MeasurableEquiv.sumPiEquivProdPi (fun _ : t ⊕ Fin d => ℝ)
      ((Matrix.fromCols V₁ V₂)ᴴ *ᵥ id g) = (V₁ᴴ *ᵥ g, V₂ᴴ *ᵥ g) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose]
    rfl
  simp only [hfun] at hpair
  have h1 : Measurable fun ξ : t → ℝ => ENNReal.ofReal ((b ⬝ᵥ ξ) ^ 2) := by
    simp only [dotProduct]
    fun_prop
  have h2 : Measurable fun η : Fin d → ℝ => ENNReal.ofReal (((‖WithLp.toLp 2 η‖ ^ 2)⁻¹) ^ 2) := by
    fun_prop
  have hnn (g : k → ℝ) : 0 ≤ (b ⬝ᵥ (V₁ᴴ *ᵥ g)) ^ 2 := sq_nonneg _
  simp only [ENNReal.ofReal_mul (hnn _)]
  rw [hpair.lintegral_comp (f := fun p : (t → ℝ) × (Fin d → ℝ) =>
      ENNReal.ofReal ((b ⬝ᵥ p.1) ^ 2) * ENNReal.ofReal (((‖WithLp.toLp 2 p.2‖ ^ 2)⁻¹) ^ 2))
      ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).aemeasurable,
    lintegral_prod_mul h1.aemeasurable h2.aemeasurable]
  congr 1
  have hdot := hasLaw_dotProduct_of_hasLaw_gaussianVector (HasLaw.id (μ := gaussianVector t)) b
  have hint : Integrable (fun ξ : t → ℝ => (b ⬝ᵥ ξ) ^ 2) (gaussianVector t) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := ‖WithLp.toLp 2 b‖₊ ^ 2) 2).integrable_sq
    have hm : Measurable fun x : ℝ => x ^ 2 := by fun_prop
    exact (hdot.integrable_comp_iff hm.aestronglyMeasurable).2 h
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  have h := integral_sq_of_hasLaw_gaussianReal hdot
  simp only [id_eq] at h
  rw [h, NNReal.coe_pow, coe_nnnorm]

/-- `E (1/χ²_d)² = 1/((d-2)(d-4))`, as a lower integral. -/
private theorem lintegral_inv_norm_sq_sq {d : ℕ} (hd : 5 ≤ d) :
    ∫⁻ η, ENNReal.ofReal (((‖WithLp.toLp 2 η‖ ^ 2)⁻¹) ^ 2) ∂(gaussianVector (Fin d)) =
      ENNReal.ofReal (1 / (((d : ℝ) - 2) * ((d : ℝ) - 4))) := by
  have hlaw : HasLaw (fun η : Fin d → ℝ => (‖WithLp.toLp 2 η‖ ^ 2)⁻¹) (invChiSq d)
      (gaussianVector (Fin d)) := ⟨by fun_prop, rfl⟩
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hint := integrable_rpow_of_hasLaw_invChiSq hlaw (s := 2) (by linarith)
  simp only [Real.rpow_two] at hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun η =>
    sq_nonneg _), integral_sq_of_hasLaw_invChiSq hlaw hd]

/-- **The off-diagonal second moment**: `E ((G Gᴴ)⁻¹ⱼᵢ)² = 1 / ((k - r) (k - r - 1) (k - r - 3))`,
by the Schur complement of row `i` and the independence of the regression coefficients and the
residual. -/
private theorem lintegral_inv_mul_conjTranspose_apply_sq (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 4 ≤ Fintype.card k) {i j : r} (hji : j ≠ i) :
    ∫⁻ ω, ENNReal.ofReal ((X ω * (X ω)ᴴ)⁻¹ j i ^ 2) ∂μ =
      ENNReal.ofReal (((Fintype.card k : ℝ) - Fintype.card r)⁻¹ *
        (1 / ((((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 2) *
          (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 4)))) := by
  classical
  have := hX.isProbabilityMeasure
  set d := Fintype.card k - Fintype.card r + 1 with hd
  set t := {j // j ≠ i}
  have hcard : Fintype.card t + d = Fintype.card k := card_subtype_ne_add (by omega)
  set j' : t := ⟨j, hji⟩
  set m₂ : ℝ := 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) with hm₂
  set ψ : (k → ℝ) × Matrix t k ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((pinv p.2ᴴ *ᵥ p.1) j' ^ 2 *
      ((‖WithLp.toLp 2 ((1 - rangeProjector p.2ᴴ) *ᵥ p.1)‖ ^ 2)⁻¹) ^ 2) with hψ
  have hψm : Measurable ψ := by
    have hc : Measurable fun p : (k → ℝ) × Matrix t k ℝ => (pinv p.2ᴴ *ᵥ p.1) j' :=
      (measurable_pi_apply j').comp ((measurable_pinv.comp
        ((continuous_id.matrix_conjTranspose).measurable.comp measurable_snd)).matrix_mulVec
        measurable_fst)
    exact ((hc.pow_const 2).mul (((((continuous_norm.comp
      (PiLp.continuous_toLp 2 _)).measurable.comp
        measurable_one_sub_rangeProjector_mulVec).pow_const 2).inv).pow_const 2)).ennreal_ofReal
  have hHlaw : HasLaw (fun ω => (X ω).submatrix (Subtype.val : t → r) id) (gaussianMatrix t k) μ :=
    hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Subtype.val_injective Function.injective_id
  have htk : Fintype.card t ≤ Fintype.card k := by omega
  have hdiag : ∫ H, (H * Hᴴ)⁻¹ j' j' ∂(gaussianMatrix t k) =
      ((Fintype.card k : ℝ) - Fintype.card r)⁻¹ := by
    have h := integral_inv_mul_conjTranspose_apply (HasLaw.id (μ := gaussianMatrix t k))
      (by omega) j' j'
    simp only [id_eq] at h
    rw [h, Matrix.one_apply_eq, mul_one]
    congr 1
    have h1 : (Fintype.card t : ℝ) + d = Fintype.card k := by exact_mod_cast hcard
    have h2 : (d : ℝ) = Fintype.card k - Fintype.card r + 1 := by
      rw [hd, Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
    linarith
  calc ∫⁻ ω, ENNReal.ofReal ((X ω * (X ω)ᴴ)⁻¹ j i ^ 2) ∂μ =
        ∫⁻ ω, ψ (X ω i, (X ω).submatrix (Subtype.val : t → r) id) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_injective_conjTranspose_mulVec hHlaw htk] with ω hω
        rw [inv_mul_conjTranspose_apply_of_ne (X ω) hji hω, neg_mul, neg_sq, mul_pow]
        rfl
    _ = ∫⁻ p, ψ p ∂((gaussianVector k).prod (gaussianMatrix t k)) :=
        (hasLaw_row_otherRows hX i).lintegral_comp hψm.aemeasurable
    _ = ∫⁻ H, ∫⁻ g, ψ (g, H) ∂(gaussianVector k) ∂(gaussianMatrix t k) :=
        lintegral_prod_symm _ hψm.aemeasurable
    _ = ∫⁻ H, ENNReal.ofReal ((H * Hᴴ)⁻¹ j' j') * ENNReal.ofReal m₂ ∂(gaussianMatrix t k) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_injective_conjTranspose_mulVec
          (HasLaw.id (μ := gaussianMatrix t k)) htk] with H hinj
        obtain ⟨V₁, V₂, hV, h₁, h₂⟩ := exists_frame_rangeProjector Hᴴ hinj hcard
        have hV₂ := (hasOrthonormalCols_fromCols_iff.1 hV).2.1
        set M := pinv Hᴴ * V₁ with hM
        have hPinv : pinv Hᴴ * rangeProjector Hᴴ = pinv Hᴴ := by
          rw [← mul_pinv, ← Matrix.mul_assoc, pinv_mul_mul_pinv]
        have hc (g : k → ℝ) : (pinv Hᴴ *ᵥ g) j' = (fun l => M j' l) ⬝ᵥ (V₁ᴴ *ᵥ g) := by
          rw [← hPinv, ← h₁, ← Matrix.mul_assoc, ← hM, ← Matrix.mulVec_mulVec]
          rfl
        have hs (g : k → ℝ) : ‖WithLp.toLp 2 ((1 - rangeProjector Hᴴ) *ᵥ g)‖ =
            ‖WithLp.toLp 2 (V₂ᴴ *ᵥ g)‖ := by
          rw [← h₂, ← Matrix.mulVec_mulVec, hV₂.norm_toLp_mulVec]
        have hb : ‖WithLp.toLp 2 (fun l => M j' l)‖ ^ 2 = (H * Hᴴ)⁻¹ j' j' := by
          have hunit : IsUnit (H * Hᴴ) := by
            simpa only [Matrix.conjTranspose_conjTranspose] using
              (isUnit_conjTranspose_mul_self_iff (A := Hᴴ)).2 hinj
          have hMM : M * Mᴴ = (H * Hᴴ)⁻¹ := by
            rw [hM, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V₁, h₁,
              ← Matrix.mul_assoc, hPinv, ← pinv_conjTranspose_mul_self,
              Matrix.conjTranspose_conjTranspose, pinv_of_isUnit hunit]
          rw [← hMM, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, Matrix.mul_apply]
          simp only [dotProduct, Matrix.conjTranspose_apply, star_trivial]
        simp only [hψ, hc, hs]
        rw [lintegral_sq_dotProduct_mul_inv_sq hV, hb, lintegral_inv_norm_sq_sq (by omega)]
    _ = _ := by
        have hint : Integrable (fun H : Matrix t k ℝ => (H * Hᴴ)⁻¹ j' j') (gaussianMatrix t k) :=
          integrable_inv_mul_conjTranspose_apply (HasLaw.id (μ := gaussianMatrix t k))
            (by omega) j' j'
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun H => by
              simpa only [Matrix.mulVec_single_one, single_dotProduct, Matrix.col_apply, one_mul,
                Pi.zero_apply] using
                dotProduct_inv_mul_conjTranspose_mulVec_nonneg H (Pi.single j' 1)),
          hdiag, ← ENNReal.ofReal_mul (inv_nonneg.2 (by
            have : (Fintype.card r : ℝ) + 4 ≤ Fintype.card k := by exact_mod_cast hrk
            linarith))]


/-! ### Second moments of the entries -/

private theorem memLp_two_of_hasLaw_invChiSq {Y : Ω → ℝ} {d : ℕ} (hY : HasLaw Y (invChiSq d) μ)
    (hd : 5 ≤ d) : MemLp Y 2 μ := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrable_rpow_of_hasLaw_invChiSq hY (s := 2) (by linarith)
  simp only [Real.rpow_two] at h
  exact (memLp_two_iff_integrable_sq hY.aemeasurable.aestronglyMeasurable).2 h

omit [Fintype r] [Fintype k] [DecidableEq r] in
private theorem memLp_of_memLp_add_div_two {f g h : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfgh : MemLp (fun ω => (f ω + g ω) / 2 + 1 * h ω) 2 μ) : MemLp h 2 μ := by
  have e : h = (fun ω => (f ω + g ω) / 2 + 1 * h ω) - fun ω => 2⁻¹ * (f ω + g ω) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  rw [e]
  exact hfgh.sub ((hf.add hg).const_mul 2⁻¹)

omit [Fintype r] [Fintype k] [DecidableEq r] in
/-- The polarisation behind the product moment: `x y = Q₊² + Q₋² - 2 z² - (x² + y²)/2` with
`Q± = (x + y)/2 ± z`. -/
private theorem integral_mul_eq_of_memLp {x y z : Ω → ℝ} (hx : MemLp x 2 μ) (hy : MemLp y 2 μ)
    (hz : MemLp z 2 μ) :
    ∫ ω, x ω * y ω ∂μ =
      ∫ ω, ((x ω + y ω) / 2 + 1 * z ω) ^ 2 ∂μ + ∫ ω, ((x ω + y ω) / 2 + -1 * z ω) ^ 2 ∂μ -
        2 * ∫ ω, z ω ^ 2 ∂μ - 2⁻¹ * (∫ ω, x ω ^ 2 ∂μ + ∫ ω, y ω ^ 2 ∂μ) := by
  have hQ (ε : ℝ) : Integrable (fun ω => ((x ω + y ω) / 2 + ε * z ω) ^ 2) μ := by
    have h : MemLp (fun ω => (x ω + y ω) / 2 + ε * z ω) 2 μ := by
      have e : (fun ω => (x ω + y ω) / 2 + ε * z ω) =
          (fun ω => 2⁻¹ * (x ω + y ω)) + fun ω => ε * z ω := by
        funext ω
        simp only [Pi.add_apply]
        ring
      rw [e]
      exact ((hx.add hy).const_mul 2⁻¹).add (hz.const_mul ε)
    exact h.integrable_sq
  have e : (fun ω => x ω * y ω) = fun ω =>
      ((x ω + y ω) / 2 + 1 * z ω) ^ 2 + ((x ω + y ω) / 2 + -1 * z ω) ^ 2 - 2 * z ω ^ 2 -
        2⁻¹ * (x ω ^ 2 + y ω ^ 2) := by
    funext ω
    ring
  have h3 : Integrable (fun ω => ((x ω + y ω) / 2 + 1 * z ω) ^ 2 +
      ((x ω + y ω) / 2 + -1 * z ω) ^ 2) μ := (hQ 1).add (hQ (-1))
  have hz2 : Integrable (fun ω => 2 * z ω ^ 2) μ := hz.integrable_sq.const_mul 2
  have h1 : Integrable (fun ω => ((x ω + y ω) / 2 + 1 * z ω) ^ 2 +
      ((x ω + y ω) / 2 + -1 * z ω) ^ 2 - 2 * z ω ^ 2) μ := h3.sub hz2
  have hxy : Integrable (fun ω => x ω ^ 2 + y ω ^ 2) μ := hx.integrable_sq.add hy.integrable_sq
  have h2 : Integrable (fun ω => 2⁻¹ * (x ω ^ 2 + y ω ^ 2)) μ := hxy.const_mul _
  rw [e, integral_sub h1 h2, integral_sub h3 hz2, integral_add (hQ 1) (hQ (-1)),
    integral_const_mul, integral_const_mul, integral_add hx.integrable_sq hy.integrable_sq]

private theorem memLp_inv_mul_conjTranspose_apply (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 4 ≤ Fintype.card k) (i j : r) :
    MemLp (fun ω => (X ω * (X ω)ᴴ)⁻¹ i j) 2 μ := by
  have hd : 5 ≤ Fintype.card k - Fintype.card r + 1 := by omega
  have hdiag (l : r) : MemLp (fun ω => (X ω * (X ω)ᴴ)⁻¹ l l) 2 μ :=
    memLp_two_of_hasLaw_invChiSq (hasLaw_inv_mul_conjTranspose_apply_self hX (by omega) l) hd
  by_cases hij : i = j
  · subst hij
    exact hdiag i
  have hQ := memLp_two_of_hasLaw_invChiSq
    (hasLaw_add_div_two_add_mul_inv_apply hX (by omega) hij (ε := 1) (by norm_num)) hd
  exact memLp_of_memLp_add_div_two (hdiag i) (hdiag j) hQ

/-- `E (G Gᴴ)⁻¹ᵢᵢ (G Gᴴ)⁻¹ⱼⱼ` is `a` on the diagonal and `a - 2c` off it, with
`a = E (1/χ²_{k-r+1})²` and `c = a / (k - r)` the off-diagonal second moment. -/
private theorem integral_inv_mul_conjTranspose_apply_self_mul (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 4 ≤ Fintype.card k) (i j : r) :
    ∫ ω, (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j ∂μ =
      (1 / ((((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 2) *
          (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 4))) *
        (1 - 2 * ((Fintype.card k : ℝ) - Fintype.card r)⁻¹ * (1 - (1 : Matrix r r ℝ) i j)) := by
  have := hX.isProbabilityMeasure
  have hd : 5 ≤ Fintype.card k - Fintype.card r + 1 := by omega
  set a := 1 / ((((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 2) *
    (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) - 4)) with ha
  have hsq (l : r) : ∫ ω, (X ω * (X ω)ᴴ)⁻¹ l l ^ 2 ∂μ = a :=
    integral_sq_of_hasLaw_invChiSq (hasLaw_inv_mul_conjTranspose_apply_self hX (by omega) l) hd
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, sub_self, mul_zero, sub_zero, mul_one, ← hsq i]
    simp only [sq]
  have hc : ∫ ω, (X ω * (X ω)ᴴ)⁻¹ i j ^ 2 ∂μ =
      ((Fintype.card k : ℝ) - Fintype.card r)⁻¹ * a := by
    have h := lintegral_inv_mul_conjTranspose_apply_sq hX hrk (i := j) (j := i) hij
    have hint : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i j ^ 2) μ :=
      (memLp_inv_mul_conjTranspose_apply hX hrk i j).integrable_sq
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      hint.aestronglyMeasurable, h, ENNReal.toReal_ofReal]
    have : (Fintype.card r : ℝ) + 4 ≤ Fintype.card k := by exact_mod_cast hrk
    have hd' : (5 : ℝ) ≤ ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) := by exact_mod_cast hd
    exact mul_nonneg (inv_nonneg.2 (by linarith)) (by apply div_nonneg <;> nlinarith)
  have hQ (ε : ℝ) (hε : ε ^ 2 = 1) := hasLaw_add_div_two_add_mul_inv_apply hX (by omega) hij hε
  have hQsq (ε : ℝ) (hε : ε ^ 2 = 1) := integral_sq_of_hasLaw_invChiSq (hQ ε hε) hd
  rw [integral_mul_eq_of_memLp (memLp_inv_mul_conjTranspose_apply hX hrk i i)
    (memLp_inv_mul_conjTranspose_apply hX hrk j j) (memLp_inv_mul_conjTranspose_apply hX hrk i j),
    hQsq 1 (by norm_num), hQsq (-1) (by norm_num), hc, hsq, hsq, Matrix.one_apply_ne hij]
  ring

/-! ### The moments of the probes -/

/-- **Probes of `(G Gᴴ)⁻¹` have the moments of `1 / χ²_{k-r+1}`**: for a unit vector `u` and
`q < (k - r + 1)/2`, `(u ⬝ (G Gᴴ)⁻¹ u)^q` is integrable. -/
theorem integrable_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r ≤ Fintype.card k)
    {u : r → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) {q : ℝ}
    (hq : q < ((Fintype.card k : ℝ) - Fintype.card r + 1) / 2) :
    Integrable (fun ω => (u ⬝ᵥ ((X ω * (X ω)ᴴ)⁻¹ *ᵥ u)) ^ q) μ := by
  classical
  have hcast : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) =
      (Fintype.card k : ℝ) - Fintype.card r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrk, Nat.cast_one]
  exact integrable_rpow_of_hasLaw_invChiSq
    (hasLaw_dotProduct_inv_mul_conjTranspose_mulVec hX hrk hu) (by rwa [hcast])

/-- **Probes of `(G Gᴴ)⁻¹` have the moments of `1 / χ²_{k-r+1}`**: for a unit vector `u` and
`q < (k - r + 1)/2`, `E (u ⬝ (G Gᴴ)⁻¹ u)^q = 2^{-q} Γ((k - r + 1)/2 - q) / Γ((k - r + 1)/2)`. The
diagonal entries of `(G Gᴴ)⁻¹` are the case `u = eᵢ`. -/
theorem integral_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r ≤ Fintype.card k)
    {u : r → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) {q : ℝ}
    (hq : q < ((Fintype.card k : ℝ) - Fintype.card r + 1) / 2) :
    ∫ ω, (u ⬝ᵥ ((X ω * (X ω)ᴴ)⁻¹ *ᵥ u)) ^ q ∂μ =
      2 ^ (-q) * Real.Gamma (((Fintype.card k : ℝ) - Fintype.card r + 1) / 2 - q) /
        Real.Gamma (((Fintype.card k : ℝ) - Fintype.card r + 1) / 2) := by
  classical
  have hcast : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) =
      (Fintype.card k : ℝ) - Fintype.card r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrk, Nat.cast_one]
  rw [integral_rpow_of_hasLaw_invChiSq (hasLaw_dotProduct_inv_mul_conjTranspose_mulVec hX hrk hu)
    (by rwa [hcast]), hcast]

end Entries

/-! ### The mean and the Frobenius moments -/

/-- `(G Gᴴ)⁻¹` is integrable for a standard Gaussian `G : r × k` with `r + 2 ≤ k`. -/
theorem integrable_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹) μ := by
  classical
  exact Matrix.integrable_iff.2 fun i j => integrable_inv_mul_conjTranspose_apply hX hrk i j

/-- **The mean of the inverse Wishart matrix**: `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1` for `r + 2 ≤ k`. -/
theorem integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, (X ω * (X ω)ᴴ)⁻¹ ∂μ =
      ((Fintype.card k : ℝ) - Fintype.card r - 1)⁻¹ • (1 : Matrix r r ℝ) := by
  classical
  ext i j
  rw [Matrix.integral_apply (fun i j => integrable_inv_mul_conjTranspose_apply hX hrk i j),
    integral_inv_mul_conjTranspose_apply hX hrk, Matrix.smul_apply, smul_eq_mul]

/-- Almost surely `‖G†‖_F² = tr (G Gᴴ)⁻¹`. -/
private theorem ae_frobNorm_pinv_sq_eq_sum [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (X ω)) ^ 2 = ∑ i, (X ω * (X ω)ᴴ)⁻¹ i i := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hX] with ω hω
  have hinj : Function.Injective (X ω)ᴴ.mulVec := by
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, hω, min_eq_left hrk]
  rw [frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose hinj, RCLike.re_to_real]
  rfl

/-- `‖G†‖_F²` is integrable for `r + 2 ≤ k`. -/
theorem integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 2) μ := by
  classical
  refine (integrable_finsetSum Finset.univ fun i _ =>
    integrable_inv_mul_conjTranspose_apply hX hrk i i).congr ?_
  filter_upwards [ae_frobNorm_pinv_sq_eq_sum hX (by omega)] with ω hω
  rw [hω]

/-- **`E ‖G†‖_F² = r / (k - r - 1)`** (Halko, Martinsson and Tropp, Proposition 10.2). -/
theorem integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 2 ∂μ =
      (Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  classical
  rw [integral_congr_ae (ae_frobNorm_pinv_sq_eq_sum hX (by omega)),
    integral_finsetSum _ fun i _ => integrable_inv_mul_conjTranspose_apply hX hrk i i]
  simp only [integral_inv_mul_conjTranspose_apply hX hrk, Matrix.one_apply_eq, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

private theorem aestronglyMeasurable_frobNorm_pinv (hX : HasLaw X (gaussianMatrix r k) μ) :
    AEStronglyMeasurable (fun ω => frobNorm (pinv (X ω))) μ :=
  ((measurable_frobNorm.comp measurable_pinv).comp_aemeasurable
    hX.aemeasurable).aestronglyMeasurable

private theorem memLp_frobNorm_pinv (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    MemLp (fun ω => frobNorm (pinv (X ω))) 2 μ :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_frobNorm_pinv hX)).2
    (integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hX hrk)

/-- `‖G†‖_F` is integrable for `r + 2 ≤ k`. -/
theorem integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω))) μ := by
  have := hX.isProbabilityMeasure
  exact (memLp_frobNorm_pinv hX hrk).integrable one_le_two

/-- `E ‖G†‖_F ≤ √(r / (k - r - 1))`, by Jensen. -/
theorem integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ∂μ ≤
      √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) := by
  have := hX.isProbabilityMeasure
  have hvar := variance_nonneg (fun ω => frobNorm (pinv (X ω))) μ
  rw [variance_eq_sub (memLp_frobNorm_pinv hX hrk)] at hvar
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [← integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hX hrk]
  simp only [Pi.pow_apply] at hvar
  linarith

private theorem ae_frobNorm_pinv_pow_four_eq [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (X ω)) ^ 4 =
      ∑ i, ∑ j, (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j := by
  filter_upwards [ae_frobNorm_pinv_sq_eq_sum hX hrk] with ω hω
  rw [show 4 = 2 * 2 by rfl, pow_mul, hω, sq, Finset.sum_mul_sum]

/-- `‖G†‖_F⁴` is integrable for `r + 4 ≤ k`. -/
theorem integrable_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 4) μ := by
  classical
  have hint (i j : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j) μ :=
    (memLp_inv_mul_conjTranspose_apply hX hrk i i).integrable_mul
      (memLp_inv_mul_conjTranspose_apply hX hrk j j)
  refine (integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hint i j).congr ?_
  filter_upwards [ae_frobNorm_pinv_pow_four_eq hX (by omega)] with ω hω
  rw [hω]

/-- The fourth moment of `‖G†‖_F` (Halko, Martinsson and Tropp, Proposition 10.3):
`E ‖G†‖_F⁴ = (r² (k - r) - 2 r (r - 1)) / ((k - r) (k - r - 1) (k - r - 3))` for `r + 4 ≤ k`. -/
theorem integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 4 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 * ((Fintype.card k : ℝ) - Fintype.card r) -
          2 * Fintype.card r * ((Fintype.card r : ℝ) - 1)) /
        (((Fintype.card k : ℝ) - Fintype.card r) * ((Fintype.card k : ℝ) - Fintype.card r - 1) *
          ((Fintype.card k : ℝ) - Fintype.card r - 3)) := by
  classical
  have hint (i j : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j) μ :=
    (memLp_inv_mul_conjTranspose_apply hX hrk i i).integrable_mul
      (memLp_inv_mul_conjTranspose_apply hX hrk j j)
  rw [integral_congr_ae (ae_frobNorm_pinv_pow_four_eq hX (by omega)),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [integral_finsetSum _ fun j _ => hint _ j,
    integral_inv_mul_conjTranspose_apply_self_mul hX hrk]
  have hcast : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) =
      (Fintype.card k : ℝ) - Fintype.card r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hone (i : r) : ∑ j, (1 : Matrix r r ℝ) i j = 1 := by
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hone, hcast]
  have hkr : (Fintype.card r : ℝ) + 4 ≤ Fintype.card k := by exact_mod_cast hrk
  have h1 : (Fintype.card k : ℝ) - Fintype.card r ≠ 0 := by linarith
  have h2 : (Fintype.card k : ℝ) - Fintype.card r - 1 ≠ 0 := by linarith
  have h3 : (Fintype.card k : ℝ) - Fintype.card r - 3 ≠ 0 := by linarith
  have h2' : (Fintype.card k : ℝ) - Fintype.card r + 1 - 2 ≠ 0 := by linarith
  have h3' : (Fintype.card k : ℝ) - Fintype.card r + 1 - 4 ≠ 0 := by linarith
  field_simp
  ring

end NLAlib
