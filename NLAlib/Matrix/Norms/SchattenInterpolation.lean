/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Complex.Hadamard
public import NLAlib.Matrix.Norms.SchattenHolder

/-!
# Interpolation between spectral and Schatten norm bounds

A holomorphic matrix on a vertical strip has its intermediate Schatten norm bounded by a
weighted geometric mean of the boundary estimates. This is the finite-dimensional
Stein–Hirschman inequality with spectral norm on the left boundary.

The proof adapts the original formalization in `tchen-research/NLAlib@77514ce`.

## Main results

* `NLAlib.schattenNorm_le_exp_integral_stripHarmonicMeasure`: interpolation with bounded
  measurable logarithmic boundary majorants.

-/

@[expose] public section

open Set MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n]

private theorem schatten_pow_sum (A : Matrix n n ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) A ^ p =
      ∑ i ∈ Finset.range (Fintype.card n), singularValues A i ^ p := by
  simpa only [ENNReal.toReal_ofReal hp.le] using
    schattenNorm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top A
      A.rank_le_card_width

private theorem schatten_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) (Matrix.diagonal d) = (∑ i, ‖d i‖ ^ p) ^ p⁻¹ := by
  let D := Matrix.diagonal d
  have hD : Dᴴ * D = (1 : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => ((‖d i‖ ^ 2 : ℝ) : ℂ)) * (1 : Matrix ι ι ℂ)ᴴ := by
    simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    congr 1
    funext i
    simpa only [Pi.star_apply, Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (d i)
  have h1 : HasOrthonormalCols (1 : Matrix ι ι ℂ) := hasOrthonormalCols_one
  obtain ⟨e, he⟩ := h1.exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose
    rfl hD
  have hs (i : ι) : ‖d i‖ = singularValues D (e i) := by
    have he' : ‖d i‖ ^ 2 = singularValues D (e i) ^ 2 :=
      (he i).trans (singularValues_sq D (e i)).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (singularValues_nonneg D _)).mp he'
  rw [schattenNorm_eq_sum_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top _
    (Matrix.rank_le_card_width _), ENNReal.toReal_ofReal hp.le]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => singularValues D i ^ p) (Fintype.card ι)]
  exact (e.sum_comp fun j => singularValues D j ^ p).symm.trans (Finset.sum_congr rfl
    fun i _ => congrArg (fun t : ℝ => t ^ p) (hs i).symm)


private theorem norm_pos_of_ne_zero (A : Matrix n n ℂ) {p : ℝ} (hA : A ≠ 0) :
    0 < schattenNorm (ENNReal.ofReal p) A :=
  lt_of_le_of_ne (schattenNorm_nonneg _ A)
    (Ne.symm (fun h => hA ((schattenNorm_eq_zero_iff _).mp h)))

/-- Every normalized singular coefficient belongs to the unit interval. -/
private theorem normalized_singular_mem (A : Matrix n n ℂ)
    {p : ℝ} (hp : 0 < p) (hA : A ≠ 0) (i : ℕ) :
    singularValues A i / schattenNorm (ENNReal.ofReal p) A ∈ Set.Icc (0 : ℝ) 1 := by
  have hC := norm_pos_of_ne_zero (p := p) A hA
  exact ⟨div_nonneg (singularValues_nonneg A i) hC.le,
    (div_le_one hC).mpr ((singularValues_le_specNorm A i).trans
      (specNorm_le_schattenNorm (ENNReal.ofReal_ne_zero_iff.mpr hp) A))⟩

/-- Normalizing by the Schatten norm makes the source powers sum to one. -/
private theorem sum_normalized_pow (A : Matrix n n ℂ)
    {p : ℝ} (hp : 0 < p) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (Fintype.card n),
      (singularValues A i / schattenNorm (ENNReal.ofReal p) A) ^ p) = 1 := by
  have hC := norm_pos_of_ne_zero (p := p) A hA
  simp_rw [Real.div_rpow (singularValues_nonneg A _) hC.le]
  rw [← Finset.sum_div, ← schatten_pow_sum A hp,
    div_self (Real.rpow_pos_of_pos hC p).ne']

/-- The normalized singular dual powers recover the original Schatten norm
in the scalar singular-value pairing. -/
private theorem sum_normalized_pairing
    (A : Matrix n n ℂ) {p : ℝ} (hp : 1 < p) (hA : A ≠ 0) :
    (∑ i ∈ Finset.range (Fintype.card n),
      singularValues A i * (singularValues A i / schattenNorm (ENNReal.ofReal p) A) ^ (p - 1)) =
      schattenNorm (ENNReal.ofReal p) A := by
  have hp0 := lt_trans zero_lt_one hp
  have hC := norm_pos_of_ne_zero (p := p) A hA
  have hterm (i : ℕ) :
      singularValues A i * (singularValues A i / schattenNorm (ENNReal.ofReal p) A) ^ (p - 1) =
        schattenNorm (ENNReal.ofReal p) A *
          (singularValues A i / schattenNorm (ENNReal.ofReal p) A) ^ p := by
    let w := singularValues A i / schattenNorm (ENNReal.ofReal p) A
    have hw : 0 ≤ w := div_nonneg (singularValues_nonneg A i) hC.le
    have hσ : singularValues A i = schattenNorm (ENNReal.ofReal p) A * w := by dsimp [w]; field_simp
    have hprod : w * w ^ (p - 1) = w ^ p := by
      calc
        _ = w ^ (1 : ℝ) * w ^ (p - 1) := by rw [Real.rpow_one]
        _ = w ^ (1 + (p - 1)) :=
          (Real.rpow_add_of_nonneg hw zero_le_one (sub_nonneg.mpr hp.le)).symm
        _ = _ := by congr 1; ring
    change singularValues A i * w ^ (p - 1) = schattenNorm (ENNReal.ofReal p) A * w ^ p
    rw [hσ, mul_assoc, hprod]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_normalized_pow A hp0 hA, mul_one]


/-- One coefficient of the analytic Schatten dual test. The positive branch
is entire in `z`; a zero singular direction contributes the zero function. -/
private noncomputable def dualCoefficient (r p w : ℝ) (z : ℂ) : ℂ :=
  if 0 < w then Complex.exp (((p : ℂ) - z) / (r : ℂ) * (Real.log w : ℂ)) else 0

/-- Each fixed singular direction gives an entire analytic test coefficient. -/
@[fun_prop] private theorem differentiable_dualCoefficient (r p w : ℝ) :
    Differentiable ℂ (dualCoefficient r p w) := by
  unfold dualCoefficient
  split_ifs
  · fun_prop
  · exact differentiable_const _

/-- The modulus of a positive analytic test coefficient is its real power
at the real coordinate of the strip. -/
private theorem norm_dualCoefficient_of_pos {w : ℝ} (hw : 0 < w)
    (r p : ℝ) (z : ℂ) :
    ‖dualCoefficient r p w z‖ = w ^ ((p - z.re) / r) := by
  rw [dualCoefficient, if_pos hw, Complex.norm_exp, Real.rpow_def_of_pos hw]
  congr 1
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, mul_zero]
  ring

/-- Every normalized singular coefficient has test modulus at most one on
any point to the left of the strip's right boundary. -/
private theorem norm_dualCoefficient_le_one {r p w : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ≤ 1) : ‖dualCoefficient r p w z‖ ≤ 1 := by
  by_cases hwpos : 0 < w
  · rw [norm_dualCoefficient_of_pos hwpos]
    exact Real.rpow_le_one hw.1 hw.2 (div_nonneg (by linarith) hr.le)
  · simp only [dualCoefficient, if_neg hwpos, norm_zero, zero_le_one]

/-- On the left boundary the modulus is the normalized source power,
including zero singular directions. -/
private theorem norm_dualCoefficient_left {r p w : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hw : 0 ≤ w) (t : ℝ) :
    ‖dualCoefficient r p w ((t : ℂ) * Complex.I)‖ = w ^ (p / r) := by
  by_cases hwpos : 0 < w
  · rw [norm_dualCoefficient_of_pos hwpos]
    simp
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [dualCoefficient, Real.zero_rpow (div_pos hp hr).ne']

/-- At the interpolation point the coefficient is the ordinary real dual
power, with its zero convention justified by the positive exponent. -/
private theorem dualCoefficient_center {r p w : ℝ}
    (hr : 0 < r) (hpr : r < p) (hw : 0 ≤ w) :
    dualCoefficient r p w (r : ℂ) = ((w ^ (p / r - 1) : ℝ) : ℂ) := by
  by_cases hwpos : 0 < w
  · rw [dualCoefficient, if_pos hwpos, Real.rpow_def_of_pos hwpos,
      Complex.ofReal_exp]
    congr 1
    push_cast
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp [hrC]
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    have hexp : 0 < p / r - 1 := by rw [sub_pos, one_lt_div hr]; exact hpr
    simp [dualCoefficient, Real.zero_rpow hexp.ne']

/-- On the right boundary, raising the modulus to the conjugate exponent
reproduces the left-boundary power sum. -/
private theorem norm_dualCoefficient_right_rpow {r p q w : ℝ}
    (hr : 0 < r) (hpq : Real.HolderConjugate p q) (hw : 0 ≤ w) (t : ℝ) :
    ‖dualCoefficient r p w (1 + (t : ℂ) * Complex.I)‖ ^ q = w ^ (p / r) := by
  by_cases hwpos : 0 < w
  · rw [norm_dualCoefficient_of_pos hwpos]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    rw [← Real.rpow_mul hw]
    congr 1
    have heq := hpq.sub_one_mul_conj
    field_simp
    nlinarith
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [dualCoefficient, Real.zero_rpow hpq.symm.ne_zero,
      Real.zero_rpow (div_pos hpq.pos hr).ne']

/-- The analytic dual tester in fixed full singular frames. The orientation
is chosen so that the scalar analytic pairing is `trace (T(z) * G(z))`. -/
private noncomputable def dualTest
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (r p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) (z : ℂ) : Matrix n n ℂ :=
  V * Matrix.diagonal (fun i => dualCoefficient r p (w i) z) * Uᴴ

/-- The matrix tester is entire, including identically zero singular
coefficient directions. -/
@[fun_prop] private theorem differentiable_dualTest
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (r p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) :
    Differentiable ℂ (dualTest U V r p w) := by
  classical
  let L : (Fin (Fintype.card n) → ℂ) →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun d => V * Matrix.diagonal d * Uᴴ
      map_add' := by
        intro a b
        change V * Matrix.diagonal (fun i => a i + b i) * Uᴴ = _
        rw [← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c d
        simp only [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply] }
  have hc : Differentiable ℂ (fun z => fun i : Fin (Fintype.card n) =>
      dualCoefficient r p (w i) z) :=
    differentiable_pi.mpr fun i => differentiable_dualCoefficient r p (w i)
  have hL : Differentiable ℂ (fun d : Fin (Fintype.card n) → ℂ =>
      V * Matrix.diagonal d * Uᴴ) := by
    convert! L.toContinuousLinearMap.differentiable using 1
  exact Differentiable.comp (g := fun d : Fin (Fintype.card n) → ℂ =>
    V * Matrix.diagonal d * Uᴴ) (f := fun z : ℂ => fun i => dualCoefficient r p (w i) z) hL hc

open scoped Matrix.Norms.L2Operator in
/-- On the closed strip, the analytic dual tester is a spectral contraction
whenever its singular coefficients lie in the unit interval. -/
private theorem specNorm_dualTest_le_one
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) {w : Fin (Fintype.card n) → ℝ}
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) {z : ℂ} (hz : z.re ≤ 1) :
    specNorm (dualTest U V r p w z) ≤ 1 := by
  rw [dualTest,
    hU.specNorm_mul_conjTranspose_right,
    hV.specNorm_mul_left,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
    norm_dualCoefficient_le_one hr hp (hw i) hz

/-- The left boundary test has nuclear norm one for normalized source
power coefficients. -/
private theorem nuclearNorm_dualTest_left
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p : ℝ}
    (hr : 0 < r) (hp : 0 < p) {w : Fin (Fintype.card n) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hpower : ∑ i, w i ^ (p / r) = 1) (t : ℝ) :
    nuclearNorm (dualTest U V r p w ((t : ℂ) * Complex.I)) = 1 := by
  rw [← schattenNorm_one, dualTest,
    hU.schattenNorm_mul_conjTranspose_right, hV.schattenNorm_mul_left,
    ← ENNReal.ofReal_one, schatten_diagonal _ zero_lt_one]
  simp only [Real.rpow_one, inv_one]
  simp_rw [norm_dualCoefficient_left hr hp (hw _) t]
  exact hpower

/-- At the right boundary, a finite conjugate test has Schatten norm one.
No singular coefficient is required to be positive. -/
private theorem norm_dualTest_right
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p q : ℝ}
    (hr : 0 < r) (hpq : Real.HolderConjugate p q)
    {w : Fin (Fintype.card n) → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpower : ∑ i, w i ^ (p / r) = 1) (t : ℝ) :
    schattenNorm (ENNReal.ofReal q) (dualTest U V r p w (1 + (t : ℂ) * Complex.I)) = 1 := by
  rw [dualTest, hU.schattenNorm_mul_conjTranspose_right, hV.schattenNorm_mul_left,
    schatten_diagonal _ hpq.symm.pos]
  simp_rw [norm_dualCoefficient_right_rpow hr hpq (hw _) t]
  rw [hpower, Real.one_rpow]

/-- The actual analytic dual tester attains the original Schatten norm at
the interpolation point in the full complex trace pairing. This includes
rank-deficient nonzero matrices. -/
private theorem trace_dualTest_center_mul
    {A : Matrix n n ℂ} {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (h : IsSVD A U (fun i => singularValues A i) V)
    {r p : ℝ} (hr : 0 < r) (hpr : r < p) (hA : A ≠ 0) :
    ((dualTest U V r p
      (fun i => singularValues A i / schattenNorm (ENNReal.ofReal (p / r)) A) (r : ℂ)) * A).trace =
      (schattenNorm (ENNReal.ofReal (p / r)) A : ℂ) := by
  let C := schattenNorm (ENNReal.ofReal (p / r)) A
  have hp : 1 < p / r := (one_lt_div hr).mpr hpr
  have hpos : 0 < C := norm_pos_of_ne_zero A hA
  have hnorm := sum_normalized_pairing A hp hA
  rw [← Fin.sum_univ_eq_sum_range] at hnorm
  have hUA : Uᴴ * (A * V) =
      Matrix.diagonal (fun i : Fin (Fintype.card n) => ((singularValues A i : ℝ) : ℂ)) := by
    rw [h.mul_right_eq, ← Matrix.mul_assoc, h.hasOrthonormalCols_left.conjTranspose_mul_self,
      Matrix.one_mul]
    rfl
  rw [dualTest, Matrix.mul_assoc, Matrix.mul_assoc V, Matrix.trace_mul_comm V,
    Matrix.mul_assoc, Matrix.mul_assoc,
    hUA, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  conv_rhs => rw [← hnorm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualCoefficient_center hr hpr (div_nonneg (singularValues_nonneg A i) hpos.le),
    Complex.ofReal_mul, mul_comm]


private theorem norm_trace_mul_le_card_mul_specNorm {T : Matrix n n ℂ}
    (hT : specNorm T ≤ 1) (A : Matrix n n ℂ) :
    ‖(T * A).trace‖ ≤ Fintype.card n * specNorm A := by
  have hTnuclear : nuclearNorm T ≤ (Fintype.card n : ℝ) := by
    calc
      nuclearNorm T ≤ (T.rank : ℝ) * specNorm T := nuclearNorm_le_rank_mul_specNorm _
      _ ≤ (Fintype.card n : ℝ) * 1 :=
        mul_le_mul (by exact_mod_cast T.rank_le_card_width) hT
          (specNorm_nonneg _) (Nat.cast_nonneg _)
      _ = _ := mul_one _
  calc
    ‖(T * A).trace‖ ≤ nuclearNorm T * specNorm A := by
      simpa only [schattenNorm_one, schattenNorm_top] using
        norm_trace_mul_le_schattenNorm_mul T A (q := 1) (r := ∞)
    _ ≤ _ := mul_le_mul_of_nonneg_right hTnuclear (specNorm_nonneg _)

variable [DecidableEq n]

/-- Finite-dimensional matrix Stein–Hirschman interpolation from the spectral to a finite
Schatten norm, with bounded measurable logarithmic majorants on both boundary lines
[SutterBertaTomamichel2017, Theorem 3.1]. -/
theorem schattenNorm_le_exp_integral_stripHarmonicMeasure
    {r p B H : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hp : 1 ≤ p)
    {G : ℂ → Matrix n n ℂ}
    (hG : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (G z) ≤ B)
    (h₀ h₁ : ℝ → ℝ) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∀ t, |h₀ t| ≤ H) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, specNorm (G ((t : ℂ) * Complex.I)) ≤ Real.exp (h₀ t))
    (hright : ∀ t : ℝ,
      schattenNorm (ENNReal.ofReal p) (G (1 + (t : ℂ) * Complex.I)) ≤ Real.exp (h₁ t)) :
    schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ)) ≤ Real.exp (
      (1 - r) * (∫ t, h₀ t ∂Real.stripHarmonicMeasure (1 - r)) +
      r * (∫ t, h₁ t ∂Real.stripHarmonicMeasure r)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hα : 0 < p / r := div_pos hp0 hr.1
  by_cases hA : G (r : ℂ) = 0
  · rw [hA, schattenNorm_zero]
    exact (Real.exp_pos _).le
  obtain ⟨U, V, hSVD⟩ := exists_isSVD (G (r : ℂ)) (Matrix.rank_le_card_width _) le_rfl le_rfl
  let w : Fin (Fintype.card n) → ℝ := fun i =>
    singularValues (G (r : ℂ)) i / schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ))
  let T := dualTest U V r p w
  have hw : ∀ i, w i ∈ Icc (0 : ℝ) 1 := fun i =>
    normalized_singular_mem _ hα hA i
  have hpower : ∑ i, w i ^ (p / r) = 1 := by
    change (∑ i : Fin (Fintype.card n),
      (singularValues (G (r : ℂ)) i /
        schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ))) ^ (p / r)) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (singularValues (G (r : ℂ)) i / schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ))) ^ (p / r))]
    exact
      sum_normalized_pow (G (r : ℂ)) hα hA
  have hTdiff : Differentiable ℂ T := differentiable_dualTest U V r p w
  have hTnorm {z : ℂ} (hz : z.re ≤ 1) : specNorm (T z) ≤ 1 :=
    specNorm_dualTest_le_one hSVD.hasOrthonormalCols_left
      hSVD.hasOrthonormalCols_right hr.1 hp hw hz
  let g : ℂ → ℂ := fun z => (T z * G z).trace
  let L := (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
  have hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨?_, ?_⟩
    · exact L.differentiable.comp_differentiableOn (hTdiff.differentiableOn.mul hG.differentiableOn)
    · exact L.continuous.comp_continuousOn (hTdiff.continuous.continuousOn.mul hG.continuousOn)
  have hg_bound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      ‖g z‖ ≤ (Fintype.card n : ℝ) * B := by
    intro z hz
    exact (norm_trace_mul_le_card_mul_specNorm (hTnorm hz.2) (G z)).trans
      (mul_le_mul_of_nonneg_left (hbound z hz) (Nat.cast_nonneg _))
  have hg_left (t : ℝ) : ‖g ((t : ℂ) * Complex.I)‖ ≤ Real.exp (h₀ t) := by
    have hTl := nuclearNorm_dualTest_left hSVD.hasOrthonormalCols_left
      hSVD.hasOrthonormalCols_right hr.1 hp0 (fun i => (hw i).1) hpower t
    have h := norm_trace_mul_le_schattenNorm_mul
      (T ((t : ℂ) * Complex.I)) (G ((t : ℂ) * Complex.I)) (q := 1) (r := ∞)
    change ‖g ((t : ℂ) * Complex.I)‖ ≤ _ at h
    simp only [schattenNorm_one, schattenNorm_top, T, hTl, one_mul] at h
    exact h.trans (hleft t)
  have hg_right (t : ℝ) : ‖g (1 + (t : ℂ) * Complex.I)‖ ≤ Real.exp (h₁ t) := by
    by_cases hp1 : p = 1
    · subst p
      have h := norm_trace_mul_le_schattenNorm_mul
        (T (1 + (t : ℂ) * Complex.I)) (G (1 + (t : ℂ) * Complex.I)) (q := ∞) (r := 1)
      simp only [schattenNorm_one, schattenNorm_top] at h
      apply h.trans
      calc
        _ ≤ 1 * nuclearNorm (G (1 + (t : ℂ) * Complex.I)) :=
          mul_le_mul_of_nonneg_right (hTnorm (by simp))
            (nuclearNorm_nonneg _)
        _ ≤ _ := by simpa only [one_mul, ENNReal.ofReal_one, schattenNorm_one] using hright t
    · have hp1' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
      have hpq := Real.HolderConjugate.conjExponent hp1'
      have hTr := norm_dualTest_right hSVD.hasOrthonormalCols_left
        hSVD.hasOrthonormalCols_right hr.1 hpq (fun i => (hw i).1) hpower t
      let := hpq.symm.ennrealOfReal
      have h := norm_trace_mul_le_schattenNorm_mul (q := ENNReal.ofReal (Real.conjExponent p))
        (r := ENNReal.ofReal p)
        (T (1 + (t : ℂ) * Complex.I)) (G (1 + (t : ℂ) * Complex.I))
      simp only [T, hTr, one_mul] at h
      exact h.trans (hright t)
  have hcenter : ‖g (r : ℂ)‖ = schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ)) := by
    have htr := trace_dualTest_center_mul hSVD hr.1
      (lt_of_lt_of_le hr.2 hp) hA
    change g (r : ℂ) = (schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ)) : ℂ) at htr
    rw [htr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (schattenNorm_nonneg _ _)]
  rw [← hcenter]
  exact Complex.norm_le_exp_integral_stripHarmonicMeasure hr hg hg_bound
    h₀ h₁ hm₀ hm₁ hb₀ hb₁ hg_left hg_right

/-- The matrix interpolation bound when the left boundary consists of
spectral contractions, as for ordered imaginary-time Hermitian exponentials. -/
theorem schattenNorm_le_exp_integral_stripHarmonicMeasure_of_specNorm_le_one
    {r p B H : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hp : 1 ≤ p)
    {G : ℂ → Matrix n n ℂ}
    (hG : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (G z) ≤ B)
    (h₁ : ℝ → ℝ) (hm₁ : Measurable h₁) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, specNorm (G ((t : ℂ) * Complex.I)) ≤ 1)
    (hright : ∀ t : ℝ,
      schattenNorm (ENNReal.ofReal p) (G (1 + (t : ℂ) * Complex.I)) ≤ Real.exp (h₁ t)) :
    schattenNorm (ENNReal.ofReal (p / r)) (G (r : ℂ)) ≤
      Real.exp (r * (∫ t, h₁ t ∂Real.stripHarmonicMeasure r)) := by
  have hH : 0 ≤ H := (abs_nonneg (h₁ 0)).trans (hb₁ 0)
  simpa only [mul_zero, integral_zero, zero_add] using
    schattenNorm_le_exp_integral_stripHarmonicMeasure hr hp hG hbound
      (fun _ => 0) h₁ measurable_const hm₁ (fun _ => by simpa using hH) hb₁
      (fun t => by simpa only [Real.exp_zero] using hleft t) hright


end NLAlib
