/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Perturbation.Pseudospectrum
public import NLAlib.Matrix.Perturbation.Continuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.FieldTheory.Separable

/-!
# Area near a simple spectrum

Local disks in the pseudospectrum give an eventual lower area bound in terms of individual
eigenvalue condition numbers. The statement uses an arbitrary diagonalization and existing
column and row norms, so no eigenvector choice or condition-number definition is introduced.

## Main results

* `NLAlib.eventually_sum_mul_sq_le_measureReal_inter_ball_of_mul_eq_mul_diagonal`.
-/

@[expose] public section

open scoped Matrix Topology
open MeasureTheory Filter Function

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem inv_shift (A V : Matrix n n ℂ) (d : n → ℂ) (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (z : ℂ) (hz : ∀ j, z - d j ≠ 0) :
    (z • 1 - A)⁻¹ = V * Matrix.diagonal (fun j => (z - d j)⁻¹) * V⁻¹ := by
  have h := inv_aeval_eq_mul_diagonal_mul_inv hV hAV
    (p := Polynomial.C z - Polynomial.X) (fun j => by simpa using hz j)
  simpa only [map_sub, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_eq_smul_one, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X] using h

private theorem continuousAt_rescaled_resolvent (V W : Matrix n n ℂ) (d : n → ℂ)
    (hd : Function.Injective d) (i : n) : ContinuousAt (fun z : ℂ => V * Matrix.diagonal
      (fun j => if j = i then 1 else (z - d i) * (z - d j)⁻¹) * W) (d i) := by
  apply ContinuousAt.mul
  · apply ContinuousAt.mul continuousAt_const
    apply continuous_id.matrix_diagonal.continuousAt.comp
    apply continuousAt_pi.2
    intro j
    change ContinuousAt (fun z : ℂ =>
      if j = i then (1 : ℂ) else (z - d i) * (z - d j)⁻¹) (d i)
    by_cases hj : j = i
    · simpa only [if_pos hj] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) (d i))
    · simp only [if_neg hj]
      exact (continuousAt_id.sub continuousAt_const).mul
        ((continuousAt_id.sub continuousAt_const).inv₀
            (sub_ne_zero.mpr (fun h => hj (hd h).symm)))
  · exact continuousAt_const

private theorem local_pseudo {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hd : Function.Injective d)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (i : n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      dist z (d i) < δ → dist z (d i) ≤
        ε * (‖WithLp.toLp 2 (V.col i)‖ * ‖WithLp.toLp 2 (V⁻¹.row i)‖) / 2 →
      singularValues (z • 1 - A) k ≤ ε := by
  let F : ℂ → Matrix n n ℂ := fun z => V * Matrix.diagonal
    (fun j => if j = i then 1 else (z - d i) * (z - d j)⁻¹) * V⁻¹
  have hcont : ContinuousAt F (d i) := continuousAt_rescaled_resolvent V V⁻¹ d hd i
  have hFi : F (d i) = Matrix.vecMulVec (V.col i) (V⁻¹.row i) := by
    ext a b
    rw [show F (d i) = (V * Matrix.diagonal
      (fun j => if j = i then 1 else (d i - d i) * (d i - d j)⁻¹)) * V⁻¹ from rfl,
      Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.vecMulVec_apply]
  let q := ‖WithLp.toLp 2 (V.col i)‖ * ‖WithLp.toLp 2 (V⁻¹.row i)‖
  have hq : 0 < q := by
    have hc := (Matrix.linearIndependent_cols_iff_isUnit.mpr hV).ne_zero i
    have hr := (Matrix.linearIndependent_rows_iff_isUnit.mpr
      (Matrix.isUnit_nonsing_inv_iff.mpr hV)).ne_zero i
    apply mul_pos
    · exact norm_pos_iff.mpr (fun h => hc (congrArg WithLp.ofLp h))
    · exact norm_pos_iff.mpr (fun h => hr (congrArg WithLp.ofLp h))
  have hnorm : specNorm (F (d i)) = q := by rw [hFi, specNorm_vecMulVec]
  have hncont := continuous_specNorm.continuousAt.comp hcont
  have hnear : ∀ᶠ z in 𝓝 (d i), q / 2 < specNorm (F z) :=
    hncont.eventually (eventually_gt_nhds (by
      change q / 2 < specNorm (F (d i))
      rw [hnorm]
      linarith))
  have havoid : ∀ᶠ z in 𝓝 (d i), ∀ j, j ≠ i → z ≠ d j := by
    rw [eventually_all]
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall (by simp [hj])
    · filter_upwards [eventually_ne_nhds (fun h => hj (hd h).symm)] with z hz using fun _ => hz
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hnear.and havoid)
  refine ⟨δ, hδ, fun ε hε z hz hdist => ?_⟩
  have hlist := isEigenvalueListing_of_mul_eq_mul_diagonal
    ((Matrix.isUnit_iff_isUnit_det _).mp hV) hAV
  have heig : d i ∈ spectrum ℂ A := hlist.spectrum_eq_range.symm ▸ ⟨i, rfl⟩
  rcases eq_or_ne z (d i) with rfl | hzi
  · exact (singularValues_le_iff_mem_spectrum_or_le_specNorm_inv A (d i) hk hε).2 (Or.inl heig)
  have hall : ∀ j, z - d j ≠ 0 := fun j => sub_ne_zero.mpr (by
    by_cases hj : j = i
    · simpa only [hj] using hzi
    · exact (hball hz).2 j hj)
  have hdiag : Matrix.diagonal
      (fun j => if j = i then (1 : ℂ) else (z - d i) * (z - d j)⁻¹) =
      (z - d i) • Matrix.diagonal (fun j => (z - d j)⁻¹) := by
    rw [← Matrix.diagonal_smul]
    apply congrArg Matrix.diagonal
    funext j
    change (if j = i then (1 : ℂ) else (z - d i) * (z - d j)⁻¹) =
      (z - d i) * (z - d j)⁻¹
    by_cases hj : j = i
    · simpa only [hj, if_true] using (mul_inv_cancel₀ (hall i)).symm
    · rw [if_neg hj]
  have hF : F z = (z - d i) • (z • 1 - A)⁻¹ := by
    change V * Matrix.diagonal _ * V⁻¹ = _
    rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, inv_shift A V d hV hAV z hall]
  have hlarge : q / 2 < ‖z - d i‖ * specNorm (z • 1 - A)⁻¹ := by
    simpa only [hF, specNorm_smul] using (hball hz).1
  apply (singularValues_le_iff_mem_spectrum_or_le_specNorm_inv A z hk hε).2
  right
  have hd0 : 0 < ‖z - d i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzi)
  have hi0 := specNorm_nonneg (z • 1 - A)⁻¹
  rw [dist_eq_norm] at hdist
  change ‖z - d i‖ ≤ ε * q / 2 at hdist
  rw [div_le_iff₀ hε]
  nlinarith [mul_le_mul_of_nonneg_right hdist hi0]

private theorem eventually_mul_div_two_lt {a b : ℝ} (hb : 0 < b) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ε * a / 2 < b := by
  have hc : ContinuousAt (fun ε : ℝ => ε * a / 2) 0 := by fun_prop
  exact hc.eventually (eventually_lt_nhds (by simpa using hb))

/-- **A lower area bound for the pseudospectrum near simple eigenvalues.** If an invertible
matrix diagonalizes a complex matrix with distinct diagonal entries strictly inside the disk
of radius $R$, then for all sufficiently small positive $\varepsilon$, its pseudospectrum
inside that disk has area at least $\pi\varepsilon^2/4$ times the sum of squared individual
eigenvalue condition numbers, expressed as column norms times inverse row norms.
[BanksKulkarniMukherjeeSrivastava2021, Lemma 3.2] proves the limiting equality without the
factor $1/4$; this eventual inequality suffices for polynomial conditioning tails. -/
theorem eventually_sum_mul_sq_le_measureReal_inter_ball_of_mul_eq_mul_diagonal
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hd : Function.Injective d)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {R : ℝ} (hR : ∀ i, ‖d i‖ < R) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.pi / 4 * (∑ i, (‖WithLp.toLp 2 (V.col i)‖ *
        ‖WithLp.toLp 2 (V⁻¹.row i)‖) ^ 2) * ε ^ 2 ≤
      volume.real ({z : ℂ | singularValues (z • 1 - A) k ≤ ε} ∩ Metric.ball 0 R) := by
  let q : n → ℝ := fun i => ‖WithLp.toLp 2 (V.col i)‖ * ‖WithLp.toLp 2 (V⁻¹.row i)‖
  choose δ hδ hloc using fun i => local_pseudo hV hAV hd hk i
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, ε * q i / 2 < δ i ∧
      ε * q i / 2 < R - ‖d i‖ := by
    apply eventually_all.2
    intro i
    exact (eventually_mul_div_two_lt (hδ i)).and
      (eventually_mul_div_two_lt (sub_pos.mpr (hR i)))
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i j, i ≠ j →
      ε * (q i + q j) / 2 < dist (d i) (d j) := by
    apply eventually_all.2
    intro i
    apply eventually_all.2
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (by simp [hij])
    · exact (eventually_mul_div_two_lt (dist_pos.mpr (hd.ne hij))).mono
        fun ε h _ => h
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
    hsep.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hs hp hε
  change 0 < ε at hε
  have hdisj : Pairwise (Disjoint on fun i => Metric.ball (d i) (ε * q i / 2)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hh := hp i j hij
    linarith
  have hsub : (⋃ i, Metric.ball (d i) (ε * q i / 2)) ⊆
      {z : ℂ | singularValues (z • 1 - A) k ≤ ε} ∩ Metric.ball 0 R := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    change dist z (d i) < ε * q i / 2 at hi
    refine ⟨hloc i ε hε z (hi.trans (hs i).1) hi.le, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hn := norm_le_norm_sub_add z (d i)
    rw [← dist_eq_norm] at hn
    linarith [(hs i).2]
  have hvol (i : n) : volume.real (Metric.ball (d i) (ε * q i / 2)) =
      Real.pi * (ε * q i / 2) ^ 2 := by
    have hq : 0 ≤ q i := by dsimp [q]; positivity
    simp only [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε * q i / 2),
      ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  calc
    _ = ∑ i, volume.real (Metric.ball (d i) (ε * q i / 2)) := by
      simp only [hvol, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [q]
      ring
    _ = volume.real (⋃ i, Metric.ball (d i) (ε * q i / 2)) :=
      (measureReal_iUnion_fintype hdisj (fun _ => measurableSet_ball)).symm
    _ ≤ _ := measureReal_mono hsub (by
      apply measure_ne_top_of_subset Set.inter_subset_right
      rw [Complex.volume_ball]
      finiteness)

/-- The squared individual eigenvalue condition numbers are bounded by the lower limit of
normalized pseudospectral areas along any positive sequence tending to zero. The eigenvalues
are distinct and strictly inside the disk of radius $R$.
[BanksKulkarniMukherjeeSrivastava2021, Lemma 3.2], with the sufficient factor $4$. -/
theorem ofReal_sum_sq_le_liminf_measure_inter_ball_of_mul_eq_mul_diagonal
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hd : Function.Injective d)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {R : ℝ} (hR : ∀ i, ‖d i‖ < R)
    {e : ℕ → ℝ} (he : ∀ j, 0 < e j) (he0 : Tendsto e atTop (𝓝 0)) :
    ENNReal.ofReal (∑ i, (‖WithLp.toLp 2 (V.col i)‖ *
      ‖WithLp.toLp 2 (V⁻¹.row i)‖) ^ 2) ≤
      liminf (fun j => ENNReal.ofReal (4 / (Real.pi * e j ^ 2)) *
        volume ({z : ℂ | singularValues (z • 1 - A) k ≤ e j} ∩ Metric.ball 0 R)) atTop := by
  have heT : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he0, Eventually.of_forall he⟩
  have ha := heT.eventually
    (eventually_sum_mul_sq_le_measureReal_inter_ball_of_mul_eq_mul_diagonal hV hAV hd hk hR)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [ha] with j hj
  have hej := he j
  have hfin : volume ({z : ℂ | singularValues (z • 1 - A) k ≤ e j} ∩
      Metric.ball 0 R) ≠ ⊤ := by
    apply measure_ne_top_of_subset Set.inter_subset_right
    rw [Complex.volume_ball]
    finiteness
  rw [← ofReal_measureReal hfin, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < Real.pi * e j ^ 2)]
  nlinarith

/-- A simple-spectrum matrix inside a spectral disk that admits no diagonalizer with condition
number at most $B>0$ has normalized pseudospectral area lower limit at least $B^2/n$.
The normalization includes the sufficient factor $4$ of the local area estimate.
[BanksKulkarniMukherjeeSrivastava2021, Lemmas 3.1 and 3.2]. -/
theorem ofReal_sq_div_card_le_liminf_measure_inter_ball_of_not_exists
    {A : Matrix n n ℂ} (hA : A.charpoly.Separable) {R B : ℝ}
    (hR : specNorm A < R) (hB : 0 < B)
    (hbad : ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      A * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {e : ℕ → ℝ}
    (he : ∀ j, 0 < e j) (he0 : Tendsto e atTop (𝓝 0)) :
    ENNReal.ofReal (B ^ 2 / Fintype.card n) ≤
      liminf (fun j => ENNReal.ofReal (4 / (Real.pi * e j ^ 2)) *
        volume ({z : ℂ | singularValues (z • 1 - A) k ≤ e j} ∩ Metric.ball 0 R)) atTop := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing A
  have hid : Function.Injective d :=
    Polynomial.separable_prod_X_sub_C_iff.mp (hd ▸ hA)
  have hdiag : IsDiagonalizable A := isDiagonalizable_of_injective_of_forall_mem_spectrum hid
    (fun i => hd.spectrum_eq_range.symm ▸ ⟨i, rfl⟩)
  obtain ⟨V, f, hV, hAV⟩ := hdiag
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det _).mpr hV
  have hf := isEigenvalueListing_of_mul_eq_mul_diagonal hV hAV
  have hif : Function.Injective f :=
    Polynomial.separable_prod_X_sub_C_iff.mp (hf ▸ hA)
  obtain ⟨W, hW, hAW, hκ⟩ :=
    exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_sq_le hVu hAV
  have hBW : B < pseudoConditionNumber W :=
    lt_of_not_ge (fun h => hbad ⟨W, f, hW, hAW, h⟩)
  have hn : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast (show 0 < Fintype.card n by omega)
  have hscore : B ^ 2 / (Fintype.card n : ℝ) ≤ ∑ i,
      (‖WithLp.toLp 2 (V.col i)‖ * ‖WithLp.toLp 2 (V⁻¹.row i)‖) ^ 2 := by
    rw [div_le_iff₀ hn]
    have hh := (sq_lt_sq₀ hB.le (pseudoConditionNumber_nonneg W)).2 hBW
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hscore).trans
    (ofReal_sum_sq_le_liminf_measure_inter_ball_of_mul_eq_mul_diagonal hVu hAV hif hk
      (fun i => (norm_le_specNorm_of_mul_eq_mul_diagonal hVu hAV i).trans_lt hR) he he0)

end NLAlib
