/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.RandomizedDeflation
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Global
public import NLAlib.Matrix.Perturbation.Continuity
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hermitian diagonalization in linear precision: the nodes

Randomized spectral bisection (`NLAlib.eigh`) draws
at each node of its tree an ideal sample of law `NLAlib.eighSampleLaw` (a uniform seed on
$[-1, 1]$ and two independent standard complex Gaussian matrices). This file bounds the
probability that the sample of one node is bad ([Shah2024, Lemma 4.1]) and shows that the node
at a path is a countably-valued, measurable function of the earlier samples, independent of its
own sample: all the probability argument needs about the algorithm's measurability. The global
bound, [Shah2024, Theorem 4.2], is in `NLAlib/Eigensolvers/SpectralBisection/Global.lean`.

## Main definitions

* `NLAlib.eighSampleLaw`.

## Main results

* `NLAlib.measureReal_exists_abs_sub_lt_le`: a random shift avoids the spectrum.
* `NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le_of_isEighNodeBudget`: the good
  events of a node.
* `NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
  `NLAlib.indepFun_eighNodeAt_eq`: the nodes are computed from earlier samples.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib


/-- The **law of the ideal sample of a node**: a seed uniform on $[-1, 1]$ and two independent
standard complex Gaussian $N \times N$ matrices, independent of the seed. -/
noncomputable def eighSampleLaw (N : ℕ) : Measure (EighSample ℝ ℂ N) :=
  (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).prod
    (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))

/-- **A random shift avoids a finite set** (Event I): for a finite set $\Lambda$ of reals,
$c > 0$, $w \ge 0$ and $v$ uniform on $[-1, 1]$,
$$\mathbb{P}[\exists \lambda \in \Lambda,\ \lvert \lambda - cv \rvert < w] \le
\frac{\lvert\Lambda\rvert\,w}{c} \,.$$
[Shah2024, proof of Lemma 4.1], there with the density $\ell/(2R)$ of the shift and the bound
$nw/R$, which drops the factor $\ell$; here $c = R/\ell$ gives $nw\ell/R$. -/
theorem measureReal_exists_abs_sub_lt_le (Λ : Finset ℝ) {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).real
      {v | ∃ e ∈ Λ, |e - c * v| < w} ≤ Λ.card * w / c := by
  rw [measureReal_def, cond_apply measurableSet_Icc]
  have hvol : volume (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
    rw [Real.volume_Icc]; norm_num
  have hsub : Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w} ⊆
      ⋃ e ∈ Λ, Set.Ioo ((e - w) / c) ((e + w) / c) := by
    rintro v ⟨-, e, he, hv⟩
    rw [abs_lt] at hv
    simp only [Set.mem_iUnion, Set.mem_Ioo]
    refine ⟨e, he, ?_, ?_⟩
    · rw [div_lt_iff₀ hc]; linarith [hv.2]
    · rw [lt_div_iff₀ hc]; linarith [hv.1]
  have h1 : volume (Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w}) ≤
      ∑ e ∈ Λ, volume (Set.Ioo ((e - w) / c) ((e + w) / c)) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have h2 : ∀ e : ℝ, volume (Set.Ioo ((e - w) / c) ((e + w) / c)) =
      ENNReal.ofReal (2 * w / c) := by
    intro e
    rw [Real.volume_Ioo]
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_const, nsmul_eq_mul] at h1
  have hpos : (0 : ℝ) ≤ Λ.card * w / c := by positivity
  refine ENNReal.toReal_le_of_le_ofReal hpos ?_
  rw [hvol]
  calc (ENNReal.ofReal 2)⁻¹ * volume (Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w})
      ≤ (ENNReal.ofReal 2)⁻¹ * ((Λ.card : ℝ≥0∞) * ENNReal.ofReal (2 * w / c)) := by gcongr
    _ = ENNReal.ofReal (Λ.card * w / c) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos two_pos, ← ENNReal.ofReal_mul
        (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- The sign of a shifted Hermitian matrix is a measurable function of the shift. -/
private lemma measurable_cfc_sign_sub_smul {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (a : ℝ) :
    Measurable fun v : ℝ => cfc Real.sign (A - (a * v) • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  have h : ∀ c : ℝ, cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) =
      hA.cfc fun x => Real.sign (x + -c) := by
    intro c
    have hAc : A - c • (1 : Matrix (Fin k) (Fin k) ℂ) = cfc (fun x : ℝ => x + -c) A := by
      rw [cfc_add_const (-c) (fun x : ℝ => x) A, cfc_id' ℝ A, Algebra.algebraMap_eq_smul_one,
        neg_smul, sub_eq_add_neg]
    rw [hAc, ← cfc_comp' Real.sign (fun x : ℝ => x + -c) A
      ((A.finite_real_spectrum.image _).continuousOn _), ← hA.cfc_eq]
  simp_rw [h]
  unfold Matrix.IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  have hd : Measurable fun v : ℝ => Matrix.diagonal
      (RCLike.ofReal ∘ (fun x => Real.sign (x + -(a * v))) ∘ hA.eigenvalues : Fin k → ℂ) := by
    refine (continuous_id.matrix_diagonal).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    exact Complex.measurable_ofReal.comp (hs.comp (measurable_const.add
      (measurable_const.mul measurable_id).neg))
  have hc : Continuous fun X : Matrix (Fin k) (Fin k) ℂ =>
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * X *
        star (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) := by fun_prop
  exact hc.measurable.comp hd

/-- The trace of $\mathbf{V}\mathbf{V}^{\mathsf{H}}$ is the number of orthonormal columns. -/
private lemma HasOrthonormalCols.re_trace_mul_conjTranspose {k m : ℕ} {V : Matrix (Fin k) (Fin m) ℂ}
    (hV : HasOrthonormalCols V) : RCLike.re (V * Vᴴ).trace = m := by
  rw [Matrix.trace_mul_comm, hV.conjTranspose_mul_self, Matrix.trace_one, Fintype.card_fin]
  simp

/-- For $k \le N$ the leading block is the submatrix along `Fin.castLE`. -/
private lemma leadingBlock_eq_submatrix {k N : ℕ} (h : k ≤ N)
    (G : Matrix (Fin N) (Fin N) ℂ) :
    leadingBlock k G = G.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp [leadingBlock, Fin.castLE, show (i : ℕ) < N from i.isLt.trans_le h,
    show (j : ℕ) < N from j.isLt.trans_le h]

/-- The leading block of either test matrix of a sample is standard complex Gaussian. -/
private lemma hasLaw_leadingBlock_apply {k N : ℕ} (h : k ≤ N) (b : Bool) :
    HasLaw (fun G : Bool → Matrix (Fin N) (Fin N) ℂ => leadingBlock k (G b))
      (complexGaussianMatrix (Fin k) (Fin k))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) := by
  have h0 : HasLaw (fun G : Bool → Matrix (Fin N) (Fin N) ℂ => G b)
      (complexGaussianMatrix (Fin N) (Fin N))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) :=
    ⟨(measurePreserving_eval (fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))
        b).measurable.aemeasurable,
      (measurePreserving_eval (fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) b).map_eq⟩
  have := hasLaw_submatrix_of_hasLaw_complexGaussianMatrix h0 (Fin.castLE_injective h)
    (Fin.castLE_injective h)
  simpa only [leadingBlock_eq_submatrix h] using this

/-- Event II fails on one side with probability at most $\rho/16 + 15\rho/16$ for a fixed frame:
the norm tail $e^{-s^2}$ and the smaller of the tails $r^2x^2$, $e\,r x^2$ of the smallest
singular value. -/
private lemma measure_not_eventII_le {k N m : ℕ} (hkN : k ≤ N) (b : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hm : 0 < m) (hmk : m ≤ k) {V : Matrix (Fin k) (Fin m) ℂ}
    (hV : HasOrthonormalCols V) :
    (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))
      ({G | 2 * √2 * √(k : ℝ) + √(Real.log (16 / ρ)) ≤ specNorm (leadingBlock k (G b))} ∪
        {G | singularValues (Vᴴ * (leadingBlock k (G b)).submatrix id (Fin.castLE hmk)) (m - 1) ≤
          √(15 * ρ / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k)))}) ≤ ENNReal.ofReal ρ := by
  set μ := Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)
  have hL := hasLaw_leadingBlock_apply hkN b
  have hlog : 0 ≤ Real.log (16 / ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have h1 := measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix hL
    (Real.sqrt_nonneg (Real.log (16 / ρ)))
  simp only [Fintype.card_fin] at h1
  rw [Real.sq_sqrt hlog, Real.exp_neg, Real.exp_log (by positivity), inv_div] at h1
  have hK := hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix
    (hasLaw_submatrix_of_hasLaw_complexGaussianMatrix hL Function.injective_id
      (Fin.castLE_injective hmk)) hV
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hm.trans_le hmk
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hD : 0 < min ((k : ℝ) ^ 2) (Real.exp 1 * k) := by positivity
  have hx : √(15 * ρ / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k))) ^ 2 =
      15 * ρ / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k)) := Real.sq_sqrt (by positivity)
  have h2 : μ.real {G | singularValues (Vᴴ * (leadingBlock k (G b)).submatrix id
      (Fin.castLE hmk)) (m - 1) ≤ √(15 * ρ / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k)))} ≤
      15 * ρ / 16 := by
    rcases min_choice ((k : ℝ) ^ 2) (Real.exp 1 * k) with hmin | hmin
    · refine (measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hK
        (k := m - 1) (by simp; omega) (Real.sqrt_nonneg _)).trans ?_
      simp only [Fintype.card_fin]
      rw [hx, hmin, mul_div_assoc', div_le_iff₀ (by positivity)]
      have : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmk' 2
      nlinarith
    · refine (measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix hK
        (k := m - 1) (by simp; omega) (Real.sqrt_nonneg _)).trans ?_
      simp only [Fintype.card_fin]
      rw [hx, hmin, mul_div_assoc', div_le_iff₀ (by positivity)]
      have := Real.exp_pos 1
      nlinarith [mul_le_mul_of_nonneg_left hmk' (by positivity : (0 : ℝ) ≤ Real.exp 1 * k * ρ)]
  refine (measure_union_le _ _).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : {G : Bool → Matrix (Fin N) (Fin N) ℂ |
      2 * √2 * √(k : ℝ) + √(Real.log (16 / ρ)) ≤ specNorm (leadingBlock k (G b))} =
      {G | √2 * (√(k : ℝ) + √(k : ℝ)) + √(Real.log (16 / ρ)) ≤
        specNorm (leadingBlock k (G b))} := by
    ext G; simp only [Set.mem_ofPred_eq]; ring_nf
  rw [e1]
  linarith

/-- Off the spectrum, each spectral projector of a shift has a frame with orthonormal columns. -/
private lemma exists_frame_of_forall_ne {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian)
    {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) (b : Bool) :
    ∃ m, ∃ V : Matrix (Fin k) (Fin m) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) •
        cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) := by
  cases b
  · have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
      intro x hx hxc
      rw [← spectrum.neg_eq] at hx
      exact hc (-x) hx (by rw [hxc, neg_neg])
    obtain ⟨V, hV, hVV, -⟩ := hA.neg.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
    refine ⟨_, V, hV, ?_⟩
    have hX : (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)).IsHermitian :=
      hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])
    have h1 : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -(A - c • 1) := by
      rw [neg_smul, sub_neg_eq_add, neg_sub', sub_neg_eq_add]
    have h2 : cfc Real.sign (-(A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) =
        -cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [← cfc_comp_neg Real.sign (A - c • 1)
        (((A - c • 1).finite_real_spectrum.image _).continuousOn _) hX.isSelfAdjoint,
        ← cfc_neg]
      simp only [Real.sign_neg]
    rw [hVV, h1, h2]
    simp
  · obtain ⟨V, hV, hVV, -⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
    exact ⟨_, V, hV, by rw [hVV]; simp⟩

/-- The spectral projector of side `b` at the ideal shift $Lv$. -/
private noncomputable def sideProj {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L : ℝ) (b : Bool)
    (v : ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) •
    cfc Real.sign (A - (L * v) • (1 : Matrix (Fin k) (Fin k) ℂ)))

/-- The seeds of Event I at which the positive projector has rank strictly between $0$ and $k$. -/
private def splitSeeds {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L w : ℝ) : Set ℝ :=
  (Set.Icc (-1 : ℝ) 1 ∩ ⋂ e ∈ spectrum ℝ A, {v | w ≤ |e - L * v|}) ∩
    ({v | 0 < RCLike.re (sideProj A L true v).trace} ∩
      {v | RCLike.re (sideProj A L true v).trace < k})

/-- A measurable superset of the failure of Event II on side `b` at the seeds of
`splitSeeds`, with the frame replaced by the projector. -/
private def sideBad {k : ℕ} (N : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) (L w x t : ℝ) (b : Bool) :
    Set (EighSample ℝ ℂ N) :=
  {s | s.1 ∈ splitSeeds A L w ∧ ∃ r : Fin k, 0 < (r : ℕ) ∧
    RCLike.re (sideProj A L b s.1).trace = ((r : ℕ) : ℝ) ∧
    (t ≤ specNorm (leadingBlock k (s.2 b)) ∨
      singularValues (sideProj A L b s.1 * (leadingBlock k (s.2 b)).submatrix id
        (Fin.castLE r.isLt.le)) ((r : ℕ) - 1) ≤ x)}

/-- Membership in `splitSeeds`. -/
private lemma mem_splitSeeds {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} {L w v : ℝ} :
    v ∈ splitSeeds A L w ↔ (v ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ e ∈ spectrum ℝ A, w ≤ |e - L * v|) ∧
      0 < RCLike.re (sideProj A L true v).trace ∧
        RCLike.re (sideProj A L true v).trace < k := by
  simp only [splitSeeds, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The two projectors have traces adding up to $k$. -/
private lemma re_trace_sideProj_add {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L v : ℝ) :
    RCLike.re (sideProj A L true v).trace + RCLike.re (sideProj A L false v).trace = k := by
  have : sideProj A L true v + sideProj A L false v = 1 := by
    simp only [sideProj, if_true, Bool.false_eq_true, if_false, one_smul, neg_smul]
    module
  rw [← map_add, ← Matrix.trace_add, this, Matrix.trace_one, Fintype.card_fin]
  simp

/-- The trace function of a projector is measurable in the seed. -/
private lemma measurable_sideProj_and_re_trace {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (L : ℝ) (b : Bool) :
    Measurable (sideProj A L b) ∧ Measurable fun v => RCLike.re (sideProj A L b v).trace := by
  have h : Measurable (sideProj A L b) :=
    (Continuous.measurable (by fun_prop) : Measurable fun S : Matrix (Fin k) (Fin k) ℂ =>
      (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) • S)).comp
        (measurable_cfc_sign_sub_smul hA L)
  exact ⟨h, (Continuous.measurable (by fun_prop : Continuous fun X : Matrix (Fin k) (Fin k) ℂ =>
    RCLike.re X.trace)).comp h⟩

/-- `splitSeeds` is measurable. -/
private lemma measurableSet_splitSeeds {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (L w : ℝ) : MeasurableSet (splitSeeds A L w) :=
  (measurableSet_Icc.inter (A.finite_real_spectrum.measurableSet_biInter fun _ _ =>
    measurableSet_le measurable_const
      (continuous_const.sub (continuous_const.mul continuous_id)).abs.measurable)).inter
    ((measurableSet_lt measurable_const (measurable_sideProj_and_re_trace hA L true).2).inter
      (measurableSet_lt (measurable_sideProj_and_re_trace hA L true).2 measurable_const))

/-- `sideBad` is measurable. -/
private lemma measurableSet_sideBad {k N : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (hkN : k ≤ N) (L w x t : ℝ) (b : Bool) :
    MeasurableSet (sideBad N A L w x t b) := by
  have hLB : Measurable fun G : Bool → Matrix (Fin N) (Fin N) ℂ => leadingBlock k (G b) := by
    simp_rw [leadingBlock_eq_submatrix hkN]
    exact ((continuous_apply b).matrix_submatrix _ _).measurable
  obtain ⟨hP, htr⟩ := measurable_sideProj_and_re_trace hA L b
  refine measurableSet_setOfPred.2 ((measurableSet_setOfPred.1
    (measurable_fst (measurableSet_splitSeeds hA L w))).and
    (Measurable.exists fun r => measurable_const.and
      ((measurableSet_setOfPred.1 (measurableSet_eq_fun (htr.comp measurable_fst)
        measurable_const)).and ((measurableSet_setOfPred.1 (measurableSet_le measurable_const
          (continuous_specNorm.measurable.comp (hLB.comp measurable_snd)))).or
          (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const))))))
  refine (continuous_singularValues _).measurable.comp ?_
  exact Continuous.measurable2 (by fun_prop) (hP.comp measurable_fst)
    ((Continuous.matrix_submatrix continuous_id _ _).measurable.comp (hLB.comp measurable_snd))

/-- Each side fails Event II with probability at most $\rho$ on the seeds of `splitSeeds`:
`MeasureTheory.Measure.prod_apply` and the fibre bound for a frame of the projector. -/
private lemma measure_sideBad_le {k N : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (hkN : k ≤ N) {L w ρ : ℝ} (hw : 0 < w) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (μ : Measure ℝ) (b : Bool) :
    (μ.prod (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)))
      (sideBad N A L w (√(15 * ρ / (16 * min ((k : ℝ) ^ 2) (Real.exp 1 * k))))
        (2 * √2 * √(k : ℝ) + √(Real.log (16 / ρ))) b) ≤
      ENNReal.ofReal ρ * μ (splitSeeds A L w) := by
  rw [Measure.prod_apply (measurableSet_sideBad hA hkN L w _ _ b),
    ← lintegral_indicator_const (measurableSet_splitSeeds hA L w)]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ splitSeeds A L w
  · rw [Set.indicator_of_mem hv]
    obtain ⟨⟨-, hI⟩, -⟩ := mem_splitSeeds.1 hv
    obtain ⟨m, V, hV, hVV⟩ := exists_frame_of_forall_ne hA (c := L * v) (fun e he hev => by
      have := hI e he
      rw [hev, sub_self, abs_zero] at this
      linarith) b
    change V * Vᴴ = sideProj A L b v at hVV
    have htrV := hV.re_trace_mul_conjTranspose
    rw [hVV] at htrV
    by_cases hm : 0 < m ∧ m ≤ k
    · refine (measure_mono ?_).trans (measure_not_eventII_le hkN b hρ hρ₁ hm.1 hm.2 hV)
      intro G hG
      obtain ⟨-, ⟨r, hrk⟩, -, hrtr, hbad⟩ := hG
      have hrm : r = m := by exact_mod_cast hrtr.symm.trans htrV
      subst hrm
      rcases hbad with h | h
      · exact Or.inl h
      · right
        rw [Set.mem_ofPred_eq, ← hV.singularValues_mul_left, ← Matrix.mul_assoc, hVV]
        exact h
    · refine le_of_eq_of_le (measure_mono_null (fun G hG => ?_) measure_empty) zero_le
      obtain ⟨-, ⟨r, hrk⟩, hr0, hrtr, -⟩ := hG
      have hrm : r = m := by exact_mod_cast hrtr.symm.trans htrV
      exact hm ⟨hrm ▸ hr0, hrm ▸ hrk.le⟩
  · rw [Set.indicator_of_notMem hv]
    exact le_of_eq (measure_mono_null (fun G hG => hv hG.1) measure_empty)

/-- Event I fails with probability at most $kw/L$ (`NLAlib.measureReal_exists_abs_sub_lt_le`; the
seed lies in $[-1, 1]$ almost surely). -/
private lemma measure_not_eventI_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian)
    {L w : ℝ} (hL : 0 < L) (hw : 0 < w) {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] :
    ((ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).prod ν)
      (Prod.fst ⁻¹' ({v | v ∉ Set.Icc (-1 : ℝ) 1} ∪
        {v | ∃ e ∈ spectrum ℝ A, |e - L * v| < w})) ≤ ENNReal.ofReal (k * w / L) := by
  classical
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
  refine (measure_union_le _ _).trans ?_
  have h0 : ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)
      {v | v ∉ Set.Icc (-1 : ℝ) 1} = 0 := by
    rw [cond_apply measurableSet_Icc]
    have : Set.Icc (-1 : ℝ) 1 ∩ {v | v ∉ Set.Icc (-1 : ℝ) 1} = ∅ := by
      ext v; simp
    rw [this, measure_empty, mul_zero]
  have hΛ : {v : ℝ | ∃ e ∈ spectrum ℝ A, |e - L * v| < w} =
      {v | ∃ e ∈ Finset.univ.image hA.eigenvalues, |e - L * v| < w} := by
    ext v
    simp [hA.spectrum_real_eq_range_eigenvalues]
  rw [h0, zero_add, hΛ, ← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ((measureReal_exists_abs_sub_lt_le _ hL hw.le).trans ?_)
  have hΛk : ((Finset.univ.image hA.eigenvalues).card : ℝ) ≤ k := by
    have := Finset.card_image_le (s := Finset.univ) (f := hA.eigenvalues)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  gcongr

/-- The failure of the good events lies in the failure of Event I or in `sideBad` on a side:
on Event I a frame of a projector with $0 < r < k$ columns pins the trace to $r$, and
`NLAlib.HasOrthonormalCols.singularValues_mul_left` replaces the frame by the projector. -/
private lemma not_isEighGoodSample_subset {F : Type*} {dec : F → ℝ} {w x t : ℝ}
    {y : EighNode F} {N : ℕ} :
    {s : EighSample ℝ ℂ N | ¬ IsEighGoodSample dec w x t y s} ⊆
      Prod.fst ⁻¹' ({v | v ∉ Set.Icc (-1 : ℝ) 1} ∪
        {v | ∃ e ∈ spectrum ℝ (decodeMatrix dec y.A), |e - dec y.R / y.ℓ * v| < w}) ∪
      (sideBad N (decodeMatrix dec y.A) (dec y.R / y.ℓ) w x t true ∪
        sideBad N (decodeMatrix dec y.A) (dec y.R / y.ℓ) w x t false) := by
  intro s hs
  simp only [IsEighGoodSample, Set.mem_ofPred_eq] at hs
  generalize decodeMatrix dec y.A = A at hs ⊢
  generalize dec y.R / (y.ℓ : ℝ) = L at hs ⊢
  by_cases h1 : s.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ e ∈ spectrum ℝ A, w ≤ |e - L * s.1|
  · right
    have h2 := not_and.1 hs h1
    push Not at h2
    obtain ⟨b, r, V, hr0, hrk, hV, hVV, hbad⟩ := h2
    change V * Vᴴ = sideProj A L b s.1 at hVV
    have htrV := hV.re_trace_mul_conjTranspose
    rw [hVV] at htrV
    have hsT : s.1 ∈ splitSeeds A L w := by
      refine mem_splitSeeds.2 ⟨h1, ?_⟩
      have hrk' : (r : ℝ) < y.k := by exact_mod_cast hrk
      have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
      have := re_trace_sideProj_add A L s.1
      cases b
      · rw [htrV] at this
        constructor <;> linarith
      · rw [htrV]
        exact ⟨hr0', hrk'⟩
    have hmem : s ∈ sideBad N A L w x t b := by
      refine ⟨hsT, ⟨r, hrk⟩, hr0, htrV, ?_⟩
      rcases le_or_gt t (specNorm (leadingBlock y.k (s.2 b))) with ht | ht
      · exact Or.inl ht
      · obtain ⟨h, hσ⟩ := hbad ht
        right
        rw [← hVV, Matrix.mul_assoc, hV.singularValues_mul_left]
        exact hσ
    cases b
    · exact Or.inr hmem
    · exact Or.inl hmem
  · left
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq]
    by_cases hv : s.1 ∈ Set.Icc (-1 : ℝ) 1
    · right
      push Not at h1
      exact h1 hv
    · exact Or.inl hv

/-- **Probability of the good events of a node**: let the machine meet
`NLAlib.FloatMachine.IsAccurate`, and let the node $y = (k, \mathbf{A}, R, \varepsilon, \ell)$ of
size $2 \le k \le N$, at which the leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ fails, meet the
node budget `NLAlib.FloatMachine.IsEighNodeBudget` with shift distance $w$, singular value
threshold $x = \sqrt{15\rho/(16\min(k^2, e k))}$ and norm threshold
$t = 2\sqrt2\sqrt k + \sqrt{\log(16/\rho)}$, for $0 < \rho \le 1$. Then the sample law
`NLAlib.eighSampleLaw` $N$ gives the bad events (`NLAlib.IsEighGoodSample` with $w$, $x$, $t$
failing) probability at most
$$\frac{kw\ell}{R} + 2\rho\,\mathbb{P}[\text{the node splits}] \,,$$
the node splitting when `NLAlib.eighStep` is `NLAlib.EighStep.split`. [Shah2024, Lemma 4.1],
"Event I occurs with probability at least $1 - wn/R$ and Event II with probability at least
$1 - 2\rho$"; here Event II on each side fails with probability at most $\rho/16$ (the norm tail
$e^{-s^2}$ above $2\sqrt2\sqrt k$) plus $15\rho/16$ (the tail $\min(r^2, e r)x^2$ of the
smallest singular value). -/
theorem FloatMachine.IsAccurate.measure_not_isEighGoodSample_le_of_isEighNodeBudget
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F}
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w
      (√(15 * ρ / (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / ρ))) y)
    (hk : 2 ≤ y.k) (hkN : y.k ≤ N) (hint : M.le y.R (M.mul y.ε R₀) = false) (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) :
    eighSampleLaw N {s | ¬ IsEighGoodSample dec w
      (√(15 * ρ / (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / ρ))) y s} ≤
      ENNReal.ofReal (y.k * w * y.ℓ / dec y.R) + ENNReal.ofReal (2 * ρ) *
        eighSampleLaw N {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
  have hA := hB.isHermitian
  have hRpos : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hℓpos : (0 : ℝ) < y.ℓ := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    linarith
  have hLpos : 0 < dec y.R / y.ℓ := div_pos hRpos hℓpos
  set μ₁ := ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)
  set ν := Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)
  set T := splitSeeds (decodeMatrix dec y.A) (dec y.R / y.ℓ) w
  -- the seeds of `T` split the node (rank recovery on Event I)
  have hTsplit : μ₁ T ≤
      (μ₁.prod ν) {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
    calc μ₁ T = (μ₁.prod ν) (T ×ˢ Set.univ) := by rw [Measure.prod_prod, measure_univ, mul_one]
      _ ≤ _ := measure_mono fun s hs => ?_
    obtain ⟨⟨hv, hI⟩, h0, h1⟩ := mem_splitSeeds.1 hs.1
    have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * s.1) fun e he hev => by
      have := hI e he
      rw [hev, sub_self, abs_zero] at this
      linarith [hB.pos_w]
    have hPt : sideProj (decodeMatrix dec y.A) (dec y.R / y.ℓ) true s.1 =
        (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * s.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) := by
      simp [sideProj]
    rw [hPt, htr] at h0 h1
    exact (hM.eighStep_isSplit_iff_of_isEighNodeBudget hB hk hint hv hI).2
      ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  refine (measure_mono not_isEighGoodSample_subset).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_not_eventI_le hA hLpos hB.pos_w ν) ((measure_union_le _ _).trans
    (add_le_add (measure_sideBad_le hA hkN hB.pos_w hρ hρ₁ μ₁ true)
      (measure_sideBad_le hA hkN hB.pos_w hρ hρ₁ μ₁ false)))).trans ?_
  rw [div_div_eq_mul_div, ← add_mul, ← ENNReal.ofReal_add hρ.le hρ.le, ← two_mul]
  gcongr
  exact hTsplit

/-- The computed shift and the computed leading blocks of a sample at the node `x`; the child of
`x` depends on the sample only through them. -/
private def eighSampleKey {F : Type*} (M : FloatMachine F ℝ ℂ) {N : ℕ} (x : EighNode F)
    (s : EighSample ℝ ℂ N) : F × (Bool → Matrix (Fin x.k) (Fin x.k) (F × F)) :=
  (M.unif (M.div x.R (M.ofNat x.ℓ)) s.1, fun b => (leadingBlock x.k (s.2 b)).map M.normal)

/-- The keys of the samples at a node form a countable set. -/
private lemma countable_range_eighSampleKey {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N : ℕ) (x : EighNode F) : (Set.range (eighSampleKey M (N := N) x)).Countable := by
  refine ((hunif (M.div x.R (M.ofNat x.ℓ))).prod (Set.countable_pi fun _ =>
    Set.countable_pi fun _ => Set.countable_pi fun _ => hnormal)).mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, rfl⟩, fun b i j => ⟨_, rfl⟩⟩

-- the proof names the size bound of `eighStep` to restate it without the sample
set_option linter.auxLemma false in
/-- The child of a node depends on its sample only through `eighSampleKey`. -/
private lemma eighChild_eq_of_eighSampleKey_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) {s s' : EighSample ℝ ℂ N}
    (h : eighSampleKey M x s = eighSampleKey M x s') (b : Bool) :
    eighChild M N signFuel R₀ β x s b = eighChild M N signFuel R₀ β x s' b := by
  simp only [eighSampleKey, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hd : ∀ r P b, deflate M r P (leadingBlock x.k (s.2 b)) =
      deflate M r P (leadingBlock x.k (s'.2 b)) := by
    intro r P b
    have h2b : (leadingBlock x.k (s.2 b)).map M.normal =
        (leadingBlock x.k (s'.2 b)).map M.normal := congrFun h2 b
    unfold deflate
    rw [h2b]
  have hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s =
      eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s' := by
    obtain ⟨v, G⟩ := s
    obtain ⟨v', G'⟩ := s'
    calc eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (v, G)
        = eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (v, G') := by
          unfold eighStep
          simp only [hd]
      _ = _ := by
          dsimp only at h1
          unfold eighStep
          by_cases hk : x.k ≤ 1
          · simp only [hk, if_true]
          · simp (config := {zeta := false}) only [hk, if_false]
            -- the size bound of the split mentions the sample: restate it without it
            rw [show eighStep._proof_1 M N signFuel β x.A x.R x.ℓ (v, G') = min_le_left _ _
              from rfl, h1]
  unfold eighChild
  rw [hs]

/-- The child of a node has countably many values as the ideal sample varies. -/
private lemma countable_range_eighChild {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N signFuel : ℕ) (R₀ β : F) (x : EighNode F) (b : Bool) :
    (Set.range fun s : EighSample ℝ ℂ N => eighChild M N signFuel R₀ β x s b).Countable := by
  classical
  refine ((countable_range_eighSampleKey hunif hnormal N x).image fun t =>
    if hs : ∃ s, eighSampleKey M x s = t then eighChild M N signFuel R₀ β x hs.choose b
    else none).mono ?_
  rintro _ ⟨s, rfl⟩
  have hs : ∃ s', eighSampleKey M x s' = eighSampleKey M x s := ⟨s, rfl⟩
  refine ⟨_, ⟨s, rfl⟩, ?_⟩
  dsimp only
  rw [dif_pos hs]
  exact eighChild_eq_of_eighSampleKey_eq x hs.choose_spec b

/-- The nodes take countably many values: if the computed samples have countably many values
(the uniform sampler at every scale and the normal sampler have countable ranges, as the
floating-point numbers do), then for every root and path the node `NLAlib.eighNodeAt` ranges over
a countable set as the samples vary. No printed source.
The algorithm can reach its ideal samples only through the samplers, since their types are
abstract in `NLAlib.eighStep` (§2.0 of the note). -/
theorem countable_range_eighNodeAt {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N signFuel : ℕ) (R₀ β : F) (a : List Bool) (x : EighNode F) :
    (Set.range fun s : List Bool → EighSample ℝ ℂ N =>
      eighNodeAt M N signFuel R₀ β a x s).Countable := by
  induction a generalizing x with
  | nil =>
    refine (Set.countable_singleton (some x)).mono ?_
    rintro _ ⟨s, rfl⟩
    exact Set.mem_singleton _
  | cons b a ih =>
    let S : Option (EighNode F) → Set (Option (EighNode F)) := fun y => match y with
      | none => {none}
      | some y' => Set.range fun s => eighNodeAt M N signFuel R₀ β a y' s
    have hS : ∀ y, (S y).Countable := by
      intro y
      cases y with
      | none => exact Set.countable_singleton _
      | some y' => exact ih y'
    have hY : (Set.range fun s : List Bool → EighSample ℝ ℂ N =>
        eighChild M N signFuel R₀ β x (s []) b).Countable :=
      (countable_range_eighChild hunif hnormal N signFuel R₀ β x b).mono (by
        rintro _ ⟨s, rfl⟩
        exact ⟨s [], rfl⟩)
    refine (hY.biUnion fun y _ => hS y).mono ?_
    rintro _ ⟨s, rfl⟩
    simp only [Set.mem_iUnion]
    refine ⟨eighChild M N signFuel R₀ β x (s []) b, ⟨s, rfl⟩, ?_⟩
    rcases hy : eighChild M N signFuel R₀ β x (s []) b with _ | y'
    · simp [S, eighNodeAt, hy]
    · exact ⟨fun a' => s (b :: a'), by simp [eighNodeAt, hy]⟩

/-- A map with countable range and measurable fibres has measurable preimages. -/
private lemma measurableSet_preimage_of_countable_range_fibres {Ω' α : Type*}
    {mΩ' : MeasurableSpace Ω'} {f : Ω' → α} (hc : (Set.range f).Countable)
    (hf : ∀ z, MeasurableSet (f ⁻¹' {z})) (T : Set α) : MeasurableSet (f ⁻¹' T) := by
  have : f ⁻¹' T = ⋃ z ∈ T ∩ Set.range f, f ⁻¹' {z} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (hc.mono Set.inter_subset_right) fun z _ => hf z

/-- The node at a path is an event of the earlier samples: if the samplers have measurable
fibres and countable ranges and each sample $\zeta_b$ is measurable, then for every root $x$, path
$a$ and possible node $y$, the set of outcomes at which the node at $a$ is $y$ is measurable. No
printed source. -/
theorem measurableSet_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (a : List Bool)
    (x : EighNode F) (y : Option (EighNode F)) :
    MeasurableSet {ω | eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y} := by
  induction a generalizing x ζ with
  | nil =>
    simp only [eighNodeAt]
    exact MeasurableSet.const _
  | cons b a ih =>
    -- the computed shift and leading blocks: countable range and measurable fibres
    have hκc : (Set.range fun ω => eighSampleKey M x (ζ [] ω)).Countable :=
      (countable_range_eighSampleKey hunif hnormal N x).mono (by
        rintro _ ⟨ω, rfl⟩
        exact ⟨_, rfl⟩)
    have hκm : ∀ t, MeasurableSet ((fun ω => eighSampleKey M x (ζ [] ω)) ⁻¹' {t}) := by
      intro t
      have : (fun ω => eighSampleKey M x (ζ [] ω)) ⁻¹' {t} =
          {ω | M.unif (M.div x.R (M.ofNat x.ℓ)) (ζ [] ω).1 = t.1} ∩ ⋂ b, ⋂ i, ⋂ j,
            {ω | M.normal (leadingBlock x.k ((ζ [] ω).2 b) i j) = t.2 b i j} := by
        ext ω
        simp only [eighSampleKey, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Set.mem_ofPred_eq, Prod.ext_iff, funext_iff (β := fun _ : Bool => _),
          ← Matrix.ext_iff, Matrix.map_apply]
      rw [this]
      refine ((hunifm _ t.1).preimage (measurable_fst.comp (hζ []))).inter
        (MeasurableSet.iInter fun b => MeasurableSet.iInter fun i =>
          MeasurableSet.iInter fun j => ?_)
      by_cases h : (i : ℕ) < N ∧ (j : ℕ) < N
      · simp only [leadingBlock, Matrix.of_apply, dif_pos h]
        have := hζ []
        exact (hnormalm _).preimage (by fun_prop)
      · simp only [leadingBlock, Matrix.of_apply, dif_neg h]
        exact MeasurableSet.const _
    -- the child: countable range and measurable fibres
    set C := fun ω => eighChild M N signFuel R₀ β x (ζ [] ω) b
    have hCm : ∀ z, MeasurableSet (C ⁻¹' {z}) := by
      intro z
      have : C ⁻¹' {z} = (fun ω => eighSampleKey M x (ζ [] ω)) ⁻¹'
          {t | ∃ s, eighSampleKey M x s = t ∧ eighChild M N signFuel R₀ β x s b = z} := by
        ext ω
        refine ⟨fun h => ⟨ζ [] ω, rfl, h⟩, ?_⟩
        rintro ⟨s, hs, hz⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, C, ← hz]
        exact eighChild_eq_of_eighSampleKey_eq x hs.symm b
      rw [this]
      exact measurableSet_preimage_of_countable_range_fibres hκc hκm _
    have hCc : (Set.range C).Countable := by
      refine (countable_range_eighNodeAt hunif hnormal N signFuel R₀ β [b] x).mono ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨fun _ => ζ [] ω, by simp [eighNodeAt, C]⟩
    -- the node below the child
    have : {ω | eighNodeAt M N signFuel R₀ β (b :: a) x (fun b => ζ b ω) = y} =
        ⋃ z ∈ Set.range C, C ⁻¹' {z} ∩ {ω | z.bind (fun y' =>
          eighNodeAt M N signFuel R₀ β a y' fun a' => ζ (b :: a') ω) = y} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_range, exists_prop]
      constructor
      · exact fun h => ⟨C ω, ⟨ω, rfl⟩, rfl, h⟩
      · rintro ⟨z, -, hz, h⟩
        rw [← hz] at h
        exact h
    rw [this]
    refine MeasurableSet.biUnion hCc fun z _ => (hCm z).inter ?_
    cases z with
    | none => exact MeasurableSet.const (none = y)
    | some y' => exact ih (fun a' => hζ _) y'

/-- The node at a path depends on the samples only at the proper prefixes of the path. -/
private lemma eighNodeAt_eq_of_forall_lt_length {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} (a : List Bool) (x : EighNode F)
    {s s' : List Bool → EighSample ℝ ℂ N} (h : ∀ i < a.length, s (a.take i) = s' (a.take i)) :
    eighNodeAt M N signFuel R₀ β a x s = eighNodeAt M N signFuel R₀ β a x s' := by
  induction a generalizing x s s' with
  | nil => rfl
  | cons b a ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_zero] at h0
    simp only [eighNodeAt, h0]
    congr 1
    funext y
    exact ih y fun i hi => h (i + 1) (by simpa using hi)

/-- **The node at a path is independent of its own sample**: let the machine's samplers have
measurable
fibres and countable ranges (`M.unif c` for every stored scale $c$, and `M.normal`), and let the
ideal samples $(\zeta_b)_b$ be measurable and mutually independent. Then for every path $a$, root
and value $y$ the event that the node at the path $a$ is $y$ is
independent of $\zeta_a$. No printed source; [Shah2024, proof of Theorem 4.2] uses it implicitly
("Event I ... $c'$ is sampled from a density bounded by $\ell/2R$"). -/
theorem indepFun_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (hind : iIndepFun ζ μ)
    (a : List Bool) (x : EighNode F) (y : Option (EighNode F)) :
    IndepFun (fun ω => eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y) (ζ a) μ := by
  -- the proper prefixes of `a`
  set S : Finset (List Bool) := (Finset.range a.length).image fun i => a.take i
  have haS : a ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi he
    have := congrArg List.length he
    simp only [List.length_take] at this
    omega
  have hST := hind.indepFun_finset S {a} (Finset.disjoint_singleton_right.mpr haS) hζ
  -- the samples on `S`, extended by a default value
  let ext : (S → EighSample ℝ ℂ N) → List Bool → EighSample ℝ ℂ N :=
    fun t c => if h : c ∈ S then t ⟨c, h⟩ else default
  have hext : ∀ c, Measurable fun t => ext t c := by
    intro c
    by_cases h : c ∈ S
    · simp only [ext, dif_pos h]
      exact measurable_pi_apply _
    · simp only [ext, dif_neg h]
      exact measurable_const
  have hφ : Measurable fun t => eighNodeAt M N signFuel R₀ β a x (ext t) = y :=
    measurableSet_setOfPred.mp
      (measurableSet_eighNodeAt_eq hunifm hunif hnormalm hnormal (ζ := fun c t => ext t c)
        hext a x y)
  have hψ : Measurable fun t : ({a} : Finset (List Bool)) → EighSample ℝ ℂ N =>
      t ⟨a, Finset.mem_singleton_self a⟩ :=
    measurable_pi_apply _
  convert hST.comp hφ hψ using 1
  · funext ω
    simp only [Function.comp]
    congr 1
    refine eighNodeAt_eq_of_forall_lt_length a x fun i hi => ?_
    have hi' : a.take i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)
    simp only [ext, dif_pos hi']
  · rfl

/-- The node at `a ++ [b]` is the child on side `b` of the node at `a`. -/
theorem eighNodeAt_append_singleton {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) (b : Bool) :
    ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample Su Sg N),
      eighNodeAt M N signFuel R₀ β (a ++ [b]) x s =
        (eighNodeAt M N signFuel R₀ β a x s).bind fun y => eighChild M N signFuel R₀ β y (s a) b
  | [], x, s => by simp [eighNodeAt]
  | c :: a, x, s => by
    simp only [List.cons_append, eighNodeAt, Option.bind_assoc]
    congr 1; funext y
    exact eighNodeAt_append_singleton M N signFuel R₀ β b a y _

/-- The samples at which a node splits form a measurable set: the split depends on the sample only
through the computed shift, which has countable range and measurable fibres. -/
theorem measurableSet_setOf_eighStep_isSplit {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable) (N signFuel : ℕ) (R₀ β : F) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ) :
    MeasurableSet {s : EighSample ℝ ℂ N | (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit} := by
  have hK : ∀ s : EighSample ℝ ℂ N, (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit ↔
      ¬ k ≤ 1 ∧ ¬ M.le R (M.mul ε R₀) = true ∧
        min k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift (newtonSchulzSign M β
          (M.mul (M.ofNat 2) R) signFuel (M.hermShift A (M.unif (M.div R (M.ofNat ℓ)) s.1)))
          (M.neg M.one)) (M.ofNat 2))) (M.div M.one (M.ofNat 2)))) ≠ k ∧
        min k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift (newtonSchulzSign M β
          (M.mul (M.ofNat 2) R) signFuel (M.hermShift A (M.unif (M.div R (M.ofNat ℓ)) s.1)))
          (M.neg M.one)) (M.ofNat 2))) (M.div M.one (M.ofNat 2)))) ≠ 0 := by
    intro s
    simp only [eighStep]
    split_ifs <;> simp only [EighStep.IsSplit] <;> tauto
  have hdep : ∀ s s' : EighSample ℝ ℂ N,
      M.unif (M.div R (M.ofNat ℓ)) s.1 = M.unif (M.div R (M.ofNat ℓ)) s'.1 →
      ((eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit ↔
        (eighStep M N signFuel R₀ β A R ε ℓ s').IsSplit) := by
    intro s s' h
    rw [hK, hK, h]
  have heq : {s : EighSample ℝ ℂ N | (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit} =
      ⋃ z ∈ {z | ∃ s : EighSample ℝ ℂ N, M.unif (M.div R (M.ofNat ℓ)) s.1 = z ∧
        (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit},
        Prod.fst ⁻¹' (M.unif (M.div R (M.ofNat ℓ)) ⁻¹' {z}) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    exact ⟨fun h => ⟨_, ⟨s, rfl, h⟩, rfl⟩,
      fun ⟨z, ⟨s', hs', h'⟩, hz⟩ => (hdep s s' (hz.trans hs'.symm)).2 h'⟩
  rw [heq]
  refine MeasurableSet.biUnion ((hunifc (M.div R (M.ofNat ℓ))).mono ?_) fun z _ =>
    measurable_fst (hunifm (M.div R (M.ofNat ℓ)) z)
  rintro _ ⟨s, rfl, -⟩
  exact ⟨s.1, rfl⟩

end NLAlib
