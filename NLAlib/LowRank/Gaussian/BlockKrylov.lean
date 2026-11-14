/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.LowRank.Gaussian.Filter
public import NLAlib.LowRank.Structural.BlockKrylov
import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
import NLAlib.ForMathlib.RingTheory.Polynomial.Chebyshev

/-!
# Gapped bounds for randomized block Krylov and subspace iteration

Expected errors of randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$
and of randomized subspace iteration with $p$ power steps,
$\mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})$, for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, in terms of the relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ (`NLAlib.singularGapRatio A h t`) between
the last singular value $\sigma_h$ of the head, $h + 1 = r$, and a tail index $t \ge r$ with
$t + 2 \le \ell$:
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
and the same with $e^{-8p\gamma}$ for subspace iteration; likewise in the Frobenius norm, in every
quadratic unitarily invariant norm, and for the late-truncated outputs
$\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r$ with the same right sides (reverse
Eckart–Young and Gu's projected form). These are Tropp and Webber's gapped bounds at an even number
$m = 2q$, respectively $m = 2p + 2$, of matrix products. The RBKI bounds come from the filtered
range finder (`NLAlib.LowRank.Gaussian.Filter`) at the Chebyshev filter
$T_{q-1}(2x/\sigma_t^2 - 1)$, of degree $q - 1$, through
`NLAlib.singularValues_sub_rbki_le_of_degree_lt`.

## Main results

* `NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, and the
  Gram form in the `NLAlib.SymmetricGauge` namespace: RBKI.
* `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, and
  the Gram form: RSI.
* `NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  and their RSI twins: the late-truncated outputs.
* the asymptotic forms of these eight spectral and Frobenius bounds at a positive gap $\gamma$:
  depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ for RBKI and
  $O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps for RSI give relative error
  $1 + \varepsilon$; named `NLAlib.exists_forall_` followed by the explicit name with
  `_le_singularGapRatio_` replaced by `_le_of_singularGapRatio_pos_` (their threshold
  arithmetic is in `NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean`).

The integrability companions are law-free, in `NLAlib.LowRank.Random.RangeFinder`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}


/-! ### Shared reductions -/

/-- The filtered range finder in expectation, Gram form, with the constant $(a/c)^2$ replaced by
any $K$ that dominates it in front of the tail, and the head index $r'$ replaced by any $r$ with
the same truncation. -/
private theorem integral_gram_sub_rsvd_aeval_le (Φ : SymmetricGauge) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r' r t : ℕ}
    (hr' : truncatedSVD A r' = truncatedSVD A r) (hrt : r' ≤ t) (ht : t + 2 ≤ Fintype.card l)
    {c a K : ℝ} (hc : 0 < c) (hhead : ∀ i < r', c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a)
    (hK : (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
      K * frobNorm (A - truncatedSVD A t) ^ 2) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (aeval (Aᴴ * A) f * X ω))ᴴ *
        (A - rsvd A (aeval (Aᴴ * A) f * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * K * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h := Φ.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix
    A hX f hrt ht hc hhead htail
  rw [hr'] at h
  refine h.trans (add_le_add le_rfl ?_)
  have hτ := natCast_div_sub_sub_one_nonneg (K := ℝ) ht
  calc Φ (Finsupp.single 0 1) * (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        frobNorm (A - truncatedSVD A t) ^ 2
      = Φ (Finsupp.single 0 1) * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          ((a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2) := by ring
    _ ≤ Φ (Finsupp.single 0 1) * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          (K * frobNorm (A - truncatedSVD A t) ^ 2) := by gcongr
    _ = _ := by ring

/-- RBKI beats every polynomial filter of degree below $q$ in expectation, Gram form. -/
private theorem integral_gram_sub_rbki_le_sub_rsvd_aeval (Φ : SymmetricGauge) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {q : ℕ} {f : ℝ[X]} (hf : f.degree < q) :
    ∫ ω, Φ.matrixNorm ((A - rbki A (X ω) q)ᴴ * (A - rbki A (X ω) q)) ∂μ ≤
      ∫ ω, Φ.matrixNorm ((A - rsvd A (aeval (Aᴴ * A) f * X ω))ᴴ *
        (A - rsvd A (aeval (Aᴴ * A) f * X ω))) ∂μ := by
  have := hX.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => aeval (Aᴴ * A) f * X ω) μ :=
    (measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable
  refine integral_mono (Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rbki A hX.aemeasurable q)
    (Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd A hmeas) fun ω => ?_
  refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
  rw [singularValues_conjTranspose_mul_self, singularValues_conjTranspose_mul_self]
  exact pow_le_pow_left₀ (singularValues_nonneg _ _)
    (singularValues_sub_rbki_le_of_degree_lt A (X ω) hf i) 2

/-- The late-truncated randomized SVD at any test matrix $\mathbf{Y}$ whose sketch range contains
that of the filtered sketch, in expectation, Frobenius norm: Gu's projected form and head capture
in expectation. -/
private theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le {k : Type*} [Fintype k]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X])
    {Y : Ω → Matrix n k ℝ} (hY : AEMeasurable Y μ)
    (hrange : ∀ ω, LinearMap.range (A * aeval (Aᴴ * A) f * X ω).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) {r' r t : ℕ}
    (hr' : truncatedSVD A r' = truncatedSVD A r) (hrt : r' ≤ t) (ht : t + 2 ≤ Fintype.card l)
    {c a K : ℝ} (hc : 0 < c) (hhead : ∀ i < r', c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a)
    (hK : (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
      K * frobNorm (A - truncatedSVD A t) ^ 2) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (Y ω)) r) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        K * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  have hH :=
    integral_frobNorm_one_sub_rangeProjector_mul_truncatedSVD_sq_le_of_hasLaw_gaussianMatrix A hX f
      hrt ht hc hhead htail
  rw [hr'] at hH
  have hint := integrable_frobNorm_one_sub_rangeProjector_mul_sq (A * aeval (Aᴴ * A) f)
    (truncatedSVD A r) hX.aemeasurable
  have hpt : ∀ ω, frobNorm (A - truncatedSVD (rsvd A (Y ω)) r) ^ 2 ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ^ 2 := by
    intro ω
    refine (frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add A (Y ω) r).trans
      (add_le_add le_rfl (pow_le_pow_left₀ (frobNorm_nonneg _) ?_ 2))
    have h := (lpGauge 2).matrixNorm_le_of_singularValues_le
      (singularValues_one_sub_rangeProjector_mul_le_of_range_le (hrange ω) (truncatedSVD A r))
    rwa [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, Matrix.sub_mul, Matrix.one_mul] at h
  have hI : Integrable (fun ω => frobNorm (A - truncatedSVD A r) ^ 2 +
      frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ^ 2) μ :=
    (integrable_const _).add hint
  refine (integral_mono (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hY r) hI hpt).trans ?_
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  refine add_le_add le_rfl (hH.trans ?_)
  have hτ := natCast_div_sub_sub_one_nonneg (K := ℝ) ht
  calc (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        frobNorm (A - truncatedSVD A t) ^ 2
      = ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          ((a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2) := by ring
    _ ≤ ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          (K * frobNorm (A - truncatedSVD A t) ^ 2) := by gcongr
    _ = _ := by ring

/-- The spectral twin of the previous bound, by reverse Eckart–Young in expectation. -/
private theorem integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le {k : Type*} [Fintype k]
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X])
    {Y : Ω → Matrix n k ℝ} (hY : AEMeasurable Y μ)
    (hrange : ∀ ω, LinearMap.range (A * aeval (Aᴴ * A) f * X ω).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) {r' r t : ℕ}
    (hr' : truncatedSVD A r' = truncatedSVD A r) (hrt : r' ≤ t) (ht : t + 2 ≤ Fintype.card l)
    {c a K : ℝ} (hc : 0 < c) (hhead : ∀ i < r', c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a)
    (hK : (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
      K * frobNorm (A - truncatedSVD A t) ^ 2) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A (Y ω)) r) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        K * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have := hX.isProbabilityMeasure
  have h1 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le A hX f hY hrange hr' hrt ht
    hc hhead htail hK
  have h2 := integral_specNorm_sub_truncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le A hY r
  linarith

/-! ### The filters -/

omit [DecidableEq n] in
/-- The head bound of `exists_rbki_filter`: for $\sigma_t > 0$ and $i \le h \le t$, the
Chebyshev filter has $\lvert T_{q-1}(2\sigma_i^2/\sigma_t^2 - 1)\rvert \ge
\tfrac12 e^{4(q-1)\sqrt\gamma}$, with $\gamma$ the gap ratio of $h$ and $t$. -/
private theorem exp_div_two_le_abs_eval_T_comp (A : Matrix m n ℝ) {h t q i : ℕ} (hq : 1 ≤ q)
    (hσ : 0 < singularValues A t) (hht : h ≤ t) (hih : i ≤ h) :
    Real.exp (4 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) / 2 ≤
      |((Polynomial.Chebyshev.T ℝ ((q - 1 : ℕ) : ℤ)).comp
        (C (2 / singularValues A t ^ 2) * Polynomial.X - 1)).eval (singularValues A i ^ 2)| := by
  set σt := singularValues A t
  set γ := singularGapRatio A h t
  have hσh : σt ≤ singularValues A h := singularValues_antitone A hht
  have hγ0 : 0 ≤ γ := singularGapRatio_nonneg A hht
  have hγ1 : γ < 1 := by
    rw [show γ = (singularValues A h - σt) / (singularValues A h + σt) from rfl,
      div_lt_one (by linarith)]
    linarith
  have hratio : (1 + γ) / (1 - γ) = singularValues A h / σt := by
    have hs : singularValues A h + σt ≠ 0 := by linarith
    have h1 : 1 + γ = 2 * singularValues A h / (singularValues A h + σt) := by
      rw [show γ = (singularValues A h - σt) / (singularValues A h + σt) from rfl]
      field_simp
      ring
    have h2 : 1 - γ = 2 * σt / (singularValues A h + σt) := by
      rw [show γ = (singularValues A h - σt) / (singularValues A h + σt) from rfl]
      field_simp
      ring
    rw [h1, h2]
    field_simp
  have hσi : singularValues A h ≤ singularValues A i := singularValues_antitone A hih
  have hx : 2 / σt ^ 2 * singularValues A i ^ 2 - 1 =
      2 * (singularValues A i / σt) ^ 2 - 1 := by
    rw [div_pow]; ring
  have h1h : 1 ≤ singularValues A h / σt := by rw [le_div_iff₀ hσ]; linarith
  have hhi : singularValues A h / σt ≤ singularValues A i / σt := by gcongr
  have hmono := Polynomial.Chebyshev.monotoneOn_eval_T_real (2 * (q - 1)) h1h
    (h1h.trans hhi) hhi
  have hgrowth := Polynomial.Chebyshev.exp_mul_sqrt_div_two_le_eval_T_real (2 * (q - 1)) hγ0 hγ1
  rw [hratio] at hgrowth
  have hT : (Polynomial.Chebyshev.T ℝ (((2 * (q - 1) : ℕ) : ℤ))).eval
      (singularValues A i / σt) =
      (Polynomial.Chebyshev.T ℝ ((q - 1 : ℕ) : ℤ)).eval
        (2 * (singularValues A i / σt) ^ 2 - 1) := by
    rw [← Polynomial.Chebyshev.eval_T_two_mul]
    push_cast
    rfl
  have hexp : Real.exp (2 * ((2 * (q - 1) : ℕ) : ℝ) * Real.sqrt γ) =
      Real.exp (4 * ((q : ℝ) - 1) * Real.sqrt γ) := by
    congr 1
    push_cast [Nat.cast_sub hq]
    ring
  rw [hexp] at hgrowth
  simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]
  rw [hx, ← hT]
  exact (hgrowth.trans hmono).trans (le_abs_self _)

omit [DecidableEq n] in
/-- A Chebyshev filter of every degree: for a real matrix $\mathbf{A}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ and a degree $d$, there are a real polynomial $f$ of degree
at most $d$ and constants $c > 0$ and $a$ with $\lvert f(\sigma_i^2) \rvert \ge c$ for $i < r$,
$\lvert f \rvert \le a$ on $[0, \sigma_t^2]$, and
$(a/c)^2 \le 4e^{-8d\sqrt{\gamma}}$, where
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ (zero when $\sigma_h = 0$). For
$\sigma_t > 0$ the filter is $f(x) = T_d(2x/\sigma_t^2 - 1)$ with $a = 1$ and
$c = \tfrac12 e^{4d\sqrt{\gamma}}$; for $\sigma_t = 0 < \sigma_h$ it is $x^d$, and for
$\sigma_h = 0$ it is $1$. -/
theorem exists_degree_lt_div_sq_le_exp_singularGapRatio (A : Matrix m n ℝ) {h r t : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt (singularGapRatio A h t)) := by
  have hht : h ≤ t := by omega
  rcases (singularValues_nonneg A t).eq_or_lt with hσ | hσ
  · rcases (singularValues_nonneg A h).eq_or_lt with hσh | hσh
    · -- $\sigma_h = \sigma_t = 0$: the gap ratio is zero and the constant filter does.
      refine ⟨1, by rw [degree_one]; exact_mod_cast Nat.succ_pos d, 1, 1, one_pos,
        fun i _ => by simp, fun x _ => by simp, ?_⟩
      simp [singularGapRatio, ← hσ, ← hσh]
    · -- $\sigma_t = 0 < \sigma_h$: the power $x^d$ vanishes on the tail for $d \ge 1$.
      refine ⟨Polynomial.X ^ d, by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_self d,
        (singularValues A h ^ 2) ^ d, (0 : ℝ) ^ d, by positivity, fun i hi => ?_, fun x hx => ?_,
        ?_⟩
      · have hi' : singularValues A h ≤ singularValues A i :=
          singularValues_antitone A (by omega)
        rw [eval_pow, eval_X, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hσh.le hi' 2) d
      · rw [← hσ] at hx
        have hx0 : x = 0 := le_antisymm (by simpa using hx.2) hx.1
        simp [hx0]
      · rcases Nat.eq_zero_or_pos d with rfl | hd
        · norm_num
        · rw [zero_pow hd.ne', zero_div, zero_pow two_ne_zero]
          positivity
  set σt := singularValues A t
  set γ := singularGapRatio A h t
  refine ⟨(Polynomial.Chebyshev.T ℝ (d : ℤ)).comp (C (2 / σt ^ 2) * Polynomial.X - 1), ?_,
    Real.exp (4 * (d : ℝ) * Real.sqrt γ) / 2, 1, by positivity, ?_, ?_, ?_⟩
  · refine degree_le_natDegree.trans_lt ?_
    have h := Polynomial.Chebyshev.natDegree_T_comp_le (d : ℤ)
      (p := C (2 / σt ^ 2) * Polynomial.X - 1) (by compute_degree)
    rw [Int.natAbs_natCast] at h
    exact_mod_cast h.trans_lt (by omega)
  · intro i hi
    have h := exp_div_two_le_abs_eval_T_comp A (Nat.succ_pos d) hσ hht (i := i) (by omega)
    simpa using h
  · exact fun x hx => Polynomial.Chebyshev.abs_eval_T_comp_C_mul_X_sub_one_le _ (by positivity) hx
  · refine le_of_eq ?_
    rw [div_div_eq_mul_div, one_mul, div_pow, show -8 * (d : ℝ) * Real.sqrt γ =
      -(4 * (d : ℝ) * Real.sqrt γ) + -(4 * (d : ℝ) * Real.sqrt γ) by ring,
      Real.exp_add, Real.exp_neg]
    field_simp
    ring

omit [DecidableEq n] in
/-- **The Chebyshev filter of RBKI**: for $q \ge 1$, a head of $r = h + 1$ singular values and a
tail index $t \ge r$, there is a filter of degree below $q$ (the Chebyshev filter
$T_{q-1}(2x/\sigma_t^2 - 1)$ when $\sigma_t > 0$) with $(a/c)^2 \le 4e^{-8(q-1)\sqrt\gamma}$
in front of the tail. -/
private theorem exists_rbki_filter (A : Matrix m n ℝ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : 1 ≤ q) :
    ∃ f : ℝ[X], f.degree < q ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨f, hf, c, a, hc, hhead, htail, hK⟩ :=
    exists_degree_lt_div_sq_le_exp_singularGapRatio A hr hrt (q - 1)
  rw [Nat.sub_add_cancel hq] at hf
  rw [Nat.cast_sub hq, Nat.cast_one] at hK
  exact ⟨f, hf, c, a, hc, hhead, htail, mul_le_mul_of_nonneg_right hK (sq_nonneg _)⟩

omit [DecidableEq n] in
/-- **The power filter of RSI**: for a head of $r = h + 1$ singular values and a tail index
$t \ge r$, the filter $x^p$ meets the hypotheses of the filtered range finder with
$(a/c)^2 \le e^{-8p\gamma}$ in front of the tail, at the head index $r$ when $\sigma_h > 0$ and at
the rank of $\mathbf{A}$ otherwise, which has the same truncation. -/
private theorem exists_rsi_filter (A : Matrix m n ℝ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (p : ℕ) :
    ∃ r', truncatedSVD A r' = truncatedSVD A r ∧ r' ≤ t ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r', c ≤ |(Polynomial.X ^ p : ℝ[X]).eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |(Polynomial.X ^ p : ℝ[X]).eval x| ≤ a) ∧
      (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  have hht : h ≤ t := by omega
  have hσh : singularValues A t ≤ singularValues A h := singularValues_antitone A hht
  have htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2),
      |(Polynomial.X ^ p : ℝ[X]).eval x| ≤ (singularValues A t ^ 2) ^ p := fun x hx => by
    rw [eval_pow, eval_X, abs_of_nonneg (pow_nonneg hx.1 p)]
    exact pow_le_pow_left₀ hx.1 hx.2 p
  rcases (singularValues_nonneg A h).eq_or_lt with h0 | hpos
  · -- $\sigma_h = 0$: the head is the rank of $\mathbf{A}$ and the tail vanishes.
    have hrk : A.rank ≤ h := (singularValues_eq_zero_iff A).mp h0.symm
    have hF : A - truncatedSVD A t = 0 := by
      rw [truncatedSVD_of_singularValues_eq_zero A (le_antisymm (h0 ▸ hσh)
        (singularValues_nonneg A t)), sub_self]
    have hK : ∀ c a : ℝ, (a / c) ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 ≤
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          frobNorm (A - truncatedSVD A t) ^ 2 := fun _ _ => by simp [hF]
    refine ⟨A.rank, by rw [truncatedSVD_of_rank_le A le_rfl,
      truncatedSVD_of_rank_le A (by omega)], by omega, ?_⟩
    rcases Nat.eq_zero_or_pos A.rank with h0r | hposr
    · exact ⟨1, _, one_pos, fun i hi => by omega, htail, hK _ _⟩
    · have hk : 0 < singularValues A (A.rank - 1) :=
        (singularValues_pos_iff A).mpr (by omega)
      refine ⟨(singularValues A (A.rank - 1) ^ 2) ^ p, _, by positivity, fun i hi => ?_, htail,
        hK _ _⟩
      have hi' : singularValues A (A.rank - 1) ≤ singularValues A i :=
        singularValues_antitone A (by omega)
      rw [eval_pow, eval_X, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hk.le hi' 2) p
  · refine ⟨r, rfl, hrt, (singularValues A h ^ 2) ^ p, _, by positivity, fun i hi => ?_, htail,
      ?_⟩
    · have hi' : singularValues A h ≤ singularValues A i := singularValues_antitone A (by omega)
      rw [eval_pow, eval_X, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hpos.le hi' 2) p
    rcases (singularValues_nonneg A t).eq_or_lt with ht0 | htpos
    · simp [truncatedSVD_of_singularValues_eq_zero A ht0.symm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    set γ := singularGapRatio A h t
    have hγ0 : 0 ≤ γ := singularGapRatio_nonneg A hht
    have hγ1 : γ < 1 := by
      rw [show γ = (singularValues A h - singularValues A t) /
        (singularValues A h + singularValues A t) from rfl, div_lt_one (by linarith)]
      linarith
    -- $\sigma_t/\sigma_h = (1 - \gamma)/(1 + \gamma) \le e^{-2\gamma}$.
    have hratio : singularValues A t / singularValues A h ≤ Real.exp (-2 * γ) := by
      rw [← one_sub_singularGapRatio_div_one_add_singularGapRatio A hpos,
        show -2 * γ = -(2 * γ) by ring, Real.exp_neg,
        ← inv_div (1 + γ) (1 - γ)]
      exact inv_anti₀ (Real.exp_pos _) (Real.exp_two_mul_le_one_add_div_one_sub hγ0 hγ1)
    calc ((singularValues A t ^ 2) ^ p / (singularValues A h ^ 2) ^ p) ^ 2
        = (singularValues A t / singularValues A h) ^ (4 * p) := by
          rw [← div_pow, ← div_pow, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ Real.exp (-2 * γ) ^ (4 * p) := pow_le_pow_left₀ (by positivity) hratio _
      _ = Real.exp (-8 * (p : ℝ) * γ) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- The RBKI gapped bound, Gram form, proved before its spectral and Frobenius corollaries. -/
private theorem integral_gram_sub_rbki_le (Φ : SymmetricGauge) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, Φ.matrixNorm ((A - rbki A (X ω) q)ᴴ * (A - rbki A (X ω) q)) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) *
          (4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t))) *
            ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨f, hf, c, a, hc, hhead, htail, hK⟩ := exists_rbki_filter A hr hrt hq
  exact (integral_gram_sub_rbki_le_sub_rsvd_aeval Φ A hX hf).trans
    (integral_gram_sub_rsvd_aeval_le Φ A hX f rfl hrt ht hc hhead htail hK)

/-- The RSI gapped bound, Gram form, proved before its spectral and Frobenius corollaries. -/
private theorem integral_gram_sub_rsi_le (Φ : SymmetricGauge) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A ((Aᴴ * A) ^ p * X ω))ᴴ * (A - rsvd A ((Aᴴ * A) ^ p * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨r', hr', hr't, c, a, hc, hhead, htail, hK⟩ := exists_rsi_filter A hr hrt p
  have h := integral_gram_sub_rsvd_aeval_le Φ A hX (Polynomial.X ^ p) hr' hr't ht hc hhead htail hK
  rwa [aeval_X_pow] at h

/-! ### Randomized block Krylov iteration -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized block Krylov iteration, spectral norm**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
No positivity hypothesis: when $\sigma_t = 0$ the error is zero almost surely. The proof's
filter $T_{q-1}(2x/\sigma_t^2 - 1)$ is $T_{2(q-1)}(\sigma_i/\sigma_t)$ at $x = \sigma_i^2$, so
the tail factor it gives is
$T_{2(q-1)}((1 + \gamma)/(1 - \gamma))^{-2} =
\operatorname{sech}^2(4(q-1)\operatorname{artanh}\sqrt{\gamma}) \le
\operatorname{sech}^2(4(q-1)\sqrt{\gamma}) =
4e^{-8(q-1)\sqrt{\gamma}}/(1 + e^{-8(q-1)\sqrt{\gamma}})^2$; every RBKI bound of this file drops
the factor $(1 + e^{-8(q-1)\sqrt{\gamma}})^2 \le 4$, which tends to $1$
(docs/contributing/statements.md §2
rule 7).
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.2 (RBKI)], at $p = \infty$; there with $m$ products and the exponent
$4(m - 2)\sqrt{\gamma}$, indices from $1$ ($\sigma_r$, $\sigma_s$ for our $\sigma_h$, $\sigma_t$),
$k \ge s + 1$ for our $t + 2 \le \ell$; here $m = 2q$ (odd $m$ is not covered).
Result: rbki-gapped-error -/
theorem integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h := integral_gram_sub_rbki_le (lpGauge ⊤) A hX hr hrt ht hq
  simp only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul, specNorm_sub_truncatedSVD] at h
  exact h

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized block Krylov iteration, Frobenius norm**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$ singular
values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The spectral form is
`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.2 (RBKI)], at $p = 2$; there with $m = 2q$ products.
Result: rbki-gapped-error -/
theorem integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, frobNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h := integral_gram_sub_rbki_le (lpGauge 1) A hX hr hrt ht hq
  simp only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul] at h
  exact h

-- The declaration name alone, with its `SymmetricGauge` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized block Krylov iteration, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$ singular values, a
tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, in every unitarily invariant norm
$\|\cdot\|_{\Phi}$,
$$\mathbb{E}\bigl\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)\bigr\|_{\Phi} +
\Phi(\mathbf{e}_0)\,4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\mathbf{E} = \mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$: every quadratic
unitarily invariant norm, squared Schatten norms for $p \ge 2$ included ($\Phi(\mathbf{e}_0) = 1$).
[TroppWebber2023, Theorem 9.2 (RBKI)]; there for Schatten $2 \le p \le \infty$ and $m = 2q$.
Result: rbki-gapped-error -/
theorem
SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rbki_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, Φ.matrixNorm ((A - rbki A (X ω) q)ᴴ * (A - rbki A (X ω) q)) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) *
          (4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t))) *
            ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 :=
  integral_gram_sub_rbki_le Φ A hX hr hrt ht hq

/-! ### Randomized subspace iteration -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized subspace iteration, spectral norm**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular values, a
tail index $t \ge r$ with $t + 2 \le \ell$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h +
\sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_2^2 \le \sigma_r(\mathbf{A})^2 + e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
At $p = 0$ it is the bound of the randomized SVD at rank $t$, weakened to $\sigma_r$.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.2 (RSI)], at $p = \infty$; there with $m$ products and the exponent
$4(m - 2)\gamma$; here $m = 2p + 2$ (odd $m$ is not covered).
Result: rsi-gapped-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h := integral_gram_sub_rsi_le (lpGauge ⊤) A hX hr hrt ht p
  simp only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul, specNorm_sub_truncatedSVD] at h
  exact h

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized subspace iteration, Frobenius norm**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular values, a
tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The spectral form is
`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Theorem 9.2 (RSI)], at $p = 2$; there with $m = 2p + 2$ products.
Result: rsi-gapped-error -/
theorem integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, frobNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h := integral_gram_sub_rsi_le (lpGauge 1) A hX hr hrt ht p
  simp only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul] at h
  exact h

-- The declaration name alone, with its `SymmetricGauge` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized subspace iteration, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular values, a
tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, in every unitarily invariant norm
$\|\cdot\|_{\Phi}$,
$$\mathbb{E}\bigl\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)\bigr\|_{\Phi} +
\Phi(\mathbf{e}_0)\,e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\mathbf{E} = \mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})$: every quadratic unitarily invariant norm,
squared Schatten norms for $p \ge 2$ included ($\Phi(\mathbf{e}_0) = 1$).
[TroppWebber2023, Theorem 9.2 (RSI)]; there for Schatten $2 \le p \le \infty$ and $m = 2p + 2$.
Result: rsi-gapped-error -/
theorem
SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A ((Aᴴ * A) ^ p * X ω))ᴴ * (A - rsvd A ((Aᴴ * A) ^ p * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 :=
  integral_gram_sub_rsi_le Φ A hX hr hrt ht p

/-! ### The late-truncated outputs -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized block Krylov iteration, spectral norm**: for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right side
of the untruncated form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
by reverse Eckart–Young
(`NLAlib.IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le`) and Gu's projected
form. [TroppWebber2023, §9.1, remark after Theorem 9.2]; [Gu2015, Theorem 3.4]; there stated
without a proof.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
Result: rbki-gapped-error -/
theorem integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨f, hf, c, a, hc, hhead, htail, hK⟩ := exists_rbki_filter A hr hrt hq
  exact integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le A hX f
    ((measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable hX.aemeasurable)
    (fun ω => range_mul_aeval_mul_le_range_mul_blockKrylovMatrix A (Aᴴ * A) (X ω) hf) rfl hrt ht
    hc hhead htail hK

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized block Krylov iteration, Frobenius norm**: for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right side
of the untruncated form
(`NLAlib.integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
by Gu's projected form
(`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`) and head capture
in expectation. [TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
Result: rbki-gapped-error -/
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨f, hf, c, a, hc, hhead, htail, hK⟩ := exists_rbki_filter A hr hrt hq
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le A hX f
    ((measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable hX.aemeasurable)
    (fun ω => range_mul_aeval_mul_le_range_mul_blockKrylovMatrix A (Aᴴ * A) (X ω) hf) rfl hrt ht
    hc hhead htail hK

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized subspace iteration, spectral norm**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular
values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right side
of the untruncated form
(`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2 \le \sigma_r(\mathbf{A})^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: rsi-gapped-error -/
theorem
integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨r', hr', hr't, c, a, hc, hhead, htail, hK⟩ := exists_rsi_filter A hr hrt p
  exact integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le A hX (Polynomial.X ^ p)
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable)
    (fun ω => by rw [aeval_X_pow, Matrix.mul_assoc]; exact le_rfl) hr' hr't ht hc hhead htail hK

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized subspace iteration, Frobenius norm**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular
values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the rank-$r$ truncation keeps the right side
of the untruncated form
(`NLAlib.integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: rsi-gapped-error -/
theorem
integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  obtain ⟨r', hr', hr't, c, a, hc, hhead, htail, hK⟩ := exists_rsi_filter A hr hrt p
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le A hX (Polynomial.X ^ p)
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable)
    (fun ω => by rw [aeval_X_pow, Matrix.mul_assoc]; exact le_rfl) hr' hr't ht hc hhead htail hK

/-! ### Asymptotic forms -/

/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for randomized block
Krylov iteration with a gap**, spectral norm: there are absolute constants $C, \varepsilon_0 > 0$
such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$ blocks,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, whose tail
term is at most $4\lvert n \rvert^2e^{-8(q-1)\sqrt{\gamma}}\sigma_r(\mathbf{A})^2$; the proof takes
$C = 3$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (RBKI)]; there in explicit form.
Asymptotic:
NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rbki-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio A h t) ≤ q →
      ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤ (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t q ε hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one A h t)) hq
  have hexp :=
    integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX hr hrt ht hq1
  rw [← one_mul (singularValues A r ^ 2)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) (by norm_num) le_rfl
    (natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      hrt ht) hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for randomized block
Krylov iteration with a gap**, Frobenius norm: there are absolute constants $C, \varepsilon_0 > 0$
such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$ blocks,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, whose tail
term is at most $4\lvert n \rvert e^{-8(q-1)\sqrt{\gamma}}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$; the proof takes $C = 3$ and
$\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (RBKI)]; there in explicit form.
Asymptotic:
NLAlib.integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rbki-gapped-error -/
theorem
exists_forall_integral_frobNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio A h t) ≤ q →
      ∫ ω, frobNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t q ε hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one A h t)) hq
  have hexp :=
    integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX hr hrt ht hq1
  rw [← one_mul (frobNorm (A - truncatedSVD A r) ^ 2)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) (by norm_num) le_rfl
    ((natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      A hrt ht).trans (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
    hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for randomized subspace
iteration with a gap**, spectral norm: there are absolute constants $C, \varepsilon_0 > 0$ such
that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power steps,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_2^2 \le (1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, whose
tail term is at most $\lvert n \rvert^2e^{-8p\gamma}\sigma_r(\mathbf{A})^2$; the proof takes $C = 1$
and $\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (RSI)]; there in explicit form.
Asymptotic:
NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rsi-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio A h t ≤ p →
      ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t p ε hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX hr hrt
      ht p
  rw [← one_mul (singularValues A r ^ 2), ← one_mul (Real.exp _)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) zero_le_one (by norm_num)
    (natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      hrt ht) hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for randomized subspace
iteration with a gap**, Frobenius norm: there are absolute constants $C, \varepsilon_0 > 0$ such
that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power steps,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, whose
tail term is at most $\lvert n \rvert e^{-8p\gamma}\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$; the proof takes $C = 1$ and
$\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (RSI)]; there in explicit form.
Asymptotic:
NLAlib.integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rsi-gapped-error -/
theorem
exists_forall_integral_frobNorm_sub_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio A h t ≤ p →
      ∫ ω, frobNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t p ε hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX hr hrt
      ht p
  rw [← one_mul (frobNorm (A - truncatedSVD A r) ^ 2), ← one_mul (Real.exp _)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) zero_le_one (by norm_num)
    ((natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      A hrt ht).trans (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
    hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for truncated randomized
block Krylov iteration with a gap**, spectral norm: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a
head of $r = h + 1$ singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive
relative gap $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$0 < \varepsilon \le \varepsilon_0$ and $q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$
blocks,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 3$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rbki-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio A h t) ≤ q →
      ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t q ε hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one A h t)) hq
  have hexp :=
    integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX
      hr hrt ht hq1
  rw [← one_mul (singularValues A r ^ 2)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) (by norm_num) le_rfl
    (natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      hrt ht) hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for truncated randomized
block Krylov iteration with a gap**, Frobenius norm: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a
head of $r = h + 1$ singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive
relative gap $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$0 < \varepsilon \le \varepsilon_0$ and $q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$
blocks,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r
\|_{\mathsf{F}}^2 \le (1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 3$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rbki-gapped-error -/
theorem
exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio A h t) ≤ q →
      ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t q ε hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one A h t)) hq
  have hexp :=
    integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix A hX
      hr hrt ht hq1
  rw [← one_mul (frobNorm (A - truncatedSVD A r) ^ 2)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) (by norm_num) le_rfl
    ((natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      A hrt ht).trans (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
    hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for truncated randomized
subspace iteration with a gap**, spectral norm: there are absolute constants $C, \varepsilon_0 > 0$
such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power steps,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 1$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rsi-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio A h t ≤ p →
      ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t p ε hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
      A hX hr hrt ht p
  rw [← one_mul (singularValues A r ^ 2), ← one_mul (Real.exp _)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) zero_le_one (by norm_num)
    (natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq A
      hrt ht) hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for truncated randomized
subspace iteration with a gap**, Frobenius norm: there are absolute constants $C, \varepsilon_0 > 0$
such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power steps,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 1$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: rsi-gapped-error -/
theorem
exists_forall_integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → h + 1 = r → r ≤ t →
      t + 2 ≤ Fintype.card l → 0 < singularGapRatio A h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio A h t ≤ p →
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X h r t p ε hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le A (k := h) (by omega),
        singularValues_of_card_cols_le A (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
      A hX hr hrt ht p
  rw [← one_mul (frobNorm (A - truncatedSVD A r) ^ 2), ← one_mul (Real.exp _)] at hexp
  exact Real.le_add_mul_of_le_add_mul_exp hexp (sq_nonneg _) zero_le_one (by norm_num)
    ((natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      A hrt ht).trans (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)))
    hN hε hε₀ (by nlinarith)

end NLAlib
